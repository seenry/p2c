# rocq — a Caracara IR backend for p4c

Lowers a P4 program to a `GeneralCaracaraProgramDef` s-expression, the `.ir`
format `~/proj/ir`'s `Shim.load_general_program` reads. The output goes to
stdout; the header allocation goes to stderr as `;` comments.

```
rocq [options] prog.p4 > prog.ir
```

Built as a p4c extension, so it is picked up automatically by CMake:

```
cd translation/p4c/build && make rocq
```

## Options beyond p4c's own

| | |
|---|---|
| `--table-entries FILE` | entries for tables the source does not populate itself |

Tofino-native programs need p4c's own flags as well:

```
rocq -O1 -D__TARGET_TOFINO__=1 -I <p4c>/backends/tofino/bf-p4c/p4include prog.p4
```

`-O1` matters for more than optimization: it enables the frontend's `Inline`
pass, which flattens a sub-parser into its caller. TNA's ingress parser applies
a `TofinoIngressParser` instance, and the IR parser is one flat FSM, so without
it the sub-parser is never seen.

### `--table-entries`

A table populated by the control plane has no entries in its source, and they
cannot be left to the control plane either: a `Ctrl` variable is seeded per
program (`CrVarLike.v`, `prefix ++ "ctrl_"`), so the two programs a comparison
is about would get unrelated configurations and the solver would satisfy "the
outputs differ" by handing them different tables. See `~/proj/ir` TODO.md 1.7.
So entries are supplied instead, one per line:

```
# <table> <key>... -> <action> [<arg>...]
ipv4_lpm 0x0a000101/32 -> ipv4_forward 0x000000000101 1
ipv4_lpm 0x0a000000/8  -> ipv4_forward 0x000000000303 3
ipv4_lpm 0/0           -> drop
```

A key is a number (exact), `v/n` (an lpm prefix of n bits), `v&&&m` (ternary),
or `*` (any). Numbers are decimal, or hex with `0x`. Names are the ones the
*source* uses — the frontend renames declarations, so a table written `calc`
arrives here as `calc_0`, and both spellings are accepted.

Entries are sorted by specificity, not file order: P4 resolves an lpm table by
longest prefix and a rule list resolves by order, so the sort is what makes the
two agree. `const entries` in the source needs no file and takes precedence.

## How a P4 program becomes a network

- **Parser** → one `ParserModule`. A state doing *n* things becomes a chain of
  *n* IR states, since a state carries one `ParserOp`.
- **Controls** → a chain of `TransformerModule`s, one per guarded statement
  group. Control flow lowers by **predication**: a P4 control is structured and
  acyclic, so the condition under which a statement runs is a static predicate,
  replicated into the rules that carry it. There is no program counter.
  Negation comes from rule order — only the first matching rule fires, so
  `P and not N` is `[(N, nop); (P, ops); (true, nop)]`.
- **A table** → one module of ordered rules, which is what a match-action unit
  already is.
- **Deparser** → one `DeparserModule`.

Two things are derived rather than stored:

- **`isValid()`** is read off the parser. A header is valid exactly when the
  parser reached a state that extracts it, which is a predicate over
  already-parsed fields. A header reachable several ways gives a *disjunction*,
  emitted as several rules with the same action. Only a **cycle** defeats this:
  the condition would be "on the nth time round" at a different cursor each
  time. `translation/tests/valid_merge*` pins the derived predicate against a
  hand-written one.
- **A boolean local** is a named condition, not a value. `bool v = h.isValid()`
  cannot be a Header holding a value — `CrVal` has no boolean, and validity is
  a predicate — so the name binds to the condition and `!v` negates it.

## What lowers today

p4lang/tutorials, 5 of 13 (`solution/` variants, with `--table-entries` where
the table is runtime-populated):

| Lowers | Blocked by |
|---|---|
| `basic`, `qos`, `ecn`, `basic_tunnel`, `multicast` | — |
| | `calc` — `lookahead<T>()` into a temporary, and a 3-key tuple select |
| | `firewall`, `load_balance` — a hash extern |
| | `mri`, `source_routing`, `link_monitor` — header stacks |
| | `flowcache` — cloning |
| | `p4runtime/advanced_tunnel` — `setValid`/`setInvalid`, and counters |

Princeton-Cabernet/p4-projects, 1 of 19 — `ConQuest/baseline`. Note when
surveying these that p4c aborts after 20 errors with an uncaught exception,
which looks like a crash and is not one; pass `--maxErrorCount 2000`. With
that, 18 of the 19 finish in 1–15s.

- **Nine are rejected by p4c itself**, before this backend sees anything:
  `Meta4/netassay_*` (×4), `PRECISION`, `RTT` and `SmartCookie-CRC` /
  `SmartCookie-HalfSipHash` fail type inference on `RegisterAction`'s index
  parameter, and `Fridge/UnbiasedRtt` needs headers a Python generator
  produces. `p4test` fails on all nine the same way.
- **Nine reach this backend:**

  | | errors | stops on |
  |---|---|---|
  | `ConQuest/baseline` | — | lowers |
  | `SipHash/halfsiphash24_ingressonly` | 3 | `setValid`/`setInvalid`, `Random` |
  | `SipHash/siphash24_ingressonly` | 3 | the same |
  | `SipHash/halfsiphash24_ingressegress` | 4 | the same, plus the egress pipeline |
  | `AES-tofino/aes_oneround` | 22 | `setValid`, an extern in `apply`, and 17 tables whose entries a Python generator produces |
  | `SmartCookie-AES` | 38 | as above |
  | `AES-tofino/aes_tworound` | 38 | as above |
  | `ONTAS/p4anony` | 56 | CRC externs in actions, assignments inside parser states |
  | `P40f/p40f_tofino` | 276 | its TCP-option parser assigns and calls inside parser states |

- **One does not terminate**: `AES.p4app/AES.p4`, still running after 150s.
  `p4test` alone does not finish it either, so the cost is plausibly upstream.

## Outstanding work

Roughly in order of value per unit of effort.

1. **`Random`** — a free input the two compared programs *share*, which is the
   right modelling for a relational check. Needs somewhere for a free value to
   come from, which is the same metadata-prefix work `standard_metadata`'s
   input fields need. Closes out the SipHash family bar validity.
2. **Extern calls in an `apply` block or an action.** Today only
   `mark_to_drop` is allowed. Recognising a `counter.count()` as a no-op with a
   warning would be wrong; recognising it as a `MemRegion` store would not.
   See `~/proj/ir` TODO.md 1.6.
3. **Assignments and calls inside parser states.** A `ParserOp` is an extract
   or a seek, so this is an IR limit rather than a backend gap — but it is 226
   of `p40f`'s 276 errors, so it is worth knowing what a `SetOp` would cost
   (`~/proj/ir` TODO.md 1.8 measures the validity half of that question).
4. **Tuple `select`** — desugars to a chain of action-free states, which
   `calc.p4` and several TNA parsers need.
5. **`lookahead<T>()` into a temporary**, the other half of `calc.p4`.
6. **The egress pipeline.** Only the first pipeline control is translated;
   `halfsiphash24_ingressegress` wants both. The package instantiation is also
   still unread, so ingress and egress are told apart by declaration order.
7. **`standard_metadata_t` input fields** are uninitialized rather than free.
   They are deliberately not zeroed — pinning `ingress_port` to 0 is a wronger
   lie than leaving it undefined — but they should be extracted from a
   metadata prefix ahead of the packet.
8. **A `--field-table` sidecar.** The header allocation goes to stderr as
   comments; written to a file it would make the `.ir` diffable and let a
   reader map header 7 back to `ipv4.flags`. It is also how you would check
   that two programs being compared agree about which uid means which field,
   which is a front-end obligation nothing currently verifies.

Blocked on the IR rather than on this backend: `setValid`/`setInvalid` and a
deparser that emits only valid headers (`~/proj/ir` TODO.md 1.8), a hash,
registers, header stacks, and cloning.

## Refused by name, and why

Each of these errors rather than producing wrong output. Half the value of a
front-end for a verification tool is failing where it cannot be faithful.

| | |
|---|---|
| `setValid` / `setInvalid` | the IR has no header validity bit, and a deparser emits unconditionally. `~/proj/ir` TODO.md 1.8 measures what fixing it would buy |
| `hash()` / `Hash<>` | no lowering; would have to be unrolled or made an uninterpreted function |
| `Register` / `RegisterAction` | should become `MemRegion` loads and stores — runtime-indexed and shared between the compared programs, which `State` is not |
| `Random` | should become a free input the two programs *share* |
| header stacks, `varbit` | no equivalent |
| `clone` / `resubmit` / `mirror`, `mcast_grp` | one packet in, one packet out |
| a runtime table with no supplied entries | see `--table-entries` above |
| tuple `select` | desugars to a chain of single-key states; not built yet |
| a disjunct that is itself negated | `(not A and not B) or (not C)` is not a rule list: a rule matches or it does not, and there is no trying the next disjunct |

## Tests

`translation/tests/run.sh`. The oracle is `EqCheck`, not a concrete run —
`run_net` seeds memory regions but not the read tape, so any program with a
parser rejects under it. Asking instead whether two lowerings of the same
computation agree for *every* input is both runnable and stronger.

Each pair is followed by a deliberately wrong variant, so a lowering that
quietly produced a constant could not pass. A `<name>.entries` or
`<name>.flags` sidecar is picked up automatically.
