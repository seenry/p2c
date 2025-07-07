set(ROCQ_SRCS
 main.cpp options.cpp
# XXX These should be in a library.
${P4C_SOURCE_DIR}/test/gtest/helpers.cpp)
add_executable(rocq ${ROCQ_SRCS})
target_link_libraries(rocq ${P4C_LIBRARIES} ${P4C_LIB_DEPS})
add_dependencies(rocq frontend midend gtestp4c)
add_custom_target(
 linkrocq_out COMMAND ${CMAKE_COMMAND} -E create_symlink ${CMAKE_CURRENT_BINARY_DIR}/rocq
${P4C_BINARY_DIR}/rocq
COMMAND ${CMAKE_COMMAND} -E create_symlink ${P4C_BINARY_DIR}/p4include
${CMAKE_CURRENT_BINARY_DIR}/p4include
)
add_dependencies(p4c_driver linkrocq_out)