# Makefile for the toZ3

# sources for toZ3
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/version.h.cmake"
  "${CMAKE_CURRENT_BINARY_DIR}/version.h" @ONLY)

set (TOZ3_SRCS
    toz3Options.cpp
    toz3Options.h
  codegen.cpp
  codegen.h
    main.cpp
    )
add_cpplint_files (${CMAKE_CURRENT_SOURCE_DIR} "${TOZ3_SRCS}")

#build_unified(TOZ3_SRCS)
add_executable(p4toz3 ${TOZ3_SRCS})
message (STATUS "libs ${P4C_LIBRARIES}")
message (STATUS "deps ${P4C_LIB_DEPS}")
# target_link_libraries (p4toz3 ${P4C_LIBRARIES} ${P4C_LIB_DEPS})
# target_link_libraries (p4toz3 ${P4C_LIBRARIES} ${P4C_LIB_DEPS})
target_link_libraries (p4toz3 ${P4C_LIBRARIES} ${P4C_LIB_DEPS})
add_dependencies(p4toz3 genIR frontend)
#add_dependencies(p4toz3 genIR frontend)

install(TARGETS p4toz3 RUNTIME DESTINATION ${P4C_RUNTIME_OUTPUT_DIRECTORY})


add_custom_target(linkp4toz3
  COMMAND ${CMAKE_COMMAND} -E create_symlink ${CMAKE_CURRENT_BINARY_DIR}/p4toz3 ${P4C_BINARY_DIR}/p4toz3
  COMMAND ${CMAKE_COMMAND} -E create_symlink ${P4C_BINARY_DIR}/p4include ${CMAKE_CURRENT_BINARY_DIR}/p4include
  COMMAND ${CMAKE_COMMAND} -E create_symlink ${P4C_BINARY_DIR}/p4_14include ${CMAKE_CURRENT_BINARY_DIR}/p4_14include
  )
add_dependencies(p4c_driver linkp4toz3)

