cmake_minimum_required(VERSION 2.6)
project(formulaReducer)

SET(CMAKE_CXX_STANDARD 17)
list(APPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake)

add_definitions(-std=c++0x)
file(GLOB FORMULAREDUCER_SRC
  "ExprSimplifier.*"
  "FormulaReducer.*"
  "FormulaStats.*"
  "FormulaTraverser.*"
  "Logger.*"
  "Solver.*"
  "SMTLIBInterpreter.*"
)

SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
SET(BUILD_SHARED_LIBRARIES OFF)
SET(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")

# required if linking to static library
add_definitions(-DANTLR4CPP_STATIC)

# using /MD flag for antlr4_runtime (for Visual C++ compilers only)
set(ANTLR4_WITH_STATIC_CRT OFF)
# add external build for antlrcpp
include(ExternalAntlr4Cpp)
# add antrl4cpp artifacts to project environment
include_directories(${ANTLR4_INCLUDE_DIRS})

find_package(ANTLR REQUIRED)

# Call macro to add lexer and grammar to your build dependencies.
antlr_target(SmtLibParser parser/smtlibv2-grammar/src/main/resources/SMTLIBv2.g4 VISITOR)

# include generated files in project environment
include_directories(${ANTLR_SmtLibParser_OUTPUT_DIR}/parser/smtlibv2-grammar/src/main/resources)

set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -Wall")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -Wall")

find_library(LibZ3 z3 PATHS /usr/lib DOC "z3 library")

if(NOT LibZ3)
  message(FATAL_ERROR "Library libz3 required, but not found!")
endif(NOT LibZ3)

include_directories(${LibZ3_INCLUDE_DIRS})
set(LIBS ${LIBS} ${LibZ3})

find_package(Boost COMPONENTS system filesystem REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
link_directories(${Boost_LIBRARY_DIR})

set(LIBS ${LIBS} ${Boost_LIBRARIES})

find_package (Threads)

find_package(OpenMP)
if (OPENMP_FOUND)
    set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${OpenMP_C_FLAGS}")
    set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
endif()

add_executable(formulaReducer main.cpp ${FORMULAREDUCER_SRC} ${ANTLR_SmtLibParser_CXX_OUTPUTS})
target_link_libraries(formulaReducer ${CMAKE_THREAD_LIBS_INIT})
target_link_libraries(formulaReducer ${LIBS} antlr4_static)
### CATCH ###

# Prepare "Catch" library for other executables
set(CATCH_INCLUDE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/tests/catch)
add_library(Catch INTERFACE)
target_include_directories(Catch INTERFACE ${CATCH_INCLUDE_DIR})

# Make test executable
set(TEST_SOURCES ${CMAKE_CURRENT_SOURCE_DIR}/tests/main.cpp)
add_executable(tests ${TEST_SOURCES} ${FORMULAREDUCER_SRC} ${ANTLR_SmtLibParser_CXX_OUTPUTS})
target_link_libraries(tests PUBLIC ${CMAKE_THREAD_LIBS_INIT} ${LIBS} antlr4_static Catch)

enable_testing()
add_test(NAME SimpleSAT COMMAND ./tests [simple-sat])
