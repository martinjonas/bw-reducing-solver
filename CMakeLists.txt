cmake_minimum_required(VERSION 2.6)
project(formulaReducer)

SET(CMAKE_CXX_STANDARD 17)

#set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")

add_definitions(-std=c++0x)
file(GLOB FORMULAREDUCER_SRC
    "*.h"
    "*.cpp"
)

SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
SET(BUILD_SHARED_LIBRARIES OFF)
set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")


add_executable(formulaReducer ${FORMULAREDUCER_SRC})

set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -Wall")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -Wall")

find_library(LibZ3 z3 PATHS /usr/lib DOC "z3 library")

if(NOT LibZ3)
  message(FATAL_ERROR "Library libz3 required, but not found!")
endif(NOT LibZ3)

include_directories(${LibZ3_INCLUDE_DIRS})
set(LIBS ${LIBS} ${LibZ3})

find_package (Threads)

target_link_libraries(formulaReducer ${CMAKE_THREAD_LIBS_INIT})
target_link_libraries(formulaReducer ${LIBS})
