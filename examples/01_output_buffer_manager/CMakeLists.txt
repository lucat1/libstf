cmake_minimum_required(VERSION 3.14)
project(libstf_output_buffer_manager VERSION 0.1.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_executable(output_buffer_manager src/main.cpp)

if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR)
    add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/../../coyote/sw coyote)
    add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/../../software/ libstf)
else()
    if(NOT TARGET libstf)
        message(FATAL_ERROR "When the output buffer manager example is a subproject, parent must provide libstf")
    endif()
endif()

target_link_libraries(output_buffer_manager PRIVATE Coyote libstf)
