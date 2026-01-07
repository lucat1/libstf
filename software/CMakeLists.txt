cmake_minimum_required(VERSION 3.16)
project(libstf VERSION 0.1.0)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Collect source files
file(GLOB_RECURSE SOURCES src/libstf/*.cpp)

# Create the library
add_library(libstf SHARED ${SOURCES})

# Find dependencies

# Only add Coyote as a subdirectory if we are installing it standalone
if(CMAKE_SOURCE_DIR STREQUAL CMAKE_CURRENT_SOURCE_DIR) 
    add_subdirectory(../coyote/sw coyote)
else()
    if(NOT TARGET Coyote)
        message(FATAL_ERROR "When libstf is a subproject, parent must provide Coyote")
    endif()
endif()

list(APPEND CMAKE_PREFIX_PATH "$ENV{HOME}/opt")
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_SOURCE_DIR}/cmake")
find_package(Jemalloc REQUIRED)

# Specify include directories
target_include_directories(libstf
    PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/src ${COYOTE_INCLUDE_DIRS} ${JEMALLOC_INCLUDE_DIRS}
)

target_link_libraries(libstf PRIVATE Coyote ${JEMALLOC_LIBRARIES})
