cmake_minimum_required(VERSION 3.16)
project(acpidiff LANGUAGES CXX C)

# ---- Build settings ----
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)


if(CMAKE_C_COMPILER_ID MATCHES "GNU|Clang|AppleClang")
  add_compile_options(-g)
elseif(MSVC)
  add_compile_options(/Zi)
  add_link_options(/DEBUG)
endif()

option(USE_ACPICA_INTERNALS "Use ACPICA internal headers for AML and owner mapping" ON)

# Path to vendored ACPICA (git clone https://github.com/acpica/acpica)
# Override with -DACPICA_ROOT=/path/to/acpica
set(ACPICA_ROOT "${CMAKE_SOURCE_DIR}/vendor/acpica" CACHE PATH "Path to vendored ACPICA root")

# ---- Try system ACPICA via pkg-config; fall back to vendored build ----
include(CheckIncludeFile)

find_package(PkgConfig QUIET)
if(PkgConfig_FOUND)
  pkg_check_modules(ACPICA QUIET IMPORTED_TARGET acpica)
endif()

# Interface lib to normalize downstream linking
add_library(acpica_iface INTERFACE)

if(TARGET PkgConfig::ACPICA)
  # System-provided ACPICA
  target_link_libraries(acpica_iface INTERFACE PkgConfig::ACPICA)
  # Includes come from the pkg-config target
  message(STATUS "Using system ACPICA via pkg-config")
else()
  # Vendored ACPICA build (static)
  message(STATUS "Building vendored ACPICA from ${ACPICA_ROOT}")

  # Basic sanity: must have headers
  if(NOT EXISTS "${ACPICA_ROOT}/source/include/acpi.h")
    message(FATAL_ERROR "ACPICA headers not found at ${ACPICA_ROOT}/source/include. Set ACPICA_ROOT.")
  endif()

  # Source files: core + minimal Unix service layer
  file(GLOB_RECURSE ACPICA_CORE
       "${ACPICA_ROOT}/source/components/*.c")
  list(FILTER ACPICA_CORE EXCLUDE REGEX "/components/debugger/")
  list(FILTER ACPICA_CORE EXCLUDE REGEX "/components/disassembler/")
  list(FILTER ACPICA_CORE EXCLUDE REGEX "/components/resources/rsdump.c$")

  set(ACPICA_OSL
      "${ACPICA_ROOT}/source/os_specific/service_layers/osunixxf.c"
  )

  add_library(acpica_vendor STATIC ${ACPICA_CORE} ${ACPICA_OSL})
  set_target_properties(acpica_vendor PROPERTIES
    POSITION_INDEPENDENT_CODE ON
    OUTPUT_NAME "acpica_vendor"
  )

  target_include_directories(acpica_vendor
    PUBLIC
      "${ACPICA_ROOT}/source/include"
      "${ACPICA_ROOT}/source/include/platform"
  )

  target_compile_definitions(acpica_vendor
    PUBLIC
      ACPI_USE_SYSTEM_CLIBRARY
      ACPI_USE_DO_WHILE_0
      ACPI_USE_NATIVE_DIVIDE
      ACPI_USE_NATIVE_MATH64
      ACPI_USE_NATIVE_MEMORY_ALLOCATION
      ACPI_USE_NATIVE_ALLOCATE_ZERO_MEMORY
      ACPI_APPLICATION        # enable userland/application globals
  )

  if (CMAKE_C_COMPILER_ID MATCHES "GNU|Clang|AppleClang")
    target_compile_options(acpica_vendor PRIVATE -Wall -Wextra -Wpedantic)
  endif()

  target_link_libraries(acpica_iface INTERFACE acpica_vendor)
endif()

# ---- Tool ----
add_executable(acpidiff src/acpidiff.cpp)

# Always add vendored include path so internal headers resolve when enabled
target_include_directories(acpidiff PRIVATE
  "${ACPICA_ROOT}/source/include"
  "${ACPICA_ROOT}/source/include/platform"
)

target_link_libraries(acpidiff PRIVATE acpica_iface)

if(USE_ACPICA_INTERNALS)
  target_compile_definitions(acpidiff PRIVATE USE_ACPICA_INTERNALS=1)
endif()

if (CMAKE_CXX_COMPILER_ID MATCHES "GNU|Clang|AppleClang")
  target_compile_options(acpidiff PRIVATE -Wall -Wextra -Wpedantic -Wconversion -Wno-sign-conversion)
endif()

