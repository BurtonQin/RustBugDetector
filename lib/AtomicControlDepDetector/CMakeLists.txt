add_library(AtomicControlDepDetector MODULE
        # List your source files here.
        AtomicControlDepDetector.cpp
        )

target_link_libraries(AtomicControlDepDetector CommonLib CFG)

# Use C++11 to compile our pass (i.e., supply -std=c++11).
target_compile_features(AtomicControlDepDetector PRIVATE cxx_range_for cxx_auto_type)

# LLVM is (typically) built with no C++ RTTI. We need to match that;
# otherwise, we'll get linker errors about missing RTTI data.
set_target_properties(AtomicControlDepDetector PROPERTIES
        COMPILE_FLAGS "-fno-rtti"
        )
