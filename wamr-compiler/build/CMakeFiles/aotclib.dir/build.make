# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.16

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /home/agent/Downloads/cmake-3.16.2-Linux-x86_64/bin/cmake

# The command to remove a file.
RM = /home/agent/Downloads/cmake-3.16.2-Linux-x86_64/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build

# Include any dependencies generated for this target.
include CMakeFiles/aotclib.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/aotclib.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/aotclib.dir/flags.make

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_3) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_4) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_5) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_6) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_7) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_8) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_9) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_10) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_11) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_12) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_13) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.s

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.o: CMakeFiles/aotclib.dir/flags.make
CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.o: /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_14) "Building C object CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.o"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.o   -c /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing C source to CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.i"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -E /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c > CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.i

CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling C source to assembly CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.s"
	/usr/bin/cc $(C_DEFINES) $(C_INCLUDES) $(C_FLAGS) -S /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c -o CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.s

# Object files for target aotclib
aotclib_OBJECTS = \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.o" \
"CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.o"

# External object files for target aotclib
aotclib_EXTERNAL_OBJECTS =

libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_compiler.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_aot_file.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_compare.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_const.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_control.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_conversion.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_exception.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_function.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_memory.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_numberic.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_parametric.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_emit_variable.c.o
libaotclib.a: CMakeFiles/aotclib.dir/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/core/iwasm/compilation/aot_llvm.c.o
libaotclib.a: CMakeFiles/aotclib.dir/build.make
libaotclib.a: CMakeFiles/aotclib.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_15) "Linking C static library libaotclib.a"
	$(CMAKE_COMMAND) -P CMakeFiles/aotclib.dir/cmake_clean_target.cmake
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/aotclib.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/aotclib.dir/build: libaotclib.a

.PHONY : CMakeFiles/aotclib.dir/build

CMakeFiles/aotclib.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/aotclib.dir/cmake_clean.cmake
.PHONY : CMakeFiles/aotclib.dir/clean

CMakeFiles/aotclib.dir/depend:
	cd /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build /home/agent/WASM/ssg-dynamic-apps/wamr-wasmpoc/wamr-compiler/build/CMakeFiles/aotclib.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/aotclib.dir/depend

