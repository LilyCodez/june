# June
June is a compiled language that allows for low level programming.

```
import std.Sys;

main() {
    Sys.println("Hello from june!");
}
```

## Dependencies (building from source)

### Windows
* Must have `LLVM 14`, `clang`, `MSVC`, `cmake` and `make` installed.
* When compiling with `MSVC` you may need to set cmake's LLVM_DIR variable.

#### Building on Windows

On windows, when you use Visual Studio, you should just be able to compile the project.

### Linux
* Must have `LLVM 14`, `clang`, `gcc`, `cmake` and `make` installed.
* Tested with Ubuntu 20.04 with `gcc`

## Building on Linux

Run `cmake . && make`

This will produce a directory called `out` containing the `bin` and `lib` folders. The built `june` driver will be in `out/bin`.

### Running the june driver

When building the cmake sub-project `driver` it allows you to compile june projects from the terminal: ``june <sources> <options>``
To get help: ``june -help``

The driver will expect the environment variable ``JuneStdLibPath`` to be set. Simply set it to be the location of where the ``stdlib`` folder is at on your system. You can use the one provided in this repository under `./stdlib`

