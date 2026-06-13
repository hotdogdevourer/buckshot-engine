# BuckShot (Chess engine)

A lightweight, single-file chess engine written in C with multi-threading support and more.

## Features

- Magic bitboards
- PVS (Principal Variation Search) with aspiration windows
- Null-Move Pruning implemented with Dynamic R (3 + depth/6 + (eval-beta)/200)
- Much more.

## Compilation

Requires a C compiler with pthread support and the math library.

**Linux / macOS:**
```bash
gcc buckshot.c -o buckshot -lpthread -lm -O3
```

**Windows (MinGW):**
```bash
gcc buckshot.c -o buckshot -lpthread -lm -O3
```

## Usage

Run the executable and follow the interactive prompts to configure threads, difficulty, and search depth.

```bash
./buckshot
```

**Controls:**
- Input moves in standard algebraic notation (e.g., `e2 e4`).
- Select difficulty levels: Beginner (random), Easy (greedy), or Hard (depth search).

## Architecture

- **Board Representation**: 0x88-style array mapping.
- **Threading**: Uses thread-local storage for transposition tables to prevent race conditions.
- **Memory Management**: Configurable transposition table size via `TT_SIZE` macro to fit available RAM.

## License

**MIT Licensed**
This project is provided as-is for educational and development purposes.
Look into the LICENSE file in the project root directory for more licensing information.
