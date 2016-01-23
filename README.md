Sudoku Solver in Functional Languages
---

### Racket

* `solver.rkt` A naive searching and backtracking implementation.
* `solver-opt.rkt` An optimized searching and backtacking implementation, which will move to the unknown box that has the minimum number of possible choices.
* `amb-solver.rkt` Using `amb` non-deterministic operator to do searching and backtracking.

### Standard ML
	
* `solver-opt.sml` Similar with `solver-opt.rkt`, but using a list (as a queue) to save all decision nodes when searching, thus can find all solutions of the puzzle.
