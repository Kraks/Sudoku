(*
Sudoku Solver
Guannan Wei <guannan.wei@utah.edu>
*)

datatype Box = Just of int | Unknown of int list;
type Grid = Box list list;
datatype Result = InComplete of (unit -> Result) list
                | Success of Grid * ((unit -> Result) list);
exception NoSolution;

fun gridToString g =
  let fun aux (Just x) = Int.toString x
        | aux (Unknown _) = "_"
  in (String.concatWith "\n" (map (fn (l) => (String.concatWith " " (map aux l))) g)) ^ "\n" end;

val len = List.length;

fun ternaryEqual x y z = x = y andalso y = z;

fun update [] i ele = raise Empty
  | update (x::xs) 0 ele = ele::xs
  | update (x::xs) i ele = x::(update xs (i-1) ele);

fun partition step [] = []
  | partition step xs = if len(xs) <= step then [xs]
                        else List.take(xs, step)::(partition step (List.drop(xs, step)))

fun range stop step = List.tabulate(stop div step, fn x => x * step);

fun remove x [] = []
  | remove x (l as y :: ys) = if x = y then remove x ys else y::remove x ys

fun removeList [] ys = ys
  | removeList (x::xs) ys = removeList xs (remove x ys);

fun isolate [] = []
  | isolate (x::xs) = x::isolate(remove x xs);

fun min xs f =
  let fun aux [] i m = m
        | aux (x::xs) i m = if (f x) < (f (#2 m)) then aux xs (i+1) (i, x)
                            else aux xs (i+1) m
  in aux (tl xs) 0 (0, (f (hd xs))) end;

(************************)

fun gridGet g row col = List.nth(List.nth(g, row), col);

fun gridSet g row col ele = update g row (update (List.nth(g, row)) col ele);

fun getRow g i = List.nth(g, i);

fun getCol g i = map (fn row => List.nth(row, i)) g;

fun getBlock g m n row col =
  let fun aux row col = 
        let val rows = List.nth(partition n g, row)
        in List.concat(map (fn ln => List.nth(partition m ln, col)) rows) end
  in aux (row div n) (col div m) end;

fun eachBlocks g m n =
  let val rows = range (m*n) n
      val cols = range (m*n) m
  in List.concat(map (fn row => map (getBlock g m n row) cols) rows) end;

fun getUsedNums [] = []
  | getUsedNums ((Just x)::xs) = x::(getUsedNums xs)
  | getUsedNums (_::xs) = getUsedNums xs;

fun getConstraints grid m n row col =
  let val rowCons = getUsedNums(getRow grid row)
      val colCons = getUsedNums(getCol grid col)
      val blkCons = getUsedNums(getBlock grid m n row col)
  in isolate(List.concat [rowCons, colCons, blkCons]) end;

fun getPossibleNums grid m n row col =
  let val all = List.tabulate(m*n, fn x => x+1)
      val con = getConstraints grid m n row col
  in removeList con all end;

fun updateGrid grid m n = 
  let fun updateLine [] _ _ = []
        | updateLine ((Just x)::xs) row col = (Just x)::(updateLine xs row (col+1))
        | updateLine ((Unknown _)::xs) row col = 
            (Unknown (getPossibleNums grid m n row col))::(updateLine xs row (col+1))
      fun update [] _ = []
        | update (line::grid) row = (updateLine line row 0)::(update grid (row+1))
  in update grid 0 end;

fun isValid grid m n = 
  let fun sumOfBox [] = 0
        | sumOfBox ((Just x)::xs) = x + sumOfBox xs
        | sumOfBox (_::xs) = sumOfBox xs
      val sumOfRows = map sumOfBox grid
      val sumOfCols = map sumOfBox (map (getCol grid) (List.tabulate(len(grid), fn x => x)))
      val sumOfBlks = map sumOfBox (eachBlocks grid m n)
  in len(isolate(List.concat([sumOfRows, sumOfCols, sumOfBlks]))) = 1 end;

fun nextRowCol grid row col =
  let val sideLen = len(grid)
  in if (col+1) = sideLen then (row+1, 0) else (row, col+1) end;

fun isEnd m n row col = (m*n) = row andalso (0 = col);

fun solve grid m n x =
  let fun try grid (row, col) =
        if isEnd m n row col then Success(grid, [])
        else let val grid = updateGrid grid m n
             in case gridGet grid row col of 
                  Unknown choices => InComplete(map (fn c => fn() => let val grid = gridSet grid row col (Just c)
                                                                     in try grid (nextRowCol grid row col) end)
                                                                     choices)
                | Just _ => InComplete([fn () => try grid (nextRowCol grid row col)])
             end
      fun aux res [] = if len(res) = 0 then raise NoSolution else res
        | aux res (s::ss) = if len(res) = x then res
                            else case s() of 
                                   InComplete(others) => aux res (others@ss)
                                 | Success(grid, others) => aux (grid::res) (others@ss)

  in aux [] [fn () => try grid (0, 0)] end;

(*******************************)

fun transform g =
  let fun transLine [] = []
        | transLine (0::xs) = (Unknown [])::transLine xs
        | transLine (x::xs) = (Just x)::transLine xs
  in map transLine g end;

val grid = transform
            [[3,0,6, 5,0,8, 4,0,0],
             [5,2,0, 0,0,0, 0,0,0],
             [0,8,7, 0,0,0, 0,3,1],
            
             [0,0,3, 0,1,0, 0,8,0],
             [9,0,0, 8,6,3, 0,0,5],
             [0,5,0, 0,9,0, 6,0,0],

             [1,3,0, 0,0,0, 2,5,0],
             [0,0,0, 0,0,0, 0,7,4],
             [0,0,5, 2,0,6, 3,0,0]];

val mt = transform
            [[0,0,0, 0,0,0, 0,0,0],
             [0,0,0, 0,0,0, 0,0,0],
             [0,0,0, 0,0,0, 0,0,0],
            
             [0,0,0, 0,0,0, 0,0,0],
             [0,0,0, 0,0,0, 0,0,0],
             [0,0,0, 0,0,0, 0,0,0],

             [0,0,0, 0,0,0, 0,0,0],
             [0,0,0, 0,0,0, 0,0,0],
             [0,0,0, 0,0,0, 0,0,0]];

solve mt 3 3 3;
