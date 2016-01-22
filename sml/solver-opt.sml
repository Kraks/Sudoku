(*
Sudoku Solver
Guannan Wei <guannan.wei@utah.edu>
*)

datatype Box = Just of int | Unknown of int list;
type Grid = Box list list;

fun range i = List.tabulate(i, fn x => x);

fun update [] i ele = raise Empty
  | update (x::xs) 0 ele = ele::xs
  | update (x::xs) i ele = x::(update xs (i-1) ele);

fun gridGet g row col = List.nth(List.nth(g, row), col);

fun gridUpdate g row col ele = update g row (update (List.nth(g, row)) col ele);

fun getRow g i = List.nth(g, i);

fun getCol g i = map (fn row => List.nth(row, i)) g;

fun partition step [] = []
  | partition step xs = if List.length(xs) <= step then [xs]
                        else List.take(xs, step)::(partition step (List.drop(xs, step)))

fun getBlock g m n row col =
  let fun aux row col = 
        let val rows = List.nth(partition n g, row)
        in List.concat(map (fn ln => List.nth(partition m ln, col)) rows) end
  in aux (row div n) (col div m) end;

fun remove x [] = []
  | remove x (l as y :: ys) = if x = y then remove x ys
                              else y::(remove x ys);

fun removeList [] ys = ys
  | removeList (x::xs) ys = removeList xs (remove x ys);

fun isolate [] = []
  | isolate (x::xs) = x::isolate(remove x xs);

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

fun min xs f =
  let fun aux [] i m = m
        | aux (x::xs) i m = if (f x) < (f (#2 m)) then aux xs (i+1) (i, x)
                            else aux xs (i+1) m
  in aux (tl xs) 0 (0, (f (hd xs))) end;

fun updateGrid grid m n = 
  let fun updateLine [] _ _ = []
        | updateLine ((Just x)::xs) row col = (Just x)::(updateLine xs row (col+1))
        | updateLine ((Unknown _)::xs) row col = 
            (Unknown (getPossibleNums grid m n row col))::(updateLine xs row (col+1))
      fun update [] _ = []
        | update (line::grid) row = (updateLine line row 0)::(update grid (row+1))
  in update grid 0 end;

exception NoSolution;

fun nextRowCol grid = (1, 1);
fun isValid grid = true;

datatype Result = Fail of (unit -> Result) list
                | Success of Grid * ((unit -> Result) list);

fun solve grid m n x =
  let fun try grid (row, col) =
        let val choices = getPossibleNums grid m n row col
            val others = map (fn c => fn () => let val grid = gridUpdate grid row col (Just c) 
                                               in try grid (nextRowCol grid) end) (tl choices)
            val grid = gridUpdate grid row col (Just (hd choices))
        in if isValid grid then Fail(others) else Success(grid, others) end

      fun aux res [] = if List.length(res) = 0 then raise NoSolution else res
        | aux res (s::ss) = if List.length(res) = x then res
                            else case s() of 
                                   Fail others => aux res (others@ss)
                                 | Success(grid, others) => aux (grid::res) (others@ss)

  in aux [] [] end;


(*
getBlock [[1,2,3,4],[5,6,7,8],[9,10,11,12],[13,14,15,16]] 2 2 0 0;
getBlock [[1,2,3,4],[5,6,7,8],[9,10,11,12],[13,14,15,16]] 2 2 0 1;
getBlock [[1,2,3,4],[5,6,7,8],[9,10,11,12],[13,14,15,16]] 2 2 0 2;
getBlock [[1,2,3,4],[5,6,7,8],[9,10,11,12],[13,14,15,16]] 2 2 3 3;
*)

updateGrid [[Just 1, Just 2], [Unknown [], Unknown[]]] 2 2;
