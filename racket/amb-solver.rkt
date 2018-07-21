#lang racket

;; A Non-determinitic Sudoku Solver based on amb operator
;; Guannan Wei
;; guannan.wei@utah.edu

(require math/base)

;; Amb operator
;; The amb operator part is from Matt Might's blog
;; http://matt.might.net/articles/programming-with-continuations--exceptions-backtracking-search-threads-generators-coroutines/

(define current-continuation
  (λ () (call/cc (lambda (cc) (cc cc)))))

(define fail-stack '())

(define (fail)
  (if (not (pair? fail-stack))
      (error "back-tracking stack exhausted!")
      (let ([back-track-point (car fail-stack)])
        (set! fail-stack (cdr fail-stack))
        (back-track-point back-track-point))))

(define (amb choices)
  (let ([cc (current-continuation)])
    (cond [(null? choices) (fail)]
          [(pair? choices)
           (let ([choice (car choices)])
             (set! choices (cdr choices))
             (set! fail-stack (cons cc fail-stack))
             choice)])))

(define (require pred) (if (not pred) (fail) #t))

;; Sudoku Solver

(define (transpose grid)
    (if (null? grid) '()
        (map (λ (i) (map (λ (line) (list-ref line i)) grid))
             (range (length (car grid))))))

(define get-col (λ (g i) (map (λ (line) (list-ref line i)) g)))

(define (get-block grid M N row col)
  (let ([row (add1 (floor (/ row N)))]
        [col (floor (/ col M))])
    (flatten (for/list ([i (range (* (sub1 row) N) (* row N))])
      (take (drop (list-ref grid i) (* col M)) M)))))

(define (each-block grid M N)
  (foldl append '()
         (for/list ([row (range 0 (* M N) N)])
           (for/list ([col (range 0 (* M N) M)])
             (get-block grid M N row col)))))

(define get-used-num (curry filter (λ (x) (not (eq? '_ x)))))

(define (grid-get grid row col) (list-ref (list-ref grid row) col))

(define (grid-set grid row col ele)
  (list-set grid row (list-set (list-ref grid row) col ele)))

(define (solve grid M N)
  (define side-length (* M N))
  (define total (sum (range 1 (add1 side-length))))
  (define (end? row col) (and (= side-length row) (= 0 col)))
  (define (next-row row col)
    (if (zero? (modulo (add1 col) side-length)) (add1 row) row))
  (define (next-col row col)
    (if (zero? (modulo (add1 col) side-length)) 0 (add1 col)))
  (define (get-possible-choices grid row col)
    (if (not (eq? '_ (grid-get grid row col))) '()
        (let ([row-cns (get-used-num (list-ref grid row))]
              [col-cns (get-used-num (get-col grid col))]
              [blk-cns (get-used-num (get-block grid M N row col))])
          (remv* (remove-duplicates (flatten `(,row-cns ,col-cns ,blk-cns)))
                 (range 1 (add1 side-length))))))
  (define (gen-constraints grid row col)
    (cond [(end? row col) grid]
          [(eq? '_ (grid-get grid row col))
           (gen-constraints 
            (grid-set grid row col (amb (get-possible-choices grid row col)))
            (next-row row col) (next-col row col))]
          [else (gen-constraints grid (next-row row col) (next-col row col))]))
  
  (let ([g (gen-constraints grid 0 0)])
    (for/list ([line g]) (require (= total (sum line))))
    (for/list ([line (transpose g)]) (require (= total (sum line))))
    (for/list ([block (each-block g M N)]) (require (= total (sum block))))
    g))

;; Test

(define grid
  '([3 _ 6  5 _ 8  4 _ _]
    [5 2 _  _ _ _  _ _ _]
    [_ 8 7  _ _ _  _ 3 1]
    [_ _ 3  _ 1 _  _ 8 _]
    [9 _ _  8 6 3  _ _ 5]
    [_ 5 _  _ 9 _  6 _ _]
    [1 3 _  _ _ _  2 5 _]
    [_ _ _  _ _ _  _ 7 4]
    [_ _ 5  2 _ 6  3 _ _]))

(solve grid 3 3)
