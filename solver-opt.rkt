#lang racket

;; A Super Fast Backtracking Sudoku Solver and Generator
;; Guannan Wei
;; guannan.wei@utah.edu

(require rackunit)

;; Sudoku Solver

(struct Just (x) #:transparent)
(struct Unknown (choices) #:transparent)

; Transform a line, auxiliary function used in `transform`.
(define (trans-line line)
  (if (null? line) '()
      (let ([x (car line)])
        (cond [(= x 0) (cons (Unknown '()) (trans-line (cdr line)))]
              [else (cons (Just x) (trans-line (cdr line)))]))))

; Transform function takes a 2-d list of numbers into intermediate 
; data structure, which use (Just x) for a determined number, and
; se (Unknown) for a unknown box in the grid.
(define transform (λ (grid) (map trans-line grid)))

; Transpose the grid, auxiliary function.
(define (transpose grid)
  (if (null? grid) '()
      (map (λ (i) (map (λ (line) (list-ref line i)) grid))
           (range (length (car grid))))))

; Get i-th row from the grid.
(define get-row list-ref)

; Get i-th column from the grid.
(define get-col (λ (g i) (map (λ (line) (list-ref line i)) g)))

; Get the block as a list for current (row, col) box in a M x N grid.
(define (get-block grid M N row col)
  (let ([row (add1 (floor (/ row N)))]
        [col (floor (/ col M))])
    (flatten (for/list ([i (range (* (sub1 row) N) (* row N))])
               (take (drop (list-ref grid i) (* col M)) M)))))

; Get all used number in a list.
(define get-used-num (curry filter-map (λ (y) (and (Just? y) (Just-x y)))))

(define (grid-get grid row col) (list-ref (get-row grid row) col))

(define (grid-set grid row col ele)
  (list-set grid row (list-set (list-ref grid row) col ele)))

(define (end? M N row col) (and (= (* M N) row) (= 0 col)))

(define (solve grid M N)
  (define side-length (* M N))
  (define all-possible-choices (range 1 (add1 side-length)))
  (define (next-row row col)
    (if (zero? (modulo (add1 col) side-length)) (add1 row)
        row))
  (define (next-col row col)
    (if (zero? (modulo (add1 col) side-length)) 0
        (add1 col)))
  (define (get-possible-choices grid row col)
    (let ([ele (list-ref (list-ref grid row) col)])
      (cond [(Just? ele) `(,(Just-x ele))]
            [(Unknown? ele)
             (let ([row-cns (get-used-num (get-row grid row))]
                   [col-cns (get-used-num (get-col grid col))]
                   [blk-cns (get-used-num (get-block grid M N row col))])
               (remv* (remove-duplicates (flatten `(,row-cns ,col-cns ,blk-cns)))
                      all-possible-choices))])))
  (define (aux-update grid row col)
    (if (end? M N row col) grid
        (cond [(Unknown? (grid-get grid row col))
               (aux-update (grid-set grid row col (Unknown (get-possible-choices grid row col)))
                           (next-row row col) (next-col row col))]
              [else (aux-update grid (next-row row col) (next-col row col))])))
  (define (update grid) (aux-update grid 0 0))

  ; min is list of (len row col)
  (define (aux-next-row-col grid row col min)
    (if (end? M N row col) (cdr min)
        (let ([ele (grid-get grid row col)])
          (if (and (Unknown? ele) (<= (length (Unknown-choices ele)) (car min)))
              (aux-next-row-col grid (next-row row col) (next-col row col)
                                `(,(length (Unknown-choices ele)) ,row ,col))
              (aux-next-row-col grid (next-row row col) (next-col row col) min)))))

  (define (next-row-col grid)
    (aux-next-row-col grid 0 0 `(,(length all-possible-choices) -1 -1)))

  (define (aux-solve grid pos back)
    (match pos
      [`(,row ,col) (if (< row 0) grid
                        (try grid row col
                             (shuffle (Unknown-choices (grid-get grid row col))) back))]))

  (define (try grid row col choices back)
    (if (empty? choices) (back)
        (let ([grid (update (grid-set grid row col (Just (car choices))))])
          (aux-solve grid (next-row-col grid)
                     (λ () (try grid row col (cdr choices) back))))))

  (let ([grid (update grid)])
    (aux-solve grid (next-row-col grid) (λ () (error 'solve "can not solve")))))

;; Validate

(define ternary-equal?
  (λ (x y z) (and (equal? x y) (equal? y z))))

(define (each-block grid M N)
  (foldl append '()
         (for/list ([row (range 0 (* M N) N)])
           (for/list ([col (range 0 (* M N) M)])
             (get-block grid M N row col)))))

(define valid?
  (λ (grid M N)
    (define sum-of-justs
      (λ (lst) (foldl + 0 (map (λ (j) (Just-x j)) lst))))
    (ternary-equal?
     (map sum-of-justs grid)
     (map sum-of-justs (transpose grid))
     (map sum-of-justs (each-block grid M N)))))

;; Generator

(define mk-empty-grid
  (λ (n)
    (build-list n (λ (i) (make-list n (Unknown '()))))))

; A generator is actually solving an empty grid without any constraints,
; and then remove some elements in the grid.
; `x` is the number we want to remove from the grid.
(define generate
  (λ (M N x)
    (define side-length (* M N))
    (define remove
      (λ (grid i)
        (if (eq? x i) grid
            (let* ([x (random side-length)]
                   [y (random side-length)]
                   [cur (grid-get grid x y)])
              (cond [(Just? cur) (remove (grid-set grid x y (Unknown '())) (add1 i))]
                    [(Unknown? cur) (remove grid i)])))))
    (remove (solve (mk-empty-grid side-length) M N) 0)))

;(define g1 (generate 3 3 50))
;(define s-g1 (solve g1 3 3))

;;;;;;;;;;;;;;;;;;;
; Test
;;;;;;;;;;;;;;;;;;;

#|
(define grid
  (transform
   '((3 0 6  5 0 8  4 0 0)
     (5 2 0  0 0 0  0 0 0)
     (0 8 7  0 0 0  0 3 1)
     
     (0 0 3  0 1 0  0 8 0)
     (9 0 0  8 6 3  0 0 5)
     (0 5 0  0 9 0  6 0 0)
     
     (1 3 0  0 0 0  2 5 0)
     (0 0 0  0 0 0  0 7 4)
     (0 0 5  2 0 6  3 0 0))))
(define solved (solve grid 3 3))
solved
(valid? solved 3 3)

;;;;;;;;;;;;;;;;;;

(define grid2
  (transform
   '((1 0 0  4 0 6)
     (4 0 0  1 0 0)
     
     (0 0 4  0 0 1)
     (0 0 1  0 3 0)
     
     (3 0 0  6 1 0)
     (0 1 0  0 0 5))))
(define solved2 (solve grid2 3 2))
solved2
(valid? solved2 3 2)
|#
;;;;;;;;;;;;;;;;;;;

(define nefarious-grid
  (transform
  '((0 0 0  0 6 0  0 8 0)
    (0 2 0  0 0 0  0 0 0)
    (0 0 1  0 0 0  0 0 0)
    
    (0 7 0  0 0 0  1 0 2)
    (5 0 0  0 3 0  0 0 0)
    (0 0 0  0 0 0  4 0 0)

    (0 0 4  2 0 1  0 0 0)
    (3 0 0  7 0 0  6 0 0)
    (0 0 0  0 0 0  0 5 0))))
(time (solve nefarious-grid 3 3))
;(define nefarious-solved (solve nefarious-grid 3 3))
;nefarious-solved
;(valid? nefarious-solved 3 3)

;;;;;;;;;;;;;;;;;;;
#|
(check-equal? tgrid
              (list
               (list (Just 3) (Unknown) (Just 6) (Just 5) (Unknown) (Just 8) (Just 4) (Unknown) (Unknown))
               (list (Just 5) (Just 2) (Unknown) (Unknown) (Unknown) (Unknown) (Unknown) (Unknown) (Unknown))
               (list (Unknown) (Just 8) (Just 7) (Unknown) (Unknown) (Unknown) (Unknown) (Just 3) (Just 1))
               (list (Unknown) (Unknown) (Just 3) (Unknown) (Just 1) (Unknown) (Unknown) (Just 8) (Unknown))
               (list (Just 9) (Unknown) (Unknown) (Just 8) (Just 6) (Just 3) (Unknown) (Unknown) (Just 5))
               (list (Unknown) (Just 5) (Unknown) (Unknown) (Just 9) (Unknown) (Just 6) (Unknown) (Unknown))
               (list (Just 1) (Just 3) (Unknown) (Unknown) (Unknown) (Unknown) (Just 2) (Just 5) (Unknown))
               (list (Unknown) (Unknown) (Unknown) (Unknown) (Unknown) (Unknown) (Unknown) (Just 7) (Just 4))
               (list (Unknown) (Unknown) (Just 5) (Just 2) (Unknown) (Just 6) (Just 3) (Unknown) (Unknown))))
(check-equal? (transpose '((1 2 3) (4 5 6) (7 8 9)))
              '((1 4 7) (2 5 8) (3 6 9)))
(check-equal? (get-block grid 6 6)
              '(2 5 0 0 7 4 3 0 0))
(check-equal? (get-possible-choices tgrid 0 1) '(1 9))
(check-equal? (get-possible-choices tgrid 1 1) '(2))
|#
