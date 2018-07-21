#lang racket

;; A Fast Backtracking Sudoku Solver and Generator
;; Guannan Wei
;; guannan.wei@utah.edu

(require rackunit)

(provide solve-string-grid
         grid->string
         generate-string-grid
         valid?)

;; Sudoku Solver

(struct Just (x) #:transparent)
(struct Unknown (choices) #:transparent)

; Get i-th row from the grid.
(define get-row list-ref)

; Get i-th column from the grid.
(define get-col (λ (g i) (map (λ (line) (list-ref line i)) g)))

; Get the block as a list for current (row, col) cell in a M x N grid.
(define (get-block grid M N row col)
  (let ([row (add1 (floor (/ row N)))]
        [col (floor (/ col M))])
    (flatten (for/list ([i (range (* (sub1 row) N) (* row N))])
               (take (drop (list-ref grid i) (* col M)) M)))))

; Get all used number in a list.
(define get-used-num (curry filter-map (λ (y) (and (Just? y) (Just-x y)))))

; Get element at (row, col)
(define (grid-get grid row col) (list-ref (get-row grid row) col))

; Set element at (row, col)
(define (grid-set grid row col ele)
  (list-set grid row (list-set (list-ref grid row) col ele)))

; Decide if already moved to the last element
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

  ; Get all possible choices for (row, col) on grid
  (define (get-possible-choices grid row col)
    (let ([ele (list-ref (list-ref grid row) col)])
      (cond [(Just? ele) `(,(Just-x ele))]
            [(Unknown? ele)
             (let ([row-cns (get-used-num (get-row grid row))]
                   [col-cns (get-used-num (get-col grid col))]
                   [blk-cns (get-used-num (get-block grid M N row col))])
               (remv* (remove-duplicates (flatten `(,row-cns ,col-cns ,blk-cns)))
                      all-possible-choices))])))

  ; Update possible choices for Unknown cell
  (define (update grid) 
    (define (aux-update grid row col)
      (if (end? M N row col) grid
          (cond [(Unknown? (grid-get grid row col))
                 (aux-update (grid-set grid row col (Unknown (get-possible-choices grid row col)))
                             (next-row row col) (next-col row col))]
                [else (aux-update grid (next-row row col) (next-col row col))])))
    (aux-update grid 0 0))

  ; Move to the next cell which has minimum number of choices
  (define (next-row-col grid)
    ; `option` is list of (len row col)
    (define (aux-next-row-col grid row col option)
      (if (end? M N row col) (cdr option)
          (let ([ele (grid-get grid row col)])
            (if (and (Unknown? ele) (<= (length (Unknown-choices ele)) (car option)))
                (aux-next-row-col grid (next-row row col) (next-col row col)
                                  `(,(length (Unknown-choices ele)) ,row ,col))
                (aux-next-row-col grid (next-row row col) (next-col row col) option)))))
    (aux-next-row-col grid 0 0 `(,(length all-possible-choices) -1 -1)))

  ; If the choices is empty, we need to backtrack
  ; Otherwise, just try the first element of choices and then move to next cell
  (define (try grid row col choices back)
    (if (empty? choices) (back)
        (let ([grid (update (grid-set grid row col (Just (car choices))))])
          (aux-solve grid (next-row-col grid)
                     (λ () (try grid row col (cdr choices) back))))))

  (define (aux-solve grid pos back)
    (match pos
      [`(,row ,col) (if (< row 0) grid
                        (try grid row col
                             (shuffle (Unknown-choices (grid-get grid row col))) back))]))

  (let ([grid (update grid)])
    (aux-solve grid (next-row-col grid) (λ () (error 'solve "can not solve")))))

(define (transform-line line)
  (if (null? line) '()
      (let ([x (car line)])
        (cond [(string=? "_" x) (cons (Unknown '()) (transform-line (cdr line)))]
              [else (cons (Just (string->number x)) (transform-line (cdr line)))]))))

(define (solve-string-grid str)
  (let* ([strs (map string-split (string-split str "\n"))]
         [M (string->number (car (car strs)))]
         [N (string->number (cadr (car strs)))])
    (solve (map transform-line (cdr strs)) M N)))

;; Validate

(define ternary-equal?
  (λ (x y z) (and (equal? x y) (equal? y z))))

(define (each-block grid M N)
  (foldl append '()
         (for/list ([row (range 0 (* M N) N)])
           (for/list ([col (range 0 (* M N) M)])
             (get-block grid M N row col)))))

; Transpose the grid, auxiliary function.
(define (transpose grid)
  (if (null? grid) '()
      (map (λ (i) (map (λ (line) (list-ref line i)) grid))
           (range (length (car grid))))))

; Is the grid satisfies all constraints?
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

(define (grid->string grid)
  (define (line->string line)
    (string-join (map (λ (x) (cond [(Just? x) (number->string (Just-x x))]
                                   [(Unknown? x) "_"]))
                     line)
                 " "))
  (string-join (map line->string grid) "\n"))

(define (generate-string-grid M N x)
  (string-append (number->string M)
                 " "
                 (number->string N)
                 "\n"
                 (grid->string (generate M N x))))

;(define g1 (generate 3 3 50))
;(define s-g1 (solve g1 3 3))

;; Test

; Transform a line, auxiliary function used in `transform`.


; Transform function takes a 2-d list of numbers into intermediate 
; data structure, which use (Just x) for a determined number, and
; se (Unknown) for a unknown cell in the grid.
(define transform-from-num-grid
  (λ (grid)
    (define (trans-line line)
      (if (null? line) '()
          (let ([x (car line)])
            (cond [(= x 0) (cons (Unknown '()) (trans-line (cdr line)))]
                  [else (cons (Just x) (trans-line (cdr line)))]))))
    (map trans-line grid)))

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
(define solved3 (solve nefarious-grid 3 3))
solved3
(valid? solved3 3 3)
|#

