#lang racket

(define get-col (λ (g i) (map (λ (line) (list-ref line i)) g)))

(define (get-block grid M N row col)
  (let ([row (add1 (floor (/ row N)))]
        [col (floor (/ col M))])
    (flatten (for/list ([i (range (* (sub1 row) N) (* row N))])
      (take (drop (list-ref grid i) (* col M)) M)))))

(define get-used-num (curry filter (λ (x) (not (zero? x)))))

(define (grid-get grid row col) (list-ref (list-ref grid row) col))

(define (grid-set grid row col ele)
  (list-set grid row (list-set (list-ref grid row) col ele)))

(define (solve grid M N)
  (define side-length (* M N))
  (define (end? row col) (and (= (* M N) row) (= 0 col)))
  (define (next-row row col)
    (if (zero? (modulo (add1 col) side-length)) (add1 row) row))
  (define (next-col row col)
    (if (zero? (modulo (add1 col) side-length)) 0 (add1 col)))
  (define (get-possible-choices grid row col)
    (if (not (= 0 (grid-get grid row col))) '()
        (let ([row-cns (get-used-num (list-ref grid row))]
              [col-cns (get-used-num (get-col grid col))]
              [blk-cns (get-used-num (get-block grid M N row col))])
          (remv* (remove-duplicates (flatten `(,row-cns ,col-cns ,blk-cns)))
                 (range 1 (add1 side-length))))))
  (define (try grid row col choices back)
    (if (empty? choices) (back)
        (aux-solve (grid-set grid row col (car choices))
                   (next-row row col) (next-col row col)
                   (λ () (try grid row col (cdr choices) back)))))
  (define (aux-solve grid row col back)
    (cond [(end? row col) grid]
          [(not (= 0 (grid-get grid row col)))
           (aux-solve grid (next-row row col) (next-col row col) back)]
          [else (try grid row col (get-possible-choices grid row col) back)]))
  (aux-solve grid 0 0 (λ () (error 'solve "can not solve"))))

;;;;;;;;;;;;;;;;;;;
; Test
;;;;;;;;;;;;;;;;;;;

(define grid
  '((3 0 6  5 0 8  4 0 0)
    (5 2 0  0 0 0  0 0 0)
    (0 8 7  0 0 0  0 3 1)
    
    (0 0 3  0 1 0  0 8 0)
    (9 0 0  8 6 3  0 0 5)
    (0 5 0  0 9 0  6 0 0)
    
    (1 3 0  0 0 0  2 5 0)
    (0 0 0  0 0 0  0 7 4)
    (0 0 5  2 0 6  3 0 0)))

(define solved (solve grid 3 3))
solved
