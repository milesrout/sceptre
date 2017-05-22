#lang racket

(require racket/trace)
(require graph)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Structs
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct implication (antecedent consequent)  #:transparent)
(struct conjunction (left right) #:transparent)
(struct disjunction (left right) #:transparent)

;  
;  A
;
(struct assume
  (formula)
  #:transparent)

;
; ---
;  A
;  |
;  B
; ---
; A->B
;
(struct impl-intro
  (a-formula b-proof)
  #:transparent)

;
; A->B   A
; --------
;     B
;
(struct impl-elim
  (a->b-proof a-proof)
  #:transparent)

;
;  A   B
; -------
;   A^B
;
(struct conj-intro
  (a-proof b-proof)
  #:transparent)

;
;  A^B
; -----
;   A
;
(struct conj-elim-l
  (ab-proof)
  #:transparent)

;
;  A^B
; -----
;   B
;
(struct conj-elim-r
  (ab-proof)
  #:transparent)

(struct disj-intro-l
  (l-proof r-formula)
  #:transparent)

(struct disj-intro-r
  (l-formula r-proof)
  #:transparent)

(struct disj-elim
  (avb-proof ac-proof bc-proof)
  #:transparent)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Prover
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (prove assumptions goal)
  (struct->list (prove/up assumptions goal)))

(define (prove/up assumptions goal)
  (match goal
    [(? symbol?) (let ([alpha (amb assumptions)])
                   (assert (positive? goal alpha))
                   ((prove/down alpha assumptions goal) (assume alpha)))]
    [(implication a c) (impl-intro a (prove/up (cons a assumptions) c))]
    [(conjunction l r) (conj-intro (prove/up assumptions l) (prove/up assumptions r))]
    [(disjunction l r) (let* ([t (amb (list l r))]
                              [disj (if (eq? t l)
                                        (lambda (v) (disj-intro-l v r))
                                        (lambda (v) (disj-intro-r l v)))])
                         (disj (prove/up assumptions t)))]))

(define (negative? proposition formula)
  (match formula
    [(? symbol?)       (eq? proposition formula)]
    [(conjunction l r) (or (negative? proposition l)
                           (negative? proposition r))]
    [(disjunction l r) (or (negative? proposition l)
                           (negative? proposition r))]
    [(implication a c) (or (positive? proposition a)
                           (negative? proposition c))]))

(define (positive? proposition formula)
  (match formula
    [(? symbol?)       (eq? proposition formula)]
    [(conjunction l r) (or (positive? proposition l)
                           (positive? proposition r))]
    [(disjunction l r) (or (positive? proposition l)
                           (positive? proposition r))]
    [(implication a c) (or (negative? proposition a)
                           (positive? proposition c))]))

(define (prove/down formula assumptions goal)
  (match formula
    [(? symbol?) (if (eq? formula goal)
                     (lambda (v) v)
                     (fail))]
    [(implication a c) (define d1 (prove/down c assumptions goal))
                       (define d2 (prove/up assumptions a))
                       (lambda (d)
                         (d1 (impl-elim d d2)))]
    [(conjunction l r) (define theta (amb (list l r)))
                       (define elim (if (eq? theta l) conj-elim-l conj-elim-r))
                       (define d1 (prove/down theta assumptions goal))
                       (lambda (d)
                         (d1 (elim d)))]
    [(disjunction l r) (define d1 (prove/up (set-add assumptions l) goal))
                       (define d2 (prove/up (set-add assumptions r) goal))
                       (lambda (d)
                         (disj-elim d d1 d2))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Utilities
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (disjunction 'a (implication 'a 'b))
;   --> '(disjunction a (implication a b))
(define (struct->list s)
  (cond [(struct? s) (map struct->list (vector->list (struct->vector s)))]
        [(symbol? s) (string->symbol (regexp-replace #rx"struct:" (symbol->string s) ""))]
        [else s]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; I didn't write (amb). This implementation is from here:
; http://matt.might.net/articles/programming-with-continuations--exceptions-backtracking-search-threads-generators-coroutines/
; (the idea is far, far older)

(define (current-continuation)
  (call-with-current-continuation
   (lambda (cc)
     (cc cc))))

(define fail-stack '())

(define (fail)
  (if (not (pair? fail-stack))
      (error "back-tracking stack exhausted!")
      (begin
        (let ((back-track-point (car fail-stack)))
          (set! fail-stack (cdr fail-stack))
          (back-track-point back-track-point)))))

(define (amb choices)
  (let ((cc (current-continuation)))
    (cond
      ((null? choices)      (fail))
      ((pair? choices)      (let ((choice (car choices)))
                              (set! choices (cdr choices))
                              (set! fail-stack (cons cc fail-stack))
                              choice)))))

(define (assert condition)
  (if (not condition)
      (fail)
      #t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Examples
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define conj-commutes (prove (list (conjunction 'a (conjunction 'b 'c))) (conjunction (conjunction 'a 'b) 'c)))
(define conj-identity (prove (list (conjunction 'a 'b)) (conjunction 'a 'b)))
(define currying (prove (list (implication (conjunction 'a 'b) 'c)) (implication 'a (implication 'b 'c))))
(define reverse-currying (prove (list (implication 'a (implication 'b 'c))) (implication (conjunction 'a 'b) 'c)))

(define conj-test-a (prove (list (conjunction 'a (conjunction 'b 'c))) 'a))
(define conj-test-b (prove (list (conjunction 'a (conjunction 'b 'c))) 'b))
(define conj-test-c (prove (list (conjunction 'a (conjunction 'b 'c))) 'c))

(define disj-test-1 (prove (list 'a) (disjunction 'a 'b)))

(define dne-a ((('a . implication . 'b) . implication . 'b) . implication . 'a))
(define p6-a ((('a . implication . ('a . implication . 'b)) . implication . 'b) . implication . 'a))
;(prove (list p6-a) dne-a)
;(prove (list dne-a) p6-a)

(define p8-a (implication (implication (implication 'a 'b) 'a) 'a))
(define lem-a (disjunction 'a (implication 'a 'b)))
;(prove (list p8-a) lem-a)
;(prove (list lem-a) p8-a)

(define (nd-graph proof)
  (unweighted-graph/directed '()))

(nd-graph conj-test-a)
