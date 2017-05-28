#lang racket

(require racket/trace)
(require graph)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Structs
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct implication (antecedent consequent) #:transparent)
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
  (parameterize ([fail-stack '()]
                 [prove/up-cache (make-hash)]
                 [prove/down-cache (make-hash)])
    (struct->list (prove/up assumptions goal))))

(define prove/up-cache
  (make-parameter #f))

(define prove/down-cache
  (make-parameter #f))

(define (prove/up assumptions goal)
  (define key (list assumptions goal))
  (define cached (hash-ref (prove/up-cache) key 'nothing))
  (match cached
    ['in-progress (fail)]
    [`(done ,v) v]
    ['nothing (begin
                (hash-set! (prove/up-cache) key 'in-progress)
                (define result (%prove/up assumptions goal))
                (hash-set! (prove/up-cache) key `(done ,result))
                result)]))

(define (prove/down formula assumptions goal)
  (define key (list formula assumptions goal))
  (define cached (hash-ref (prove/down-cache) key 'nothing))
  (match cached
    ['in-progress (fail)]
    [`(done ,v) v]
    ['nothing (begin
                (hash-set! (prove/down-cache) key 'in-progress)
                (define result (%prove/down formula assumptions goal))
                (hash-set! (prove/down-cache) key `(done ,result))
                result)]))

(define (%prove/up assumptions goal)
  (if (set-member? assumptions goal)
      (assume goal)
      (if (amb '(#t #f))
          (match goal
            [(? symbol?) (fail)]
            [(implication a c) (impl-intro a (prove/up (set-add assumptions a) c))]
            [(conjunction l r) (conj-intro (prove/up assumptions l) (prove/up assumptions r))]
            [(disjunction l r) (let* ([t (amb (list l r))]
                                      [disj (if (eq? t l)
                                                (lambda (v) (disj-intro-l v r))
                                                (lambda (v) (disj-intro-r l v)))])
                                 (disj (prove/up assumptions t)))])
          (let ([alpha (amb assumptions)])
            ((prove/down alpha assumptions goal) (assume alpha))))))

(define (%prove/down formula assumptions goal)
  (match formula
    [(== goal) (lambda (v) v)]
    [(? symbol?) (fail)]
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

(define (negative? proposition formula)
  (match formula
    [(? symbol?) #f]
    [(conjunction l r) (or (negative? proposition l)
                           (negative? proposition r))]
    [(disjunction l r) (or (negative? proposition l)
                           (negative? proposition r))]
    [(implication a c) (or (positive? proposition a)
                           (negative? proposition c))]))

(define (positive? proposition formula)
  (or (eq? proposition formula)
      (match formula
        [(? symbol?)       (eq? proposition formula)]
        [(conjunction l r) (or (positive? proposition l)
                               (positive? proposition r))]
        [(disjunction l r) (or (positive? proposition l)
                               (positive? proposition r))]
        [(implication a c) (or (negative? proposition a)
                               (positive? proposition c))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Utilities
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (struct->list s)
  (cond [(struct? s) (map struct->list (vector->list (struct->vector s)))]
        [(symbol? s) (string->symbol (regexp-replace #rx"struct:" (symbol->string s) ""))]
        [else s]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; I didn't write (amb). This implementation is from here:
; http://matt.might.net/articles/programming-with-continuations--exceptions-backtracking-search-threads-generators-coroutines/
; (the idea is a lot older)

(define (current-continuation)
  (call-with-current-continuation
   (lambda (cc)
     (cc cc))))

(define fail-stack (make-parameter #f))

(define (fail)
  (cond
    [(eq? (fail-stack) #f) (error "no fail-stack set up")]
    [(not (pair? (fail-stack))) (error "back-tracking stack exhausted!")]
    [else (begin
            (let ((back-track-point (car (fail-stack))))
              (fail-stack (cdr (fail-stack)))
              (back-track-point back-track-point)))]))

(define (amb choices)
  (let ((cc (current-continuation)))
    (cond
      ((null? choices)      (fail))
      ((pair? choices)      (let ((choice (car choices)))
                              (set! choices (cdr choices))
                              (fail-stack (cons cc (fail-stack)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Examples
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (dne f) (implication (implication (implication f 'bot) 'bot) f))
(define (p6 f) (implication (implication (implication f (implication f 'bot)) 'bot) f))

(define (p8 f) (implication (implication (implication f 'bot) f) f))
(define (lem f) (disjunction f (implication f 'bot)))

(prove (list (conjunction 'a (conjunction 'b 'c))) (conjunction (conjunction 'a 'b) 'c))
(prove (list (conjunction 'a 'b)) (conjunction 'a 'b))
(prove (list (implication (conjunction 'a 'b) 'c)) (implication 'a (implication 'b 'c)))
(prove (list (implication 'a (implication 'b 'c))) (implication (conjunction 'a 'b) 'c))

(prove (list (conjunction 'a (conjunction 'b 'c))) 'a)
(prove (list (conjunction 'a (conjunction 'b 'c))) 'b)
(prove (list (conjunction 'a (conjunction 'b 'c))) 'c)

(prove (list 'a) (disjunction 'a 'b))

(prove (list (dne (lem 'a))) (lem 'a))

(prove (list (dne 'a)) (p6 'a))
(prove (list (p6 'a)) (dne 'a))

(prove (list (lem 'a)) (p8 'a))
(prove (list (p8 (lem 'a))) (lem 'a))

(define (nd-graph proof)
  (unweighted-graph/directed '()))

;(nd-graph conj-test-a)
