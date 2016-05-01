#lang racket/base

(require (for-syntax racket/base
                     racket/list
                     syntax/parse
                     racket/struct-info
                     racket/syntax)
         racket/contract
         (only-in racket/function thunk)
         racket/match
         racket/provide-syntax
         racket/set)

(provide (struct-out zipper)
         ;; Basic zipper utilities
         zipper-of/c
         zipper-in/c
         define-struct-zipper-frames
         struct-zipper-out
         (struct-out zipper-movement)
         (contract-out
          [zip (-> any/c zipper?)]
          [zipper-frame? (-> any/c boolean?)]
          [prop:zipper-frame struct-type-property?]
          [zipper-at-top? (-> any/c boolean?)]
          [zipper-not-at-top? (-> any/c boolean?)]
          [up (and/c (-> zipper-not-at-top? zipper?)
                     zipper-movement?)]
          [can-move? (-> zipper-movement? zipper? boolean?)]
          [rebuild (-> zipper? any/c)]
          [edit (-> (-> any/c any/c) zipper? zipper?)])
         ;; Pair zippers
         (struct-out pair-car-frame)
         (struct-out pair-cdr-frame)
         (contract-out
          [down/car (and/c (-> (zipper-of/c pair?) zipper?)
                           zipper-movement?)]
          [down/cdr (and/c (-> (zipper-of/c pair?) zipper?)
                           zipper-movement?)])
         ;; List zippers
         (struct-out list-item-frame)
         (contract-out
          [down/list-first (and/c (-> (zipper-of/c list?) zipper?)
                                  zipper-movement?)]
          [down/list-ref (-> exact-nonnegative-integer?
                             (and/c (-> (zipper-of/c list?)
                                        zipper?)
                                    zipper-movement?))]
          [left/list (and/c (-> (zipper-in/c list-item-frame?)
                                (zipper-in/c list-item-frame?))
                            zipper-movement?)]
          [right/list (and/c (-> (zipper-in/c list-item-frame?)
                                 (zipper-in/c list-item-frame?))
                             zipper-movement?)])
         ;; Set zippers
         (struct-out set-member-frame)
         (contract-out
          [down/set-member (-> any/c
                               (-> (zipper-of/c set?)
                                    zipper?))]))

(module+ test
  (require rackunit))

;;;; Zippers

;;; A zipper consists of a context and a focused value. Contexts are
;;; represented as lists of frames, where the empty list is the
;;; context consisting of a hole. Each frame must know how to fill its
;;; hole.
(struct zipper (focus context) #:transparent)

(define (zip obj)
  (zipper obj '()))

;;; Struct frames can be recognized, and we can fill their holes.  The
;;; property should be set to a procedure that, given the frame and a
;;; focus, returns a new focus. We recognize frames with zipper-frame?
(define-values (prop:zipper-frame zipper-frame? zipper-frame-fill)
  (make-struct-type-property 'zipper-frame))


(define (zipper-at-top? z)
  (match z
    [(zipper _ (list))
     #t]
    [_
     #f]))

(define (zipper-not-at-top? z)
  (match z
    [(zipper _ (cons _ _))
     #t]
    [_
     #f]))

(define (zipper-of/c c)
  (make-flat-contract
   #:name `(zipper-of/c ,c)
   #:first-order (lambda (z)
                   (match z
                     [(zipper focus _)
                      (c focus)]
                     [_ #f]))))

(define (zipper-in/c c)
  (make-flat-contract
   #:name `(zipper-in/c ,c)
   #:first-order (lambda (z)
                   (match z
                     [(zipper _ (cons f fs))
                      (c f)]
                     [_ #f]))))


(module+ test
  (check-false ((flat-contract-predicate (zipper-of/c pair?))
                (zip "hi")))
  (check-false ((flat-contract-predicate (zipper-of/c pair?))
                (cons 1 2)))
  (check-true ((flat-contract-predicate (zipper-of/c pair?))
               (zip (cons 1 2))))

  (check-true ((flat-contract-predicate (zipper-in/c string?))
               (zipper #f '("fake frame"))))
  (check-false ((flat-contract-predicate (zipper-in/c string?))
                (zipper #f '('fake 'context)))))

(struct zipper-movement (move possible?)
  #:property prop:procedure (struct-field-index move)
  #:transparent)

(define (can-move? direction z)
  (match direction
    [(zipper-movement _ ok?)
     (ok? z)]))

;;; To go up, we ask the most recent frame to envelop the focus
(define up
  (zipper-movement
   (lambda (z)
     (match-let* ([(zipper focus (cons frame frames)) z]
                  [filler (zipper-frame-fill frame)])
       (zipper (filler frame focus) frames)))
   (lambda (z)
     (pair? (zipper-context z)))))

;;; Go up all the way and extract the value
(define (rebuild z)
  (match z
    [(zipper focus (list))
     focus]
    [(zipper _ (cons frame frames))
     (rebuild (up z))]))

;;; Modify the focused value
(define (edit proc z)
  (match z
    [(zipper focus context)
     (zipper (proc focus) context)]))

(define-for-syntax (make-frame-name orig-stx accessor-name)
  (format-id orig-stx "~a-frame" accessor-name #:source orig-stx))

(define-for-syntax (make-down-name orig-stx accessor-name)
  (format-id orig-stx "down/~a" accessor-name #:source orig-stx))

;;; Helper for generating the zipper definitions for a single struct
;;; (see `define-struct-zipper-frames')
(define-for-syntax (generate-zipper-defs orig-stx struct-name)
  (define struct-info
    (extract-struct-info (syntax-local-value struct-name)))

  (define/with-syntax make-name (second struct-info))
  (define/with-syntax name? (third struct-info))
  (define accessors (reverse (fourth struct-info)))
  (define/with-syntax (name-field ...) accessors)
  (define/with-syntax ((frame-struct-name
                        descender-name
                        (fields-pre ...)
                        (fields-pre-patterns ...)
                        (this-field fields-post ...)
                        (fields-post-patterns ...))
                       ...)
    (for/list ([accessor (in-list accessors)]
               [index (in-naturals)])
      (define f-name (make-frame-name orig-stx accessor))
      (define d-name (make-down-name orig-stx accessor))
      (define-values (pre this+post) (split-at accessors index))
      (list f-name d-name pre (generate-temporaries pre) this+post (generate-temporaries (rest this+post)))))
  (syntax/loc orig-stx
    (begin
      (struct frame-struct-name (fields-pre ... fields-post ...)
        #:property prop:zipper-frame
        (lambda (frame focus)
          (match frame
            [(frame-struct-name fields-pre ... fields-post ...)
             (make-name fields-pre ... focus fields-post ...)]))
        #:transparent)
      ...
      (define/contract descender-name
        (and/c (-> (zipper-of/c name?) zipper?)
               zipper-movement?)
        (zipper-movement
         (lambda (z)
           (match z
             [(zipper (make-name fields-pre-patterns ...
                                 new-focus
                                 fields-post-patterns ...)
                      context)
              (zipper new-focus (cons (frame-struct-name fields-pre-patterns ... fields-post-patterns ...)
                                      context))]
             [(zipper focus _)
              (raise-argument-error 'descender-name
                                    (symbol->string 'name?)
                                    focus)]))
         (lambda (z) (name? (zipper-focus z)))))
      ...)))



;;; A macro for deriving zipper frames for structs.
;;;
;;; Essentially, this implements the product rule for the
;;; differentiation underlying zipper derivation (à la McBride).
;;;
;;; For each field in a struct, we generate a new struct representing
;;; the fact that the zipper client descended into that field. This
;;; struct maintains the values of all the other fields, and it's "go
;;; up" procedure reinstantiates them on the correct sides of the
;;; focus. Additionally, each field gets a descend prodecure that, if
;;; the appropriate struct is at the focus of a zipper, will push the
;;; corresponding frame onto the zipper's frame stack and refocus on
;;; that field.
;;;
;;; For a struct (struct s (f1 ... fn)), we generate:
;;;   1. (struct s-f1-frame (f2 ... fn)) ...
;;;      (struct s-fk-frame (f1 ... fk-1 fk+1 ... fn)) ...
;;;      (struct s-fn-frame (f1 ... fn-1))
;;;      for representing zipper frames at each choice of field
;;;
;;;   2. procedures s-f1-down ... s-fn-down for descending the zipper
;;;      into the corresponding field (that is, making s-fk-frame for
;;;      field fk)
(define-syntax (define-struct-zipper-frames stx)
  (syntax-parse stx
    [(_ name:id names:id ...)
     (quasisyntax/loc stx
       (begin #,(generate-zipper-defs stx #'name)
              #,@(map (lambda (n) (generate-zipper-defs stx n))
                      (syntax->list #'(names ...)))))]))

(define-provide-syntax (struct-zipper-out stx)
  (syntax-parse stx
    [(_ names:id ...)
     (quasisyntax/loc stx
       (combine-out
        #,@(map (lambda (struct-name)
                  (quasisyntax/loc struct-name
                    (combine-out
                     #,@(map (lambda (accessor-name)
                               (quasisyntax/loc struct-name
                                 (combine-out #,(make-frame-name stx accessor-name)
                                              #,(make-down-name stx accessor-name))))
                             (reverse (fourth (extract-struct-info
                                               (syntax-local-value struct-name))))))))
                (syntax->list #'(names ...)))))]))

(module* test-prov #f
  (provide (struct-out A)
           (struct-out B)
           (struct-zipper-out A B))
  (struct A (b c d))
  (struct B (b c d))
  (define-struct-zipper-frames A B))



(module+ test
  (require (submod ".." test-prov))
  (define foo (A-b-frame "c" "d"))

  (struct L () #:transparent)
  (struct T (left right) #:transparent)
  (define-struct-zipper-frames L)       ; no-op
  (define-struct-zipper-frames T)

  (define z1 (zip (T (T (L) (L)) (L))))
  (define z2 (down/T-left z1))
  (check-equal? z2 (zipper (T (L) (L))
                           (list (T-left-frame (L)))))
  (define z3 (up z2))
  (check-equal? z1 z3)
  (define z4 (down/T-right z3))
  (check-equal? z4 (zipper (L) (list (T-right-frame (T (L) (L))))))

  (check-exn exn:fail:contract?
             (thunk (down/T-left (zip "not a T"))))
  (check-false (can-move? down/T-left (zip (L))))
  (check-false (can-move? down/T-right (zip (L))))
  (check-true (can-move? down/T-left (zip (T (L) (L)))))
  (check-true (can-move? down/T-right (zip (T (L) (L)))))

  (struct variable (name) #:transparent)
  (struct lam (name body) #:transparent)
  (struct app (rator rand) #:transparent)
  (define-struct-zipper-frames variable lam app)

  (define ω (app (lam "x" (app (variable "x") (variable "x")))
                 (lam "x" (app (variable "x") (variable "x")))))
  (define ω-zipper (zip ω))
  (check-equal? (zipper-at-top? ω-zipper) #t)
  (check-equal? (zipper-not-at-top? ω-zipper) #f)

  (define ω-l (down/app-rator ω-zipper))
  (check-equal?
   ω-l
   (zipper (lam "x" (app (variable "x") (variable "x")))
           (list (app-rator-frame (lam "x" (app (variable "x")
                                                (variable "x")))))))
  (define ω-l-r (down/lam-body ω-l))
  (check-equal?
   ω-l-r
   (zipper (app (variable "x") (variable "x"))
           (list (lam-body-frame "x")
                 (app-rator-frame (lam "x" (app (variable "x")
                                                (variable "x")))))))
  (check-equal? (zipper-at-top? ω-l-r) #f)
  (check-equal? (zipper-not-at-top? ω-l-r) #t)

  (check-equal? (up ω-l-r) ω-l)
  (define n (down/variable-name (down/app-rand ω-l-r)))
  (check-equal?
   n
   (zipper "x"
           (list
            (variable-name-frame)
            (app-rand-frame (variable "x"))
            (lam-body-frame "x")
            (app-rator-frame (lam "x" (app (variable "x")
                                           (variable "x")))))))
  (check-equal? (rebuild n) ω)
  )


;;;; Zipper utilities for common datatypes

(struct pair-car-frame (cdr)
  #:property prop:zipper-frame
  (lambda (frame focus)
    (match frame
      [(pair-car-frame x)
       (cons focus x)]))
  #:transparent)

(define down/car
  (zipper-movement
   (match-lambda
     [(zipper (cons fst snd) context)
      (zipper fst (cons (pair-car-frame snd)
                        context))]
     [(zipper focus _)
      (raise-argument-error 'down/car
                            (symbol->string 'pair?)
                            focus)])
   (lambda (z)
     (pair? (zipper-focus z)))))

(struct pair-cdr-frame (car)
  #:property prop:zipper-frame
  (lambda (frame focus)
    (match frame
      [(pair-cdr-frame x)
       (cons x focus)]))
  #:transparent)

(define down/cdr
  (zipper-movement
   (match-lambda
     [(zipper (cons fst snd) context)
      (zipper snd (cons (pair-cdr-frame fst)
                        context))]
     [(zipper focus _)
      (raise-argument-error 'down/cdr
                            (symbol->string 'pair?)
                            focus)])
   (lambda (z)
     (pair? (zipper-focus z)))))

(struct list-item-frame (to-left to-right)
  #:property prop:zipper-frame
  (lambda (frame focus)
    (match frame
      [(list-item-frame l r)
       (append (reverse l) (list focus) r)]))
  #:transparent)

(define down/list-first
  (zipper-movement
   (lambda (z)
     (match z
       [(zipper (list-rest x xs) context)
        (zipper x (cons (list-item-frame '() xs)
                        context))]
       [(zipper focus _)
        (raise-argument-error 'down/list-first
                              (symbol->string 'list?)
                              focus)]))
   (lambda (z)
     (pair? (zipper-focus z)))))

(define left/list
  (zipper-movement
   (lambda (z)
     (match z
       [(zipper x (list-rest (list-item-frame (list-rest l ls) rs) context))
        (zipper l (cons (list-item-frame ls (cons x rs))
                        context))]
       [(zipper x (list-rest (list-item-frame (list) rs) _))
        (raise-argument-error 'left/list
                              (symbol->string 'pair?)
                              '())]
       [(zipper _ (cons f fs))
        (raise-argument-error 'left/list
                              (symbol->string list-item-frame?)
                              f)]
       [(zipper _ (list))
        (raise-argument-error 'left/list
                              (symbol->string pair?)
                              '())]))
   (lambda (z)
     (match (zipper-context z)
       [(cons (list-item-frame (cons _ _) _) _)
        #t]
       [_ #f]))))

(define right/list
  (zipper-movement
   (match-lambda
     [(zipper x (list-rest (list-item-frame ls (list-rest r rs)) context))
      (zipper r (cons (list-item-frame (cons x ls) rs) context))]
     [(zipper x (list-rest (list-item-frame ls (list)) _))
      (raise-argument-error 'right/list
                            (symbol->string 'pair?)
                            '())]
     [(zipper _ (cons f fs))
      (raise-argument-error 'right/list
                            (symbol->string 'list-item-frame?)
                            f)]
     [(zipper _ (list))
      (raise-argument-error 'right/list
                            (symbol->string 'pair?)
                            '())])
   (lambda (z)
     (match (zipper-context z)
       [(cons (list-item-frame _ (cons _ _)) _)
        #t]
       [_ #f]))))

(define (down/list-ref i)
  (define (go-right j z)
    (if (= j 0)
        z
        (go-right (sub1 j) (right/list z))))
  (if (not (exact-nonnegative-integer? i))
      (raise-argument-error 'down/list-ref
                            (symbol->string 'exact-nonnegative-integer?)
                            i)
      (zipper-movement
       (lambda (z) (go-right i (down/list-first z)))
       (match-lambda
         [(zipper (? pair? xs) _)
          (> (length xs) i)]
         [_ #f]))))

(module+ test
  (define some-list (zip '(a b c d)))
  (define right-twice (down/cdr (down/cdr some-list)))
  (check-equal? right-twice
                (zipper '(c d)
                        (list (pair-cdr-frame 'b)
                              (pair-cdr-frame 'a))))
  (check-equal? (up (down/cdr right-twice)) right-twice)
  (check-equal? (rebuild (edit reverse right-twice))
                '(a b d c))
  (check-eqv? (zipper-focus (down/car right-twice)) 'c)
  (check-equal? (rebuild (edit add1 (down/car (zip (cons 1 2)))))
                (cons 2 2))
  (check-exn exn:fail:contract?
             (thunk (down/car (zip 'nope))))
  (check-exn exn:fail:contract?
             (thunk (down/cdr (zip 'nope))))

  (check-true (can-move? down/car (zip (cons 'a 'b))))
  (check-true (can-move? down/cdr (zip (cons 'a 'b))))
  (check-false (can-move? down/car (zip 'a)))
  (check-false (can-move? down/cdr (zip 'a)))

  ;; Grabbing a list-ref gives the right focus
  (check-eqv? (zipper-focus ((down/list-ref 3) some-list))
              'd)
  ;; Moving left works
  (check-eqv? (zipper-focus (left/list ((down/list-ref 3) some-list)))
              'c)
  ;; Moving right works
  (check-eqv? (zipper-focus (right/list (left/list ((down/list-ref 3) some-list))))
              'd)

  (check-true (can-move? (down/list-ref 2) some-list))
  (check-false (can-move? (down/list-ref 5) some-list))

  ;; Can't go left past beginning
  (check-exn exn:fail:contract?
             (thunk (left/list (down/list-first some-list))))
  ;; Can't go right past end
  (check-exn exn:fail:contract?
             (thunk (right/list ((down/list-ref 3) some-list))))

  ;; Rebuilding works
  (check-equal? (rebuild
                 (edit symbol->string
                       (left/list
                        ((down/list-ref 3) some-list))))
                '(a b "c" d))

  ;; Can't grab an element past the length of a list
  (check-exn exn:fail:contract?
             (thunk ((down/list-ref 4) some-list)))

  ;; Can't give bizzarre index values to down/list-ref
  (check-exn exn:fail:contract?
             (thunk ((down/list-ref -1) some-list)))
  (check-exn exn:fail:contract?
             (thunk ((down/list-ref "blue whale") some-list)))

  ;; Focusing on list elements doesn't work when the focus isn't a list
  (check-exn exn:fail:contract?
             (thunk ((down/list-ref 0) (zip "hi"))))

  ;; Left and right should fail when the context is empty
  (check-exn exn:fail:contract?
             (thunk (left/list (zip '(a b c)))))
  (check-exn exn:fail:contract?
             (thunk (right/list (zip '(a b c)))))

  ;; Left and right should fail when the context has the wrong frame
  (check-exn exn:fail:contract?
             (thunk (left/list (down/cdr some-list))))
  (check-exn exn:fail:contract?
             (thunk (right/list (down/cdr some-list))))
)


(struct set-member-frame (other-members)
  #:property prop:zipper-frame
  (lambda (frame focus)
    (match frame
      [(set-member-frame other-members)
       (set-add other-members focus)]))
  #:transparent)

(define (down/set-member element)
  (zipper-movement
   (match-lambda
     [(zipper (? set? s) context)
      (if (set-member? s element)
          (zipper element (cons (set-member-frame (set-remove s element))
                                context))
          (raise-argument-error 'down/set-member
                                (format "(set-member? ~a ~a)" s element)
                                s))]
     [(zipper focus _)
      (raise-argument-error 'down/set-member
                            (symbol->string 'set?)
                            focus)])
   (lambda (z)
     (and (set? (zipper-focus z))
          (set-member? (zipper-focus z) element)))))

(module+ test
  (define set-of-sets (zip (set (set 1 2) (set 2 3) 'bananas)))
  (check-false (can-move? (down/set-member 'a) set-of-sets))
  (check-true (can-move? (down/set-member (set 1 2)) set-of-sets))
  (define set-12 ((down/set-member (set 1 2)) set-of-sets))
  (define one ((down/set-member 1) set-12))
  (check-equal? (zipper-focus one) 1)
  (define other-set (rebuild (edit add1 one)))
  (check-equal? other-set (set (set 2) 'bananas (set 3 2)))
  (check-exn exn:fail:contract?
             (thunk (down/set-member "halløjsa" set-of-sets)))
  (check-exn exn:fail:contract?
             (thunk (down/set-member 1 (zip (cons 1 2))))))

