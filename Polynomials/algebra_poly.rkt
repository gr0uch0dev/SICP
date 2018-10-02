#lang racket

; Follwing the section on polynomial of chapter 2 in the book SICP and solving all the excercises
; We report here all the relevant procedures
; From defining different types of numbers (complex/rational/scheme-primitive) and their operations
; To working with ratios of polynomials and allowing also addition of polynomials with a different indeterminant variable

; All the excercises of chapter 2 regarding the algebra of polynomials have been solved and embedded in the overall suite provided here

(define (set-type type obj) (cons type obj))
(define (type x) (car x))
(define (contents x) (cdr x))
 
(define (square x) (* x x))
(define *the-table* (make-hash))
 (define (put key1 key2 value) (hash-set! *the-table* (list key1 key2) value)) 
 (define (get key1 key2) (hash-ref *the-table* (list key1 key2) #f))

(define (apply-generic op . args)
  (let ( (types (map type args)))
    (let ( (proc (get op types)))
      (if proc (apply proc (map contents args))
          (error "Operation not found for the given type" types)))))

; ### UTILS  

(define (list-length items) (apply + (map (lambda (x) 1) items)))

(define (power a b)
  (if (= b 1) a (* a (power a (- b 1)))))
;max works both for (max 1 2 3) and (max '(1 2 3))
(define (max . args) ( define (fun-helper terms max)
                        (if (null? terms) max
                              (let ((first-el (car terms))
                                    (remaining (cdr terms)))
                                (if (> first-el max) (fun-helper remaining first-el) (fun-helper remaining max)))))
  (let ( (first-element (car args)))
  (if (pair? first-element) (fun-helper (cdr first-element) (car first-element))
      (fun-helper (cdr args) first-element))))

(define (remainder-num a b) (- a (* b (floor (/ a b)))))
(define (gcd-num a b)
  (if (= (remainder-num a b) 0) b
      (gcd-num b (remainder-num a b))))

;For any datatypes all the operations that can be performed on them need to be encapsulated in relevant blocks   

(define (install-package-rectangular)
  (define (complex-real-part z) (car z))
  (define (complex-img-part z) (cadr z))
  (define (complex-magnitude z) (sqrt (+ (square (complex-real-part z))
                                         (square (complex-img-part z)))))
  (define (complex-angle z) (atan (complex-real-part z) (complex-img-part z)))
  (put 'complex-real-part '(rectangular) complex-real-part)
  (put 'complex-img-part '(rectangular) complex-img-part)
  (put 'complex-magnitude '(rectangular) complex-magnitude)
  (put 'complex-angle '(rectangular) complex-angle)
  )

(define (install-package-polar)
  (define (complex-magnitude z) (car z))
  (define (complex-angle z) (cadr z))
  (define (complex-real-part z) (* (complex-magnitude z) (cos (complex-angle z))))
  (define (complex-img-part z) (* (complex-magnitude z) (sin (complex-angle z))))
  
  (put 'complex-real-part '(polar) complex-real-part)
  (put 'complex-img-part '(polar) complex-img-part)
  (put 'complex-magnitude '(polar) complex-magnitude)
  (put 'complex-angle '(polar) complex-angle)
  )

(define (install-constructor-rectangular)
  (define (tag z) (set-type 'rectangular z))
  (define (make-from-real-img a b) (list a b))
  (define (make-from-mag-angle r A) (make-from-real-img (* r (cos A)) 
                                                         (* r (sin A))))
  (put 'make-from-real-img 'rectangular (lambda (x y) (tag (make-from-real-img x y))))
  (put 'make-from-mag-angle 'rectangular (lambda (x y) (tag (make-from-mag-angle x y))))
  )

(define (install-constructor-polar)
  (define (tag z) (set-type 'polar z))
  (define (make-from-mag-angle r A) (list r A))
  (define (make-from-real-img a b) (make-from-mag-angle (sqrt (+ (square a) (square b))) (atan a b)))
  
  (put 'make-from-real-img 'polar (lambda (x y) (tag (make-from-real-img x y))))
  (put 'make-from-mag-angle 'polar (lambda (x y) (tag (make-from-mag-angle x y))))
  )
(install-package-rectangular)
(install-package-polar)
(install-constructor-rectangular)
(install-constructor-polar)

(define (complex-real-part z) (apply-generic 'complex-real-part z))
(define (complex-img-part z) (apply-generic 'complex-img-part z))
(define (complex-magnitude z) (apply-generic 'complex-magnitude z))
(define (complex-angle z) (apply-generic 'complex-angle z))
(put 'complex-real-part '(complex) complex-real-part)
(put 'complex-img-part '(complex) complex-img-part)
(put 'complex-magnitude '(complex) complex-magnitude)


(define (install-scheme-numbers)
  (define (tag x) (cons 'scheme-number x))
  (put 'add '(scheme-number scheme-number) (lambda (x y) (+ x y)))
  (put 'sub '(scheme-number scheme-number) (lambda (x y) (- x y)))
  (put 'mul '(scheme-number scheme-number) (lambda (x y) (* x y)))
  (put 'div '(scheme-number scheme-number) (lambda (x y) (/ x y)))
  (put 'make 'scheme-number (lambda (x) (tag x)))
  (put 'negate '(scheme-number) (lambda (x) (tag (- x))))
  (put '=zero? '(scheme-number) (lambda (x) (= x 0)))
  (put 'reduce '(scheme-number scheme-number) (lambda (x1 x2) (let ((g (gcd x1 x2)))
                                                                     (list (tag (/ x1 g)) (tag (/ x2 g))))))
)


; It is important to remember that the object type needs to be specified by the tag!

;package for complex numbers 
;this uses the procedures defined in the rectangular/polar packages

(define (intstall-complex-package)
  (define (tag x) (cons 'complex x))
  (define (make-from-real-img a b) ( (get 'make-from-real-img 'rectangular) a b))
  (define (make-from-mag-angle r A) ( (get 'make-from-mag-angle 'polar) r A))
  
  (define (add-complex z1 z2) (make-from-real-img (+ (complex-real-part z1) (complex-real-part z2))
                                                   (+ (complex-img-part z1) (complex-img-part z2))))

  (define (sub-complex z1 z2) (make-from-real-img (- (complex-real-part z1) (complex-real-part z2))
                                                     (- (complex-img-part z1) (complex-img-part z2))))

  (define (mul-complex z1 z2) (make-from-mag-angle (* (complex-magnitude z1) (complex-magnitude z2))
                                                      (+ (complex-angle z1) (complex-angle z2))))

  (define (div-complex z1 z2) (make-from-mag-angle (/ (complex-magnitude z1) (complex-magnitude z2))
                                                      (- (complex-angle z1) (complex-angle z2))))
  (put 'add '(complex complex) (lambda (z1 z2) (tag (add-complex z1 z2))))
  (put 'sub '(complex complex) (lambda (z1 z2) (tag (sub-complex z1 z2))))
  (put 'mul '(complex complex) (lambda (z1 z2) (tag (mul-complex z1 z2))))
  (put 'div '(complex complex) (lambda (z1 z2) (tag (div-complex z1 z2))))
  (put 'make-from-real-img 'complex (lambda (x y) (tag (make-from-real-img x y))))
  (put 'make-from-mag-angle 'complex (lambda (x y) (tag (make-from-mag-angle x y))))
  (put 'negate '(complex) (lambda (c) (tag (make-from-real-img (- complex-real-part c) (- complex-img-part c)))))
  (put '=zero? '(complex) (lambda (x) (= (complex-real-part x) 0)))
  )
; we see that when a complex is created by real/img part we create an object as: ('complex ('rectangular real img))
; It is complex with a rectangular subtype


(install-scheme-numbers)
(intstall-complex-package)

;we are now able to use the old generic apply procedure.

(define (make-complex-from-real-img a b) ( (get 'make-from-real-img 'complex) a b))
(define (make-complex-from-magnitude-angle r A) ((get 'make-from-mag-angle 'complex)  r A))

(define (make-scheme-number x) ((get 'make 'scheme-number) x))

; ######################
; ######################
(define (gcd-two-args x1 x2) (if (and (number? x1) (number? x2)) (gcd-num x1 x2) (apply-generic 'gcd x1 x2)))

(define (gcd-series args)
  (define (fun-helper terms g)
    (if (= (list-length terms) 1) (gcd-two-args (car terms) g)
        (fun-helper (cdr terms) (gcd-two-args (car terms) g))))
  (if (= (list-length args) 1) (car args)
      (fun-helper (cdr args) (car args))))

#|

; GENERIC PROCEDURES

|#

(define (=zero? x) (if (number? x) (= x 0) (apply-generic '=zero? x)))
(define (add x y) (cond ((and (number? x) (number? y)) (+ x y))
                        ((number? x) (apply-generic 'add  y (cons 'number x)))
                        ((number? y) (apply-generic 'add  x (cons 'number y)))
                        (else (apply-generic 'add x y))))
(define (sub x y) (if (and (number? x) (number? y)) (- x y) (apply-generic 'sub x y)))
(define (mul x y) (cond ( (and (number? x) (number? y)) (* x y))
                        ( (number? x) (apply-generic 'mul (cons 'scheme-number x) y))
                        ( (number? y) (apply-generic 'mul x (cons 'scheme-number y)))
                        (else (apply-generic 'mul x y))))
(define (div x y) (if (and (number? x) (number? y)) (/ x y) (apply-generic 'div x y)))
(define (negate x) (if (number? x) (- x) (apply-generic 'negate x)))

(define (all-of-same-type items) (let ((type-list (map type items)))
                                   (let ( (first-type (car type-list))
                                          (len (list-length type-list)))
                                     (let ( (how-many-of-first-type (apply + (map (lambda (x) (if (eq? x first-type) 1 0)) type-list))))
                                        (= how-many-of-first-type len)))))

(define (gcd . args) (if (all-of-same-type args) (gcd-series args)
                         (error "Arguments not of same type")))

(define (reduce x1 x2) (if (and (number? x1) (number? x2)) (reduce (cons 'scheme-number x1) (cons 'scheme-number x2))
                           (apply-generic 'reduce x1 x2)))



;introduce algebra of polynomials


; mathematical equivalence != symbolic equivalence


(define (install-polynomial-package)
  (define (tag x) (cons 'polynomial x))
  (define (same-variable? x y) (eq? x y))
  (define (poly? p) (if (not (pair? p)) #f (eq? (type p) 'polynomial)))
  (define (make-term order coeff) (list order coeff))
  (define (term-order t) (car t))
  (define (term-coeff t) (cadr t))
  (define (get-term-highest-order T) (car T))
  (define (all-but-the-highest T) (cdr T))
  (define the-empty-terms-list '())
  (define (empty-terms-list? T) (eq? T the-empty-terms-list))
  (define (adjoin-terms t T) (cond ( (poly? t) (if (=zero? t) T (cons t T)))
                                   ( (=zero? (term-coeff t)) T)
                                   (else (cons t T))))

  (define (collapse-terms terms)
  (cond ( (empty-terms-list? terms) terms)
        ( (empty-terms-list?  (cdr terms)) terms)
        (else 
         (let ( (t1 (get-term-highest-order terms)))
           (let ( (t2 (get-term-highest-order (all-but-the-highest terms))))
             (cond ((empty-terms-list? t2) (adjoin-terms t1 t2))
                   ((= (term-order t1) (term-order t2)) (adjoin-terms (make-term (term-order t1)
                                                                                 (add (term-coeff t1) (term-coeff t2)))
                                                                      (all-but-the-highest (all-but-the-highest terms))))
                   (else (adjoin-terms t1 (collapse-terms (all-but-the-highest terms))))))))))
  
  (define (make-poly variable terms) (list variable  (collapse-terms terms)))
  
  (define (poly-variable p) (car p))
  (define (poly-terms p) (cadr p))
  
  (define (add-terms T1 T2)
    (cond ( (empty-terms-list? T2) T1)
          ( (empty-terms-list? T1) T2)
          (else
           (let ( (t1 (get-term-highest-order T1))
                  (t2 (get-term-highest-order T2)))
             (cond ( (> (term-order t1) (term-order t2)) (adjoin-terms t1 (add-terms (all-but-the-highest T1) T2)))
                   ( (< (term-order t1) (term-order t2)) (adjoin-terms t2 (add-terms T1 (all-but-the-highest T2)) ))
                   (else (adjoin-terms (make-term (term-order t1) (add (term-coeff t1) (term-coeff t2)))
                                       (add-terms (all-but-the-highest T1) (all-but-the-highest T2)))))))))
  (define (negate-a-term t)
    (make-term (term-order t) (negate (term-coeff t))))
  (define (negate-terms terms) (map (lambda (x) (negate-a-term x)) terms))
  
  (define (sub-terms T1 T2)
    (add-terms T1 (negate-terms T2)))

  
  (define (mul-constant-by-poly k p)
    (if (eq? (car p) 'polynomial) (mul-constant-by-poly k (cdr p))
        (tag (make-poly (poly-variable p)
                        (map (lambda (x) (make-term (term-order x) (* (term-coeff x) k ))) (poly-terms p))))))
  
  (define (sum-term-multiplied-by-all t T)
    (if (empty-terms-list? T) the-empty-terms-list
        (let ( (t2 (get-term-highest-order T)))
          (let ( (ord-t (term-order t))
                 (coeff-t (term-coeff t))
                 (ord-t2 (term-order t2))
                 (coeff-t2 (term-coeff t2)))
            (cond ( (and (poly? coeff-t) (not (poly? coeff-t2))) (adjoin-terms (make-term (+ ord-t ord-t2) (mul-constant-by-poly coeff-t2 coeff-t))
                                                                               (sum-term-multiplied-by-all t (all-but-the-highest T))))
                  ( (and (poly? coeff-t2) (not (poly? coeff-t))) (adjoin-terms (make-term (+ ord-t ord-t2) (mul-constant-by-poly coeff-t coeff-t2))
                                                                               (sum-term-multiplied-by-all t (all-but-the-highest T))))
                  ( (and (poly? coeff-t2) (poly? coeff-t)) (adjoin-terms (make-term (+ ord-t ord-t2) (tag (mul-poly (cdr coeff-t) (cdr coeff-t2))))
                                                                         (sum-term-multiplied-by-all t (all-but-the-highest T))))
                  (else (adjoin-terms (make-term (+ ord-t ord-t2) (mul coeff-t coeff-t2))
                                      (sum-term-multiplied-by-all t (all-but-the-highest T)))))))))
  

  (define (mul-terms T1 T2)
    (if (or (empty-terms-list? T1) (empty-terms-list? T2)) the-empty-terms-list
        (let ( (t1 (get-term-highest-order T1)))
          (add-terms (sum-term-multiplied-by-all t1 T2)
                     (mul-terms (all-but-the-highest T1) T2)))))

  (define (add-poly p1 p2)
    (if (same-variable? (poly-variable p1) (poly-variable p2))
        (make-poly (poly-variable p1) (add-terms (poly-terms p1) (poly-terms p2)))
        (add-poly-different-variables p1 p2)
       ; (error "Polynomials must have the same symbol for their indeterminant"))
    ))

  (define (add-number-to-poly n p1) ; create a new poly made by just one term (the number as coeff with an order 0) and sum to p1
    (add-poly p1 (make-poly (poly-variable p1) (list (list 0 n)))))

  (define (mul-poly p1 p2)
    (if (same-variable? (poly-variable p1) (poly-variable p2))
        (make-poly (poly-variable p1) (mul-terms (poly-terms p1) (poly-terms p2)))
        (error "Polynomials must have the same symbol for their indeterminant"))
    )

  (define (opposite-sign x) (negate x))

  (define (poly-negate p)
    (let ( (new-terms (map (lambda (x) (make-term (term-order x) (opposite-sign (term-coeff x)))) (poly-terms p))))
      (make-poly (poly-variable p) new-terms))
    )
  (define (sub-poly p1 p2)
  (add-poly p1 (poly-negate p2)))
  
  (define (div-terms L1 L2)
  (if (empty-terms-list? L1) (list the-empty-terms-list the-empty-terms-list)
      (let ( (t1 (get-term-highest-order L1))
             (t2 (get-term-highest-order L2)))
        (if (> (term-order t2) (term-order t1)) (list the-empty-terms-list L1)
            (let ( (new-o (- (term-order t1) (term-order t2)))
                   (new-c (div (term-coeff t1) (term-coeff t2))))
              (let ( (RR (div-terms (sub-terms L1
                                               (sum-term-multiplied-by-all (make-term new-o new-c) L2))
                                    L2)))
                (list (adjoin-terms (make-term new-o new-c) (car RR)) (cadr RR))))))))
  
  (define (div-poly p1 p2)
    (if (same-variable? (poly-variable p1) (poly-variable p2))
        (let ((quotient-and-rest (div-terms (poly-terms p1) (poly-terms p2)))
              (var (poly-variable p1)))
          (map (lambda (x) (make-poly var x)) quotient-and-rest))
        (error "polynomials do not have the same univariate")))
            

  (define (transform-term old-var new-var t)
  (let ( (ord (term-order t))
         (coeff (term-coeff t)))
    (if (poly? coeff) (sum-term-multiplied-by-all (make-term 0  (tag (make-poly old-var (list (list ord 1)))))
                                             (poly-terms (cdr coeff))) ;terms written in accordance to the new variable
        (make-term 0 (tag (make-poly old-var (list (list ord coeff)))))))
  )

  (define (change-dominant-variable p var)
    (let ( (old-var (poly-variable p)))
      (let ((old-terms (poly-terms p)))
        (let ((new-terms (map (lambda (x) (transform-term old-var var x)) old-terms)))
          (make-poly var new-terms))))
    )

  (define (add-poly-different-variables p1 p2)
    (let ( (dominant-variable (poly-variable p1)))
      (let ( (p2-new (change-dominant-variable p2 dominant-variable)))
        (add-poly p1 p2-new))))
  
  (define (remainder-poly p1 p2) (cadr (div-poly p1 p2)))
  (define (poly-order p) (term-order (get-term-highest-order (poly-terms p))))
  (define (poly-leading-coeff p) (term-coeff (get-term-highest-order (poly-terms p))))
  ;(exp a b)
  (define (pseudo-remainder-poly p1 p2)(let ( (c (poly-leading-coeff p2))
                                              (O1 (poly-order p1))
                                              (O2 (poly-order p2)))
                                         (let( (integerizing-constant (power c (+ 1 (- O1 O2)))))
                                           (cadr (div-poly (make-poly (poly-variable p1) (map (lambda (x) (make-term (term-order x)
                                                                                                                     (mul (term-coeff x)
                                                                                                                          integerizing-constant)))   
                                                                                              (poly-terms p1)))
                                                           p2)))))
  
  (define (poly-simplify-coeffs p) (let ((g (gcd-series (map (lambda (x) (term-coeff x)) (poly-terms p)))))
                                     (make-poly (poly-variable p) (map (lambda (x) (make-term (term-order x)
                                                                                              (div (term-coeff x) g)))
                                                                       (poly-terms p)))))
  
  (define (gcd-poly p1 p2) (if (empty-terms-list? (poly-terms p2)) p1 (gcd-poly p2 (remainder-poly p1 p2))))

  (define (reduce-poly p1 p2) (if (same-variable? (poly-variable p1) (poly-variable p2))
                                  (let ( (g (gcd-poly p1 p2))
                                         (max-order-first (max (map (lambda (x) (term-order x)) (poly-terms p1))))
                                         (max-order-second (max (map (lambda (x) (term-order x)) (poly-terms p1)))))
                                    (let ( (c (poly-leading-coeff g))
                                           (O1 (max max-order-first max-order-second))
                                           (O2 (poly-order p1)))
                                      (let ( (integerizing-k (power c (+ 1 (- O1 O2))))
                                             (multiplicate-poly-terms-by-k (lambda (k p) (make-poly (poly-variable p)
                                                                                                    (map (lambda (t) (make-term (term-order t)
                                                                                                                                (mul k (term-coeff t))))
                                                                                                         (poly-terms p))))))
                                        (let ( (p1-new (multiplicate-poly-terms-by-k integerizing-k p1))
                                               (p2-new (multiplicate-poly-terms-by-k integerizing-k p2)))
                                          (map (lambda (p) (poly-simplify-coeffs p)) (list p1-new p2-new))))))
                                  (error "Polynomials with different univariates")))
    
  ; installing the polynomial interface
  ;it is in the interfece that the type should be tagged 
  (put 'make 'polynomial (lambda (x y) (tag (make-poly x y))))
  (put 'add '(polynomial polynomial) (lambda (p1 p2) (tag (add-poly p1 p2))))
  (put 'sub '(polynomial polynomial) (lambda (p1 p2) (tag (sub-poly p1 p2))))
  (put 'mul '(polynomial polynomial) (lambda (p1 p2) (tag (mul-poly p1 p2))))
  (put 'div '(polynomial polynomial) (lambda (p1 p2) (map (lambda (x)  (tag x)) (div-poly p1 p2))))
  (put '=zero? '(polynomial) (lambda (x) (empty-terms-list? (poly-terms x))))
  (put 'poly-variable 'polynomial poly-variable)
  (put 'poly-terms 'polynomial poly-terms)
  (put 'make-term 'polynomial make-term)
  (put 'negate '(polynomial) (lambda (x) (tag (poly-negate x))))
  (put 'transform-variable 'polynomial (lambda (p x) (tag (change-dominant-variable p x))))
  (put 'add '(polynomial number) (lambda (p n) (tag (add-number-to-poly n p))))
  (put 'collapse-terms 'polynomial collapse-terms)
  (put 'gcd '(polynomial polynomial) (lambda (p1 p2) (tag (poly-simplify-coeffs (gcd-poly p1 p2)))))
  (put 'make_simplified 'polynomial (lambda (v terms) (tag (poly-simplify-coeffs (make-poly v terms)))))
  (put 'reduce '(polynomial polynomial) (lambda (p1 p2) (map (lambda (x) (tag x)) (reduce-poly p1 p2))))
  (put 'mul '(scheme-number polynomial) (lambda (x p) (tag (mul-constant-by-poly x p))))
  (put 'mul '(polynomial scheme-number) (lambda (p x) (tag (mul-constant-by-poly x p)))) 
)

(install-polynomial-package)

(define (make-poly variable terms) ((get 'make 'polynomial) variable terms))
(define (make-term order coeff) ((get 'make-term 'polynomial) order coeff))
(define (make-poly-simplified var terms) ((get 'make_simplified 'polynomial) var terms))

(define A (make-poly 'x (list (make-term 5 1) (make-term 3 2) (make-term 0 (make-poly 'y (list (make-term 1 2)))))))
(define B (make-poly 'x (list (make-term 4 1) (make-term 2 2) (make-term 0 (make-poly 'y (list (make-term 1 2)))))))
(define C (make-poly 'x (list (make-term 4 2) (make-term 3 5) )))
(define D (make-poly 'x (list (make-term 6 2) (make-term 4 10) )))
(define Y (make-poly 'y (list (make-term 4 2) (make-term 3 5) )))

(define (install-rational-package)
  (define (tag x) (cons 'rational x))
  (define (make-rational num den) (reduce num den))
  (define (rational-num r) (car r))
  (define (rational-den r) (cadr r))
  ;arithmetic operations for rationals
  (define (add-rational r1 r2) (make-rational (add (mul (rational-num r1) (rational-den r2)) (mul (rational-num r2) (rational-den r1)))
                                     (mul (rational-den r1) (rational-den r2))))
  (define (sub-rational r1 r2) (make-rational (sub (mul (rational-num r1) (rational-den r2)) (mul (rational-num r2) (rational-den r1)))
                                     (mul (rational-den r1) (rational-den r2))))
  (define (mul-rational r1 r2) (make-rational (mul (rational-num r1) (rational-num r2))
                                     (mul (rational-den r1) (rational-den r2))))
  (define (div-rational r1 r2) (mul r1 (make-rational (rational-den r2) (rational-num r2))))
  (put 'add '(rational rational) (lambda (r1 r2) (tag (add-rational r1 r2))) )
  (put 'sub '(rational rational) (lambda (r1 r2) (tag (sub-rational r1 r2))) )
  (put 'mul '(rational rational) (lambda (r1 r2) (tag (mul-rational r1 r2))) )
  (put 'div '(rational rational) (lambda (r1 r2) (tag (div-rational r1 r2))) )
  (put 'numerator 'rational rational-num)
  (put 'denominator 'rational rational-den)
  (put 'make 'rational (lambda (x y) (tag (make-rational x y))))
  (put '=zero? '(rational) (lambda (x) (= (rational-num x) 0)))
  (put 'negate '(rational) (lambda (x) (tag (make-rational (- (rational-num x)) (rational-den)))))
  )
(install-rational-package)

; TEST THE PROCEDURES

(define (make-rational n d) ((get 'make 'rational) n d))  

(define p1 (make-poly 'x '((1 1)(0 1))))
(define p2 (make-poly 'x '((3 1)(0 1))))
(define rd (make-rational p1 p2))
(add rd rd)

; gcd for polynomials

(div (make-poly 'x '((5 1) (0 -1)))
     (make-poly 'x '((2 1) (0 -1))))

(define p3 (make-poly 'x '((4 1) (3 -1) (2 -2) (1 2))))
(define p4 (make-poly 'x '( (3 1) (1 -1))))


(gcd p3 p4) ;should be '(polynomial x ((2 -1) (1 1)))


(define P1 (make-poly 'x '( (2 1) (1 -2) (0 1))))
(define P2 (make-poly 'x '( (2 11) (0 7))))
(define P3 (make-poly 'x '( (1 13) (0 5))))
(define Q1 (mul P1 P2))
(define Q2 (mul P1 P3))


(define g (gcd Q1 Q2)) 
P1
g
; g and P1 are be the same. This is achieved by the trick of the integerizing constant
(div Q1 Q2)


(define S (make-poly-simplified (cadr g) (caddr g)))
(reduce P1 P1)
(newline)
; ratios made by polynomials and operations on them
(define a1 (make-poly 'x '((1 1) (0 1))))
(define a2 (make-poly 'x '((3 1) (0 -1))))
(define a3 (make-poly 'x '((1 1))))
(define a4 (make-poly 'x '((2 1) (0 -1))))

(define rf1 (make-rational a1 a2))
(define rf2 (make-rational a3 a4))
(add rf1 rf2)
(mul rf1 rf2)


(define AY (make-poly 'x (list (make-term 2 3) (make-term 1 (make-poly 'y '((2 3) (0 2)))) (make-term 0 (make-poly 'y '((1 4) (0 1))))))) 
(define BY (make-poly 'x (list (make-term 3 (make-poly 'y '((1 1) (0 5)))) (make-term 1 3) (make-term 0 (make-poly 'y '((1 -1)))))))
AY
BY
(add AY BY)
(mul AY BY)

;add two polynomials with different variables
(define py (make-poly 'y '((3 4) (2 2) (0 1))))
AY
py
(add AY py)
