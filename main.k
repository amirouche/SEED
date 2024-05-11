(define reverse
  (lambda (objects)
    (define reverse%
      (lambda (objects out)
        (if (null? objects)
            out
            (reverse% (cdr objects) (cons (car objects) out)))))
    (reverse% objects (list))))

(define pk
  (lambda args
    (display ";; ")
    (write args)
    (newline)
    (car (reverse args))))

(define add (xeno +))

(define add1
  (lambda (f)
    (pk f)
    (add f 1)))

(pk "out" (add1 (add1 40)))
