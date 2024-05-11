(define add1
  (lambda (f)
    (+ f 1)))

(display (add1 (add1 40)))
