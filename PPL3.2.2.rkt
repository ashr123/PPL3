#lang racket

(define foo
  (lambda (goo)
    (let ((a 1)
          (b 2))
      ((lambda (a b)
        (lambda (arg)
          (goo arg))) a b))))
(define goo
  (foo (lambda (y)
       (+ y 5))))
(goo 5)