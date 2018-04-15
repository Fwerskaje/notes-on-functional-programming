(defmodule ex1
  (export all))

(defun double (n)
  (* n 2))

(defun fac
  ((1) 1)
  ((n) (* n (fac (- n 1)))))

(defun convert
  ((m 'inch) (/ m 2.54))
  ((n 'centimeter) (* n 2.54)))

(defun convert-length
  (((tuple 'centimeter x)) (tuple 'inch (/ x 2.54)))
  (((tuple 'inch y))       (tuple 'centimeter (* y 2.54))))

(defun list-length
  ((()) 0)
  (((cons _ xs)) (+ 1 (list-length xs))))

(defun last
  (((cons x ())) x)
  (((cons _ xs)) (last xs)))

(defun say-something
  ([what 0] 'done)
  ([what times]
   (io:format "~p~n" (list what))
   (say-something what (- times 1))))

(defun start ()
  (spawn 'ex1 'say-something '(hello 3))
  (spawn 'ex1 'say-something '(goodbye 3)))
