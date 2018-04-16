(defmodule ex2
  (export all))
;;  (import
;;   (from clj (true? 1) (->> 1))))

(defun f ()
  (lc ((<- v
	   (when (> v 5))
	   [1 2 3 4 5 6 7 8 9 10])
       (== (rem v 2) 0))
    v))

(defmodule ex3
  (export all))

(defun id (n) n)