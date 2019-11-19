module McEliece where

open import Basics002

mod-helper : ℕ → ℕ → ℕ → ℕ → ℕ
mod-helper k m  Z    j      = k
mod-helper k m (S n)  Z   = mod-helper 0 m n m
mod-helper k m (S n) (S j) = mod-helper (S k) m n j

_%_ : ℕ → ℕ → ℕ
n % Z = n
n % (S m) = mod-helper 0 m n m
