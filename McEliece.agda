module McEliece where

open import Basics001

mod-helper : ℕ → ℕ → ℕ → ℕ → ℕ
mod-helper k m  Z    j      = k
mod-helper k m (S n)  Z   = mod-helper 0 m n m
mod-helper k m (S n) (S j) = mod-helper (S k) m n j
{-# BUILTIN NATMODSUCAUX mod-helper #-}

_%_ : ℕ → ℕ → ℕ
Z % n  =  Z
(S n) % m = mod-helper 0 n m n

_ : 4 % 2 ≡ 2
_ = ↯
