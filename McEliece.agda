module McEliece where

open import Basics002

mod-helper : ℕ → ℕ → ℕ → ℕ → ℕ
mod-helper k m  Z    j      = k
mod-helper k m (S n)  Z   = mod-helper 0 m n m
mod-helper k m (S n) (S j) = mod-helper (S k) m n j

{- mod -}
_%_ : ℕ → ℕ → ℕ
n % Z = n
n % (S m) = mod-helper 0 m n m


{- addition of vectors -}
_plus_ : {n : ℕ} → vec[ n ] → vec[ n ] → vec[ n ]
[] plus [] = []
(x ∷ xs) plus (y ∷ ys) = (x + y) ∷ (xs plus ys)

{- multiplication with a scalar -}
_scalar_ : {n : ℕ} → ℕ → vec[ n ] → vec[ n ]
k scalar [] = []
k scalar (x ∷ xs) = (k × x) ∷ (k scalar xs)

{- multiplication of a vector and a matrix -}
_v×m_ : {m n : ℕ} → vec[ m ]  → matrix[ m , n ] → vec[ n ]
[] v×m [] = Z
(x ∷ xs) v×m (ys ∷ yss) = (x scalar ys) scalar (xs v×m yss)

{- matrix multiplication -}
_m×m_ : {l m n : ℕ} → matrix[ l , m ] → matrix[ m , n ] → matrix[ l , n ]
[] m×m yss = []
(x ∷ xs) m×m (ys ∷ yss) = (x m×m ys) plus (xs m×m yss)

-- x + y ∷
-- k × x ∷
