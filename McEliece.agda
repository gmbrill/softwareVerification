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

zeros : {n : ℕ} → vec[ n ] ℕ
zeros {Z} = []
zeros {S n} = Z ∷ zeros {n}

{- addition of vectors -}
_plus_ : {n : ℕ} → vec[ n ] ℕ → vec[ n ] ℕ → vec[ n ] ℕ
[] plus [] = []
(x ∷ xs) plus (y ∷ ys) = (x + y) ∷ (xs plus ys)

{- multiplication with a scalar -}
_scalar_ : {n : ℕ} → ℕ → vec[ n ] ℕ → vec[ n ] ℕ
k scalar [] = []
k scalar (x ∷ xs) = (k × x) ∷ (k scalar xs)

{- multiplication of a vector and a matrix -}
_v×m_ : {m n : ℕ} → vec[ m ] ℕ → matrix[ m , n ] ℕ → vec[ n ] ℕ
[] v×m [] = zeros
(x ∷ xs) v×m (ys ∷ yss) = (x scalar ys) plus (xs v×m yss)

{- matrix multiplication -}
_m×m_ : {l m n : ℕ} → matrix[ l , m ] ℕ → matrix[ m , n ] ℕ → matrix[ l , n ] ℕ
[] m×m yss = []
(xs ∷ xss) m×m yss = (xs v×m yss) ∷ (xss m×m yss)
