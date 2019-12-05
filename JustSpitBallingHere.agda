module JustSpitBallingHere where

-- open import Basics001
open import Basics002


--what if we create a generating matrix

G : matrix[ 4 , 7 ] ℕ
G = [ [ 1 , 0 , 0 , 0 , 1 , 1 , 0 ] ,
      [ 0 , 1 , 0 , 0 , 1 , 0 , 1 ] ,
      [ 0 , 0 , 1 , 0 , 0 , 1 , 1 ] ,
      [ 0 , 0 , 0 , 1 , 1 , 1 , 1 ]
    ]

-- and a scrambler matrix
Sc : matrix[ 4 , 4 ] ℕ
Sc = [ [ 1 , 1 , 0 , 1 ] ,
      [ 1 , 0 , 0 , 1 ] ,
      [ 0 , 1 , 1 , 1 ] ,
      [ 1 , 1 , 0 , 0 ]
  ]

--and permutation matrix

P : matrix[ 7 , 7 ] ℕ
P = [ [ 0 , 1 , 0 , 0 , 0 , 0 , 0 ] ,
      [ 0 , 0 , 0 , 1 , 0 , 0 , 0 ] ,
      [ 0 , 0 , 0 , 0 , 0 , 0 , 1 ] ,
      [ 1 , 0 , 0 , 0 , 0 , 0 , 0 ] ,
      [ 0 , 0 , 1 , 0 , 0 , 0 , 0 ] ,
      [ 0 , 0 , 0 , 0 , 0 , 1 , 0 ] ,
      [ 0 , 0 , 0 , 0 , 1 , 0 , 0 ]
    ]

-- slice : ∀ {n : ℕ} → idx (S n) → matrix[ n , S n ] ℕ → matrix[ n , n ] ℕ
-- slice i [] = []
-- slice i [ x ] = ({!   !} ∷ {!   !}) ∷ {!   !}
-- slice i (x ∷ x₁ ∷ xss) = {!   !}

-- you can do this by:
-- ‣ not by induction
-- ‣ dropping first row (easy because because you know there are (S n)
--   rows) (maybe this is already done)
-- ‣ for all rows after the first, drop the ith element (using remove-idx)
--   you can do this with map[vec], or define directly
slice : ∀ {n : ℕ} → idx (S n) → matrix[ S n , S n ] ℕ → matrix[ n , n ] ℕ
slice Z (x ∷ m) = map[vec] (λ x₁ → {!   !}) {!   !}
slice (S i) m = map[vec] (λ x → {!   !}) {!   !}

pred : ∀ (n : ℕ) → idx n → ℕ
pred Z ()
pred (S n) Z = n
pred (S n) (S i) = S (pred n i)

remove-idx : ∀ {n : ℕ} (i : idx n) → vec[ n ] ℕ → vec[ pred n i ] ℕ
remove-idx Z (x ∷ xs) = xs
remove-idx (S i) (x ∷ xs) = x ∷ remove-idx i xs

mutual
  det-elem : ∀ {n : ℕ} → idx (S (S n)) → vec[ S (S n) ] ℕ → matrix[ S n , S (S n) ] ℕ → ℕ
  det-elem i xs xss = xs #[ i ] × (det ({!slice i xss  !}))

  -- vec-iter is now called vlfold, part of the state will be a
  -- boolean, is it plus or minus
  det : ∀ {n : ℕ} → matrix[ S n , S n ] ℕ → ℕ
  det {0} [ [ x ] ] = x
  det {S n} (xs ∷ xss) = det ((n ∷ {!   !}) ∷ {!   !})
