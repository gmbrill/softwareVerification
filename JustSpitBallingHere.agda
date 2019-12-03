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

slice : ∀ {n : ℕ} → idx (S n) → matrix[ n , S n ] ℕ → matrix[ n , n ] ℕ
slice i [] = []
slice i [ x ] = ({!   !} ∷ {!   !}) ∷ {!   !}
slice i (x ∷ x₁ ∷ xss) = {!   !}

mutual
  det-elem : ∀ {n : ℕ} → idx (S (S n)) → vec[ S (S n) ] ℕ → matrix[ S n , S (S n) ] ℕ → ℕ
  det-elem i xs xss = xs #[ i ] × (det (slice i xss))

  -- vec-iter is now called vlfold, part of the state will be a
  -- boolean, is it plus or minus
  det : ∀ {n : ℕ} → matrix[ S n , S n ] ℕ → ℕ
  det {0} [ [ x ] ] = x
  det {S n} (xs ∷ xss) = {!   !}
