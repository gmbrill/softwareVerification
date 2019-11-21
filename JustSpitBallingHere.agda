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


--determinanats
det : {n : ℕ} → matrix[ n , n ] ℕ → ℕ
det [] = Z
det (x ∷ n) = {!   !}
