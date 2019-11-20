module JustSpitBallingHere where

-- open import Basics001
open import Basics002


--what if we create a generating matrix

G : matrix[ 4 , 7 ] ℤ
G = [ [ 1 , 0 , 0 , 0 , 1 , 1 , 0 ] ,
      [ 0 , 1 , 0 , 0 , 1 , 0 , 1 ] ,
      [ 0 , 0 , 1 , 0 , 0 , 1 , 1 ] ,
      [ 0 , 0 , 0 , 1 , 1 , 1 , 1 ]
    ]

-- and a scrambler matrix
Sc : matrix[ 4 , 4 ] ℤ
Sc = [ [ 1 , 1 , 0 , 1 ] ,
      [ 1 , 0 , 0 , 1 ] ,
      [ 0 , 1 , 1 , 1 ] ,
      [ 1 , 1 , 0 , 0 ]
  ]

--and permutation matrix

P : matrix[ 7 , 7 ] ℤ
P = [ [ 0 , 1 , 0 , 0 , 0 , 0 , 0 ] ,
      [ 0 , 0 , 0 , 1 , 0 , 0 , 0 ] ,
      [ 0 , 0 , 0 , 0 , 0 , 0 , 1 ] ,
      [ 1 , 0 , 0 , 0 , 0 , 0 , 0 ] ,
      [ 0 , 0 , 1 , 0 , 0 , 0 , 0 ] ,
      [ 0 , 0 , 0 , 0 , 0 , 1 , 0 ] ,
      [ 0 , 0 , 0 , 0 , 1 , 0 , 0 ]
    ]
    --first thing is new num 2nd is what we're modding by


-- infixl 15 _mod_
-- _mod_ : ℕ → ℕ → ℕ
-- Z mod n = Z
-- S( m ) mod n = 1 + ( m mod n )

-- _ : 4 mod 3 ≡ 1
-- _ = ↯

--now we have to define matrix mul which is going to be horrifying
--_matMul_ : matrix[ m , n ] → matrix [ n , p ] → matrix [ m , p ]
--Maybe try dot product first
--
-- infixl 16 _dot_
-- _dot_ : = {m n D : ℤ} (xs : vec [ m ]) (ys : vec[ m ]) → D
-- _dot_ xs ys = ?
