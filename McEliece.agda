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


G' : matrix[ 4 , 7 ] ℕ
G' = [ [ 1 , 1 , 0 , 1 , 3 , 2 , 2 ] ,
      [ 1 , 0 , 0 , 1 , 2 , 2 , 1 ] ,
      [ 0 , 1 , 1 , 1 , 2 , 2 , 3 ] ,
      [ 1 , 1 , 0 , 0 , 2 , 1 , 1 ]
     ]

PubKey : matrix[ 4 , 7 ] ℕ
PubKey = [ [ 1 , 1 , 3 , 1 , 2 , 2 , 0 ] ,
           [ 1 , 1 , 2 , 0 , 1 , 2 , 0 ] ,
           [ 1 , 0 , 2 , 1 , 3 , 2 , 1 ] ,
           [ 0 , 1 , 2 , 1 , 1 , 1 , 0 ]
          ]

_ : Sc m×m G ≡ G'
_ = ↯

_ : G' m×m P ≡ PubKey
_ = ↯
