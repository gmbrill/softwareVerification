module JustSpitBallingHere where

-- open import Basics001
open import Basics002

-- INTEGER MINUS

infixl 25 _-_
_-_ : ℤ → ℤ → ℤ
Pos x - Pos y = x ∸ y
Pos x - NegS y = Pos (x + (S y))
NegS x - Pos y = NegS (x + y)
NegS x - NegS y = y ∸ x

-- INTEGER NEGATION

neg : ℤ → ℤ
neg x = Pos 0 - x

--won't let me do this  :(
data zvec (A : Set) : ℤ → Set where
  [] : zvec A (Pos 0)
  _∷_ : ∀ {n} → A → zvec A (Pos n) → zvec A (Pos( S n ))

--
-- zvec[_] : ℤ → Set → Set
-- zvec[ (Pos z) ] A = vec A (Pos z)
-- {-# DISPLAY vec A (Pos z = vec[ (Pos z) ] A #-}



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
-- slice : ∀ {n : ℕ} → idx (S n) → matrix[ S n , S n ] ℕ → matrix[ n , n ] ℕ
-- slice Z (x ∷ m) = map[vec] (λ x₁ → {!   !}) {!   !}
-- slice (S i) m = map[vec] (λ x → {!   !}) {!   !}

pred : ∀ (n : ℕ) → idx n → ℕ
pred Z ()
pred (S n) Z = n
pred (S n) (S i) = S (pred n i)

remove-idx : ∀ {n : ℕ} (i : idx n) → vec[ n ] ℤ → vec[ pred n i ] ℤ
remove-idx Z (x ∷ xs) = xs
remove-idx (S i) (x ∷ xs) = x ∷ remove-idx i xs

-- TODO: 1 -- this should not be too bad
--having trouble with this, can't seem to get the inductive cases???
pred-S-n : ∀ (n : ℕ ) (i : idx (S n)) → pred (S n) i ≡ n
pred-S-n Z i = {!    !}
pred-S-n (S n) i = {!   !}
-- TODO: 2 -- this should also not be too bad
-- (minus goes first)
--saying it wants a natural number for some reason? ~tyyyype errrrroooor~
--want - the first - alternating-plus-minus the rest of the vec
alternating-plus-minus : ∀ {n} → vec[ n ] ℤ → ℤ
alternating-plus-minus [] = Pos 0
alternating-plus-minus (x ∷ xs) = {! ( NegS x ) +ᶻ ( NegS alternating-plus-minus xs )     !}

-- 2 - 4 + 5 - 9
_ : alternating-plus-minus [ Pos 2 , Pos 4 , Pos 5 , Pos 9 ] ≡ neg (Pos 6)
_ = ↯

-- det-elem : ∀ {n : ℕ} → idx (S (S n)) → vec[ S (S n) ] ℕ → matrix[ S n , S (S n) ] ℕ → ℕ
-- det-elem i xs xss = xs #[ i ] × (det ({!slice i xss  !}))


-- TODO: 3 -- solve this hole
smaller : ∀ {n : ℕ} (i : idx (S n)) → matrix[ S n , S n ] ℤ → matrix[ n , n ] ℤ
smaller {n} i (xs ∷ xss) = map[vec] f xss
  where
    f : vec[ S n ] ℤ → vec[ n ] ℤ
    f xs = remove-idx {!   !} {!   !}
    --f xs = {!remove-idx i xs !}

-- vec-iter is now called vlfold, part of the state will be a
-- boolean, is it plus or minus
{-# TERMINATING #-}
det : ∀ {n : ℕ} → matrix[ S n , S n ] ℤ → ℤ
det {0} [ [ x ] ] = x
det {S n} xss =
  let sub-problems : vec[ S (S n) ] (matrix[ S n , S n ] ℤ)
      sub-problems = build[ S (S n) ] (λ i → smaller i xss)
      sub-problems-dets : vec[ S (S n) ] ℤ
      sub-problems-dets = map[vec] (λ xss′ → det xss′) sub-problems
      sub-problems-prods = build[ S (S n) ] (λ i → xss #[ Z ] #[ i ] ×ᶻ sub-problems-dets #[ i ])
      answer : ℤ
      answer = alternating-plus-minus sub-problems-prods
  in answer
  -- det (vlfold {!   !} ((n ∷ {!   !}) ∷ {!   !}) (λ x x₁ x₂ → (n ∷ {!   !}) ∷ {!   !}))
