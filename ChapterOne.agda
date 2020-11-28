module ChapterOne where

open import Function
open import Data.Nat
open import Data.Product using (_×_; _,_)


-- `Vec`'s first argument is a uniform abstraction - it's a *parameter*.
-- `Vec`'s second argument varies in each instance (we're providing an inductive definition) -- it's an *index*.
data Vec (X : Set) : ℕ → Set where
  ⟨⟩ : Vec X zero
  _,_ : {n : ℕ} → X → Vec X n → Vec X (suc n)

zipWith : ∀ {n A B C} → (f : A → B → C) → Vec A n → Vec B n → Vec C n
zipWith f ⟨⟩ ⟨⟩ = ⟨⟩
zipWith f (x , u) (y , v) = (f x y) , (zipWith f u v)

{- Exercise 1.1 -}

vec : ∀ {n A} → A → Vec A n
vec {zero} x = ⟨⟩
vec {suc n} x = x , (vec x) -- NOTE: {n} is inferred!

{- Exercise 1.2 -}

vapp : ∀ {n S T} → Vec (S → T) n → Vec S n → Vec T n
vapp ⟨⟩ ⟨⟩ = ⟨⟩
vapp (f , fs) (x , xs) = f x , vapp fs xs

{- Exercise 1.3 -}

vmap : ∀ {n S T} → (S → T) → Vec S n → Vec T n
vmap f ⟨⟩ = ⟨⟩
vmap f (x , xs) = (f x) , (vmap f xs)

{- Exercise 1.4 -}

zip : ∀ {n S T} → Vec S n → Vec T n → Vec (S × T) n
zip {n} xs ys = vapp (vapp (vec _,_) xs) ys

{- Exercise 1.5 -}

data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (suc n)
  suc : {n : ℕ} → Fin n → Fin (suc n)

proj : ∀ {n X} → Vec X n → Fin n → X
proj (x , xs) zero = x
proj (x , xs) (suc n) = proj xs n

-- NOTE: this is tricky to grok
tabulate : ∀ {n X} → (Fin n → X) → Vec X n
tabulate {zero} {X} f = ⟨⟩
tabulate {suc n} {X} f = (f zero) , (tabulate (f ∘ suc))

{-= 1.3 Applicative and Traversable Structure ===============================-}

record EndoFunctor (F : Set → Set) : Set₁ where
  field
    map : ∀ {S T} → (S → T) → (F S → F T)
open EndoFunctor {{...}} public

-- NOTE: usage of {{...}} brings into top level scope a different signature for map:
--   w/o {F : Set → Set} → EndoFunctor F → {S T : Set} → (S → T) → F S → F T
--   w/  {F : Set → Set} ⦃ r : EndoFunctor F ⦄ {S T : Set} → (S → T) → F S → F T

record Applicative (F : Set → Set) : Set₁ where
  field
    pure : ∀ {X} → X → F X
    _⊛_ : ∀ {S T} → F (S → T) → (F S → F T)
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record { map = _⊛_ ∘ pure }
open Applicative {{...}} public

applicativeVec : ∀ {n} → Applicative λ{ X → Vec X n }
applicativeVec = record { pure = vec ; _⊛_ = vapp }
endoFunctorVec : ∀ {n} → EndoFunctor λ{ X → Vec X n }
-- TODO: for some reason the instance resolution algorithm isn't picking upp applicativeVec -- why?
endoFunctorVec = applicativeEndoFunctor {{applicativeVec}}

-- TODO: this is the functor part of the reader monad, i think. Is it?
applicativeFun : ∀ {S} → Applicative λ{ X → (S → X) }
applicativeFun = record
  { pure = λ x s → x           -- a.k.a. drop environment
  ; _⊛_ = λ f a s → f s (a s)  -- a.k.a. share environment
  }

record Monad (F : Set → Set) : Set₁ where
  field
    return : ∀ {X} → X → F X
    _>>=_ : ∀ {S T} → F S → (S → F T) → F T
  monadApplicative : Applicative F
  monadApplicative = record
    { pure = return
    -- NOTE: the binds are just "opening up" the monad; onece you realize that it's just hole filling.
    ; _⊛_ = λ Ff Fs → Ff >>= λ f → Fs >>= λ s → return (f s)
    }
open Monad {{...}} public

{- Exercise 1.6 -}

-- TODO: understand https://stackoverflow.com/a/18591371/6438061 efficiency of Monad/Applicative

monadVec : {n : ℕ} → Monad λ{ X → Vec X n }
monadVec = record
  { return = vec
  ; _>>=_ = λ Fs s↦Ft → vmap ((flip proj) {!!} ∘ s↦Ft) Fs -- TODO: this is horrible and I'm stuck
  }

-- TODO: verify that monadApplicative agrees extensionally with applicativeVec

{- Exercise 1.7 -}

applicativeId : Applicative id
applicativeId = record
  { pure = id
  ; _⊛_ = _$_ -- which is just λ{ f s → f s } a.k.a. application
  }

applicativeComp : ∀ {F G} → Applicative F → Applicative G → Applicative (F ∘ G)
applicativeComp {F} {G}
  record { pure = pure₁ ; _⊛_ = _⊛₁_ }
  record { pure = pure₂ ; _⊛_ = _⊛₂_ }
  =
  record
    { pure = pure₁ ∘ pure₂
    ; _⊛_ = {!!}
    --; _⊛_ = λ [F∘G]s↦t [F∘G]s → {!!} -- TODO: stuck again :(
    }


