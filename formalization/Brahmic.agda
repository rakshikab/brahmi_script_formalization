{-# OPTIONS --safe #-}
module Brahmic where

open import Data.Maybe
open import Data.Product hiding (map)
import Relation.Binary.PropositionalEquality as Eq
open Eq
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Agda.Builtin.Unit
open import Data.Char
open import Data.Empty
open import Data.Sum
open import Data.Bool using (Bool; true; false; if_then_else_)

------------------------------------------------------------------------
-- The Two Algebraic Levels
------------------------------------------------------------------------

-- Level 1: Semigroup — total combination (English, German, etc.)
-- Any two valid tokens always combine to form a valid token.
record Orthography₁ (Token : Set) : Set where
  field
    combine  : Token → Token → Token
    assoc    : ∀ (x y z : Token) → combine (combine x y) z ≡ combine x (combine y z)

-- Level 2: Partial Semigroup — the universal model for constrained orthographies.
-- combine may fail (returns nothing) when tokens are orthographically incompatible.
-- Vietnamese, Telugu, Kannada, etc. all live here.
record Orthography₂ (Token : Set) : Set where
  field
    combine  : Token → Token → Maybe Token
    assoc    : ∀ (x y z : Token) (xy xyz : Token)
             → combine x y ≡ just xy
             → combine xy z ≡ just xyz
             → ∃ λ yz → combine y z ≡ just yz × combine x yz ≡ just xyz


------------------------------------------------------------------------
--- Brahmic orthography: a case study of Orthography₂
{-
Brahmic Unicode scripts consist of the following character types
(illustrated here with Telugu Unicode ranges) :

    VowelSuffix : [U+0C00 .. U+0C04]
    IndependentVowel : (roughly) [U+0C05 .. U+0C14]
    ConsonantSymbol : (roughly) [U+0C15 .. U0C39*]
    VowelSymbol : (roughly) [U+0C46 .. U+0C56]
    Virama : U+0C4D

    valid transitions are:

    init -> IndependentVowel;
    init -> ConsonantSymbol ;
    init -> DigitSymbol ;
    
    IndependentVowel -> init;
    IndependentVowel -> VowelSuffix;
    
    ConsonantSymbol -> Virama;
    ConsonantSymbol -> VowelSuffix;
    ConsonantSymbol -> VowelSymbol;
    ConsonantSymbol -> init;
    
    Virama -> init;
    Virama -> ConsonantSymbol;
    
    VowelSuffix -> init;
    
    VowelSymbol -> init; 
    VowelSymbol -> VowelSuffix;
-}


data UnicodeBrahmic : Set where
   Consonant : UnicodeBrahmic
   IndependentVowel : UnicodeBrahmic
   DependentVowel : UnicodeBrahmic
   VowelSuffix : UnicodeBrahmic
   Virama : UnicodeBrahmic

data IsValidBrahmicStart : UnicodeBrahmic → Set where
    ConsonantStart :  IsValidBrahmicStart Consonant
    IndependentVowelStart : IsValidBrahmicStart IndependentVowel

data _⊸_ : UnicodeBrahmic → UnicodeBrahmic → Set where
    DeadConsonant : (Consonant ⊸ Virama)
    VowelSymbol :  (Consonant ⊸ DependentVowel)
    NextVowel : ∀ {t} → t ⊸ IndependentVowel
    NextConsonant : ∀ {t} → t ⊸ Consonant
    VowelSuffix₁ :  Consonant  ⊸ VowelSuffix
    VowelSuffix₂ :  IndependentVowel ⊸ VowelSuffix
    VowelSuffix₃ :  DependentVowel ⊸ VowelSuffix

-- A chain of valid transitions, parameterized by the last element.
-- Every adjacent pair satisfies _⊸_.
data ValidChain : UnicodeBrahmic → List UnicodeBrahmic → Set where
    base : ∀ {t} → ValidChain t (t ∷ [])
    step : ∀ {t₁ t₂ last : UnicodeBrahmic} {rest : List UnicodeBrahmic}
         → (t₁ ⊸ t₂) → ValidChain last (t₂ ∷ rest) → ValidChain last (t₁ ∷ t₂ ∷ rest)

-- A valid Brahmic token is a valid chain starting with Consonant or IndependentVowel.
data ValidBrahmicToken : List UnicodeBrahmic → Set where
    consonant-start : ∀ {last : UnicodeBrahmic} {rest : List UnicodeBrahmic}
           → ValidChain last (Consonant ∷ rest) → ValidBrahmicToken (Consonant ∷ rest)
    vowel-start : ∀ {last : UnicodeBrahmic} {rest : List UnicodeBrahmic}
           → ValidChain last (IndependentVowel ∷ rest) → ValidBrahmicToken (IndependentVowel ∷ rest)


-- Concatenate two chains, bridging with a transition from last₁ to first₂
chainAppend : ∀ {first₁ last₁ first₂ last₂ : UnicodeBrahmic} {xs ys : List UnicodeBrahmic}
            → ValidChain last₁ (first₁ ∷ xs) → (last₁ ⊸ first₂) → ValidChain last₂ (first₂ ∷ ys)
            → ValidChain last₂ (first₁ ∷ xs ++ first₂ ∷ ys)
chainAppend base bridge vc₂ = step bridge vc₂
chainAppend (step tr vc₁) bridge vc₂ = step tr (chainAppend vc₁ bridge vc₂)



reassoc : ∀ { l₁ l₂ : List UnicodeBrahmic} → (t : UnicodeBrahmic ) → ValidBrahmicToken (l₁ ++ t ∷ l₂) → ValidBrahmicToken ((l₁ ++ t ∷ []) ++ l₂)   
reassoc {l₁} {l₂} t x rewrite ++-assoc l₁ (t ∷ []) l₂ =  x

-- Truncate a chain: if a chain covers (first ∷ l₁) and another covers (first ∷ l₁ ++ s ∷ l₂),
-- then we can build a chain covering just (first ∷ l₁ ++ s ∷ []).
chainTrunc : ∀ {first last₁ : UnicodeBrahmic} {l₁ : List UnicodeBrahmic}
             (s : UnicodeBrahmic) {last₂ : UnicodeBrahmic} {l₂ : List UnicodeBrahmic}
           → ValidChain last₁ (first ∷ l₁)
           → ValidChain last₂ (first ∷ l₁ ++ s ∷ l₂)
           → ValidChain s (first ∷ l₁ ++ s ∷ [])
chainTrunc s base (step tr _) = step tr base
chainTrunc s (step tr₁ vc₁) (step _ vc₂) = step tr₁ (chainTrunc s vc₁ vc₂)

-- Generic truncation for ValidBrahmicToken: drop the suffix after absorbing one element.
truncate : ∀ {l₁ l₂ : List UnicodeBrahmic} (s : UnicodeBrahmic)
         → ValidBrahmicToken l₁ → ValidBrahmicToken (l₁ ++ s ∷ l₂) → ValidBrahmicToken (l₁ ++ s ∷ [])
truncate s (consonant-start vc₁) (consonant-start vc₂) = consonant-start (chainTrunc s vc₁ vc₂)
truncate s (vowel-start vc₁) (vowel-start vc₂) = vowel-start (chainTrunc s vc₁ vc₂)

------------------------------------------------------------------------
--- Properties of valid token

--- concatenation of valid tokens is valid: if l₁ and l₂ are valid tokens, then so is l₁ ++ l₂.
valid++ : ∀ {l₁ l₂ : List UnicodeBrahmic}  → ValidBrahmicToken l₁ → ValidBrahmicToken l₂ → ValidBrahmicToken (l₁ ++ l₂)
valid++ (consonant-start vc₁) (consonant-start vc₂) = consonant-start (chainAppend vc₁ NextConsonant vc₂)
valid++ (consonant-start vc₁) (vowel-start vc₂) = consonant-start (chainAppend vc₁ NextVowel vc₂)
valid++ (vowel-start vc₁) (consonant-start vc₂) = vowel-start (chainAppend vc₁ NextConsonant vc₂)
valid++ (vowel-start vc₁) (vowel-start vc₂) = vowel-start (chainAppend vc₁ NextVowel vc₂)


-- A valid token always starts with a valid start character (consonant or independent vowel).
valid-starts : ∀ {x : UnicodeBrahmic} → {l₁ : List UnicodeBrahmic} → ValidBrahmicToken (x ∷ l₁) → IsValidBrahmicStart x
valid-starts (consonant-start _) = ConsonantStart
valid-starts (vowel-start _) = IndependentVowelStart


-- A valid token cannot start with a dependent vowel, virama, or vowel suffix.

¬dependent-vowel-start : ∀ {l} → ValidBrahmicToken (DependentVowel ∷ l) → ⊥
¬dependent-vowel-start {l} ()


¬virama-start : ∀ {l} → ValidBrahmicToken (Virama ∷ l) → ⊥
¬virama-start {l} ()

¬vowel-suffix-start : ∀ {l} → ValidBrahmicToken (VowelSuffix ∷ l) → ⊥
¬vowel-suffix-start {l} ()

------------------------------------------------------------------------
--- Lookahead-based token extension: fixToken candidate lookahead = (token, remainder)

--- Given a candidate token and a lookahead, fixToken extends the candidate with as much of the lookahead as possible to form a valid token.
fixToken : List UnicodeBrahmic → List UnicodeBrahmic → (List UnicodeBrahmic × List UnicodeBrahmic)
fixToken candidate [] = candidate , []
fixToken candidate (Consonant ∷ remaining) = candidate , Consonant ∷ remaining
fixToken candidate (IndependentVowel ∷ remaining) = candidate , IndependentVowel ∷ remaining
fixToken candidate (DependentVowel ∷ remaining) = fixToken (candidate ++ DependentVowel ∷ [] ) remaining
fixToken candidate (VowelSuffix ∷ remaining) = fixToken (candidate ++ VowelSuffix ∷ [] ) remaining
fixToken candidate (Virama ∷ remaining) = fixToken (candidate ++ Virama ∷ [] ) remaining

-------------------------------------------------------------------------
--- Properties of fixToken

-- The first component of fixToken is a valid token
fixTokenTokenValid : ∀ {l₁ l₂ : List UnicodeBrahmic} → ValidBrahmicToken l₁ → ValidBrahmicToken (l₁ ++ l₂)
                    → let (parsed , _) = fixToken l₁ l₂ in ValidBrahmicToken parsed
fixTokenTokenValid {l₁} {[]} vl vll = vl
fixTokenTokenValid {l₁} {Consonant ∷ l₂} vl vll = vl
fixTokenTokenValid {l₁} {IndependentVowel ∷ l₂} vl vll = vl
fixTokenTokenValid {l₁} {DependentVowel ∷ l₂} vl vll = fixTokenTokenValid (truncate DependentVowel vl vll) (reassoc DependentVowel vll)
fixTokenTokenValid {l₁} {VowelSuffix ∷ l₂} vl vll = fixTokenTokenValid (truncate VowelSuffix vl vll) (reassoc VowelSuffix vll)
fixTokenTokenValid {l₁} {Virama ∷ l₂} vl vll = fixTokenTokenValid (truncate Virama vl vll) (reassoc Virama vll)


RemainderOk : List UnicodeBrahmic → Set
RemainderOk [] = ⊤
RemainderOk (x ∷ _) = IsValidBrahmicStart x

-- Remainder from fixToken always starts with a valid start character or is empty
fixTokenRemainderOk : ∀ (l₁ l₂ : List UnicodeBrahmic) → let (_ , remainder) = fixToken l₁ l₂ in RemainderOk remainder
fixTokenRemainderOk l₁ [] = tt
fixTokenRemainderOk l₁ (Consonant ∷ r) = ConsonantStart
fixTokenRemainderOk l₁ (IndependentVowel ∷ r) = IndependentVowelStart
fixTokenRemainderOk l₁ (DependentVowel ∷ r) = fixTokenRemainderOk (l₁ ++ DependentVowel ∷ []) r
fixTokenRemainderOk l₁ (VowelSuffix ∷ r) = fixTokenRemainderOk (l₁ ++ VowelSuffix ∷ []) r
fixTokenRemainderOk l₁ (Virama ∷ r) = fixTokenRemainderOk (l₁ ++ Virama ∷ []) r

-- Conservation: token ++ remainder ≡ original input
fixTokenComplete : ∀ (l₁ l₂ : List UnicodeBrahmic)
                  → let (parsed , remainder) = fixToken l₁ l₂ in parsed ++ remainder ≡ l₁ ++ l₂
fixTokenComplete l₁ [] = refl
fixTokenComplete l₁ (Consonant ∷ r) = refl
fixTokenComplete l₁ (IndependentVowel ∷ r) = refl
fixTokenComplete l₁ (DependentVowel ∷ r) = trans (fixTokenComplete (l₁ ++ DependentVowel ∷ []) r) (++-assoc l₁ (DependentVowel ∷ []) r)
fixTokenComplete l₁ (VowelSuffix ∷ r) = trans (fixTokenComplete (l₁ ++ VowelSuffix ∷ []) r) (++-assoc l₁ (VowelSuffix ∷ []) r)
fixTokenComplete l₁ (Virama ∷ r) = trans (fixTokenComplete (l₁ ++ Virama ∷ []) r) (++-assoc l₁ (Virama ∷ []) r)

------------------------------------------------------------------------
-- Linking UnicodeBrahmic to Orthography₂


-- Decidable boundary check: can character s be followed by character t?
canFollow : UnicodeBrahmic → UnicodeBrahmic → Bool
canFollow _ Consonant = true
canFollow _ IndependentVowel = true
canFollow Consonant DependentVowel = true
canFollow IndependentVowel DependentVowel = false
canFollow DependentVowel DependentVowel = false
canFollow VowelSuffix DependentVowel = false
canFollow Virama DependentVowel = false
canFollow Consonant VowelSuffix = true
canFollow IndependentVowel VowelSuffix = true
canFollow DependentVowel VowelSuffix = true
canFollow VowelSuffix VowelSuffix = false
canFollow Virama VowelSuffix = false
canFollow Consonant Virama = true
canFollow IndependentVowel Virama = false
canFollow DependentVowel Virama = false
canFollow VowelSuffix Virama = false
canFollow Virama Virama = false

-- Last element of a non-empty list
getLast : UnicodeBrahmic → List UnicodeBrahmic → UnicodeBrahmic
getLast x [] = x
getLast _ (y ∷ ys) = getLast y ys

-- Key lemma: getLast distributes over append
getLast-++ : ∀ (x : UnicodeBrahmic) (xs : List UnicodeBrahmic)
             (y : UnicodeBrahmic) (ys : List UnicodeBrahmic)
           → getLast x (xs ++ y ∷ ys) ≡ getLast y ys
getLast-++ x [] y ys = refl
getLast-++ x (z ∷ xs) y ys = getLast-++ z xs y ys

-- Combine: concatenate if boundary transition is valid
combineBrahmic : List UnicodeBrahmic → List UnicodeBrahmic → Maybe (List UnicodeBrahmic)
combineBrahmic [] _ = nothing
combineBrahmic _ [] = nothing
combineBrahmic (x ∷ xs) (y ∷ ys) with canFollow (getLast x xs) y
... | true  = just (x ∷ xs ++ y ∷ ys)
... | false = nothing

-- Soundness: canFollow reflects _⊸_
canFollow→⊸ : ∀ {s t} → canFollow s t ≡ true → s ⊸ t
canFollow→⊸ {_} {Consonant} _ = NextConsonant
canFollow→⊸ {_} {IndependentVowel} _ = NextVowel
canFollow→⊸ {Consonant} {DependentVowel} _ = VowelSymbol
canFollow→⊸ {Consonant} {VowelSuffix} _ = VowelSuffix₁
canFollow→⊸ {IndependentVowel} {VowelSuffix} _ = VowelSuffix₂
canFollow→⊸ {DependentVowel} {VowelSuffix} _ = VowelSuffix₃
canFollow→⊸ {Consonant} {Virama} _ = DeadConsonant

-- Completeness: _⊸_ implies canFollow
⊸→canFollow : ∀ {s t} → s ⊸ t → canFollow s t ≡ true
⊸→canFollow DeadConsonant = refl
⊸→canFollow VowelSymbol = refl
⊸→canFollow NextVowel = refl
⊸→canFollow NextConsonant = refl
⊸→canFollow VowelSuffix₁ = refl
⊸→canFollow VowelSuffix₂ = refl
⊸→canFollow VowelSuffix₃ = refl

-- Helper: unfold combineBrahmic when boundary check succeeds
combine-yes : ∀ (x : UnicodeBrahmic) (xs : List UnicodeBrahmic)
                (y : UnicodeBrahmic) (ys : List UnicodeBrahmic)
            → canFollow (getLast x xs) y ≡ true
            → combineBrahmic (x ∷ xs) (y ∷ ys) ≡ just (x ∷ xs ++ y ∷ ys)
combine-yes x xs y ys eq with canFollow (getLast x xs) y
... | true = refl

-- Helper: unfold combineBrahmic when boundary check fails
combine-no : ∀ (x : UnicodeBrahmic) (xs : List UnicodeBrahmic)
               (y : UnicodeBrahmic) (ys : List UnicodeBrahmic)
           → canFollow (getLast x xs) y ≡ false
           → combineBrahmic (x ∷ xs) (y ∷ ys) ≡ nothing
combine-no x xs y ys eq with canFollow (getLast x xs) y
... | false = refl

-- Extract boundary evidence from a successful combine
combine-evidence : ∀ (x : UnicodeBrahmic) (xs : List UnicodeBrahmic)
                     (y : UnicodeBrahmic) (ys : List UnicodeBrahmic)
                     (r : List UnicodeBrahmic)
                 → combineBrahmic (x ∷ xs) (y ∷ ys) ≡ just r
                 → canFollow (getLast x xs) y ≡ true
combine-evidence x xs y ys r eq with canFollow (getLast x xs) y
... | true = refl

-- Extract result equality from a successful combine
combine-result : ∀ (x : UnicodeBrahmic) (xs : List UnicodeBrahmic)
                   (y : UnicodeBrahmic) (ys : List UnicodeBrahmic)
                   (r : List UnicodeBrahmic)
               → combineBrahmic (x ∷ xs) (y ∷ ys) ≡ just r
               → r ≡ x ∷ xs ++ y ∷ ys
combine-result x xs y ys r eq with canFollow (getLast x xs) y
... | true with refl ← eq = refl

-- Associativity of combineBrahmic
combineBrahmic-assoc : ∀ (x y z xy xyz : List UnicodeBrahmic)
  → combineBrahmic x y ≡ just xy
  → combineBrahmic xy z ≡ just xyz
  → ∃ λ yz → combineBrahmic y z ≡ just yz × combineBrahmic x yz ≡ just xyz
combineBrahmic-assoc [] _ _ _ _ () _
combineBrahmic-assoc (_ ∷ _) [] _ _ _ () _
combineBrahmic-assoc (_ ∷ _) (_ ∷ _) _ [] _ _ ()
combineBrahmic-assoc (_ ∷ _) (_ ∷ _) [] (_ ∷ _) _ _ ()
combineBrahmic-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) (xy₀ ∷ xys) xyz eq₁ eq₂
  with combine-evidence x xs y ys (xy₀ ∷ xys) eq₁
     | combine-result x xs y ys (xy₀ ∷ xys) eq₁
... | cfxy | refl
  with combine-evidence x (xs ++ y ∷ ys) z zs xyz eq₂
     | combine-result x (xs ++ y ∷ ys) z zs xyz eq₂
... | cfxyz | refl
  rewrite getLast-++ x xs y ys
  with combine-yes y ys z zs cfxyz
... | yz-eq
  with combine-yes x xs y (ys ++ z ∷ zs) cfxy
... | x-yz-eq rewrite ++-assoc xs (y ∷ ys) (z ∷ zs)
  = (y ∷ ys ++ z ∷ zs) , yz-eq , x-yz-eq

-- The instance
brahmicOrthography₂ : Orthography₂ (List UnicodeBrahmic)
brahmicOrthography₂ = record
  { combine = combineBrahmic
  ; assoc   = combineBrahmic-assoc
  }

------------------------------------------------------------------------
-- Valid Tokens form Orthography₁: concatenation of valid tokens is always valid.

record PackedValidBrahmicToken : Set where
  constructor packed
  field
    chars : List UnicodeBrahmic
    .valid : ValidBrahmicToken chars

packed-ext :
  ∀ {xs ys}
    .{vx : ValidBrahmicToken xs}
    .{vy : ValidBrahmicToken ys}
  → xs ≡ ys
  → packed xs vx ≡ packed ys vy
packed-ext refl = refl

combineValidBrahmic : PackedValidBrahmicToken → PackedValidBrahmicToken → PackedValidBrahmicToken
combineValidBrahmic (packed l₁ v₁) (packed l₂ v₂) = packed (l₁ ++ l₂) (valid++ v₁ v₂)

combineValidBrahmic-assoc :
  ∀ (x y z : PackedValidBrahmicToken)
  → combineValidBrahmic (combineValidBrahmic x y) z ≡ combineValidBrahmic x (combineValidBrahmic y z)
combineValidBrahmic-assoc (packed l₁ v₁) (packed l₂ v₂) (packed l₃ v₃) =
  packed-ext (++-assoc l₁ l₂ l₃)

pretokenizedOrthography₁ : Orthography₁ PackedValidBrahmicToken
pretokenizedOrthography₁ = record
  { combine = combineValidBrahmic
  ; assoc   = combineValidBrahmic-assoc
  }


-------------------------------------------------------------------------
-- Vietnamese orthography: a case study of Orthography₂ for a non-Brahmic script

-- Vietnamese Orthography in modular form(non-precomposed form) is simpler orthography than Brahmic orthography, but it still fits into the Orthography₂ framework.
data Vietnamese : Set where
  BaseCharacterᵥ : Vietnamese
  Diacriticᵥ : Vietnamese
  Toneᵥ : Vietnamese

data _⊸ᵥ_ : Vietnamese → Vietnamese → Set where
     Markᵥ : BaseCharacterᵥ ⊸ᵥ Diacriticᵥ
     ToneAfterBaseᵥ : BaseCharacterᵥ ⊸ᵥ Toneᵥ
     ToneAfterDiacriticᵥ : Diacriticᵥ ⊸ᵥ Toneᵥ
     NextBaseᵥ : ∀ {t} → t ⊸ᵥ BaseCharacterᵥ

--- fixTokenᵥ candidate lookahead = (token, remainder)
fixTokenᵥ : List Vietnamese → List Vietnamese → List Vietnamese × List Vietnamese
fixTokenᵥ candidate [] = candidate , []
fixTokenᵥ candidate (BaseCharacterᵥ ∷ remaining) = candidate , (BaseCharacterᵥ ∷ remaining)
fixTokenᵥ candidate (Diacriticᵥ ∷ remaining) = fixTokenᵥ (candidate ++ Diacriticᵥ ∷ []) remaining
fixTokenᵥ candidate (Toneᵥ ∷ remaining) = fixTokenᵥ (candidate ++ Toneᵥ ∷ []) remaining


-- Vietnamese is Orthography₂ (partial semigroup)

canFollowᵥ : Vietnamese → Vietnamese → Bool
canFollowᵥ _ BaseCharacterᵥ = true
canFollowᵥ BaseCharacterᵥ Diacriticᵥ = true
canFollowᵥ Diacriticᵥ Diacriticᵥ = false
canFollowᵥ Toneᵥ Diacriticᵥ = false
canFollowᵥ BaseCharacterᵥ Toneᵥ = true
canFollowᵥ Diacriticᵥ Toneᵥ = true
canFollowᵥ Toneᵥ Toneᵥ = false

getLastᵥ : Vietnamese → List Vietnamese → Vietnamese
getLastᵥ x [] = x
getLastᵥ _ (y ∷ ys) = getLastᵥ y ys

getLastᵥ-++ : ∀ (x : Vietnamese) (xs : List Vietnamese)
               (y : Vietnamese) (ys : List Vietnamese)
             → getLastᵥ x (xs ++ y ∷ ys) ≡ getLastᵥ y ys
getLastᵥ-++ x [] y ys = refl
getLastᵥ-++ x (z ∷ xs) y ys = getLastᵥ-++ z xs y ys

combineViet : List Vietnamese → List Vietnamese → Maybe (List Vietnamese)
combineViet [] _ = nothing
combineViet _ [] = nothing
combineViet (x ∷ xs) (y ∷ ys) with canFollowᵥ (getLastᵥ x xs) y
... | true  = just (x ∷ xs ++ y ∷ ys)
... | false = nothing

combine-yesᵥ : ∀ (x : Vietnamese) (xs : List Vietnamese)
                 (y : Vietnamese) (ys : List Vietnamese)
             → canFollowᵥ (getLastᵥ x xs) y ≡ true
             → combineViet (x ∷ xs) (y ∷ ys) ≡ just (x ∷ xs ++ y ∷ ys)
combine-yesᵥ x xs y ys eq with canFollowᵥ (getLastᵥ x xs) y
... | true = refl

combine-evidenceᵥ : ∀ (x : Vietnamese) (xs : List Vietnamese)
                      (y : Vietnamese) (ys : List Vietnamese)
                      (r : List Vietnamese)
                  → combineViet (x ∷ xs) (y ∷ ys) ≡ just r
                  → canFollowᵥ (getLastᵥ x xs) y ≡ true
combine-evidenceᵥ x xs y ys r eq with canFollowᵥ (getLastᵥ x xs) y
... | true = refl

combine-resultᵥ : ∀ (x : Vietnamese) (xs : List Vietnamese)
                    (y : Vietnamese) (ys : List Vietnamese)
                    (r : List Vietnamese)
                → combineViet (x ∷ xs) (y ∷ ys) ≡ just r
                → r ≡ x ∷ xs ++ y ∷ ys
combine-resultᵥ x xs y ys r eq with canFollowᵥ (getLastᵥ x xs) y
... | true with refl ← eq = refl

combineViet-assoc : ∀ (x y z xy xyz : List Vietnamese)
  → combineViet x y ≡ just xy
  → combineViet xy z ≡ just xyz
  → ∃ λ yz → combineViet y z ≡ just yz × combineViet x yz ≡ just xyz
combineViet-assoc [] _ _ _ _ () _
combineViet-assoc (_ ∷ _) [] _ _ _ () _
combineViet-assoc (_ ∷ _) (_ ∷ _) _ [] _ _ ()
combineViet-assoc (_ ∷ _) (_ ∷ _) [] (_ ∷ _) _ _ ()
combineViet-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) (xy₀ ∷ xys) xyz eq₁ eq₂
  with combine-evidenceᵥ x xs y ys (xy₀ ∷ xys) eq₁
     | combine-resultᵥ x xs y ys (xy₀ ∷ xys) eq₁
... | cfxy | refl
  with combine-evidenceᵥ x (xs ++ y ∷ ys) z zs xyz eq₂
     | combine-resultᵥ x (xs ++ y ∷ ys) z zs xyz eq₂
... | cfxyz | refl
  rewrite getLastᵥ-++ x xs y ys
  with combine-yesᵥ y ys z zs cfxyz
... | yz-eq
  with combine-yesᵥ x xs y (ys ++ z ∷ zs) cfxy
... | x-yz-eq rewrite ++-assoc xs (y ∷ ys) (z ∷ zs)
  = (y ∷ ys ++ z ∷ zs) , yz-eq , x-yz-eq

-- The instance
vietnameseOrthography₂ : Orthography₂ (List Vietnamese)
vietnameseOrthography₂ = record
  { combine = combineViet
  ; assoc   = combineViet-assoc
  }
