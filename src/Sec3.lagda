\begin{code}
open import Prelude
open import Generics.Recursion
open import Generics.Reflection hiding (defineFold)
open import Utils.Reflection hiding (Type)

data Type : Set where
  α : Type
  _‵→_ : Type → Type → Type

variable
  I : Set
  i j : I
  Γ Δ : List I

data RecD (I : Set) : Set₁ where
  ι : (i : I) → RecD I
  π : (A : Set) (D : A → RecD I) → RecD I

data ConD (I : Set) : Set₁ where
  ι : (i : I) → ConD I
  σ : (A : Set) (D : A → ConD I) → ConD I
  ρ : (D : RecD I) (E : ConD I) → ConD I

data ConDs (I : Set) : Set₁ where
  []  : ConDs I
  _∷_ : (D : ConD I) (Ds : ConDs I) → ConDs I

data Var : I → List I → Set where
  z : Var i (i ∷ Γ)
  s : Var i Γ → Var i (j ∷ Γ)

Syntaxʳ : RecD (I × List I) → List I → Set
Syntaxʳ (ι (_ , Γ)) Δ = Σ[ Δ' ∈ _ ] Γ ≡ Δ' <> Δ
Syntaxʳ (π _ _)     _ = ⊥

Syntaxᶜ : ConD (I × List I) → List I → Set
Syntaxᶜ (ι (_ , Γ)) Δ = Γ ≡ Δ
Syntaxᶜ (σ A D)     Δ = (a : A) → Syntaxᶜ (D a) Δ
Syntaxᶜ (ρ A D)     Δ = Syntaxʳ A Δ × Syntaxᶜ D Δ

data Lam : Type → List Type → Set where
  ‵var : ∀ {Γ σ}   → Var σ Γ        → Lam σ Γ
  ‵app : ∀ {Γ σ τ} → Lam (σ ‵→ τ) Γ → Lam σ Γ → Lam τ Γ
  ‵lam : ∀ {Γ σ τ} → Lam τ (σ ∷ Γ)  → Lam (σ ‵→ τ) Γ

extend : (∀ {i} → Var i Γ → Var i Δ)
       → Var i (j ∷ Γ) → Var i (j ∷ Δ)
extend f z = z
extend f (s v) = s (f v)

rename : (∀ {i} → Var i Γ → Var i Δ)
       → Lam j Γ → Lam j Δ
rename f (‵var x)   = ‵var (f x)
rename f (‵app x y) = ‵app (rename f x) (rename f y)
rename f (‵lam x)   = ‵lam (rename (extend f) x)

open import Generics.Description

postulate
  Syntax : DataD → Set

record Semantics
         (D : DataD)
         (Sy : Syntax D)
         (V C : I → List I → Set) : Set
  where

postulate
  Renaming : (D : DataD)
           → (Sy : Syntax D)
           → Semantics D Sy Var Lam
  SemP : (D : DataD)
       → (Sy : Syntax D)
       → Semantics D Sy Var Lam
       → FoldP

LamD = genDataD Lam

postulate
  LamSyntax : Syntax LamD

LamSemantics = Renaming LamD LamSyntax

RenameP = SemP (genDataD Lam) LamSyntax LamSemantics

defineFold : FoldP → Name → TC ⊤
defineFold _ n = declareData n 0 (quoteTerm Set) >>= λ _ →
                 defineData n [] >>= λ _ →
                 return tt

--unquoteDecl rename = defineFold RenameP rename
\end{code}
