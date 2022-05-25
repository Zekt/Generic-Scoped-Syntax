\begin{code}
open import Prelude

data Desc (I : Set) : Set₁ where
  σ  : (A : Set) → (A → Desc I) → Desc I
  ‵X : List I → I → Desc I → Desc I
  ■  : I → Desc I

variable
  I : Set
  i j : I
  Γ Δ : List I
  d : Desc I

data Type : Set where
  α : Type
  _‵→_ : Type → Type → Type

data ‵STLC : Set where
  App Lam : Type → Type → ‵STLC

STLC : Desc Type
STLC = σ ‵STLC λ where
  (App i j) → ‵X [] (i ‵→ j) (‵X [] i (■ j))
  (Lam i j) → ‵X (i ∷ []) j (■ (i ‵→ j))

⟦_⟧ : Desc I
    → (List I → I → List I → Set)
    → (I → List I → Set)
⟦ σ A D ⟧ X i Γ = Σ[ a ∈ A ] ⟦ D a ⟧ X i Γ
⟦ ‵X Δ j D ⟧ X i Γ = X Δ j Γ × ⟦ D ⟧ X i Γ
⟦ ■ j ⟧ X i Γ = i ≡ j

data Tm (d : Desc I) : I → List I → Set where

data Var : I → List I → Set where
  z : Var i (i ∷ Γ)
  s : Var i Γ → Var i (j ∷ Γ)

record Semantics (d : Desc I) (V C : I → List I → Set) : Set where

postulate
  semantics : ∀ {V C : I → List I → Set} {d : Desc I}
            → Semantics d V C
            → (Var i Γ → V i Δ)
            → (∀ {σ} → Tm d σ Γ → C σ Δ)

  Ren : Semantics d Var (Tm d)

  Sub : Semantics d (Tm d) (Tm d)

ren : ∀ {σ d}
    → (Var i Γ → Var i Δ)
    → Tm d σ Γ → Tm d σ Δ
ren ρ t = semantics Ren ρ t

sub : ∀ {σ d}
    → (Var i Γ → Tm d i Δ)
    → Tm d σ Γ → Tm d σ Δ
sub ρ t = semantics Sub ρ t
\end{code}
