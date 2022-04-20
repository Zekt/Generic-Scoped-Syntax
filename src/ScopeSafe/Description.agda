module ScopeSafe.Description where

open import Prelude

import Generics.Description as D
open import Generics.Telescope   as T
--open import Utils.Reflection hiding (Type)

private variable
  A B S I : Set ℓ
  Γ Δ Θ : List I

infixr 10 _⇒_

_-Scoped : {ℓ : Level} → Set ℓ → Set (lsuc ℓ)
_-Scoped {ℓ} I  = I → List I → Set ℓ

_⇒_ : {A : Set ℓ} (P Q : A → Set ℓ) → (A → Set ℓ)
(P ⇒ Q) x = P x → Q x

_⊢_ : {A B : Set ℓ} → (A → B) → (B → Set ℓ) → (A → Set ℓ)
(f ⊢ P) x = P (f x)

∀[_] : {A : Set ℓ} → (A → Set ℓ) → Set ℓ
∀[ P ] = ∀ {x} → P x

data Var {I : Set ℓ} : I -Scoped where
  z : ∀ {σ : I}   → ∀[ (σ ∷_) ⊢ Var σ ]
  s : ∀ {σ τ : I} → ∀[ Var σ ⇒ (τ ∷_) ⊢ Var σ ]

data Type : Set where
  α    : Type
  _‵→_ : Type → Type → Type

variable
  σ τ : Type
  W C : I -Scoped
  i : I

data Lam : Type -Scoped where
  ‵var : ∀[ Var σ ⇒ Lam σ ]
  ‵app : ∀ {σ τ} → ∀[ Lam (σ ‵→ τ) ⇒ Lam σ ⇒ Lam τ ]
  ‵lam : ∀ {σ τ} → ∀[ (σ ∷_) ⊢ Lam τ ⇒ Lam (σ ‵→ τ) ]

data Desc' (I : Set ℓ) : Setω where
  `σ : (A : Set ℓ) → (A → Desc' I) → Desc' I
  `X : List I → I → Desc' I      → Desc' I
  `▪ : I                         → Desc' I

⟦_⟧ : Desc' I → (List I → I -Scoped) → I -Scoped
⟦ `σ A d   ⟧ X i Γ =  Σ[ a ∈ A ] ⟦ d a ⟧ X i Γ 
⟦ `X Δ j d ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
⟦ `▪ j     ⟧ X i Γ = i ≡ j

{-- Debug
printLam : TC _
printLam = do t ← getType (quote Lam)
              debugPrint "meta" 5 [ termErr t ]
              return tt

unquoteDecl = printLam
--}
