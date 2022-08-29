module ScopeSafe.Description where

open import Prelude hiding (lookup)

import Generics.Description as D
open import Generics.Telescope   as T
open import Generics.Reflection
open import Generics.Recursion
open import Generics.RecursionScheme
--open import Utils.Reflection hiding (Type)

private variable
  A B S I : Set ℓ
  Γ Δ Θ : List I
  i : I
  cb : D.ConB

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

weakenVarL : Var i Γ → Var i (Δ <> Γ)
weakenVarL {Δ = []} V = V
weakenVarL {Δ = x ∷ Δ} V = s (weakenVarL V)

weakenVarR : Var i Γ → Var i (Γ <> Δ)
weakenVarR z = z
weakenVarR (s V) = s (weakenVarR V)

data Type : Set where
  α    : Type
  `ℕ    : Type
  _‵→_ : Type → Type → Type

private variable
  σ τ : Type
  W V C : I -Scoped

data Lam : Type → List Type → Set where
  ‵var : Var σ Γ        → Lam σ Γ
  ‵app : ∀ {Γ σ τ} → Lam (σ ‵→ τ) Γ → Lam σ Γ → Lam τ Γ
  ‵lam : ∀ {Γ σ τ} → Lam τ (σ ∷ Γ)  → Lam (σ ‵→ τ) Γ

--Indexˢ : Set ℓ → Set ℓ
--Indexˢ Ty = Ty × List Ty × ⊤
--
--data Desc' (I : Set ℓ) : D.ConB → Setω where
--  `σ : (A : Set ℓ) → (A → Desc' I cb) → Desc' I (inl ℓ ∷ cb)
--  `X : List I → I → Desc' I cb → Desc' I (inr [] ∷ cb)
--  `▪ : I → Desc' I []
--
--fromDesc' : (Desc' I cb) → List I → D.ConD (Indexˢ I) cb
--fromDesc' (`σ A D')   Δ = D.σ A λ a → fromDesc' (D' a) Δ
--fromDesc' (`X Γ i D') Δ = D.ρ (D.ι (i , Γ <> Δ , tt)) (fromDesc' D' Δ)
--fromDesc' (`▪ i)      Δ = D.ι (i , Δ , tt)
--
--⟦_⟧ : Desc' I cb → (List I → I -Scoped) → I -Scoped
--⟦ `σ A d   ⟧ X i Γ =  Σ[ a ∈ A ] ⟦ d a ⟧ X i Γ
--⟦ `X Δ j d ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
--⟦ `▪ j     ⟧ X i Γ = i ≡ j

instance
  LamC : Named (quote Lam) _
  unNamed LamC = genDataC LamD (genDataT LamD Lam)
    where LamD = genDataD Lam

foldLamP : FoldP
foldLamP = fold-operator (quote Lam)

--foldrT : FoldT foldLamP
--foldrT ps (tt , T , v , a , l , tt ) = foldr {!v!} {!!} {!!}

unquoteDecl foldLam = defineFold foldLamP foldLam

record _-Env {I : Set ℓ} (Γ : List I) (V : I -Scoped) (Δ : List I) : Set ℓ where
  constructor pack
  field lookup : Var i Γ → V i Δ

open _-Env

weaken : (Γ -Env) Var (σ ∷ Γ)
lookup weaken v = s v

_•_ : (Γ -Env) V Δ → V σ Δ → ((σ ∷ Γ) -Env) V Δ
lookup (ρ • v) z     = v
lookup (ρ • v) (s k) = lookup ρ k

bifmap : (∀ {i} → V i Δ → W i Θ) → (Γ -Env) V Δ → (Γ -Env) W Θ
lookup (bifmap f ρ) k = f (lookup ρ k)

_Env++_ : (Γ -Env) V Θ → (Δ -Env) V Θ → ((Γ <> Δ) -Env) V Θ
lookup (_Env++_ {Γ = []}    ρ v) k = lookup v k
lookup (_Env++_ {Γ = x ∷ Γ} ρ v) z = lookup ρ z
lookup (_Env++_ {Γ = x ∷ Γ} ρ v) (s k) = lookup (pack (λ x → lookup ρ (s x)) Env++ v) k

--record Semantics (V C : Type -Scoped) : Setω where
--  field
--    thⱽ : V σ Γ → (Γ -Env) Var Δ → (V σ) Δ
--    var : V σ Γ → C σ Γ
--    app : C (σ ‵→ τ) Γ → C σ Γ → C τ Γ
--    lam : (∀ {Δ} → ((Γ -Env) Var Δ) → V σ Δ → C τ Δ) → C (σ ‵→ τ) Γ
--  extend : (Δ -Env) Var Θ → (Γ -Env) V Δ → V σ Θ → ((σ ∷ Γ) -Env) V Θ
--  extend σ ρ v = bifmap (λ t → thⱽ t σ) ρ • v
--
--  SemP : Semantics V C → FoldP
--SemP {V} {C} S = record
--              { Conv = unNamed LamC
--              ; #levels = 0
--              ; level = λ {tt → tt}
--              ; Param = λ {tt → []}
--              ; ParamV = []
--              ; ParamN = []
--              ; param = λ _ → tt
--              ; Carrier = λ { tt tt (σ' , Γ' , tt)
--                            → ∀ Δ → (Γ' -Env) V Δ → C σ' Δ}
--              ; algebra = λ { tt (inl (σ , Γ , k , refl)) → λ _ ρ → var (lookup ρ k)
--                            ; ps (inr (inl (σ , τ , Γ , C₁ , C₂ , refl))) → λ _ ρ → app (C₁ _ ρ) (C₂ _ ρ)
--                            ; ps (inr (inr (inl (fst₁ , fst₂ , fst₃ , C₁ , refl)))) → λ _ ρ → lam (λ σ v → C₁ _ (extend σ ρ v))}
--              }
--  where open Semantics S
--
--Renaming : Semantics Var Lam
--Renaming = record { thⱽ = λ x ρ → lookup ρ x
--                  ; var = ‵var
--                  ; app = ‵app
--                  ; lam = λ b → ‵lam (b weaken z)
--                  }
--
--unquoteDecl rename = defineFold (SemP Renaming) rename
--
--Subst : Semantics Lam Lam
--Subst = record { thⱽ = λ t ρ → rename t _ ρ
--               ; var = id
--               ; app = ‵app
--               ; lam = λ b → ‵lam (b weaken (‵var z)) }
--
----unquoteDecl substitute = defineFold (SemP Subst) substitute
--
--substitute : {a : Type} {a1 : List Type} (l : Lam a a1) {Δ : List Type} (_ : (a1 -Env) Lam Δ) → Lam a Δ
--substitute (‵var x) = λ ρ → lookup ρ x
--substitute (‵app {σ} x x₁) = λ ρ → ‵app (substitute x ρ) (substitute x₁ ρ)
--substitute (‵lam x) = λ ρ → ‵lam (substitute x (bifmap (λ {i} t → rename t _ weaken) ρ • ‵var z))
--
--SubstT : FoldT (SemP Subst)
--SubstT tt tt L Δ = substitute L
--
--substC = genFoldC' (SemP Subst) SubstT


--id₂ : {A : Set} → A → A
--id₂ = λ x → x -- error

--semantics : Semantics V C → (Γ -Env) V Δ → (Lam σ Γ → C σ Δ)

--Fold on Lam
--foldLam : ∀[ V σ ⇒ C σ ]
--        → ∀[ C (σ ‵→ τ) ⇒ C σ ⇒ C τ ]
--        → ∀[ (σ ∷_) ⊢ C τ ⇒ C (σ ‵→ τ) ]
--        → ∀[ Lam σ ⇒ C τ ]
--foldLam v a l (‵var x) = {!!}
--foldLam v a l (‵app L L₁) = {!!}
--foldLam v a l (‵lam x) = {!!}

{-- Debug
printLam : TC _
printLam = do t ← getType (quote Lam)
              debugPrint "meta" 5 [ termErr t ]
              return tt

unquoteDecl = printLam
--}
