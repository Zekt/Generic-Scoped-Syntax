module Demo where

open import Prelude hiding (lookup)
open import ScopeSafe.Description
open import ScopeSafe.Semantics

import Generics.Description as D
open import Generics.Telescope   as T
open import Generics.Reflection
open import Generics.Recursion
open import Generics.RecursionScheme
open import Generics.Predicates
open import Utils.Reflection.Print

private variable
  A B S I : Set ℓ
  Γ Δ Θ : List I
  i : I
  cb : D.ConB
  σ τ : Type
  W V C : I -Scoped

data STLC : Type → List Type → Set where
  ‵var : Var σ Γ        → STLC σ Γ
  ‵app : ∀ {Γ σ τ} → STLC (σ ‵→ τ) Γ → STLC σ Γ → STLC τ Γ
  ‵lam : ∀ {Γ σ τ} → STLC τ (σ ∷ Γ)  → STLC (σ ‵→ τ) Γ

STLCD' = genDataD STLC
STLCC' = genDataC STLCD' (genDataT STLCD' STLC)

instance
  STLCC : Named (quote STLC) _
  unNamed STLCC = genDataC STLCD (genDataT STLCD STLC)
    where STLCD = genDataD STLC

SyntaxSTLC : Syntaxᵈ Type (genDataD STLC)
SyntaxSTLC = _
        ,ωω refl
        ,ωω (refl ,ωω refl)
        ,ωω _
        ,ωω refl
        ,ωω refl
        ,ωω (_ ,ω _ ,ωω _ ,ωω refl ,ωω (λ _ → refl))
        ,ωω (_ ,ω _ ,ωω _ ,ωω refl ,ωω (λ _ → refl))
        ,ωω lift tt

RenameSTLCSem : Semantics (findDataD (quote STLC)) SyntaxSTLC Var STLC
RenameSTLCSem = Renaming (findDataC (quote STLC)) SyntaxSTLC

RenameSTLC = SemP (findDataC (quote STLC)) SyntaxSTLC RenameSTLCSem

unquoteDecl renameSTLC = defineFold RenameSTLC renameSTLC

data PCF : Type → List Type → Set where
  ‵var : Var σ Γ   → PCF σ Γ
  ‵app : ∀ {Γ σ τ} → PCF (σ ‵→ τ) Γ → PCF σ Γ → PCF τ Γ
  ‵lam : ∀ {Γ σ τ} → PCF τ (σ ∷ Γ)  → PCF (σ ‵→ τ) Γ
  ‵zero : ∀ {Γ} → PCF `ℕ Γ
  ‵suc_ : ∀ {Γ} → PCF `ℕ Γ → PCF `ℕ Γ

instance
  PCFC : Named (quote PCF) _
  unNamed PCFC = genDataC PCFD (genDataT PCFD PCF)
    where PCFD = genDataD PCF

SyntaxPCF : Syntaxᵈ Type (findDataD (quote PCF))
SyntaxPCF = _
        ,ωω refl
        ,ωω (refl ,ωω refl)
        ,ωω _
        ,ωω refl
        ,ωω refl
        ,ωω (_ ,ω _ ,ωω _ ,ωω refl ,ωω (λ _ → refl))
        ,ωω (_ ,ω _ ,ωω _ ,ωω refl ,ωω (λ _ → refl))
        ,ωω (_ ,ω _ ,ωω _ ,ωω refl ,ωω (λ _ → refl))
        ,ωω (_ ,ω _ ,ωω _ ,ωω refl ,ωω (λ _ → refl))
        ,ωω lift tt

RenamePCFSem : Semantics (findDataD (quote PCF)) SyntaxPCF Var PCF
RenamePCFSem = Renaming (findDataC (quote PCF)) SyntaxPCF

RenamePCF = SemP (findDataC (quote PCF)) SyntaxPCF RenamePCFSem

unquoteDecl renamePCF = defineFold RenamePCF renamePCF

data exPCF : Type → List Type → Set where
  ‵lam : ∀ {Γ σ τ} → exPCF τ (σ ∷ Γ)  → exPCF (σ ‵→ τ) Γ
  case : ∀ {Γ A} → exPCF `ℕ Γ → exPCF A Γ → exPCF A (`ℕ ∷ Γ) → exPCF A Γ
  -- μ_ : ∀ {Γ A} → exPCF A (A ∷ Γ)  → exPCF A Γ

exPCFD = genDataD exPCF
exPCFT = genDataT exPCFD exPCF
exPCFC : DataC exPCFD λ { tt tt (t , ts , tt) → exPCF t ts}
exPCFC = datac (λ { (inl (_ , _ , _ , x4 , refl)) → ‵lam x4
                  ; (inr (inl (_ , _ , x3 , x4 , x5 , refl))) → case x3 x4 x5})
               (λ { (‵lam x) → inl (_ , _ , _ , _ , refl)
                  ; (case x x₁ x₂) → inr (inl (_ , _ , _ , _ , _ , refl))})
               (λ { (inl (_ , _ , _ , _ , refl)) → refl
                  ; (inr (inl (_ , _ , _ , _ , _ , refl))) → refl})
               (λ { (‵lam n) → refl
                  ; (case n n₁ n₂) → refl})
-- DataC.toN exPCFC (inl (_ , _ , _ , x4 , refl)) = ‵lam x4
-- DataC.toN exPCFC (inr (inl (_ , _ , x3 , x4 , x5 , refl))) = case x3 x4 x5
-- DataC.fromN exPCFC (‵lam x) = inl (_ , _ , _ , _ , refl)
-- DataC.fromN exPCFC (case x x₁ x₂) = inr (inl (_ , _ , x , x₁ , x₂ , refl))
-- DataC.fromN-toN exPCFC (inl (_ , _ , _ , _ , refl)) = refl
-- DataC.fromN-toN exPCFC (inr (inl (_ , _ , _ , _ , _ , refl))) = refl
-- DataC.fromN-toN exPCFC (inr (inl (_ , _ , _ , _ , _ , refl))) = refl
-- exPCFC = genDataC exPCFD exPCFT

--instance
--  exPCFC : Named (quote exPCF) _
--  unNamed exPCFC = genDataC exPCFD (genDataT exPCFD exPCF)
--    where exPCFD = genDataD exPCF

--SyntaxExPCF : Syntaxᵈ Type (findDataD (quote PCF))
-- SyntaxPCF = _
--         ,ωω refl
--         ,ωω (refl ,ωω refl)
--         ,ωω _
--         ,ωω refl
--         ,ωω refl
--         ,ωω (_ ,ω _ ,ωω _ ,ωω refl ,ωω (λ _ → refl))
--         ,ωω (_ ,ω _ ,ωω _ ,ωω refl ,ωω (λ _ → refl))
--         ,ωω (_ ,ω _ ,ωω _ ,ωω refl ,ωω (λ _ → refl))
--         ,ωω (_ ,ω _ ,ωω _ ,ωω refl ,ωω (λ _ → refl))
--         ,ωω lift tt
-- 
-- RenamePCFSem : Semantics (findDataD (quote PCF)) SyntaxPCF Var PCF
-- RenamePCFSem = Renaming (findDataC (quote PCF)) SyntaxPCF
-- 
-- RenamePCF = SemP (findDataC (quote PCF)) SyntaxPCF RenamePCFSem
-- 
-- unquoteDecl renamePCF = defineFold RenamePCF renamePCF
