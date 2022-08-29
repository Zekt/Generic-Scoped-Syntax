module Generics.Predicates where

open import Prelude

open import Generics.Description
open import Generics.Telescope
open import ScopeSafe.Description

private variable
  rb  : RecB
  cb  : ConB
  cbs : ConBs
  ξ   : Tel ℓ
  Ty  : Set ℓ
  A B S I : Set ℓ
  Γ Δ Θ : List I

-- ≡ ⟦ [ _ ∶ Ty ] [ _ ∶ List Ty ] [] ⟧ᵗ
Indexˢ : Set ℓ → Set ℓ
Indexˢ Ty = Ty × List Ty × ⊤

data Desc' (I : Set ℓ) : ConB → Setω where
  `σ : (A : Set ℓ) → (A → Desc' I cb) → Desc' I (inl ℓ ∷ cb)
  `X : List I → I → Desc' I cb → Desc' I (inr [] ∷ cb)
  `▪ : I → Desc' I []

fromDesc' : (Desc' I cb) → List I → ConD (Indexˢ I) cb
fromDesc' (`σ A D')   Δ = σ A λ a → fromDesc' (D' a) Δ
fromDesc' (`X Γ i D') Δ = ρ (ι (i , Γ <> Δ , tt)) (fromDesc' D' Δ)
fromDesc' (`▪ i)      Δ = ι (i , Δ , tt)

⟦_⟧ : Desc' I cb → (List I → I -Scoped) → I -Scoped
⟦ `σ A d   ⟧ X i Γ =  Σ[ a ∈ A ] ⟦ d a ⟧ X i Γ
⟦ `X Δ j d ⟧ X i Γ = X Δ j Γ × ⟦ d ⟧ X i Γ
⟦ `▪ j     ⟧ X i Γ = i ≡ j

Syntaxⁱ : Set ℓ → (⊤ → Tel ℓ') → Setω
Syntaxⁱ {ℓ} {ℓ'} Ty tel = (ℓ ,ω (λ _ → [ _ ∶ Ty ] [ _ ∶ List Ty ] [])) ≡ω (ℓ' ,ω tel) --????

Syntaxʳ : RecD (Indexˢ Ty) rb → List Ty → Setω
Syntaxʳ (ι (_ , Γ , tt)) Δ = Liftω (Σ[ Δ' ∈ _ ] Γ ≡ Δ' <> Δ)
Syntaxʳ (π _ _)          _ = Liftω ⊥

Syntaxᵛ : Σω[ cb ∈ _ ] ConD (Indexˢ Ty) cb → Setω
Syntaxᵛ {Ty = Ty} D = D ≡ω (_ ,ω σ[ s ∶ Ty ]
                                 σ[ Γ ∶ List Ty ]
                                 σ[ _ ∶ Var s Γ ]
                                 ι (s , Γ , tt))

-- Assume a field taken by σ has no level for now.
Syntaxᶜ : ConD (Indexˢ Ty) cb → List Ty → Setω
Syntaxᶜ (ι (_ , Γ , tt)) Δ = Liftω (Γ ≡ Δ)
Syntaxᶜ (σ {ℓ} A D)      Δ = Σω (ℓ ≡ lzero) (λ refl → (a : A) → Syntaxᶜ (D a) Δ)
Syntaxᶜ (ρ A D)          Δ = Syntaxʳ A Δ ×ωω Syntaxᶜ D Δ

Syntaxᶜˢ : {Ty : Set ℓ} → ConDs (Indexˢ Ty) cbs → Setω
Syntaxᶜˢ [] = Liftω ⊤
Syntaxᶜˢ {ℓ = ℓ} {cbs = cb ∷ cbs} {Ty = Ty} (D ∷ Ds) =
   (Σω[ cb' ∈ ConB ]
  Σωω[ D' ∈ (List Ty → ConD (Indexˢ Ty) cb') ]
  Σωω[ D'' ∈ Desc' Ty cb' ]
    (cb ,ω D) ≡ω (inl ℓ ∷ cb' ,ω σ (List Ty) D'
      ⦂ω Σω ConB (λ cb → ConD (Indexˢ Ty) cb))
    ×ωω (∀ Δ → fromDesc' D'' Δ ≡ω D' Δ))
    ×ωω Syntaxᶜˢ Ds

Syntaxᶜˢ' : Set ℓ → ConDs (Indexˢ Ty) (cb ∷ cbs) → Setω
Syntaxᶜˢ' {ℓ = ℓ} {cb = cb} I (D ∷ Ds) =
         Syntaxᵛ  (cb ,ω D) ×ωω
         Syntaxᶜˢ Ds

-- Conditions for syntax:
--   * No parameters
--   * Scoped index (Index consists of an `I` and a `List I`)
--   * For constructors:
--     - Recursions are not functions
--     - ... something about indices

Syntax : Set ℓ → PDataD → Setω
Syntax {ℓ} Ty PD =
  Σωω Scoped
      λ { (refl ,ωω refl) →
            Σωω[ (cb' ,ω cbs' ,ω D' ,ωω Ds')
                   ∈ SyntaxConDs ⟦ Index tt ⟧ᵗ ]
            (struct       ,ω applyP)              ≡ω
             ((cb' ∷ cbs' ,ω λ _ → (D' ∷ Ds'))
                ⦂ω Σω ConBs (λ cbs → ⊤ → ConDs _ cbs))
            ×ωω Syntaxᶜˢ' ⟦ Index tt ⟧ᵗ (D' ∷ Ds')
        }
  where
    open PDataD PD
    SyntaxConDs : Set ℓ → Setω
    SyntaxConDs X =  Σω[ cb  ∈ ConB      ]
                     Σω[ cbs ∈ ConBs     ]
                    Σωω[ D   ∈ ConD X cb ]
                      ConDs X cbs
    Scoped : Setω
    Scoped = Σωω ((alevel ,ω plevel ,ω Param) ≡ω
                 ((lzero  ,ω lzero  ,ω [])
                   ⦂ω (Σω Level λ _ → Σω Level λ x → Tel x) ))
                 λ {refl →
                    Syntaxⁱ {ℓ} {ilevel} Ty (Index)
                 }

Syntaxᵈ : Set ℓ → DataD → Setω
Syntaxᵈ Ty D = Σωω PDataD λ PD → (#levels ,ω applyL) ≡ω
                                  ((0 ,ω λ _ → PD)
                                    ⦂ω Σω ℕ (λ _ → Levels → PDataD))
                                 ×ωω Syntax Ty PD
  where open DataD D

-- Fin can be used here
open import Prelude.Fin
private
  lengthᴰ : ConDs I cbs → ℕ
  lengthᴰ []       = 0
  lengthᴰ (D ∷ Ds) = suc (lengthᴰ Ds)
