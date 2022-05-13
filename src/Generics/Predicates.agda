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
Syntaxⁱ {ℓ} {ℓ'} Ty tel = Σω (ℓ ≡ ℓ') λ {refl → tel ≡ω λ _ → [ _ ∶ Ty ] [ _ ∶ List Ty ] []}

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
   Σω[ cb' ∈ ConB ]
  Σωω[ D' ∈ (List Ty → ConD (Indexˢ Ty) cb') ]
  Σωω ((cb ,ω D) ≡ω (((inl ℓ ∷ cb') ,ω σ (List Ty) D') ⦂ω Σω ConB (ConD (Indexˢ Ty))))
      λ {refl → Σωω[ D'' ∈ Desc' Ty cb' ]
                  (∀ Δ → (fromDesc' D'' Δ) ≡ω D' Δ) ×ωω
                  Syntaxᶜˢ Ds}

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

-- Cannot define as a record due to bugs on substω₁
--record Syntax (D : D.PDataD) : Setω where
--  open D.PDataD D
--  field
--    Ty     : Set
--    Pless  : isEmpty (plevel ,ω Param)
--    Scoped : let isEmpty : Σω[ p ∈ Level ] Tel p → Setω
--                 isEmpty σ = σ ≡ω (lzero ,ω [])
--              in Σωω (isEmpty (plevel ,ω Param))
--                     λ { refl →
--                         Σωω (Syntaxⁱ (ilevel ,ω Index tt))
--                             λ { (fstω₁ ,ω sndω₁) →
--                                 {!!}}
--                       }

Syntax : Set ℓ → PDataD → Setω
Syntax {ℓ} Ty PD =
  Σωω Scoped
      λ { (refl ,ω refl ,ωω refl ,ω refl) →
            Σωω[ (cb' ,ω cbs' ,ω D' ,ωω Ds')
                   ∈ SyntaxConDs ⟦ Index tt ⟧ᵗ ]
            Σω (struct ≡ (cb' ∷ cbs'))
               (λ {refl → applyP ≡ω λ tt → (D' ∷ Ds')})
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
    Scoped = Σω ((alevel , plevel) ≡ (lzero , lzero)) (λ {refl →
                Σωω (Param ≡ω []) (λ {refl →
                  Syntaxⁱ {ℓ} {ilevel} Ty (Index)
                })
              })

-- A possibly better (or worse) way to handle equalities
--    Scoped : Setω
--    Scoped = _≡ω_ {Σω[ p ∈ Level ]
--                   Σω[ i ∈ Level ]
--                   Σωω[ Par ∈ Tel p ] (⟦ Par ⟧ᵗ → Tel i)}
--                  (plevel ,ω ilevel ,ω Param ,ωω Index)
--                  (lzero  ,ω lzero  ,ω []    ,ωω λ {tt → [ _ ∶ Ty ] [ _ ∶ List Ty ] []})

Syntaxᵈ : Set ℓ → DataD → Setω
Syntaxᵈ Ty D = Σω (DataD.#levels D ≡ 0) λ _ →
               Σωω PDataD λ PD →
               Σωω (DataD.applyL D ≡ω λ _ → PD)
                  λ {refl → Syntax Ty PD}

--toDescᶜ : (D : ConD (Indexˢ I) cb) → Syntaxᶜ D Γ → Desc' I
--toDescᶜ (ι (t , ts , tt)) (lift refl) = `▪ t
--toDescᶜ (σ A D) (refl ,ω Sy) = `σ (Lift _ A) λ {(lift a) → toDescᶜ (D a) (Sy a)}
--toDescᶜ (ρ (ι (i , _ , tt)) D) (lift (is_ , refl) ,ωω prfᶜ) = `X is_ i (toDescᶜ D prfᶜ)

-- Fin can be used here
open import Prelude.Fin
private
  lengthᴰ : ConDs I cbs → ℕ
  lengthᴰ []       = 0
  lengthᴰ (D ∷ Ds) = suc (lengthᴰ Ds)

--toDescᶜˢ : (Ds : ConDs (Indexˢ I) cbs) → Syntaxᶜˢ Ds → Desc' I
--toDescᶜˢ [] _ = `σ (Lift _ ⊥) λ ()
--toDescᶜˢ (D ∷ Ds) (_ ,ω _ ,ωω refl ,ωω Syᶜ ,ωω Syᶜˢ) with lengthᴰ Ds
--... | n = `σ (Lift _ (Fin n))
--             λ { (lift zero)    → toDescᶜ  D {!!}
--               ; (lift (suc m)) → toDescᶜˢ Ds {!!}}
--
---- Ignore (but still require) the first constructor taking Var,
---- since the variable case is freely generated by the generic programs
--toDescᶜˢ' : (Ds : ConDs (I × List I × ⊤) (cb ∷ cbs))
--       → Syntaxᶜˢ' I Ds
--       → Desc' I
--toDescᶜˢ' (D ∷ Ds) (refl ,ωω Syᶜˢ) = toDescᶜˢ Ds Syᶜˢ
--
--toDesc : (P : PDataD) → Syntax I P → Desc' I
--toDesc (pdatad lzero [] Index applyP)
--       ((refl ,ω refl ,ωω refl ,ω refl)  ,ωω
--       Δ                                 ,ω
--       (cb' ,ω cbs' ,ω D' ,ωω Ds')       ,ωω
--       (refl ,ω refl)                    ,ωω
--       refl                              ,ωω
--       Syᶜˢ
--       ) = toDescᶜˢ' (applyP tt) (refl ,ωω Syᶜˢ)
--
--toDescᵈ : (D : DataD) → Syntaxᵈ I D → Desc' I
--toDescᵈ D (refl ,ω PD ,ωω refl ,ωω Sy) = toDesc PD Sy
--  where open DataD D

{-- Cursed attempt of conversion
toDescᵈ : (D : D.DataD) → Σω[ Ty ∈ Set ] Syntaxᵈ Ty D → Σ[ I ∈ Set ] Desc' I
toDescᵈ D (Ty ,ω refl ,ω (a ,ω b) ,ωω f) with D.DataD.applyL D tt
toDescᵈ .(D.datad _ _) (Ty
                      ,ω  refl
                      ,ω  (refl ,ω refl ,ωω refl ,ω prf)
                      ,ωω Δ
                      ,ω  (_ ,ω _ ,ω D' ,ωω Ds')
                      ,ωω (refl ,ω cds≡)
                      ,ωω Synᵛ
                      ,ωω Synᶜˢ)
     | D.pdatad alevel .[] Index applyP with applyP tt
toDescᵈ .(D.datad _ _)
       (Ty
         ,ω  refl
         ,ω  (refl ,ω refl ,ωω refl ,ω prf)
         ,ωω Δ
         ,ω  (_ ,ω _ ,ω .D ,ωω .Ds)
         ,ωω (refl ,ω refl)
         ,ωω Synᵛ
         ,ωω Synᶜˢ)
     | D.pdatad alevel .[] Index applyP | (D D.∷ Ds) = Ty , {!!}
--}
