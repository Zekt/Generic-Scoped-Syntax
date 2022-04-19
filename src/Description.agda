module Description where

open import Prelude

import Generics.Description as D
open import Generics.Telescope   as T
open import Utils.Reflection hiding (Type)

variable
  A B S : Set ℓ
  I : Set ℓ
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

variable
  rb  : D.RecB
  cb  : D.ConB
  cbs : D.ConBs
  ξ : Tel i
  Ty : Set ℓ

-- ≡ ⟦ [ _ ∶ Ty ] [ _ ∶ List Ty ] [] ⟧ᵗ
Indexˢ : Set ℓ → Set ℓ
Indexˢ Ty = Ty × List Ty × ⊤

Syntaxⁱ : Set ℓ → Tel ℓ' → Setω
Syntaxⁱ {ℓ} {ℓ'} Ty tel = Σω (ℓ ≡ ℓ') λ {refl → tel ≡ω [ _ ∶ Ty ] [ _ ∶ List Ty ] []}

Syntaxʳ : D.RecD (Indexˢ Ty) rb → List Ty → Setω
Syntaxʳ (D.ι (_ , Γ , tt)) Δ = Liftω (Σ[ Δ' ∈ _ ] Γ ≡ Δ' <> Δ)
Syntaxʳ (D.π _ _)          _ = Liftω ⊥

Syntaxᵛ : Σω[ cb ∈ _ ] D.ConD (Indexˢ Ty) cb → Setω
Syntaxᵛ {Ty = Ty} D = D ≡ω (_ ,ω D.σ[ s ∶ Ty ]
                                 D.σ[ Γ ∶ List Ty ]
                                 D.σ[ _ ∶ Var s Γ ]
                                 D.ι (s , Γ , tt))

-- Assume a field taken by σ has no level for now.
Syntaxᶜ : D.ConD (Indexˢ Ty) cb → List Ty → Setω
Syntaxᶜ (D.ι (_ , Γ , tt)) Δ = Liftω (Γ ≡ Δ)
Syntaxᶜ (D.σ {ℓ} A D)      Δ = Σω (ℓ ≡ lzero) (λ refl → (a : A) → Syntaxᶜ (D a) Δ)
Syntaxᶜ (D.ρ A D)          Δ = Syntaxʳ A Δ ×ωω Syntaxᶜ D Δ

Syntaxᶜˢ : D.ConDs (Indexˢ Ty) cbs → Setω
Syntaxᶜˢ D.[]       = Liftω ⊤
Syntaxᶜˢ (D D.∷ Ds) = Σω[ Δ ∈ _ ] Syntaxᶜ D Δ ×ωω
                      Syntaxᶜˢ Ds

Syntaxᶜˢ' : {ξ : Tel ℓ} → D.ConDs ⟦ ξ ⟧ᵗ (cb ∷ cbs) → Setω
Syntaxᶜˢ' {ℓ = ℓ} {cb = cb} {ξ = ξ} (D D.∷ Ds) =
  Σω[ I ∈ Set ℓ ]
  Σωω (Syntaxⁱ I ξ)
      λ {(refl ,ω refl) →
         Syntaxᵛ  (cb ,ω D) ×ωω
         Syntaxᶜˢ Ds
        }

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
Syntax : Set ℓ → D.PDataD → Setω
Syntax {ℓ} Ty PD =
  Σωω isEmpty
      λ { (refl ,ω refl ,ωω refl ,ω prf) →
             Σω[ Δ ∈ List Ty ]
            Σωω[ (cb' ,ω cbs' ,ω D' ,ωω Ds') ∈ SyntaxConDs ⟦ Index tt ⟧ᵗ ]
            Σωω[ _ ∈ Σω (struct ≡ (cb' ∷ cbs'))
                        (λ {refl → applyP tt ≡ω (D' D.∷ Ds')}) ]
               Syntaxᶜˢ' (D' D.∷ Ds')
        }
  where
    open D.PDataD PD
    SyntaxConDs : Set ℓ → Setω
    SyntaxConDs X =  Σω[ cb  ∈ D.ConB      ]
                     Σω[ cbs ∈ D.ConBs     ]
                    Σωω[ D   ∈ D.ConD X cb ]
                      D.ConDs X cbs
    isEmpty : Setω
    isEmpty = Σω (plevel ≡ lzero) (λ {refl →
                Σωω (Param ≡ω []) (λ {refl →
                  Syntaxⁱ {ℓ} {ilevel} Ty (Index tt)
                })
              })

-- A possibly better (or worse) way to handle equalities
--    Scoped : Setω
--    Scoped = _≡ω_ {Σω[ p ∈ Level ]
--                   Σω[ i ∈ Level ]
--                   Σωω[ Par ∈ Tel p ] (⟦ Par ⟧ᵗ → Tel i)}
--                  (plevel ,ω ilevel ,ω Param ,ωω Index)
--                  (lzero  ,ω lzero  ,ω []    ,ωω λ {tt → [ _ ∶ Ty ] [ _ ∶ List Ty ] []})

Syntaxᵈ : Set ℓ → D.DataD → Setω
Syntaxᵈ Ty D = Σω (D.DataD.#levels D ≡ 0)
                  λ {refl → Syntax Ty (D.DataD.applyL D tt)}

toDescᶜ : (D : D.ConD (Indexˢ I) cb) → Syntaxᶜ D Γ → Desc' I
toDescᶜ (D.ι (t , ts , tt)) (lift refl) = `▪ t
toDescᶜ (D.σ A D) (refl ,ω Sy) = `σ (Lift _ A) λ {(lift a) → toDescᶜ (D a) (Sy a)}
toDescᶜ (D.ρ (D.ι (i , _ , tt)) D) (lift (is_ , refl) ,ωω prfᶜ) = `X is_ i (toDescᶜ D prfᶜ)

-- Fin can be used here
open import Prelude.Fin
private
  lengthᴰ : D.ConDs I cbs → ℕ
  lengthᴰ D.[]       = 0
  lengthᴰ (D D.∷ Ds) = suc (lengthᴰ Ds)

toDescᶜˢ : (Ds : D.ConDs (Indexˢ I) cbs) → Syntaxᶜˢ Ds → Desc' I
toDescᶜˢ D.[] _ = `σ (Lift _ ⊥) λ ()
toDescᶜˢ (D D.∷ Ds) (Γ ,ω Syᶜ ,ωω Syᶜˢ) with lengthᴰ Ds
... | n = `σ (Lift _ (Fin n))
             λ { (lift zero)    → toDescᶜ D Syᶜ
               ; (lift (suc m)) → toDescᶜˢ Ds Syᶜˢ}

-- Ignore (but still require) the first constructor taking Var,
-- since the variable case is freely generated in the generic programs
{--
toDesc : ∀ {ξ : Tel lzero}
       → (Ds : D.ConDs ⟦ ξ ⟧ᵗ (cb ∷ cbs))
       → Syntaxᶜˢ' Ds
       → Desc' I
--}

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

