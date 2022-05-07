module ScopeSafe.Semantics where

open import Prelude hiding (lookup)
open import ScopeSafe.Description
open import Generics.Description
open import Generics.Recursion
open import Generics.Predicates
open import Generics.Telescope
open import Generics.Reflection

private variable
  I : Set ℓ
  i : I
  V C : I -Scoped
  Γ Γ' Δ Δ' Θ : List I
  X : I → Set ℓ
  cb : ConB
  cbs : ConBs
  rb : RecB

Thinning : {I : Set ℓ} → List I → List I → Set ℓ
Thinning Γ Δ = (Γ -Env) Var Δ

□ : {I : Set ℓ} → (List I → Set ℓ) → (List I → Set ℓ)
(□ T) Γ = ∀[ Thinning Γ ⇒ T ]

Thinnable : {I : Set ℓ} → (List I → Set ℓ) → Set ℓ
Thinnable T = ∀[ T ⇒ □ T ]

Kripke : (V C : I -Scoped) → (List I → I -Scoped)
Kripke V C [] j = C j
--Kripke V C Δ  j = □ ((Δ -Env) V ⇒ C j)
Kripke V C Δ j Γ = ∀ {Θ} → (Γ -Env) Var Θ → (Δ -Env) V Θ → C j Θ

⟦_⟧′ʳ : (R : RecD (Indexˢ I) rb)
      → Syntaxʳ R Δ
      → (List I → I -Scoped)
      → I -Scoped
⟦ ι (j , ._ , tt) ⟧′ʳ (lift (Δ , refl)) X i Γ = X Δ j Γ

⟦_⟧′ᶜ : (D : ConD (Indexˢ I) cb) → (Syntaxᶜ D Δ) → (List I → I -Scoped) → I -Scoped
⟦ ι (j , _ , tt) ⟧′ᶜ (lift k) X i Γ = i ≡ j
⟦ σ A D ⟧′ᶜ (refl ,ω Syᶜ) X i Γ = Σ[ a ∈ A ] ⟦ D a ⟧′ᶜ (Syᶜ a) X i Γ
⟦ ρ R D ⟧′ᶜ (Syʳ ,ωω Syᶜ) X i Γ = ⟦ R ⟧′ʳ Syʳ X i Γ × ⟦ D ⟧′ᶜ Syᶜ X i Γ

⟦_⟧′ᶜˢ : ∀ (Ds : ConDs (Indexˢ I) cbs)
       → Syntaxᶜˢ Ds
       → (List I → I -Scoped)
       → I -Scoped
⟦ [] ⟧′ᶜˢ (lift tt) X i Γ = Lift _ ⊥
⟦ .(σ (List _) D') ∷ Ds ⟧′ᶜˢ (_ ,ω D' ,ωω refl ,ωω Syᶜ ,ωω Syᶜˢ) X i Γ = (Σ[ Δ ∈ _ ] ⟦ D' Δ ⟧′ᶜ (Syᶜ Δ) X i Γ) ⊎ ⟦ Ds ⟧′ᶜˢ Syᶜˢ X i Γ

⟦_⟧′ᶜˢ' : ∀ (Ds : ConDs (Indexˢ I) (cb ∷ cbs))
        → Syntaxᶜˢ' I Ds
        → I -Scoped
        → (List I → I -Scoped)
        → I -Scoped
⟦ ._ ∷ Ds ⟧′ᶜˢ' (refl ,ωω Syᶜˢ) V X i Γ = (V i Γ) ⊎ ⟦ Ds ⟧′ᶜˢ Syᶜˢ X i Γ

⟦_⟧′ : (P : PDataD)
     → Syntax I P
     → I -Scoped
     → (List I → I -Scoped)
     → I -Scoped
⟦ P ⟧′ ((refl ,ω refl ,ωω refl ,ω refl) ,ωω
        (cb' ,ω cbs' ,ω D' ,ωω Ds')     ,ωω
        (refl ,ω refl)                  ,ωω
        Sy')
       V X i Γ = ⟦ applyP tt ⟧′ᶜˢ' Sy' V X i Γ
  where open PDataD P

⟦_⟧′ᵈ : (D : DataD)
      → Syntaxᵈ I D
      → I -Scoped
      → (List I → I -Scoped)
      → I -Scoped
⟦ D ⟧′ᵈ (refl ,ω PD ,ωω refl ,ωω Sy) V X i Γ = ⟦ PD ⟧′ Sy V X i Γ

ContextEq : ∀ {D : ConD (Indexˢ I) cb} → Syntaxᶜ D Δ → ⟦ D ⟧ᶜ X (i , Γ , tt) → Δ ≡ Γ
ContextEq {D = ι .(_ , _ , tt)} (lift refl) refl = refl
ContextEq {D = σ A D} (refl ,ω Syᶜ) (a , ⟦D⟧) = ContextEq (Syᶜ a) ⟦D⟧
ContextEq {D = ρ R D} (_ ,ωω Syᶜ) (_ , ⟦D⟧) = ContextEq Syᶜ ⟦D⟧

translateʳ : ∀ {R : RecD (Indexˢ I) rb}
           → (Syʳ : Syntaxʳ R Γ)
           → (Γ -Env) V Δ
           → (∀ {i Γ Δ} → V i Γ → (Γ -Env) Var Δ → (V i) Δ)
           → ⟦ R ⟧ʳ (λ { (σ' , Γ' , tt) →
                       (∀ Δ → (Γ' -Env) V Δ → C σ' Δ)})
           → ⟦ R ⟧′ʳ Syʳ (Kripke V C) i Δ
translateʳ {R = ι (σ' , ._ , tt)}
           (lift ([] , refl))
           ρ'
           thⱽ
           ⟦R⟧ = ⟦R⟧ _ ρ'
translateʳ {R = ι (σ' , ._ , tt)}
           (lift (x ∷ Δ' , refl))
           ρ'
           thⱽ
           ⟦R⟧ = λ E₁ E₂ → ⟦R⟧ _ (E₂ Env++ bifmap (λ v → thⱽ v E₁) ρ')

translateᶜ : ∀ {D : ConD (Indexˢ I) cb} → (Syᶜ : Syntaxᶜ D Γ)
           → (Γ -Env) V Δ
           → (∀ {i Γ Δ} → V i Γ → (Γ -Env) Var Δ → (V i) Δ)
           → ⟦ D ⟧ᶜ (λ { (σ' , Γ' , tt) →
                       ∀ Δ → (Γ' -Env) V Δ → C σ' Δ}) (i , Γ , tt)
           → ⟦ D ⟧′ᶜ Syᶜ (Kripke V C) i Δ
translateᶜ {D = ι (j , Θ , tt)} (lift refl) ρ' thⱽ ⟦D⟧ = cong fst (sym ⟦D⟧)
translateᶜ {D = σ A D} (refl ,ω Syᶜ) ρ' thⱽ (a , ⟦D⟧) = a , translateᶜ (Syᶜ a) ρ' thⱽ ⟦D⟧
translateᶜ {D = ρ R D} (Syʳ ,ωω Syᶜ) ρ' thⱽ (⟦R⟧ , ⟦D⟧) = translateʳ Syʳ ρ' thⱽ ⟦R⟧ , translateᶜ Syᶜ ρ' thⱽ ⟦D⟧

--translateᵏ :`
translateᶜˢ : ∀ {i Γ}
                {Ds : ConDs (Indexˢ I) cbs}
              → (Syᶜˢ : Syntaxᶜˢ Ds)
              → (Γ -Env) V Δ
              → (∀ {i Γ Δ} → V i Γ → (Γ -Env) Var Δ → (V i) Δ)
              → ⟦ Ds ⟧ᶜˢ (λ { (σ' , Γ' , tt) →
                   ∀ Δ → (Γ' -Env) V Δ → C σ' Δ}) (i , Γ , tt)
              → ⟦ Ds ⟧′ᶜˢ Syᶜˢ (Kripke V C) i Δ
translateᶜˢ {Ds = .(σ (List _) D') ∷ Ds}
            (cb ,ω D' ,ωω refl ,ωω Syᶜ ,ωω Syᶜˢ)
            ρ'
            thⱽ
            (inl (Γ' , ⟦D'⟧)) with ContextEq (Syᶜ Γ') ⟦D'⟧
...       | refl = inl (Γ' , translateᶜ (Syᶜ Γ') ρ' thⱽ ⟦D'⟧)
translateᶜˢ {Ds = .(σ (List _) D') ∷ Ds} (cb ,ω D' ,ωω refl ,ωω Syᶜ ,ωω Syᶜˢ) ρ' thⱽ (inr ⟦Ds⟧) = inr (translateᶜˢ Syᶜˢ ρ' thⱽ ⟦Ds⟧)

--translate : ∀ {D ps is i Γ} → (Sy : Syntaxᵈ I D) → ⟦ D ⟧ᵈ (λ x → {!!}) is → ⟦ D ⟧′ᵈ Sy _ (Kripke V C) i Γ
--translate (refl ,ω pdatad alevel .[] .(λ _ → ∷-syntaxᵗ _ (λ _ → ∷-syntaxᵗ (List _) (λ _ → []))) .(λ tt₁ → σ _ (λ s₁ → σ (List _) (λ Γ → σ (Var s₁ Γ) (λ _ → ι (s₁ , Γ , tt)))) ∷ Ds') ,ωω refl ,ωω (refl ,ω refl ,ωω refl ,ω refl) ,ωω (.(inl _ ∷ inl _ ∷ [ inl _ ]) ,ω cbs' ,ω .(σ _ (λ s₁ → σ (List _) (λ Γ → σ (Var s₁ Γ) (λ _ → ι (s₁ , Γ , tt))))) ,ωω Ds') ,ωω (refl ,ω refl) ,ωω refl ,ωω Syᶜˢ) (inl (σ' , Γ' , V , refl)) = {!!}
--translate {D} (refl ,ω PD ,ωω refl ,ωω (refl ,ω refl ,ωω refl ,ω refl) ,ωω (.(inl _ ∷ inl _ ∷ [ inl _ ]) ,ω cbs' ,ω .(σ _ (λ s₁ → σ (List _) (λ Γ → σ (Var s₁ Γ) (λ _ → ι (s₁ , Γ , tt))))) ,ωω Ds') ,ωω (refl ,ω refl) ,ωω refl ,ωω Syᶜˢ) (inr y) = {!!}

record Semantics (D : DataD) (Sy : Syntaxᵈ I D) (V C : I -Scoped) : Setω where
  field
    thⱽ : V i Γ → (Γ -Env) Var Δ → (V i) Δ
    --var : V i Γ → C i Γ
    alg : ⟦ D ⟧′ᵈ Sy V (Kripke V C) i Γ → C i Γ

open _-Env

SemP : ∀ {D N} {V C : I -Scoped}
     → (Con : DataC D N) → (Sy : Syntaxᵈ I D)
     → Semantics D Sy V C → FoldP
SemP {ℓ} {I} {D} {N} {V} {C} Con
     (refl ,ω
     (pdatad lzero [] Index applyP) ,ωω
     refl ,ωω
       ((refl ,ω refl ,ωω refl ,ω refl) ,ωω
       (cb' ,ω cbs' ,ω D' ,ωω Ds')      ,ωω
       (refl ,ω refl)                   ,ωω
       refl                             ,ωω
       Syᶜˢ
     )) S = record
  { Conv = Con
  ; #levels = 0
  ; level = λ _ → tt
  ; Param = λ _ → []
  ; ParamV = []
  ; ParamN = []
  ; param = λ _ → tt
  ; Carrier = λ _ _ (σ' , Γ' , tt) → ∀ Δ → (Γ' -Env) V Δ → C σ' Δ
  ; algebra = λ { tt (inl (σ' , Γ' , v , refl)) Δ ρ' → alg (inl (lookup ρ' v))
                ; tt (inr C₁) Δ ρ' → alg (inr (translateᶜˢ Syᶜˢ ρ' thⱽ C₁)) }
 -- ; algebra = λ { tt (inl (σ' , Γ' , v , refl)) ρ' → var (lookup ρ' v)
 --               ; tt (inr C) ρ' → alg {!C!} }
  }
  where open Semantics S
        --test1 :  ⟦ Ds' ⟧ᶜˢ
        -- (λ (a , b , c) →
        --    {Δ : List I} →
        --    (b -Env) V Δ →
        --    C a Δ)
        -- i
        --test2 : ⟦ Ds' ⟧′ᶜˢ Syᶜˢ (Kripke V C) (fst i) Δ

SyntaxLam : Syntaxᵈ Type (findDataD (quote Lam))
SyntaxLam = refl ,ω (_ ,ωω refl ,ωω (refl ,ω (refl ,ωω (refl ,ω refl))) ,ωω _ ,ωω (refl ,ω refl) ,ωω (refl ,ωω _ ,ω (_ ,ωω (refl ,ωω (λ Δ → refl ,ω (λ a → refl ,ω (λ x → lift ([] , refl) ,ωω lift ([] , refl) ,ωω lift refl))) ,ωω _ ,ω (_ ,ωω (refl ,ωω ((λ x → refl ,ω (λ x₁ → refl ,ω (λ x₂ → lift ([ x₁ ] , refl) ,ωω lift refl))) ,ωω lift tt)))))))

Renaming : Semantics (findDataD (quote Lam)) SyntaxLam Var Lam
Renaming = record { thⱽ = th^Var
                  ; alg = λ { (inl x) → ‵var x
                            ; (inr (inl (Γ' , σ' , τ' , E₁ , E₂ , refl))) → ‵app E₁ E₂
                            ; (inr (inr (inl (Γ' , σ' , τ' , E , refl)))) → ‵lam (E weaken (pack (λ {z → z})))} }
  where th^Var : Var i Γ → (Γ -Env) Var Δ → Var i Δ
        th^Var V e = lookup e V

unquoteDecl rename = defineFold (SemP (findDataC (quote Lam)) SyntaxLam Renaming) rename
