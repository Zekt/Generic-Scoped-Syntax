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

⟦_⟧′ᶜ : ∀ {I : Set ℓ} {Δ : List I}
      → (D : ConD (Indexˢ I) cb)
      → (Syntaxᶜ D Δ)
      → (List I → I -Scoped)
      → I → (Γ : List I) → Set ℓ
⟦_⟧′ᶜ (ι (j , Δ , tt)) (lift refl) X i Γ = i ≡ j
⟦_⟧′ᶜ (σ A D) (refl ,ω Syᶜ) X i Γ = Σ[ a ∈ A ] ⟦ D a ⟧′ᶜ (Syᶜ a) X i Γ
⟦_⟧′ᶜ (ρ R D) (Syʳ ,ωω Syᶜ) X i Γ = ⟦ R ⟧′ʳ Syʳ X i Γ × ⟦ D ⟧′ᶜ Syᶜ X i Γ

⟦_⟧′ᶜˢ : ∀ (Ds : ConDs (Indexˢ I) cbs)
       → Syntaxᶜˢ Ds
       → (List I → I -Scoped)
       → I -Scoped
⟦ [] ⟧′ᶜˢ (lift tt) X i Γ = Lift _ ⊥
⟦ .(σ (List _) D) ∷ Ds ⟧′ᶜˢ (_ ,ω D ,ωω refl ,ωω D' ,ωω eq ,ωω Syᶜˢ) X i Γ =
  ⟦ D' ⟧ X i Γ ⊎ ⟦ Ds ⟧′ᶜˢ Syᶜˢ X i Γ

⟦_⟧′ᶜˢ' : ∀ (Ds : ConDs (Indexˢ I) (cb ∷ cbs))
        → Syntaxᶜˢ' I Ds
        → I -Scoped
        → (List I → I -Scoped)
        → I -Scoped
⟦ ._ ∷ Ds ⟧′ᶜˢ' (refl ,ωω Syᶜˢ) V X i Γ =
  (V i Γ) ⊎ ⟦ Ds ⟧′ᶜˢ Syᶜˢ X i Γ

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

ContextEq : ∀ {D' : Desc' I cb}
          --→ Syntaxᶜ D Δ
          → ⟦ fromDesc' D' Δ ⟧ᶜ X (i , Γ , tt)
          → Δ ≡ Γ
ContextEq {D' = `σ _ _}   (_ , ⟦D'⟧) = ContextEq ⟦D'⟧
ContextEq {D' = `X _ _ _} (_ , ⟦D'⟧) = ContextEq ⟦D'⟧
ContextEq {D' = `▪ _}     ⟦D'⟧       = cong fst (cong snd ⟦D'⟧)

--translateʳ : ∀ {R : RecD (Indexˢ I) rb}
--           → (Syʳ : Syntaxʳ R Γ)
--           → (Γ -Env) V Δ
--           → (∀ {i Γ Δ} → V i Γ → (Γ -Env) Var Δ → (V i) Δ)
--           → ⟦ R ⟧ʳ (λ { (σ' , Γ' , tt) →
--                       (∀ Δ → (Γ' -Env) V Δ → C σ' Δ)})
--           → ⟦ R ⟧′ʳ Syʳ (Kripke V C) i Δ
--translateʳ {R = ι (σ' , ._ , tt)}
--           (lift ([] , refl))
--           ρ'
--           thⱽ
--           ⟦R⟧ = ⟦R⟧ _ ρ'
--translateʳ {R = ι (σ' , ._ , tt)}
--           (lift (x ∷ Δ' , refl))
--           ρ'
--           thⱽ
--           ⟦R⟧ = λ E₁ E₂ → ⟦R⟧ _ (E₂ Env++ bifmap (λ v → thⱽ v E₁) ρ')

--translateᶜ : ∀ {D : ConD (Indexˢ I) cb} → (Syᶜ : Syntaxᶜ D Γ)
--           → (Γ -Env) V Δ
--           → (∀ {i Γ Δ} → V i Γ → (Γ -Env) Var Δ → V i Δ)
--           → (d : ⟦ D ⟧ᶜ (λ { (σ' , Γ' , tt) →
--                       ∀ Δ → (Γ' -Env) V Δ → C σ' Δ}) (i , Γ , tt))
--           → ⟦ D ⟧′ᶜ Syᶜ (Kripke V C) i Δ
--translateᶜ {D = ι (j , Θ , tt)} (lift refl) ρ' thⱽ ⟦D⟧  = cong fst (sym ⟦D⟧) , ContextEq (lift refl) {!!}
--translateᶜ {D = σ A D} (refl ,ω Syᶜ) ρ' thⱽ (a , ⟦D⟧)   = a , translateᶜ (Syᶜ a) ρ' thⱽ ⟦D⟧
--translateᶜ {D = ρ R D} (Syʳ ,ωω Syᶜ) ρ' thⱽ (⟦R⟧ , ⟦D⟧) = translateʳ Syʳ ρ' thⱽ ⟦R⟧ , translateᶜ Syᶜ ρ' thⱽ ⟦D⟧

--translateᵏ :`

translateᶜ : ∀ {D' : Desc' I cb}
           → (Γ -Env) V Δ
           → (∀ {i Γ Δ} → V i Γ → (Γ -Env) Var Δ → V i Δ)
           → ⟦ fromDesc' D' Γ ⟧ᶜ (λ { (σ' , Γ' , tt) →
                                        (Δ₁ : List I)
                                      → (Γ' -Env) V Δ₁
                                      → C σ' Δ₁ })
                                 (i , Γ , tt)
           → ⟦ D' ⟧ (Kripke V C) i Δ
translateᶜ {D' = `σ A x} ρ' thⱽ (a , ⟦D'⟧) =
  a , (translateᶜ ρ' thⱽ ⟦D'⟧)
translateᶜ {D' = `X [] i D'} ρ' thⱽ (⟦R'⟧ , ⟦D'⟧) =
  ⟦R'⟧ _ ρ' , (translateᶜ ρ' thⱽ ⟦D'⟧)
translateᶜ {D' = `X (x ∷ is) i D'} ρ' thⱽ (⟦R'⟧ , ⟦D'⟧) =
  (λ E₁ E₂ → ⟦R'⟧ _ (E₂ Env++ bifmap (λ v → thⱽ v E₁) ρ')) , (translateᶜ ρ' thⱽ ⟦D'⟧)
translateᶜ {D' = `▪ x} ρ' thⱽ ⟦D'⟧ = cong fst (sym ⟦D'⟧)

translateᶜˢ : ∀ {i Γ}
                {Ds : ConDs (Indexˢ I) cbs}
              → (Syᶜˢ : Syntaxᶜˢ Ds)
              → (Γ -Env) V Δ
              → (∀ {i Γ Δ} → V i Γ → (Γ -Env) Var Δ → V i Δ)
              → ⟦ Ds ⟧ᶜˢ (λ { (σ' , Γ' , tt) →
                   ∀ Δ → (Γ' -Env) V Δ → C σ' Δ}) (i , Γ , tt)
              → ⟦ Ds ⟧′ᶜˢ Syᶜˢ (Kripke V C) i Δ
translateᶜˢ {Ds = .(σ (List _) D) ∷ Ds}
            (cb ,ω D ,ωω refl ,ωω D' ,ωω eq ,ωω Syᶜˢ)
            ρ'
            thⱽ
            (inl (Γ' , ⟦D'⟧)) with D Γ' | eq Γ'
... | ._ | refl with ContextEq ⟦D'⟧
... | refl = inl (translateᶜ ρ' thⱽ ⟦D'⟧)
translateᶜˢ {Ds = .(σ (List _) D) ∷ Ds}
            (cb ,ω D ,ωω refl ,ωω D' ,ωω eq ,ωω Syᶜˢ)
            ρ'
            thⱽ
            (inr ⟦Ds⟧) = inr (translateᶜˢ Syᶜˢ ρ' thⱽ ⟦Ds⟧)

record Semantics (D : DataD) (Sy : Syntaxᵈ I D) (V C : I -Scoped) : Setω where
  field
    thⱽ : V i Γ → (Γ -Env) Var Δ → V i Δ
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
                ; tt (inr C₁) Δ ρ' → alg (inr (translateᶜˢ Syᶜˢ ρ' thⱽ C₁))}
  }
  where open Semantics S

SyntaxLam : Syntaxᵈ Type (findDataD (quote Lam))
SyntaxLam = refl
         ,ω  _
         ,ωω refl
         ,ωω (refl ,ω (refl ,ωω (refl ,ω refl)))
         ,ωω _
         ,ωω (refl ,ω refl)
         ,ωω refl
         ,ωω _
         ,ω  _
         ,ωω refl
         ,ωω (`σ Type (λ t →
              `σ Type (λ u →
              `X [] (t ‵→ u)
              (`X [] t (`▪ u)))))
         ,ωω (λ _ → refl)
         ,ωω _
         ,ω _
         ,ωω refl
         ,ωω ((`σ Type λ t →
               `σ Type (λ u →
               `X (t ∷ []) u
               (`▪ (t ‵→ u))))
         ,ωω (λ _ → refl) ,ωω (lift tt))

private
  th^Var : Var i Γ → (Γ -Env) Var Δ → Var i Δ
  th^Var V e = lookup e V

toSyntaxᶜ : ∀ {D' : Desc' Type cb}
              {D : ConD (Indexˢ Type) cb}
              {N : Indexˢ Type → Set}
          → fromDesc' D' Γ ≡ω D
          → ⟦ D' ⟧ (Kripke Var (λ ℓs ps → N (ℓs , ps , tt))) i Γ
          → ⟦ D ⟧ᶜ N (i , Γ , tt)
toSyntaxᶜ {D' = `σ A x}    refl (a , ⟦D⟧) = a , toSyntaxᶜ refl ⟦D⟧
toSyntaxᶜ {D' = `X [] _ _} refl (K , ⟦D⟧) = K , toSyntaxᶜ refl ⟦D⟧
toSyntaxᶜ {Γ = Γ} {D' = `X (x ∷ Δ) _ _} refl (K , ⟦D⟧) =
  K (bifmap {Δ = Δ} {Γ = Γ}       weakenVarL (pack id))
    (bifmap {Δ = Γ} {Γ = (x ∷ Δ)} weakenVarR (pack id))
  , toSyntaxᶜ refl ⟦D⟧
toSyntaxᶜ {D' = `▪ x} refl refl = refl

toSyntax : ∀ {Ds : ConDs (Indexˢ Type) cbs}
             {N : Indexˢ Type → Set}
             {Syᶜ}
         → ⟦ Ds ⟧′ᶜˢ Syᶜ (Kripke Var (λ ℓs ps → N (ℓs , ps , tt))) i Γ
         → ⟦ Ds ⟧ᶜˢ N (i , Γ , tt)

toSyntax {Γ = Γ} {Ds = ._ ∷ Ds}
         {Syᶜ = cb ,ω D ,ωω refl ,ωω D' ,ωω eq ,ωω Syᶜˢ}
         (inl ⟦D'⟧)  = inl (Γ , (toSyntaxᶜ (eq Γ) ⟦D'⟧))
toSyntax {Ds = ._ ∷ Ds}
         {Syᶜ = _ ,ω _ ,ωω refl ,ωω _ ,ωω _ ,ωω Syᶜˢ}
         (inr ⟦Ds'⟧) = inr (toSyntax ⟦Ds'⟧)

--Renaming : Semantics (findDataD (quote Lam)) SyntaxLam Var Lam
--Renaming = record { thⱽ = th^Var
--                  ; alg = λ { (inl x) → ‵var x
--                            ; (inr (inl (Γ' , σ' , τ' , E₁ , E₂ , refl))) → ‵app E₁ E₂
--                            ; (inr (inr (inl (Γ' , σ' , τ' , E , refl)))) → ‵lam (E weaken (pack (λ {z → z})))} }

RenameT : ∀ {D N} (C : DataC D N) → (Sy : Syntaxᵈ Type D) → Setω
RenameT {D} {N} C Sy@(refl                            ,ω
                      _                               ,ωω
                      refl                            ,ωω
                      (refl ,ω refl ,ωω refl ,ω refl) ,ωω
                      _) = Semantics D Sy Var (curryN (N tt tt))
  where curryN : ∀ {I : Set ℓ} → (Indexˢ I → Set ℓ) → I -Scoped
        curryN ind = λ i Γ → ind (i , Γ , tt)

Renaming : ∀ {D N}
         → (C : DataC D N)
         → (Sy : Syntaxᵈ Type D)
         → RenameT C Sy
Renaming {D = D} {N} C
         (refl                            ,ω
          PD                              ,ωω
          refl                            ,ωω
          (refl ,ω refl ,ωω refl ,ω refl) ,ωω
          (_ ,ω _ ,ω E ,ωω Es)            ,ωω
          (refl ,ω refl)                  ,ωω
          refl                            ,ωω
          Syᶜ) = record { thⱽ = th^Var
                        ; alg = λ { (inl x)    → toN (inl (_ , _ , x , refl))
                                  ; (inr ⟦Es⟧) → toN (inr (toSyntax ⟦Es⟧)) }}
  where open DataC C

RenameLamSem : Semantics (findDataD (quote Lam)) SyntaxLam Var Lam
RenameLamSem = Renaming (findDataC (quote Lam)) SyntaxLam

RenameP = SemP (findDataC (quote Lam)) SyntaxLam RenameLamSem

unquoteDecl rename = defineFold RenameP rename

RenameC = genFoldC RenameP rename

SubstT : ∀ {D N} (C : DataC D N) → (Sy : Syntaxᵈ Type D) → Setω
SubstT {D} {N} C Sy@(refl
                 ,ω  _
                 ,ωω refl
                 ,ωω (refl ,ω refl ,ωω refl ,ω refl)
                 ,ωω _) = Semantics D Sy curriedN curriedN
  where curryN : ∀ {I : Set ℓ} → (Indexˢ I → Set ℓ) → I -Scoped
        curryN ind = λ i Γ → ind (i , Γ , tt)
        curriedN = curryN (N tt tt)

Subst : ∀ {D N}
      → (C : DataC D N)
      → (Sy : Syntaxᵈ Type D)
      → SubstT C Sy
