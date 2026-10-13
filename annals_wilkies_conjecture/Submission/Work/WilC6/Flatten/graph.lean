/-
  WilC6 / Flatten — graphs of terms are existentially definable.

  For every term `t` of `LEc = expRing[[ℝ]]` with variables indexed by `κ`, the *graph*

    `Gr t = {u : (κ ⊕ Fin 1) → ℝ | u (Sum.inr 0) = t.realize (u ∘ Sum.inl)}`

  is `ExpExistI`.  This is the syntactic input for the flattening of `IsEF` formulas: equations and
  inequations of terms reduce to graphs of terms together with the closure of `ExpExistI` under
  intersections and projections.

  The proof is an induction on the term.  We first prove the statement for terms of `Lexp = expRing`
  with a *parameter map* `c : A → ℝ` (using `Term.constantsToVars` to pass from `LEc` to `Lexp`).
  For each function symbol we combine the graphs of the subterms with the equation defining the
  operation, then project the auxiliary coordinates away.
-/
import Mathlib
import Submission.Work.WilC6.Base
import Submission.Work.WilkiesB.Defs
import Submission.Work.WilkiesB.Closure

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Classical FirstOrder FirstOrder.Language
open FirstOrder.Language.Structure
open WilkiesDesign.CG
open WilkiesConjecture
open Work.WilkiesB

namespace Work.WilC6.Flatten

/-! ## 0. Function symbols with the "right" types

  Elaborating `Sum.inl ringFunc.add : expRing.Functions 2` forces the type checker to unfold
  `Language.sum`, which then blocks later rewrites.  We therefore introduce abbreviations carrying
  the sum-language types explicitly. -/

abbrev addSymL : Lexp.Functions 2 := Sum.inl FirstOrder.Ring.addFunc
abbrev mulSymL : Lexp.Functions 2 := Sum.inl FirstOrder.Ring.mulFunc
abbrev negSymL : Lexp.Functions 1 := Sum.inl FirstOrder.Ring.negFunc
abbrev zeroSymL : Lexp.Functions 0 := Sum.inl FirstOrder.Ring.zeroFunc
abbrev oneSymL : Lexp.Functions 0 := Sum.inl FirstOrder.Ring.oneFunc
abbrev expFuncSym : WilkiesConjecture.Language.exp.Functions 1 :=
  WilkiesConjecture.expFunc.exp
abbrev expSymL : Lexp.Functions 1 := Sum.inr expFuncSym

abbrev addSymE : LEc.Functions 2 := Sum.inl addSymL
abbrev mulSymE : LEc.Functions 2 := Sum.inl mulSymL
abbrev negSymE : LEc.Functions 1 := Sum.inl negSymL
abbrev expSymE : LEc.Functions 1 := Sum.inl expSymL

/-! ## 1. Zero sets of exp-polynomials in the ambient coordinates -/

/-- The zero set of an exp-polynomial in the plain variables is `ExpExistI`. -/
theorem expExistI_evalZero {κ : Type*} (P : MvPolynomial (κ ⊕ κ) ℝ) :
    ExpExistI {x : κ → ℝ | expEval x P = 0} := by
  refine ⟨Fin 0, inferInstance,
    MvPolynomial.rename (polyMap (Sum.inl : κ → κ ⊕ Fin 0)) P, ?_⟩
  ext x
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hx
    exact ⟨Fin.elim0, by simpa [expEval_rename, sumElim_comp_inl] using hx⟩
  · rintro ⟨y, hy⟩
    simpa [expEval_rename, sumElim_comp_inl] using hy

/-! ## 2. Graphs -/

/-- Graph of a term of `Lexp` with parameter map `c`. -/
def GrL {A κ : Type*} (c : A → ℝ) (t : Lexp.Term (A ⊕ κ)) : Set (κ ⊕ Fin 1 → ℝ) :=
  {u | u (Sum.inr 0) = t.realize (Sum.elim c (u ∘ Sum.inl))}

/-- Graph of a term of `LEc`. -/
def Gr {κ : Type*} (t : LEc.Term κ) : Set (κ ⊕ Fin 1 → ℝ) :=
  {u | u (Sum.inr 0) = t.realize (u ∘ Sum.inl)}

/-! ## 3. Realisation of the term constructors of `LEc` -/

/-- `t₁ + t₂` as a term of `LEc`. -/
def tAdd {κ : Type*} (t₁ t₂ : LEc.Term κ) : LEc.Term κ := Term.func addSymE ![t₁, t₂]

/-- `t₁ * t₂` as a term of `LEc`. -/
def tMul {κ : Type*} (t₁ t₂ : LEc.Term κ) : LEc.Term κ := Term.func mulSymE ![t₁, t₂]

/-- `-t` as a term of `LEc`. -/
def tNeg {κ : Type*} (t : LEc.Term κ) : LEc.Term κ := Term.func negSymE ![t]

theorem funMap_addL (x : Fin 2 → ℝ) :
    (@funMap Lexp ℝ _ 2 addSymL x) = x 0 + x 1 := by
  show (@funMap (Language.ring.sum Language.exp) ℝ _ 2
    (Sum.inl FirstOrder.Ring.addFunc) x) = x 0 + x 1
  rw [funMap_sumInl]; simp

theorem funMap_mulL (x : Fin 2 → ℝ) :
    (@funMap Lexp ℝ _ 2 mulSymL x) = x 0 * x 1 := by
  show (@funMap (Language.ring.sum Language.exp) ℝ _ 2
    (Sum.inl FirstOrder.Ring.mulFunc) x) = x 0 * x 1
  rw [funMap_sumInl]; simp

theorem funMap_negL (x : Fin 1 → ℝ) :
    (@funMap Lexp ℝ _ 1 negSymL x) = - x 0 := by
  show (@funMap (Language.ring.sum Language.exp) ℝ _ 1
    (Sum.inl FirstOrder.Ring.negFunc) x) = - x 0
  rw [funMap_sumInl]; simp

theorem funMap_zeroL (x : Fin 0 → ℝ) :
    (@funMap Lexp ℝ _ 0 zeroSymL x) = 0 := by
  show (@funMap (Language.ring.sum Language.exp) ℝ _ 0
    (Sum.inl FirstOrder.Ring.zeroFunc) x) = 0
  rw [funMap_sumInl]; simp

theorem funMap_oneL (x : Fin 0 → ℝ) :
    (@funMap Lexp ℝ _ 0 oneSymL x) = 1 := by
  show (@funMap (Language.ring.sum Language.exp) ℝ _ 0
    (Sum.inl FirstOrder.Ring.oneFunc) x) = 1
  rw [funMap_sumInl]; simp

theorem funMap_expL (x : Fin 1 → ℝ) :
    (@funMap Lexp ℝ _ 1 expSymL x) = Real.exp (x 0) := by
  show (@funMap (Language.ring.sum Language.exp) ℝ _ 1
    (Sum.inr expFuncSym) x) = Real.exp (x 0)
  rw [funMap_sumInr]; rfl

theorem funMap_addE (x : Fin 2 → ℝ) :
    (@funMap LEc ℝ _ 2 addSymE x) = x 0 + x 1 := by
  show (@funMap (Lexp.sum (Language.constantsOn ℝ)) ℝ _ 2 (Sum.inl addSymL) x) = x 0 + x 1
  rw [funMap_sumInl]; exact funMap_addL x

theorem funMap_mulE (x : Fin 2 → ℝ) :
    (@funMap LEc ℝ _ 2 mulSymE x) = x 0 * x 1 := by
  show (@funMap (Lexp.sum (Language.constantsOn ℝ)) ℝ _ 2 (Sum.inl mulSymL) x) = x 0 * x 1
  rw [funMap_sumInl]; exact funMap_mulL x

theorem funMap_negE (x : Fin 1 → ℝ) :
    (@funMap LEc ℝ _ 1 negSymE x) = - x 0 := by
  show (@funMap (Lexp.sum (Language.constantsOn ℝ)) ℝ _ 1 (Sum.inl negSymL) x) = - x 0
  rw [funMap_sumInl]; exact funMap_negL x

@[simp] theorem realize_tAdd {κ : Type*} (t₁ t₂ : LEc.Term κ) (v : κ → ℝ) :
    (tAdd t₁ t₂).realize v = t₁.realize v + t₂.realize v := by
  rw [tAdd, Term.realize_func, funMap_addE]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

@[simp] theorem realize_tMul {κ : Type*} (t₁ t₂ : LEc.Term κ) (v : κ → ℝ) :
    (tMul t₁ t₂).realize v = t₁.realize v * t₂.realize v := by
  rw [tMul, Term.realize_func, funMap_mulE]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

@[simp] theorem realize_tNeg {κ : Type*} (t : LEc.Term κ) (v : κ → ℝ) :
    (tNeg t).realize v = - t.realize v := by
  rw [tNeg, Term.realize_func, funMap_negE]
  simp only [Matrix.cons_val_fin_one]

/-- `(t₁ - t₂) * z`, over the index type `κ ⊕ Fin 1` (where `z = Sum.inr 0`). -/
def subMulTerm {κ : Type*} (t₁ t₂ : LEc.Term κ) : LEc.Term (κ ⊕ Fin 1) :=
  tMul (tAdd (t₁.relabel Sum.inl) (tNeg (t₂.relabel Sum.inl))) (Term.var (Sum.inr 0))

@[simp] theorem realize_subMulTerm {κ : Type*} (t₁ t₂ : LEc.Term κ)
    (v : κ ⊕ Fin 1 → ℝ) :
    (subMulTerm t₁ t₂).realize v =
      (t₁.realize (v ∘ Sum.inl) - t₂.realize (v ∘ Sum.inl)) * v (Sum.inr 0) := by
  simp only [subMulTerm, realize_tMul, realize_tAdd, realize_tNeg, Term.realize_relabel,
    Term.realize_var]
  ring

/-! ## 4. Auxiliary maps selecting the value coordinates -/

/-- The map `(κ ⊕ Fin 1) → (κ ⊕ Fin 1) ⊕ Fin 2` selecting the first auxiliary coordinate. -/
def fAdd0 (κ : Type*) : (κ ⊕ Fin 1) → (κ ⊕ Fin 1) ⊕ Fin 2
  | Sum.inl i => Sum.inl (Sum.inl i)
  | Sum.inr _ => Sum.inr (0 : Fin 2)

/-- The map `(κ ⊕ Fin 1) → (κ ⊕ Fin 1) ⊕ Fin 2` selecting the second auxiliary coordinate. -/
def fAdd1 (κ : Type*) : (κ ⊕ Fin 1) → (κ ⊕ Fin 1) ⊕ Fin 2
  | Sum.inl i => Sum.inl (Sum.inl i)
  | Sum.inr _ => Sum.inr (1 : Fin 2)

/-- The map `(κ ⊕ Fin 1) → (κ ⊕ Fin 1) ⊕ Fin 1` selecting the unique auxiliary coordinate. -/
def fUn (κ : Type*) : (κ ⊕ Fin 1) → (κ ⊕ Fin 1) ⊕ Fin 1
  | Sum.inl i => Sum.inl (Sum.inl i)
  | Sum.inr _ => Sum.inr (0 : Fin 1)

theorem comp_fAdd0_inl {κ : Type*} (ζ : κ ⊕ Fin 1 → ℝ) (u : Fin 2 → ℝ) :
    ((Sum.elim ζ u) ∘ fAdd0 κ) ∘ (Sum.inl : κ → κ ⊕ Fin 1) = ζ ∘ Sum.inl := by
  funext i; rfl

theorem comp_fAdd1_inl {κ : Type*} (ζ : κ ⊕ Fin 1 → ℝ) (u : Fin 2 → ℝ) :
    ((Sum.elim ζ u) ∘ fAdd1 κ) ∘ (Sum.inl : κ → κ ⊕ Fin 1) = ζ ∘ Sum.inl := by
  funext i; rfl

theorem comp_fUn_inl {κ : Type*} (ζ : κ ⊕ Fin 1 → ℝ) (u : Fin 1 → ℝ) :
    ((Sum.elim ζ u) ∘ fUn κ) ∘ (Sum.inl : κ → κ ⊕ Fin 1) = ζ ∘ Sum.inl := by
  funext i; rfl

theorem eval_fAdd0_val {κ : Type*} (ζ : κ ⊕ Fin 1 → ℝ) (u : Fin 2 → ℝ) :
    (Sum.elim ζ u) (fAdd0 κ (Sum.inr (0 : Fin 1))) = u 0 := by
  change (Sum.elim ζ u) (Sum.inr (0 : Fin 2)) = u 0
  rfl

theorem eval_fAdd1_val {κ : Type*} (ζ : κ ⊕ Fin 1 → ℝ) (u : Fin 2 → ℝ) :
    (Sum.elim ζ u) (fAdd1 κ (Sum.inr (0 : Fin 1))) = u 1 := by
  change (Sum.elim ζ u) (Sum.inr (1 : Fin 2)) = u 1
  rfl

theorem eval_fUn_val {κ : Type*} (ζ : κ ⊕ Fin 1 → ℝ) (u : Fin 1 → ℝ) :
    (Sum.elim ζ u) (fUn κ (Sum.inr (0 : Fin 1))) = u 0 := by
  change (Sum.elim ζ u) (Sum.inr (0 : Fin 1)) = u 0
  rfl

/-- Membership of a pulled-back point in the graph of `t`, for the first auxiliary map. -/
theorem mem_GrL_fAdd0 {A κ : Type*} (c : A → ℝ) (t : Lexp.Term (A ⊕ κ))
    (ζ : κ ⊕ Fin 1 → ℝ) (u : Fin 2 → ℝ) :
    (Sum.elim ζ u) ∘ fAdd0 κ ∈ GrL c t ↔ u 0 = t.realize (Sum.elim c (ζ ∘ Sum.inl)) := by
  have h1 : ((Sum.elim ζ u) ∘ fAdd0 κ) (Sum.inr (0 : Fin 1)) = u 0 := by
    rw [Function.comp_apply]; exact eval_fAdd0_val ζ u
  have h2 := comp_fAdd0_inl ζ u
  show ((Sum.elim ζ u) ∘ fAdd0 κ) (Sum.inr (0 : Fin 1)) =
      t.realize (Sum.elim c (((Sum.elim ζ u) ∘ fAdd0 κ) ∘ Sum.inl)) ↔
    u 0 = t.realize (Sum.elim c (ζ ∘ Sum.inl))
  rw [h1, h2]

/-- Membership of a pulled-back point in the graph of `t`, for the second auxiliary map. -/
theorem mem_GrL_fAdd1 {A κ : Type*} (c : A → ℝ) (t : Lexp.Term (A ⊕ κ))
    (ζ : κ ⊕ Fin 1 → ℝ) (u : Fin 2 → ℝ) :
    (Sum.elim ζ u) ∘ fAdd1 κ ∈ GrL c t ↔ u 1 = t.realize (Sum.elim c (ζ ∘ Sum.inl)) := by
  have h1 : ((Sum.elim ζ u) ∘ fAdd1 κ) (Sum.inr (0 : Fin 1)) = u 1 := by
    rw [Function.comp_apply]; exact eval_fAdd1_val ζ u
  have h2 := comp_fAdd1_inl ζ u
  show ((Sum.elim ζ u) ∘ fAdd1 κ) (Sum.inr (0 : Fin 1)) =
      t.realize (Sum.elim c (((Sum.elim ζ u) ∘ fAdd1 κ) ∘ Sum.inl)) ↔
    u 1 = t.realize (Sum.elim c (ζ ∘ Sum.inl))
  rw [h1, h2]

/-- Membership of a pulled-back point in the graph of `t`, for the unique auxiliary map. -/
theorem mem_GrL_fUn {A κ : Type*} (c : A → ℝ) (t : Lexp.Term (A ⊕ κ))
    (ζ : κ ⊕ Fin 1 → ℝ) (u : Fin 1 → ℝ) :
    (Sum.elim ζ u) ∘ fUn κ ∈ GrL c t ↔ u 0 = t.realize (Sum.elim c (ζ ∘ Sum.inl)) := by
  have h1 : ((Sum.elim ζ u) ∘ fUn κ) (Sum.inr (0 : Fin 1)) = u 0 := by
    rw [Function.comp_apply]; exact eval_fUn_val ζ u
  have h2 := comp_fUn_inl ζ u
  show ((Sum.elim ζ u) ∘ fUn κ) (Sum.inr (0 : Fin 1)) =
      t.realize (Sum.elim c (((Sum.elim ζ u) ∘ fUn κ) ∘ Sum.inl)) ↔
    u 0 = t.realize (Sum.elim c (ζ ∘ Sum.inl))
  rw [h1, h2]

/-! ## 5. The induction step for the function symbols -/

theorem GrL_add {A κ : Type*} (c : A → ℝ) (ts : Fin 2 → Lexp.Term (A ⊕ κ))
    (h₀ : ExpExistI (GrL c (ts 0))) (h₁ : ExpExistI (GrL c (ts 1))) :
    ExpExistI (GrL c (Term.func addSymL ts)) := by
  have hC : ExpExistI {z : (κ ⊕ Fin 1) ⊕ Fin 2 → ℝ |
      z (Sum.inl (Sum.inr (0 : Fin 1))) = z (Sum.inr (0 : Fin 2)) + z (Sum.inr (1 : Fin 2))} := by
    refine (expExistI_evalZero (κ := (κ ⊕ Fin 1) ⊕ Fin 2)
      (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) -
        MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 2))) -
        MvPolynomial.X (Sum.inl (Sum.inr (1 : Fin 2))))).of_eq ?_
    ext z
    change (expEval z
        (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) -
          MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 2))) -
          MvPolynomial.X (Sum.inl (Sum.inr (1 : Fin 2))))) = 0 ↔
      z (Sum.inl (Sum.inr (0 : Fin 1))) = z (Sum.inr (0 : Fin 2)) + z (Sum.inr (1 : Fin 2))
    constructor <;> intro h <;>
      · simp only [expEval_sub, expEval_X_inl] at h ⊢
        linarith
  have hY : ExpExistI ({z : (κ ⊕ Fin 1) ⊕ Fin 2 → ℝ | z ∘ fAdd0 κ ∈ GrL c (ts 0)} ∩
      {z | z ∘ fAdd1 κ ∈ GrL c (ts 1)} ∩
      {z | z (Sum.inl (Sum.inr (0 : Fin 1))) =
        z (Sum.inr (0 : Fin 2)) + z (Sum.inr (1 : Fin 2))}) :=
    ExpExistI.inter (ExpExistI.inter
      (ExpExistI.pullback (fAdd0 κ) h₀) (ExpExistI.pullback (fAdd1 κ) h₁)) hC
  refine ExpExistI.of_eq ?_ (ExpExistI.existsBlock (μ := Fin 2) hY)
  ext ζ
  constructor
  · rintro ⟨u, ⟨⟨h0, h1⟩, hc⟩⟩
    have e0 := (mem_GrL_fAdd0 c (ts 0) ζ u).mp h0
    have e1 := (mem_GrL_fAdd1 c (ts 1) ζ u).mp h1
    simp only [GrL, Set.mem_ofPred_eq, Term.realize_func, funMap_addL]
    rw [← e0, ← e1]
    simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr] at hc
    exact hc
  · intro hz
    have hz' : ζ (Sum.inr (0 : Fin 1)) =
        (ts 0).realize (Sum.elim c (ζ ∘ Sum.inl)) +
          (ts 1).realize (Sum.elim c (ζ ∘ Sum.inl)) := by
      simpa only [GrL, Set.mem_ofPred_eq, Term.realize_func, funMap_addL] using hz
    exact ⟨![(ts 0).realize (Sum.elim c (ζ ∘ Sum.inl)),
        (ts 1).realize (Sum.elim c (ζ ∘ Sum.inl))],
      ⟨⟨(mem_GrL_fAdd0 c (ts 0) ζ _).mpr (by simp),
        (mem_GrL_fAdd1 c (ts 1) ζ _).mpr (by simp)⟩,
        by simpa [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
          Matrix.cons_val_one] using hz'⟩⟩

theorem GrL_mul {A κ : Type*} (c : A → ℝ) (ts : Fin 2 → Lexp.Term (A ⊕ κ))
    (h₀ : ExpExistI (GrL c (ts 0))) (h₁ : ExpExistI (GrL c (ts 1))) :
    ExpExistI (GrL c (Term.func mulSymL ts)) := by
  have hC : ExpExistI {z : (κ ⊕ Fin 1) ⊕ Fin 2 → ℝ |
      z (Sum.inl (Sum.inr (0 : Fin 1))) = z (Sum.inr (0 : Fin 2)) * z (Sum.inr (1 : Fin 2))} := by
    refine (expExistI_evalZero (κ := (κ ⊕ Fin 1) ⊕ Fin 2)
      (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) -
        MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 2))) *
        MvPolynomial.X (Sum.inl (Sum.inr (1 : Fin 2))))).of_eq ?_
    ext z
    change (expEval z
        (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) -
          MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 2))) *
          MvPolynomial.X (Sum.inl (Sum.inr (1 : Fin 2))))) = 0 ↔
      z (Sum.inl (Sum.inr (0 : Fin 1))) = z (Sum.inr (0 : Fin 2)) * z (Sum.inr (1 : Fin 2))
    constructor <;> intro h <;>
      · simp only [expEval_sub, expEval_mul, expEval_X_inl] at h ⊢
        linarith
  have hY : ExpExistI ({z : (κ ⊕ Fin 1) ⊕ Fin 2 → ℝ | z ∘ fAdd0 κ ∈ GrL c (ts 0)} ∩
      {z | z ∘ fAdd1 κ ∈ GrL c (ts 1)} ∩
      {z | z (Sum.inl (Sum.inr (0 : Fin 1))) =
        z (Sum.inr (0 : Fin 2)) * z (Sum.inr (1 : Fin 2))}) :=
    ExpExistI.inter (ExpExistI.inter
      (ExpExistI.pullback (fAdd0 κ) h₀) (ExpExistI.pullback (fAdd1 κ) h₁)) hC
  refine ExpExistI.of_eq ?_ (ExpExistI.existsBlock (μ := Fin 2) hY)
  ext ζ
  constructor
  · rintro ⟨u, ⟨⟨h0, h1⟩, hc⟩⟩
    have e0 := (mem_GrL_fAdd0 c (ts 0) ζ u).mp h0
    have e1 := (mem_GrL_fAdd1 c (ts 1) ζ u).mp h1
    simp only [GrL, Set.mem_ofPred_eq, Term.realize_func, funMap_mulL]
    rw [← e0, ← e1]
    simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr] at hc
    exact hc
  · intro hz
    have hz' : ζ (Sum.inr (0 : Fin 1)) =
        (ts 0).realize (Sum.elim c (ζ ∘ Sum.inl)) *
          (ts 1).realize (Sum.elim c (ζ ∘ Sum.inl)) := by
      simpa only [GrL, Set.mem_ofPred_eq, Term.realize_func, funMap_mulL] using hz
    exact ⟨![(ts 0).realize (Sum.elim c (ζ ∘ Sum.inl)),
        (ts 1).realize (Sum.elim c (ζ ∘ Sum.inl))],
      ⟨⟨(mem_GrL_fAdd0 c (ts 0) ζ _).mpr (by simp),
        (mem_GrL_fAdd1 c (ts 1) ζ _).mpr (by simp)⟩,
        by simpa [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
          Matrix.cons_val_one] using hz'⟩⟩

theorem GrL_neg {A κ : Type*} (c : A → ℝ) (ts : Fin 1 → Lexp.Term (A ⊕ κ))
    (h : ExpExistI (GrL c (ts 0))) :
    ExpExistI (GrL c (Term.func negSymL ts)) := by
  have hC : ExpExistI {z : (κ ⊕ Fin 1) ⊕ Fin 1 → ℝ |
      z (Sum.inl (Sum.inr (0 : Fin 1))) = - z (Sum.inr (0 : Fin 1))} := by
    refine (expExistI_evalZero (κ := (κ ⊕ Fin 1) ⊕ Fin 1)
      (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) +
        MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))))).of_eq ?_
    ext z
    change (expEval z
        (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) +
          MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))))) = 0 ↔
      z (Sum.inl (Sum.inr (0 : Fin 1))) = - z (Sum.inr (0 : Fin 1))
    constructor <;> intro h <;>
      · simp only [expEval_add, expEval_X_inl] at h ⊢
        linarith
  have hY : ExpExistI ({z : (κ ⊕ Fin 1) ⊕ Fin 1 → ℝ | z ∘ fUn κ ∈ GrL c (ts 0)} ∩
      {z | z (Sum.inl (Sum.inr (0 : Fin 1))) = - z (Sum.inr (0 : Fin 1))}) :=
    ExpExistI.inter (ExpExistI.pullback (fUn κ) h) hC
  refine ExpExistI.of_eq ?_ (ExpExistI.existsBlock (μ := Fin 1) hY)
  ext ζ
  constructor
  · rintro ⟨u, ⟨h0, hc⟩⟩
    have e0 := (mem_GrL_fUn c (ts 0) ζ u).mp h0
    simp only [GrL, Set.mem_ofPred_eq, Term.realize_func, funMap_negL]
    rw [← e0]
    simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr] at hc
    exact hc
  · intro hz
    have hz' : ζ (Sum.inr (0 : Fin 1)) =
        - (ts 0).realize (Sum.elim c (ζ ∘ Sum.inl)) := by
      simpa only [GrL, Set.mem_ofPred_eq, Term.realize_func, funMap_negL] using hz
    exact ⟨![(ts 0).realize (Sum.elim c (ζ ∘ Sum.inl))],
      ⟨(mem_GrL_fUn c (ts 0) ζ _).mpr (by simp),
        by simpa [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_fin_one]
          using hz'⟩⟩

theorem GrL_exp {A κ : Type*} (c : A → ℝ) (ts : Fin 1 → Lexp.Term (A ⊕ κ))
    (h : ExpExistI (GrL c (ts 0))) :
    ExpExistI (GrL c (Term.func expSymL ts)) := by
  have hC : ExpExistI {z : (κ ⊕ Fin 1) ⊕ Fin 1 → ℝ |
      z (Sum.inl (Sum.inr (0 : Fin 1))) = Real.exp (z (Sum.inr (0 : Fin 1)))} := by
    refine (expExistI_evalZero (κ := (κ ⊕ Fin 1) ⊕ Fin 1)
      (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) -
        MvPolynomial.X (Sum.inr (Sum.inr (0 : Fin 1))))).of_eq ?_
    ext z
    change (expEval z
        (MvPolynomial.X (Sum.inl (Sum.inl (Sum.inr (0 : Fin 1)))) -
          MvPolynomial.X (Sum.inr (Sum.inr (0 : Fin 1))))) = 0 ↔
      z (Sum.inl (Sum.inr (0 : Fin 1))) = Real.exp (z (Sum.inr (0 : Fin 1)))
    constructor <;> intro h <;>
      · simp only [expEval_sub, expEval_X_inl, expEval_X_inr] at h ⊢
        linarith
  have hY : ExpExistI ({z : (κ ⊕ Fin 1) ⊕ Fin 1 → ℝ | z ∘ fUn κ ∈ GrL c (ts 0)} ∩
      {z | z (Sum.inl (Sum.inr (0 : Fin 1))) = Real.exp (z (Sum.inr (0 : Fin 1)))}) :=
    ExpExistI.inter (ExpExistI.pullback (fUn κ) h) hC
  refine ExpExistI.of_eq ?_ (ExpExistI.existsBlock (μ := Fin 1) hY)
  ext ζ
  constructor
  · rintro ⟨u, ⟨h0, hc⟩⟩
    have e0 := (mem_GrL_fUn c (ts 0) ζ u).mp h0
    simp only [GrL, Set.mem_ofPred_eq, Term.realize_func, funMap_expL]
    rw [← e0]
    simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr] at hc
    exact hc
  · intro hz
    have hz' : ζ (Sum.inr (0 : Fin 1)) =
        Real.exp ((ts 0).realize (Sum.elim c (ζ ∘ Sum.inl))) := by
      simpa only [GrL, Set.mem_ofPred_eq, Term.realize_func, funMap_expL] using hz
    exact ⟨![(ts 0).realize (Sum.elim c (ζ ∘ Sum.inl))],
      ⟨(mem_GrL_fUn c (ts 0) ζ _).mpr (by simp),
        by simpa [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_fin_one]
          using hz'⟩⟩

/-! ## 6. The base cases -/

theorem GrL_var_inl {A κ : Type*} (c : A → ℝ) (a : A) :
    ExpExistI (GrL c (Term.var (Sum.inl a) : Lexp.Term (A ⊕ κ))) := by
  refine (expExistI_evalZero (κ := κ ⊕ Fin 1)
    (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) - MvPolynomial.C (c a))).of_eq ?_
  ext u
  change (expEval u
      (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) - MvPolynomial.C (c a))) = 0 ↔
    u (Sum.inr (0 : Fin 1)) = c a
  constructor <;> intro h <;>
    · simp only [expEval_sub, expEval_X_inl, expEval_C] at h ⊢
      linarith

theorem GrL_var_inr {A κ : Type*} (c : A → ℝ) (i : κ) :
    ExpExistI (GrL c (Term.var (Sum.inr i) : Lexp.Term (A ⊕ κ))) := by
  refine (expExistI_evalZero (κ := κ ⊕ Fin 1)
    (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) -
      MvPolynomial.X (Sum.inl (Sum.inl i)))).of_eq ?_
  ext u
  change (expEval u
      (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) -
        MvPolynomial.X (Sum.inl (Sum.inl i)))) = 0 ↔
    u (Sum.inr (0 : Fin 1)) = u (Sum.inl i)
  constructor <;> intro h <;>
    · simp only [expEval_sub, expEval_X_inl] at h ⊢
      linarith

theorem GrL_zero {A κ : Type*} (c : A → ℝ) (ts : Fin 0 → Lexp.Term (A ⊕ κ)) :
    ExpExistI (GrL c (Term.func zeroSymL ts)) := by
  refine (expExistI_evalZero (κ := κ ⊕ Fin 1)
    (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))))).of_eq ?_
  ext u
  change (expEval u
      (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))))) = 0 ↔
    u (Sum.inr (0 : Fin 1)) = 0
  constructor <;> intro h <;>
    · simpa only [expEval_X_inl] using h

theorem GrL_one {A κ : Type*} (c : A → ℝ) (ts : Fin 0 → Lexp.Term (A ⊕ κ)) :
    ExpExistI (GrL c (Term.func oneSymL ts)) := by
  refine (expExistI_evalZero (κ := κ ⊕ Fin 1)
    (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) - 1)).of_eq ?_
  ext u
  change (expEval u
      (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) - 1)) = 0 ↔
    u (Sum.inr (0 : Fin 1)) = 1
  constructor <;> intro h <;>
    · simp only [expEval_sub, expEval_X_inl, expEval_one] at h ⊢
      linarith

/-! ## 7. Main graph lemma -/

theorem GrL_expExist {A κ : Type*} (c : A → ℝ) :
    ∀ t : Lexp.Term (A ⊕ κ), ExpExistI (GrL c t) := by
  intro t
  induction t with
  | var x =>
      rcases x with a | i
      · exact GrL_var_inl c a
      · exact GrL_var_inr c i
  | func f ts ih =>
      rcases f with rf | ex
      · rcases rf with _ | _ | _ | _ | _
        · exact GrL_add c ts (ih 0) (ih 1)
        · exact GrL_mul c ts (ih 0) (ih 1)
        · exact GrL_neg c ts (ih 0)
        · exact GrL_zero c ts
        · exact GrL_one c ts
      · cases ex
        exact GrL_exp c ts (ih 0)

/-- **Graphs of `LEc`-terms are existentially definable.** -/
theorem Gr_expExist {κ : Type*} (t : LEc.Term κ) : ExpExistI (Gr t) := by
  have h := GrL_expExist (A := ℝ) (κ := κ) (fun a : ℝ => (Lexp.con a : ℝ))
    (Term.constantsToVars t)
  refine h.of_eq ?_
  ext u
  change u (Sum.inr (0 : Fin 1)) =
      (Term.constantsToVars t).realize (Sum.elim (fun a : ℝ => (Lexp.con a : ℝ))
        (u ∘ Sum.inl)) ↔
    u (Sum.inr (0 : Fin 1)) = t.realize (u ∘ Sum.inl)
  simp only [Term.realize_constantsToVars]

/-! ## 8. Atoms: equations and inequations of terms -/

/-- The set where two `LEc`-terms agree is `ExpExistI`. -/
theorem expExistI_eq_term {κ : Type*} (t₁ t₂ : LEc.Term κ) :
    ExpExistI {z : κ → ℝ | t₁.realize z = t₂.realize z} := by
  have h : ExpExistI (Gr t₁ ∩ Gr t₂) := ExpExistI.inter (Gr_expExist t₁) (Gr_expExist t₂)
  refine (ExpExistI.projLast h).of_eq ?_
  ext z
  constructor
  · rintro ⟨a, h1, h2⟩
    have h1' : a = t₁.realize z := by
      simpa [Gr, Set.mem_ofPred_eq, sumElim_comp_inl, Sum.elim_inr] using h1
    have h2' : a = t₂.realize z := by
      simpa [Gr, Set.mem_ofPred_eq, sumElim_comp_inl, Sum.elim_inr] using h2
    exact h1'.symm.trans h2'
  · intro h
    exact ⟨t₁.realize z,
      by simp [Gr, Set.mem_ofPred_eq, sumElim_comp_inl, Sum.elim_inr],
      by simpa [Gr, Set.mem_ofPred_eq, sumElim_comp_inl, Sum.elim_inr] using h⟩

/-- The set where two `LEc`-terms differ is `ExpExistI` (over `ℝ`, `x ≠ y ↔ ∃ z, (x-y) z = 1`). -/
theorem expExistI_ne_term {κ : Type*} (t₁ t₂ : LEc.Term κ) :
    ExpExistI {z : κ → ℝ | t₁.realize z ≠ t₂.realize z} := by
  have hone : ExpExistI {u : (κ ⊕ Fin 1) ⊕ Fin 1 → ℝ | u (Sum.inr (0 : Fin 1)) = 1} := by
    refine (expExistI_evalZero (κ := (κ ⊕ Fin 1) ⊕ Fin 1)
      (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) - 1)).of_eq ?_
    ext u
    change (expEval u
        (MvPolynomial.X (Sum.inl (Sum.inr (0 : Fin 1))) - 1)) = 0 ↔
      u (Sum.inr (0 : Fin 1)) = 1
    constructor <;> intro h <;>
      · simp only [expEval_X_inl, expEval_sub, expEval_one] at h ⊢
        linarith
  have hZ : ExpExistI {u : κ ⊕ Fin 1 → ℝ | (subMulTerm t₁ t₂).realize u = 1} := by
    refine (ExpExistI.projLast (ExpExistI.inter (Gr_expExist (subMulTerm t₁ t₂)) hone)).of_eq ?_
    ext u
    constructor
    · rintro ⟨a, h1, h2⟩
      have h1' : a = (subMulTerm t₁ t₂).realize u := by
        simpa [Gr, Set.mem_ofPred_eq, sumElim_comp_inl, Sum.elim_inr] using h1
      have h2' : a = 1 := by simpa [Set.mem_ofPred_eq, Sum.elim_inr] using h2
      rw [Set.mem_ofPred_eq, ← h1', h2']
    · intro h
      exact ⟨1, by simpa [Gr, Set.mem_ofPred_eq, sumElim_comp_inl, Sum.elim_inr] using h.symm,
        by simp [Set.mem_ofPred_eq, Sum.elim_inr]⟩
  refine (ExpExistI.projLast hZ).of_eq ?_
  ext z
  constructor
  · rintro ⟨a, ha⟩
    simp only [Set.mem_ofPred_eq, realize_subMulTerm, sumElim_comp_inl, Sum.elim_inr] at ha
    intro h
    rw [h, sub_self, zero_mul] at ha
    exact one_ne_zero ha.symm
  · intro hne
    refine ⟨(t₁.realize z - t₂.realize z)⁻¹, ?_⟩
    simp only [Set.mem_ofPred_eq, realize_subMulTerm, sumElim_comp_inl, Sum.elim_inr]
    exact mul_inv_cancel₀ (sub_ne_zero.mpr hne)

end Work.WilC6.Flatten
