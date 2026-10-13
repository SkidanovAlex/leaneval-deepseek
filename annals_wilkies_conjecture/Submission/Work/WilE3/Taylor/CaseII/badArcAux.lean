import Mathlib
import Submission.Work.WilE3.Taylor.CaseII.Defs
import Submission.Work.WilE3.Taylor.CaseII.PertShear
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.Taylor.Grad.badSeqOnPolarSet
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Polar.Basic
import Submission.Work.WilE3.Taylor.Polar.Lagrange
import Submission.Work.Taylor.Grad.grad_eaEval

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **auxiliary vocabulary for the fixed-ball
  bad-arc lemma** `Work.WilE3.Taylor.CaseII.badArc_fixedBall` (node T3 of
  `cbc/wilkies_e3_caseII.md` §3): the evaluation lemmas for the perturbed polar minors, the
  witness predicates (interior / boundary / degenerate), the two basic semianalytic sets used in
  the curve selection and their analyticity, and the finite pigeonhole.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-! ## §1. Elementary helpers -/

/-- The finite pigeonhole: a frequently satisfied predicate on a finite index type is frequently
satisfied for one fixed index. -/
lemma frequently_exists_of_finite {α β : Type*} [Finite α] {l : Filter β} {p : β → α → Prop}
    (h : ∃ᶠ b in l, ∃ a, p b a) : ∃ a, ∃ᶠ b in l, p b a := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ᶠ b in l, ∀ a, ¬ p b a := eventually_all.2 hcon
  obtain ⟨b, hb⟩ := (h.and_eventually hall).exists
  obtain ⟨a, ha⟩ := hb.1
  exact hb.2 a ha

/-- The evaluation of `pertMinor3`. -/
lemma eaEval_pertMinor3 (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ) (i₀ j₀ l : Fin k)
    (x : Fin k → ℝ) :
    eaEval c (pertMinor3 c Φ v y i₀ j₀ l) x =
      (eaEval c (eaD c i₀ (sqGrad c Φ)) x + v i₀ * eaEval c (sqGrad c Φ) x)
        * (eaEval c (eaD c j₀ Φ) x * (x l - y l) - eaEval c (eaD c l Φ) x * (x j₀ - y j₀))
      - (eaEval c (eaD c j₀ (sqGrad c Φ)) x + v j₀ * eaEval c (sqGrad c Φ) x)
        * (eaEval c (eaD c i₀ Φ) x * (x l - y l) - eaEval c (eaD c l Φ) x * (x i₀ - y i₀))
      + (eaEval c (eaD c l (sqGrad c Φ)) x + v l * eaEval c (sqGrad c Φ) x)
        * (eaEval c (eaD c i₀ Φ) x * (x j₀ - y j₀) - eaEval c (eaD c j₀ Φ) x * (x i₀ - y i₀)) := by
  simp only [pertMinor3, eaEval, map_sub, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Sum.elim_inl]

/-- The evaluation of `sphereP`. -/
lemma eaEval_sphereP (c : EAChain k r) (y : Fin k → ℝ) (δ2 : ℝ) (x : Fin k → ℝ) :
    eaEval c (sphereP y δ2) x = (∑ i : Fin k, (x i - y i) ^ 2) - δ2 := by
  simp only [sphereP, eaEval, map_sub, map_sum, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Sum.elim_inl]

/-- A vanishing sum of squares vanishes termwise. -/
lemma eq_zero_of_sum_sq_eq_zero {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (h : ∑ i, (f i) ^ 2 = 0) : ∀ i, f i = 0 := by
  have h' := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun i => (f i) ^ 2) (fun i _ => sq_nonneg _)).mp h
  exact fun i => sq_eq_zero_iff.mp (h' i (Finset.mem_univ i))

/-- The perturbed polar minor vanishes as soon as the gradient of the perturbed squared gradient
norm is a multiple of `∇Φ`. -/
lemma pertMinor_eq_zero_of_lagrange (c : EAChain k r) (Φ : EAPoly k r) (v : Fin k → ℝ)
    (i₀ : Fin k) (x : Fin k → ℝ) (cc : ℝ)
    (h : ∀ i : Fin k, eaEval c (eaD c i (sqGrad c Φ)) x + v i * eaEval c (sqGrad c Φ) x
      = cc * eaEval c (eaD c i Φ) x) :
    ∀ i : Fin k, eaEval c (pertMinor c Φ v i₀ i) x = 0 := by
  intro i
  rw [eaEval_pertMinor, h i, h i₀]
  ring

/-- `pertMinor3` vanishes when two of its three indices coincide. -/
lemma eaEval_pertMinor3_self (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ)
    (i₀ j₀ : Fin k) (x : Fin k → ℝ) :
    eaEval c (pertMinor3 c Φ v y i₀ j₀ i₀) x = 0 ∧
      eaEval c (pertMinor3 c Φ v y i₀ j₀ j₀) x = 0 := by
  constructor <;> rw [eaEval_pertMinor3] <;> ring

/-- The perturbed radial minor vanishes as soon as the gradient of the perturbed squared gradient
norm lies in the span of `∇Φ` and `x - y`. -/
lemma pertMinor3_eq_zero_of_combo (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ)
    (i₀ j₀ : Fin k) (x : Fin k → ℝ) (a b : ℝ)
    (h : ∀ i : Fin k, eaEval c (eaD c i (sqGrad c Φ)) x + v i * eaEval c (sqGrad c Φ) x
      = a * eaEval c (eaD c i Φ) x + b * (x i - y i)) :
    ∀ l : Fin k, eaEval c (pertMinor3 c Φ v y i₀ j₀ l) x = 0 := by
  intro l
  rw [eaEval_pertMinor3, h i₀, h j₀, h l]
  ring

/-- The coordinate gradient of the squared gradient norm, in `eaEval` form. -/
lemma grad_sqGradSumSq (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) (i : Fin k) :
    Work.WilE3.Taylor.grad
        (fun z : Fin k → ℝ => ∑ l : Fin k, (eaEval c (eaD c l Q) z) ^ 2) x i
      = eaEval c (eaD c i (sqGrad c Q)) x := by
  have hfun : (fun z : Fin k → ℝ => ∑ l : Fin k, (eaEval c (eaD c l Q) z) ^ 2)
      = fun z : Fin k → ℝ => eaEval c (sqGrad c Q) z := by
    funext z; rw [eaEval_sqGrad]
  rw [hfun]
  exact Work.Taylor.Grad.grad_eaEval c (sqGrad c Q) x i

/-- The coordinate gradient of the squared gradient norm of `eaEval c Φ`, in `eaEval` form. -/
lemma grad_grad_sumSq (c : EAChain k r) (Φ : EAPoly k r) (x : Fin k → ℝ) (i : Fin k) :
    Work.WilE3.Taylor.grad
        (fun w : Fin k → ℝ =>
          ∑ l : Fin k, (Work.WilE3.Taylor.grad (fun w' : Fin k → ℝ => eaEval c Φ w') w l) ^ 2)
        x i
      = eaEval c (eaD c i (sqGrad c Φ)) x := by
  have hfun : (fun w : Fin k → ℝ =>
        ∑ l : Fin k, (Work.WilE3.Taylor.grad (fun w' : Fin k → ℝ => eaEval c Φ w') w l) ^ 2)
      = fun w : Fin k → ℝ => ∑ l : Fin k, (eaEval c (eaD c l Φ) w) ^ 2 := by
    funext w
    exact Finset.sum_congr rfl fun l _ => by rw [Work.Taylor.Grad.grad_eaEval]
  rw [hfun, grad_sqGradSumSq]

/-- `∑ₗ (∂ₗΦ)²` in the `grad` vocabulary. -/
lemma sum_grad_sq_eq (c : EAChain k r) (Φ : EAPoly k r) (x : Fin k → ℝ) :
    (∑ l : Fin k, (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Φ w) x l) ^ 2)
      = eaEval c (sqGrad c Φ) x := by
  have h : (∑ l : Fin k, (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Φ w) x l) ^ 2)
      = ∑ l : Fin k, (eaEval c (eaD c l Φ) x) ^ 2 :=
    Finset.sum_congr rfl fun l _ => by rw [Work.Taylor.Grad.grad_eaEval]
  rw [h, eaEval_sqGrad]

/-- Analyticity of `z ↦ ∑ₗ (∂ₗΦ(z))²`. -/
lemma analyticAt_sqGradEval (c : EAChain k r) (Φ : EAPoly k r) (x : Fin k → ℝ) :
    AnalyticAt ℝ (fun z : Fin k → ℝ => ∑ l : Fin k, (eaEval c (eaD c l Φ) z) ^ 2) x := by
  refine (Finset.analyticAt_sum (Finset.univ : Finset (Fin k))
    (fun l _ => (eaEval_analytic c (eaD c l Φ) x).pow 2)).congr ?_
  filter_upwards with z
  simp [Finset.sum_apply]

/-- Analyticity of `z ↦ ∑ᵢ (zᵢ - yᵢ)²`. -/
lemma analyticAt_sphereSq (y : Fin k → ℝ) (x : Fin k → ℝ) :
    AnalyticAt ℝ (fun z : Fin k → ℝ => ∑ i : Fin k, (z i - y i) ^ 2) x := by
  refine (Finset.analyticAt_sum (Finset.univ : Finset (Fin k))
    (fun i _ => (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).analyticAt x).sub
      (analyticAt_const (v := y i))).pow 2)).congr ?_
  filter_upwards with z
  simp [Finset.sum_apply, ContinuousLinearMap.proj_apply]

/-- Analyticity of the linear form `z ↦ ∑ᵢ vᵢ (zᵢ - yᵢ)`. -/
lemma analyticAt_linForm (v y : Fin k → ℝ) (x : Fin k → ℝ) :
    AnalyticAt ℝ (fun z : Fin k → ℝ => ∑ i : Fin k, v i * (z i - y i)) x := by
  refine (Finset.analyticAt_sum (Finset.univ : Finset (Fin k))
    (fun i _ => (analyticAt_const (v := v i)).mul
      (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).analyticAt x).sub
        (analyticAt_const (v := y i))))).congr ?_
  filter_upwards with z
  simp [Finset.sum_apply, ContinuousLinearMap.proj_apply]

/-! ## §2. The witness predicates -/

/-- The interior-type witness with pivot `i₀`: bad, `∂_{i₀}Φ ≠ 0`, and the perturbed polar minors
with pivot `i₀` vanish. -/
def IntWit (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ) (Cs : ℝ) (p q : ℕ) (i₀ : Fin k)
    (x : Fin k → ℝ) : Prop :=
  0 < eaEval c Φ x ∧
    (∑ l : Fin k, (eaEval c (eaD c l Φ) x) ^ 2) ^ q < Cs * (eaEval c Φ x) ^ (2 * p) ∧
    eaEval c (eaD c i₀ Φ) x ≠ 0 ∧
    ∀ i : Fin k, i ≠ i₀ → eaEval c (pertMinor c Φ v i₀ i) x = 0

/-- The boundary-type witness with pivots `i₀ ≠ j₀`: bad, on the sphere of radius `δ` about `y`,
with a nonzero `2×2` minor of `(∇Φ, x - y)` and vanishing `3×3` minors of `(∇G + G•v, ∇Φ, x - y)`. -/
def BndWit (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ) (Cs δ : ℝ) (p q : ℕ)
    (i₀ j₀ : Fin k) (x : Fin k → ℝ) : Prop :=
  0 < eaEval c Φ x ∧
    (∑ l : Fin k, (eaEval c (eaD c l Φ) x) ^ 2) ^ q < Cs * (eaEval c Φ x) ^ (2 * p) ∧
    (∑ i : Fin k, (x i - y i) ^ 2) = δ ^ 2 ∧ i₀ ≠ j₀ ∧
    eaEval c (eaD c i₀ Φ) x * (x j₀ - y j₀)
        - eaEval c (eaD c j₀ Φ) x * (x i₀ - y i₀) ≠ 0 ∧
    ∀ l : Fin k, l ≠ i₀ → l ≠ j₀ → eaEval c (pertMinor3 c Φ v y i₀ j₀ l) x = 0

/-- The two degenerate alternatives at a minimiser, excluded for all but finitely many `n`. -/
def DegWit (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (δ : ℝ) (x : Fin k → ℝ) : Prop :=
  (∀ l : Fin k, eaEval c (eaD c l Φ) x = 0) ∨
    ((∑ i : Fin k, (x i - y i) ^ 2) = δ ^ 2 ∧
      ∀ i j : Fin k, eaEval c (eaD c i Φ) x * (x j - y j)
        - eaEval c (eaD c j Φ) x * (x i - y i) = 0)

/-- The case index of the pigeonhole. -/
abbrev CIdx (k : ℕ) := (Fin k) ⊕ {pp : Fin k × Fin k // pp.1 ≠ pp.2}

/-- The witness set of a case index. -/
def CSet (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ) (Cs δ : ℝ) (p q : ℕ) :
    CIdx k → Set (Fin k → ℝ) := fun a =>
  match a with
  | Sum.inl i₀ => {x | IntWit c Φ v y Cs p q i₀ x}
  | Sum.inr pp => {x | BndWit c Φ v y Cs δ p q pp.1.1 pp.1.2 x}

/-- The `2×2` minor of `(∇Φ, x - y)` at `x`. -/
def muP (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k) (x : Fin k → ℝ) : ℝ :=
  eaEval c (eaD c i₀ Φ) x * (x j₀ - y j₀) - eaEval c (eaD c j₀ Φ) x * (x i₀ - y i₀)

lemma muP_self (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i : Fin k)
    (x : Fin k → ℝ) : muP c Φ y i i x = 0 := by
  simp only [muP]; ring

lemma continuous_muP (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i₀ j₀ : Fin k) :
    Continuous (muP c Φ y i₀ j₀) := by
  have h1 : Continuous (fun x : Fin k → ℝ => eaEval c (eaD c i₀ Φ) x) :=
    continuous_iff_continuousAt.mpr fun x => (eaEval_analytic c _ x).continuousAt
  have h2 : Continuous (fun x : Fin k → ℝ => eaEval c (eaD c j₀ Φ) x) :=
    continuous_iff_continuousAt.mpr fun x => (eaEval_analytic c _ x).continuousAt
  have h3 : Continuous (fun x : Fin k → ℝ => x j₀ - y j₀) :=
    (continuous_apply j₀).sub continuous_const
  have h4 : Continuous (fun x : Fin k → ℝ => x i₀ - y i₀) :=
    (continuous_apply i₀).sub continuous_const
  exact (h1.mul h3).sub (h2.mul h4)

/-! ## §2b. The basic semianalytic sets used in the curve selection -/

/-- The sum of squares of the perturbed polar minors with pivot `i₀`. -/
def FInt (c : EAChain k r) (Φ : EAPoly k r) (v : Fin k → ℝ) (i₀ : Fin k)
    (x : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, (eaEval c (pertMinor c Φ v i₀ i) x) ^ 2

/-- The inequalities of the interior case. -/
def GInt (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) (Cs : ℝ) (p q : ℕ) :
    Fin 3 → (Fin k → ℝ) → ℝ :=
  ![fun z => eaEval c Φ z,
    fun z => Cs * (eaEval c Φ z) ^ (2 * p)
      - (∑ l : Fin k, (eaEval c (eaD c l Φ) z) ^ 2) ^ q,
    fun z => (eaEval c (eaD c i₀ Φ) z) ^ 2]

/-- The equation of the boundary case: the sphere and the `3×3` minors. -/
def FBnd (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ) (δ2 : ℝ) (i₀ j₀ : Fin k)
    (x : Fin k → ℝ) : ℝ :=
  ((∑ i : Fin k, (x i - y i) ^ 2) - δ2) ^ 2
    + ∑ l : Fin k, (eaEval c (pertMinor3 c Φ v y i₀ j₀ l) x) ^ 2

/-- The inequalities of the boundary case. -/
def GBnd (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (Cs δ2 : ℝ) (p q : ℕ)
    (i₀ j₀ : Fin k) : Fin 3 → (Fin k → ℝ) → ℝ :=
  ![fun z => eaEval c Φ z,
    fun z => Cs * (eaEval c Φ z) ^ (2 * p)
      - (∑ l : Fin k, (eaEval c (eaD c l Φ) z) ^ 2) ^ q,
    fun z => (muP c Φ y i₀ j₀ z) ^ 2]

lemma GInt_zero (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) (Cs : ℝ) (p q : ℕ) :
    GInt c Φ i₀ Cs p q 0 = (fun z : Fin k → ℝ => eaEval c Φ z) := by
  simp [GInt]

lemma GInt_one (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) (Cs : ℝ) (p q : ℕ) :
    GInt c Φ i₀ Cs p q 1 = (fun z : Fin k → ℝ => Cs * (eaEval c Φ z) ^ (2 * p)
      - (∑ l : Fin k, (eaEval c (eaD c l Φ) z) ^ 2) ^ q) := by
  simp [GInt]

lemma GInt_two (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) (Cs : ℝ) (p q : ℕ) :
    GInt c Φ i₀ Cs p q 2 = (fun z : Fin k → ℝ => (eaEval c (eaD c i₀ Φ) z) ^ 2) := by
  simp [GInt]

lemma GBnd_zero (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (Cs δ2 : ℝ) (p q : ℕ)
    (i₀ j₀ : Fin k) : GBnd c Φ y Cs δ2 p q i₀ j₀ 0 = (fun z : Fin k → ℝ => eaEval c Φ z) := by
  simp [GBnd]

lemma GBnd_one (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (Cs δ2 : ℝ) (p q : ℕ)
    (i₀ j₀ : Fin k) :
    GBnd c Φ y Cs δ2 p q i₀ j₀ 1 = (fun z : Fin k → ℝ => Cs * (eaEval c Φ z) ^ (2 * p)
      - (∑ l : Fin k, (eaEval c (eaD c l Φ) z) ^ 2) ^ q) := by
  simp [GBnd]

lemma GBnd_two (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (Cs δ2 : ℝ) (p q : ℕ)
    (i₀ j₀ : Fin k) :
    GBnd c Φ y Cs δ2 p q i₀ j₀ 2 = (fun z : Fin k → ℝ => (muP c Φ y i₀ j₀ z) ^ 2) := by
  simp [GBnd]

lemma analyticAt_FInt (c : EAChain k r) (Φ : EAPoly k r) (v : Fin k → ℝ) (i₀ : Fin k)
    (x : Fin k → ℝ) : AnalyticAt ℝ (fun z : Fin k → ℝ => FInt c Φ v i₀ z) x := by
  unfold FInt
  refine (Finset.analyticAt_sum (Finset.univ : Finset (Fin k))
    (fun i _ => (eaEval_analytic c (pertMinor c Φ v i₀ i) x).pow 2)).congr ?_
  filter_upwards with z
  simp [Finset.sum_apply]

lemma analyticAt_GInt (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) (Cs : ℝ) (p q : ℕ)
    (x : Fin k → ℝ) (j : Fin 3) : AnalyticAt ℝ (GInt c Φ i₀ Cs p q j) x := by
  have hG := analyticAt_sqGradEval c Φ x
  have hΦ := eaEval_analytic c Φ x
  have hd := eaEval_analytic c (eaD c i₀ Φ) x
  fin_cases j
  · change AnalyticAt ℝ (GInt c Φ i₀ Cs p q 0) x
    rw [GInt_zero]; exact hΦ
  · change AnalyticAt ℝ (GInt c Φ i₀ Cs p q 1) x
    rw [GInt_one]
    exact (analyticAt_const.mul (hΦ.pow (2 * p))).sub (hG.pow q)
  · change AnalyticAt ℝ (GInt c Φ i₀ Cs p q 2) x
    rw [GInt_two]; exact hd.pow 2

lemma analyticAt_FBnd (c : EAChain k r) (Φ : EAPoly k r) (v y : Fin k → ℝ) (δ2 : ℝ)
    (i₀ j₀ : Fin k) (x : Fin k → ℝ) :
    AnalyticAt ℝ (fun z : Fin k → ℝ => FBnd c Φ v y δ2 i₀ j₀ z) x := by
  unfold FBnd
  have h1 : AnalyticAt ℝ (fun z : Fin k → ℝ => ((∑ i : Fin k, (z i - y i) ^ 2) - δ2) ^ 2) x :=
    ((analyticAt_sphereSq y x).sub (analyticAt_const (v := δ2))).pow 2
  have h2 : AnalyticAt ℝ (fun z : Fin k → ℝ =>
      ∑ l : Fin k, (eaEval c (pertMinor3 c Φ v y i₀ j₀ l) z) ^ 2) x := by
    refine (Finset.analyticAt_sum (Finset.univ : Finset (Fin k))
      (fun l _ => (eaEval_analytic c (pertMinor3 c Φ v y i₀ j₀ l) x).pow 2)).congr ?_
    filter_upwards with z
    simp [Finset.sum_apply]
  exact h1.add h2

lemma analyticAt_GBnd (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (Cs δ2 : ℝ) (p q : ℕ)
    (i₀ j₀ : Fin k) (x : Fin k → ℝ) (j : Fin 3) :
    AnalyticAt ℝ (GBnd c Φ y Cs δ2 p q i₀ j₀ j) x := by
  have hG := analyticAt_sqGradEval c Φ x
  have hΦ := eaEval_analytic c Φ x
  have hmu : AnalyticAt ℝ (muP c Φ y i₀ j₀) x := by
    have h1 := eaEval_analytic c (eaD c i₀ Φ) x
    have h2 := eaEval_analytic c (eaD c j₀ Φ) x
    have h3 : AnalyticAt ℝ (fun z : Fin k → ℝ => z j₀ - y j₀) x :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j₀).analyticAt x).sub
        (analyticAt_const (v := y j₀))
    have h4 : AnalyticAt ℝ (fun z : Fin k → ℝ => z i₀ - y i₀) x :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i₀).analyticAt x).sub
        (analyticAt_const (v := y i₀))
    exact (h1.mul h3).sub (h2.mul h4)
  fin_cases j
  · change AnalyticAt ℝ (GBnd c Φ y Cs δ2 p q i₀ j₀ 0) x
    rw [GBnd_zero]; exact hΦ
  · change AnalyticAt ℝ (GBnd c Φ y Cs δ2 p q i₀ j₀ 1) x
    rw [GBnd_one]
    exact (analyticAt_const.mul (hΦ.pow (2 * p))).sub (hG.pow q)
  · change AnalyticAt ℝ (GBnd c Φ y Cs δ2 p q i₀ j₀ 2) x
    rw [GBnd_two]; exact hmu.pow 2


end Work.WilE3.Taylor.CaseII
