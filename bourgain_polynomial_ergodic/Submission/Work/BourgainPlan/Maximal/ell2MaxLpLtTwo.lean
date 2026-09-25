import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.ell2InterpConst
import Submission.Work.BourgainPlan.Maximal.ell2Max_rpow_half_add_le
import Submission.Work.BourgainPlan.Maximal.lintegral_ell2Max_le_uniform
import Submission.Work.BourgainPlan.Maximal.ennRealMarcinkiewicz

/-!
# The `L^p(ℓ²)` bound, `1 < p < 2`, for the `ℓ²`-valued dyadic maximal function

`ell2Max f x = Σ_t (dyMax ‖f t ·‖ₑ x)²` is the square of the `ℓ²`-valued dyadic maximal function
and `ell2Sq f x = Σ_t ‖f t x‖ₑ²` the square of the `ℓ²`-norm of `f · x`.  `ell2MaxWeakOne` is the
weak-`(1,1)` bound of `(ell2Max f)^{1/2}` against `∫⁻ (ell2Sq f)^{1/2}`, and this file proves that
together with the strong-`(2,2)` bound (`lintegral_ell2Max_le`) it implies

`∫⁻ (ell2Max f)^{p/2} ≤ C^p ∫⁻ (ell2Sq f)^{p/2}`   for `1 < p < 2`,

with `C` *uniform in the number of components* `n` (of `f : Fin n → ℝ → ℝ`) — this is
Marcinkiewicz interpolation (weak `(1,1)` + strong `(2,2)`), i.e. the Fefferman--Stein
vector-valued maximal inequality in the range `1 < p < 2`.

The interpolation step is factored through the abstract lemma
`Work.BourgainPlan.Maximal.ennRealMarcinkiewicz`, applied to the normed space
`EuclideanSpace ℝ (Fin n)`: a family `f : Fin n → ℝ → ℝ` is the same thing as a function
`ℝ → EuclideanSpace ℝ (Fin n)` whose norm is `(ell2Sq f)^{1/2}`, and the `ℓ²`-valued maximal
function of the family is the `ℝ≥0∞`-valued operator `ell2MaxOp`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- The `EuclideanSpace ℝ (Fin n)`-valued function attached to a finite family `f`; its norm is
the `ℓ²`-norm `(ell2Sq f x)^{1/2}`. -/
noncomputable def toVec {n : ℕ} (f : Fin n → ℝ → ℝ) : ℝ → EuclideanSpace ℝ (Fin n) :=
  fun y => WithLp.toLp 2 (fun t => f t y)

/-- The family of coordinate functions of an `EuclideanSpace`-valued function. -/
noncomputable def ofVec {n : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin n)) : Fin n → ℝ → ℝ :=
  fun t y => g y t

@[simp] lemma toVec_apply {n : ℕ} (f : Fin n → ℝ → ℝ) (y : ℝ) (t : Fin n) :
    toVec f y t = f t y := rfl

@[simp] lemma ofVec_apply {n : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin n)) (t : Fin n) (y : ℝ) :
    ofVec g t y = g y t := rfl

lemma ofVec_toVec {n : ℕ} (f : Fin n → ℝ → ℝ) : ofVec (toVec f) = f := rfl

@[simp] lemma toVec_add {n : ℕ} (f h : Fin n → ℝ → ℝ) : toVec (f + h) = toVec f + toVec h := by
  funext y
  ext t
  rfl

/-- The `ℓ²`-valued dyadic maximal operator, as an `ℝ≥0∞`-valued function of an
`EuclideanSpace`-valued function: `(Σ_t (dyMax ‖g · t‖ₑ x)²)^{1/2}`. -/
noncomputable def ell2MaxOp {n : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin n)) : ℝ → ℝ≥0∞ :=
  fun x => (ell2Max (ofVec g) x) ^ ((1 : ℝ) / 2)

@[simp] lemma ell2MaxOp_apply {n : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin n)) (x : ℝ) :
    ell2MaxOp g x = (ell2Max (ofVec g) x) ^ ((1 : ℝ) / 2) := rfl

@[simp] lemma ell2MaxOp_toVec {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) :
    ell2MaxOp (toVec f) x = (ell2Max f x) ^ ((1 : ℝ) / 2) := by
  rw [ell2MaxOp_apply, ofVec_toVec]

lemma measurable_toVec {n : ℕ} {f : Fin n → ℝ → ℝ} (hf : ∀ t, Measurable (f t)) :
    Measurable (toVec f) := by
  unfold toVec
  exact (WithLp.measurable_toLp (2 : ℝ≥0∞) (Fin n → ℝ)).comp (measurable_pi_iff.mpr hf)

lemma measurable_ofVec {n : ℕ} {g : ℝ → EuclideanSpace ℝ (Fin n)} (hg : Measurable g)
    (t : Fin n) : Measurable (fun y => ofVec g t y) :=
  (measurable_pi_apply t).comp
    ((WithLp.measurable_ofLp (2 : ℝ≥0∞) (Fin n → ℝ)).comp hg)

lemma aemeasurable_ell2MaxOp {n : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin n)) :
    AEMeasurable (ell2MaxOp g) :=
  ((ENNReal.continuous_rpow_const (y := ((1 : ℝ) / 2))).measurable.comp
    (ell2Max_measurable _)).aemeasurable

/-- The `enorm` of an `EuclideanSpace`-valued function is the square root of `ell2Sq` of its
coordinate family. -/
lemma enorm_eq_ell2Sq_rpow_half {n : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin n)) (x : ℝ) :
    ‖g x‖ₑ = (ell2Sq (ofVec g) x) ^ ((1 : ℝ) / 2) := by
  have h1 : ‖g x‖ = Real.sqrt (∑ t, (g x t) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  have h2 : ell2Sq (ofVec g) x = ENNReal.ofReal (∑ t, (g x t) ^ 2) := by
    unfold ell2Sq
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => by positivity)]
    apply Finset.sum_congr rfl
    intro t _
    rw [Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    simp only [ofVec]
  rw [← ofReal_norm, h1, Real.sqrt_eq_rpow, h2,
    ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun t _ => by positivity)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- Rewriting `(a^{1/2})^p` as `a^{p/2}`. -/
lemma rpow_half_rpow (a : ℝ≥0∞) (p : ℝ) : (a ^ ((1 : ℝ) / 2)) ^ p = a ^ (p / 2) := by
  rw [← ENNReal.rpow_mul]
  congr 1
  ring

lemma rpow_half_sq (a : ℝ≥0∞) : (a ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = a := by
  rw [rpow_half_rpow, show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one]

/-- The weak-`(1,1)` bound transported to the `EuclideanSpace`-valued formulation. -/
lemma volume_lt_ell2MaxOp_le {n : ℕ} {C₀ : ℝ}
    (h : ∀ (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) → ∀ lam : ℝ, 0 < lam →
      volume {x : ℝ | ENNReal.ofReal lam < (ell2Max f x) ^ ((1 : ℝ) / 2)}
        ≤ ENNReal.ofReal (C₀ / lam) * ∫⁻ x, (ell2Sq f x) ^ ((1 : ℝ) / 2))
    (g : ℝ → EuclideanSpace ℝ (Fin n)) (hg : Measurable g) :
    ∀ lam : ℝ, 0 < lam →
      volume {x : ℝ | ENNReal.ofReal lam < ell2MaxOp g x}
        ≤ ENNReal.ofReal (C₀ / lam) * ∫⁻ x, ‖g x‖ₑ := by
  intro lam hlam
  have h' := h (ofVec g) (fun t => measurable_ofVec hg t) lam hlam
  have hset : {x : ℝ | ENNReal.ofReal lam < ell2MaxOp g x}
      = {x : ℝ | ENNReal.ofReal lam < (ell2Max (ofVec g) x) ^ ((1 : ℝ) / 2)} := rfl
  rw [hset]
  refine h'.trans (le_of_eq ?_)
  congr 1
  exact lintegral_congr fun x => (enorm_eq_ell2Sq_rpow_half g x).symm

/-- The strong-`(2,2)` bound transported to the `EuclideanSpace`-valued formulation. -/
lemma lintegral_ell2MaxOp_sq_le {n : ℕ} {A₁ : ℝ}
    (h : ∀ (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∫⁻ x, ell2Max f x ≤ ENNReal.ofReal (A₁ ^ (2 : ℝ)) * ∫⁻ x, ell2Sq f x)
    (g : ℝ → EuclideanSpace ℝ (Fin n)) (hg : Measurable g) :
    ∫⁻ x, (ell2MaxOp g x) ^ (2 : ℝ) ≤ ENNReal.ofReal (A₁ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) := by
  have h' := h (ofVec g) (fun t => measurable_ofVec hg t)
  have e1 : ∫⁻ x, (ell2MaxOp g x) ^ (2 : ℝ) = ∫⁻ x, ell2Max (ofVec g) x := by
    apply lintegral_congr
    intro x
    rw [ell2MaxOp_apply, rpow_half_sq]
  have e2 : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) = ∫⁻ x, ell2Sq (ofVec g) x := by
    apply lintegral_congr
    intro x
    rw [enorm_eq_ell2Sq_rpow_half, rpow_half_sq]
  rw [e1, e2]
  refine h'.trans (le_of_eq ?_)
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The `p`-th power of `ell2MaxOp (toVec f)` is the `p/2`-th power of `ell2Max f`. -/
lemma lintegral_ell2MaxOp_rpow_toVec {n : ℕ} (f : Fin n → ℝ → ℝ) (p : ℝ) :
    ∫⁻ x, (ell2MaxOp (toVec f) x) ^ p = ∫⁻ x, (ell2Max f x) ^ (p / 2) := by
  apply lintegral_congr
  intro x
  rw [ell2MaxOp_toVec, rpow_half_rpow]

/-- The `p`-th power of the norm of `toVec f` is the `p/2`-th power of `ell2Sq f`. -/
lemma lintegral_enorm_toVec_rpow {n : ℕ} (f : Fin n → ℝ → ℝ) (p : ℝ) :
    ∫⁻ x, ‖toVec f x‖ₑ ^ p = ∫⁻ x, (ell2Sq f x) ^ (p / 2) := by
  apply lintegral_congr
  intro x
  rw [enorm_eq_ell2Sq_rpow_half, ofVec_toVec, rpow_half_rpow]

/-- Subadditivity of the `ℓ²`-valued dyadic maximal operator on `EuclideanSpace`-valued
functions (from the `ℓ²` triangle inequality for the family version). -/
lemma ell2MaxOp_add_le {n : ℕ} (f h : ℝ → EuclideanSpace ℝ (Fin n))
    (hf : Measurable f) (hh : Measurable h) (x : ℝ) :
    ell2MaxOp (f + h) x ≤ ell2MaxOp f x + ell2MaxOp h x := by
  have hfam : ofVec (f + h) = ofVec f + ofVec h := by
    funext t y
    rfl
  have key := ell2Max_rpow_half_add_le (ofVec f) (ofVec h)
    (fun t => measurable_ofVec hf t) (fun t => measurable_ofVec hh t) x
  rw [ell2MaxOp_apply, hfam, ell2MaxOp_apply, ell2MaxOp_apply]
  exact key

/-- **The `L^p(ℓ²)` bound, `1 < p < 2`, for the `ℓ²`-valued dyadic maximal function**, with a
constant uniform in the number of components. -/
theorem ell2MaxLpLtTwo {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hweak : ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) → ∀ lam : ℝ, 0 < lam →
      MeasureTheory.volume {x : ℝ | ENNReal.ofReal lam < (Work.BourgainPlan.Maximal.ell2Max f x) ^ ((1 : ℝ) / 2)}
        ≤ ENNReal.ofReal (C₀ / lam) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ ((1 : ℝ) / 2))
    {p : ℝ} (hp₁ : 1 < p) (hp₂ : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Max f x) ^ (p / 2) ≤ ENNReal.ofReal (C ^ p) *
        ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ (p / 2) := by
  obtain ⟨A₁, hA₁pos, hA₁⟩ := lintegral_ell2Max_le_uniform
  set K : ℝ := marcConst p C₀ A₁ with hKdef
  have hKpos : 0 < K := by
    rw [hKdef, marcConst]
    have h1 : (0 : ℝ) < 12 * (2 : ℝ) ^ (p - 1) / (p - 1) := by positivity
    have h2 : (0 : ℝ) < 16 / (2 - p) := by positivity
    have h3 : (0 : ℝ) < C₀ ^ (2 - p) := Real.rpow_pos_of_pos hC₀ _
    have h4 : (0 : ℝ) < A₁ ^ (2 * p - 2) := Real.rpow_pos_of_pos hA₁pos _
    positivity
  have hKK : (K ^ (1 / p)) ^ p = K := by
    rw [← Real.rpow_mul hKpos.le, one_div,
      inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one hp₁)), Real.rpow_one]
  refine ⟨K ^ (1 / p), Real.rpow_pos_of_pos hKpos _, ?_⟩
  intro n f hf
  have hmain : ∫⁻ x, (ell2MaxOp (toVec f) x) ^ p
      ≤ ENNReal.ofReal (marcConst p C₀ A₁) * ∫⁻ x, ‖toVec f x‖ₑ ^ p :=
    ennRealMarcinkiewicz (E := EuclideanSpace ℝ (Fin n))
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (T := ell2MaxOp (n := n))
      (fun f h hf hh x => ell2MaxOp_add_le f h hf hh x)
      (fun g => aemeasurable_ell2MaxOp g) hC₀ hA₁pos hp₁ hp₂
      (volume_lt_ell2MaxOp_le (fun g hg => hweak n g hg))
      (fun g hg => lintegral_ell2MaxOp_sq_le (fun g' hg' => hA₁ n g' hg') g hg)
      (toVec f) (measurable_toVec hf)
  calc ∫⁻ x, (ell2Max f x) ^ (p / 2)
      = ∫⁻ x, (ell2MaxOp (toVec f) x) ^ p := (lintegral_ell2MaxOp_rpow_toVec f p).symm
    _ ≤ ENNReal.ofReal (marcConst p C₀ A₁) * ∫⁻ x, ‖toVec f x‖ₑ ^ p := hmain
    _ = ENNReal.ofReal (marcConst p C₀ A₁) * ∫⁻ x, (ell2Sq f x) ^ (p / 2) := by
        rw [lintegral_enorm_toVec_rpow f p]
    _ = ENNReal.ofReal ((K ^ (1 / p)) ^ p) * ∫⁻ x, (ell2Sq f x) ^ (p / 2) := by
        congr 1
        congr 1
        rw [← hKdef]
        exact hKK.symm

end Work.BourgainPlan.Maximal
