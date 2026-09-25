import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2MaxShiftDefs
import Submission.Work.BourgainPlan.Maximal.ell2MaxShift_rpow_half_add_le
import Submission.Work.BourgainPlan.Maximal.lintegral_ell2MaxShift_le_uniform
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal
import Submission.Work.BourgainPlan.Maximal.hlMaxTwoGrid
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.ell2MaxLpLtTwo
import Submission.Work.BourgainPlan.Maximal.lintegral_rpow_le_of_weak_one_l2
import Submission.Work.BourgainPlan.Maximal.ell2F_hlMax_twoGrids
import Submission.Work.BourgainPlan.Maximal.ell2Max_rpow_half_add_le

/-!
# The `L^p(ℓ²)` bound, `1 < p < 2`, for the *half-shifted* `ℓ²`-valued dyadic maximal function

`ell2MaxShift f x = Σ_t (dyMaxShift (1/2) (‖f t ·‖ₑ) x)²` is the square of the `ℓ²`-valued maximal
function over the half-shifted (non-laminar) dyadic grid, and
`ell2Sq f x = Σ_t ‖f t x‖ₑ²` the square of the `ℓ²`-norm of `f · x`.  This file proves that the
weak-`(1,1)` bound of `(ell2MaxShift f)^{1/2}` against `∫⁻ (ell2Sq f)^{1/2}` — the hypothesis
`hweak`, i.e. the content of `ell2MaxShiftWeakOne` — together with the strong-`(2,2)` bound proved
in `lintegral_ell2MaxShift_le_uniform` (itself a consequence of the scalar Hardy--Littlewood L²
bound via `dyMaxShift α φ ≤ hlMax φ`) implies

`∫⁻ (ell2MaxShift f)^{p/2} ≤ C^p ∫⁻ (ell2Sq f)^{p/2}`   for `1 < p < 2`,

with `C` uniform in the number of components `n` (of `f : Fin n → ℝ → ℝ`).

This is Marcinkiewicz interpolation (weak `(1,1)` + strong `(2,2)`) for the vector-valued maximal
operator of the shifted grid; it is the shifted analogue of `ell2MaxLpLtTwo`.  The interpolation
step is factored through the abstract lemma `Work.BourgainPlan.Maximal.ennRealMarcinkiewicz`
applied to the normed space `EuclideanSpace ℝ (Fin n)`: a family `f : Fin n → ℝ → ℝ` is the same
thing as a function `ℝ → EuclideanSpace ℝ (Fin n)` whose norm is `(ell2Sq f)^{1/2}`, and the
`ℓ²`-valued maximal function of the family is the `ℝ≥0∞`-valued operator `ell2MaxShiftOp`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- The `ℓ²`-valued *half-shifted* dyadic maximal operator, as an `ℝ≥0∞`-valued function of an
`EuclideanSpace`-valued function: `(Σ_t (dyMaxShift (1/2) ‖g · t‖ₑ x)²)^{1/2}`. -/
noncomputable def ell2MaxShiftOp {n : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin n)) : ℝ → ℝ≥0∞ :=
  fun x => (ell2MaxShift (ofVec g) x) ^ ((1 : ℝ) / 2)

@[simp] lemma ell2MaxShiftOp_apply {n : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin n)) (x : ℝ) :
    ell2MaxShiftOp g x = (ell2MaxShift (ofVec g) x) ^ ((1 : ℝ) / 2) := rfl

@[simp] lemma ell2MaxShiftOp_toVec {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) :
    ell2MaxShiftOp (toVec f) x = (ell2MaxShift f x) ^ ((1 : ℝ) / 2) := by
  rw [ell2MaxShiftOp_apply, ofVec_toVec]

lemma aemeasurable_ell2MaxShiftOp {n : ℕ} (g : ℝ → EuclideanSpace ℝ (Fin n)) :
    AEMeasurable (ell2MaxShiftOp g) :=
  ((ENNReal.continuous_rpow_const (y := ((1 : ℝ) / 2))).measurable.comp
    (ell2MaxShift_measurable (ofVec g))).aemeasurable

/-- The weak-`(1,1)` bound transported to the `EuclideanSpace`-valued formulation. -/
lemma volume_lt_ell2MaxShiftOp_le {n : ℕ} {C₀ : ℝ}
    (h : ∀ (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) → ∀ lam : ℝ, 0 < lam →
      MeasureTheory.volume {x : ℝ | ENNReal.ofReal lam < (∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)}
        ≤ ENNReal.ofReal (C₀ / lam) * ∫⁻ x, (ell2Sq f x) ^ ((1 : ℝ) / 2))
    (g : ℝ → EuclideanSpace ℝ (Fin n)) (hg : Measurable g) :
    ∀ lam : ℝ, 0 < lam →
      volume {x : ℝ | ENNReal.ofReal lam < ell2MaxShiftOp g x}
        ≤ ENNReal.ofReal (C₀ / lam) * ∫⁻ x, ‖g x‖ₑ := by
  intro lam hlam
  have h' := h (ofVec g) (fun t => measurable_ofVec hg t) lam hlam
  have hset : {x : ℝ | ENNReal.ofReal lam < ell2MaxShiftOp g x}
      = {x : ℝ | ENNReal.ofReal lam < (ell2MaxShift (ofVec g) x) ^ ((1 : ℝ) / 2)} := rfl
  rw [hset]
  refine h'.trans (le_of_eq ?_)
  congr 1
  exact lintegral_congr fun x => (enorm_eq_ell2Sq_rpow_half g x).symm

/-- The strong-`(2,2)` bound transported to the `EuclideanSpace`-valued formulation. -/
lemma lintegral_ell2MaxShiftOp_sq_le {n : ℕ} {A₁ : ℝ}
    (h : ∀ (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∫⁻ x, ell2MaxShift f x ≤ ENNReal.ofReal (A₁ ^ (2 : ℝ)) * ∫⁻ x, ell2Sq f x)
    (g : ℝ → EuclideanSpace ℝ (Fin n)) (hg : Measurable g) :
    ∫⁻ x, (ell2MaxShiftOp g x) ^ (2 : ℝ) ≤ ENNReal.ofReal (A₁ ^ 2) * ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) := by
  have h' := h (ofVec g) (fun t => measurable_ofVec hg t)
  have e1 : ∫⁻ x, (ell2MaxShiftOp g x) ^ (2 : ℝ) = ∫⁻ x, ell2MaxShift (ofVec g) x := by
    apply lintegral_congr
    intro x
    rw [ell2MaxShiftOp_apply, rpow_half_sq]
  have e2 : ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) = ∫⁻ x, ell2Sq (ofVec g) x := by
    apply lintegral_congr
    intro x
    rw [enorm_eq_ell2Sq_rpow_half, rpow_half_sq]
  rw [e1, e2]
  refine h'.trans (le_of_eq ?_)
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The `p`-th power of `ell2MaxShiftOp (toVec f)` is the `p/2`-th power of `ell2MaxShift f`. -/
lemma lintegral_ell2MaxShiftOp_rpow_toVec {n : ℕ} (f : Fin n → ℝ → ℝ) (p : ℝ) :
    ∫⁻ x, (ell2MaxShiftOp (toVec f) x) ^ p = ∫⁻ x, (ell2MaxShift f x) ^ (p / 2) := by
  apply lintegral_congr
  intro x
  rw [ell2MaxShiftOp_toVec, rpow_half_rpow]

/-- Subadditivity of the `ℓ²`-valued half-shifted dyadic maximal operator on
`EuclideanSpace`-valued functions (from the `ℓ²` triangle inequality for the family version). -/
lemma ell2MaxShiftOp_add_le {n : ℕ} (f h : ℝ → EuclideanSpace ℝ (Fin n))
    (hf : Measurable f) (hh : Measurable h) (x : ℝ) :
    ell2MaxShiftOp (f + h) x ≤ ell2MaxShiftOp f x + ell2MaxShiftOp h x := by
  have hfam : ofVec (f + h) = ofVec f + ofVec h := by
    funext t y
    rfl
  have key := ell2MaxShift_rpow_half_add_le (ofVec f) (ofVec h)
    (fun t => measurable_ofVec hf t) (fun t => measurable_ofVec hh t) x
  rw [ell2MaxShiftOp_apply, hfam, ell2MaxShiftOp_apply, ell2MaxShiftOp_apply]
  exact key

/-- **The `L^p(ℓ²)` bound, `1 < p < 2`, for the `ℓ²`-valued half-shifted dyadic maximal
function**, with a constant uniform in the number of components. -/
theorem ell2MaxShiftLpLtTwo (hweak : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) → ∀ lam : ℝ, 0 < lam → MeasureTheory.volume {x : ℝ | ENNReal.ofReal lam < (∑ t, (Work.BourgainPlan.Maximal.dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)} ≤ ENNReal.ofReal (C / lam) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ ((1 : ℝ) / 2)) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : ∃ C' : ℝ, 0 < C' ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) → ∫⁻ x, (∑ t, (Work.BourgainPlan.Maximal.dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2) ≤ ENNReal.ofReal (C' ^ p) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ (p / 2) := by
  obtain ⟨C₀, hC₀pos, hweak'⟩ := hweak
  obtain ⟨A₁, hA₁pos, hA₁⟩ := lintegral_ell2MaxShift_le_uniform
  set K : ℝ := marcConst p C₀ A₁ with hKdef
  have hKpos : 0 < K := by
    rw [hKdef, marcConst]
    have h1 : (0 : ℝ) < 12 * (2 : ℝ) ^ (p - 1) / (p - 1) := by positivity
    have h2 : (0 : ℝ) < 16 / (2 - p) := by positivity
    have h3 : (0 : ℝ) < C₀ ^ (2 - p) := Real.rpow_pos_of_pos hC₀pos _
    have h4 : (0 : ℝ) < A₁ ^ (2 * p - 2) := Real.rpow_pos_of_pos hA₁pos _
    positivity
  have hKK : (K ^ (1 / p)) ^ p = K := by
    rw [← Real.rpow_mul hKpos.le, one_div,
      inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one hp1)), Real.rpow_one]
  refine ⟨K ^ (1 / p), Real.rpow_pos_of_pos hKpos _, ?_⟩
  intro n f hf
  have hmain : ∫⁻ x, (ell2MaxShiftOp (toVec f) x) ^ p
      ≤ ENNReal.ofReal (marcConst p C₀ A₁) * ∫⁻ x, ‖toVec f x‖ₑ ^ p :=
    ennRealMarcinkiewicz (E := EuclideanSpace ℝ (Fin n))
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (T := ell2MaxShiftOp (n := n))
      (fun f h hf hh x => ell2MaxShiftOp_add_le f h hf hh x)
      (fun g => aemeasurable_ell2MaxShiftOp g) hC₀pos hA₁pos hp1 hp2
      (volume_lt_ell2MaxShiftOp_le (fun g hg => hweak' n g hg))
      (fun g hg => lintegral_ell2MaxShiftOp_sq_le (fun g' hg' => hA₁ n g' hg') g hg)
      (toVec f) (measurable_toVec hf)
  have h1 : ∫⁻ x, (∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2)
      = ∫⁻ x, (ell2MaxShiftOp (toVec f) x) ^ p := by
    rw [lintegral_ell2MaxShiftOp_rpow_toVec f p]
    rfl
  calc ∫⁻ x, (∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2)
      = ∫⁻ x, (ell2MaxShiftOp (toVec f) x) ^ p := h1
    _ ≤ ENNReal.ofReal (marcConst p C₀ A₁) * ∫⁻ x, ‖toVec f x‖ₑ ^ p := hmain
    _ = ENNReal.ofReal (marcConst p C₀ A₁) * ∫⁻ x, (ell2Sq f x) ^ (p / 2) := by
        rw [lintegral_enorm_toVec_rpow f p]
    _ = ENNReal.ofReal ((K ^ (1 / p)) ^ p) * ∫⁻ x, (ell2Sq f x) ^ (p / 2) := by
        congr 1
        congr 1
        rw [← hKdef]
        exact hKK.symm

end Work.BourgainPlan.Maximal
