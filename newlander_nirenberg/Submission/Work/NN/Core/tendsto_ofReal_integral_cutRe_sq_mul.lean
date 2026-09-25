/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The radial cut-off is an approximation of the identity for the energy

This file proves that the `L¹`-weighted squared radial cut-off
`(z ↦ cutRe R z ^ 2 * F z)` recovers the (possibly infinite) Lebesgue integral
of a continuous nonnegative `F`, in the sense that

`∫ z, cutRe (N+1) z ^ 2 * F z → ∫⁻ z, ofReal (F z)`  as `N → ∞`,

with the right-hand side read in `ℝ≥0∞` (so the statement also covers
non-integrable `F`, where both sides go to `⊤`).

The proof is a monotone convergence argument: `cutRe R` is monotone in the radius `R`
and increases pointwise to `1`, the truncated integrals are honest finite Bochner
integrals (the integrand is continuous with compact support), and for each fixed `N`
`ENNReal.ofReal` of the Bochner integral is the lintegral of the integrand.
-/
import Mathlib
import Submission.Work.NN.Core.czbL2Cut

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-! ## Monotonicity of the radial cut-off -/

/-- The smooth radial profile is nonincreasing. -/
lemma cutProfile_antitone : Antitone Work.CR.Flat.Cauchy.cutProfile := by
  intro a b hab
  rw [Work.CR.Flat.Cauchy.cutProfile]
  exact Real.smoothTransition.monotone (by linarith)

/-- The radial cut-off is monotone in the radius (for positive radii). -/
lemma cutRe_mono {n : ℕ} {R R' : ℝ} (hR : 0 < R) (h : R ≤ R') (z : Fin n → ℂ) :
    cutRe (n := n) R z ≤ cutRe (n := n) R' z := by
  rw [cutRe, cutRe]
  exact cutProfile_antitone
    (div_le_div_of_nonneg_left (nrmSq_nonneg z) (pow_pos hR 2) (pow_le_pow_left₀ hR.le h 2))

/-- Along `R = N + 1` the radial cut-off is monotone in `N`. -/
lemma cutRe_monotone_nat {n : ℕ} (z : Fin n → ℂ) :
    Monotone (fun N : ℕ => cutRe (n := n) ((N : ℝ) + 1) z) := by
  intro a b hab
  refine cutRe_mono (R := (a : ℝ) + 1) (R' := (b : ℝ) + 1) (by positivity) ?_ z
  have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  linarith

/-- Along `R = N + 1` the squared radial cut-off tends to `1` pointwise. -/
lemma tendsto_cutRe_sq_nat {n : ℕ} (z : Fin n → ℂ) :
    Tendsto (fun N : ℕ => (cutRe (n := n) ((N : ℝ) + 1) z) ^ 2) atTop (nhds 1) := by
  have h1 : Tendsto (fun N : ℕ => cutRe (n := n) ((N : ℝ) + 1) z) atTop (nhds 1) := by
    obtain ⟨N0, hN0⟩ := exists_nat_ge (2 * nrmSq z)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N0] with N hN
    have h1 : 2 * nrmSq z ≤ (N0 : ℝ) := hN0
    have h2 : (N0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNn : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hsq : 2 * nrmSq z ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg ((N : ℝ))]
    rw [cutRe_eq_one hsq]
  simpa using h1.pow 2

/-- The `ℝ≥0∞`-valued truncated integrands converge pointwise to `ofReal F`. -/
lemma tendsto_ofReal_cutRe_sq_mul {n : ℕ} {F : (Fin n → ℂ) → ℝ} (z : Fin n → ℂ) :
    Tendsto (fun N : ℕ => ENNReal.ofReal ((cutRe (n := n) ((N : ℝ) + 1) z) ^ 2 * F z))
      atTop (nhds (ENNReal.ofReal (F z))) := by
  have h : Tendsto (fun N : ℕ => (cutRe (n := n) ((N : ℝ) + 1) z) ^ 2 * F z)
      atTop (nhds (F z)) := by
    have := (tendsto_cutRe_sq_nat z).mul_const (F z)
    simpa using this
  exact (ENNReal.continuous_ofReal.tendsto (F z)).comp h

/-- The `ℝ≥0∞`-valued truncated integrands are monotone in `N` when `F ≥ 0`. -/
lemma monotone_ofReal_cutRe_sq_mul {n : ℕ} {F : (Fin n → ℂ) → ℝ} (hF0 : ∀ z, 0 ≤ F z)
    (z : Fin n → ℂ) :
    Monotone (fun N : ℕ => ENNReal.ofReal ((cutRe (n := n) ((N : ℝ) + 1) z) ^ 2 * F z)) := by
  intro a b hab
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (cutRe_nonneg _ z) (cutRe_monotone_nat z hab) 2) (hF0 z)

/-! ## Compact support and integrability of the truncated integrand -/

/-- The truncated integrand is supported in the closed ball of radius `N + 1`. -/
lemma hasCompactSupport_cutRe_sq_mul {n : ℕ} {F : (Fin n → ℂ) → ℝ} (N : ℕ) :
    HasCompactSupport (fun z : Fin n → ℂ => (cutRe (n := n) ((N : ℝ) + 1) z) ^ 2 * F z) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall (0 : Fin n → ℂ) ((N : ℝ) + 1)) (isCompact_closedBall _ _) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  have hR : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hz0 : cutRe (n := n) ((N : ℝ) + 1) z = 0 := by
    apply cutRe_eq_zero hR
    rw [nrmSq_eq_eucNorm_sq]
    have h1 : (N : ℝ) + 1 < eucNorm z := lt_of_lt_of_le hcon (pi_norm_le_eucNorm z)
    nlinarith [eucNorm_nonneg z]
  exact hz (by simp [hz0])

/-- The truncated integrand is continuous. -/
lemma continuous_cutRe_sq_mul {n : ℕ} {F : (Fin n → ℂ) → ℝ} (hF : Continuous F) (N : ℕ) :
    Continuous (fun z : Fin n → ℂ => (cutRe (n := n) ((N : ℝ) + 1) z) ^ 2 * F z) :=
  (((contDiff_cutRe (n := n) ((N : ℝ) + 1)).continuous).pow 2).mul hF

/-! ## The main convergence statement -/

theorem tendsto_ofReal_integral_cutRe_sq_mul {n : ℕ} {F : (Fin n → ℂ) → ℝ}
    (hF : Continuous F) (hF0 : ∀ z, 0 ≤ F z) :
    Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (∫ z, (Work.NN.Core.cutRe (n := n) (N + 1) z) ^ 2 * F z))
      Filter.atTop (nhds (∫⁻ z, ENNReal.ofReal (F z))) := by
  have hrew : ∀ N : ℕ,
      ENNReal.ofReal (∫ z, (cutRe (n := n) (N + 1) z) ^ 2 * F z)
        = ∫⁻ z, ENNReal.ofReal ((cutRe (n := n) (N + 1) z) ^ 2 * F z) := by
    intro N
    refine MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((continuous_cutRe_sq_mul hF N).integrable_of_hasCompactSupport
        (hasCompactSupport_cutRe_sq_mul N)) ?_
    exact Eventually.of_forall (fun z => mul_nonneg (sq_nonneg _) (hF0 z))
  simp only [hrew]
  exact MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone
    (fun N => (continuous_cutRe_sq_mul hF N).measurable.ennreal_ofReal.aemeasurable)
    (Eventually.of_forall (fun z => monotone_ofReal_cutRe_sq_mul hF0 z))
    (Eventually.of_forall (fun z => tendsto_ofReal_cutRe_sq_mul z))

end Work.NN.Core
