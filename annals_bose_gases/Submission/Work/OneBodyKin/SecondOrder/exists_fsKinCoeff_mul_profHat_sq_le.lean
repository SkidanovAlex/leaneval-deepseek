import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.SecondOrder.exists_fsKinCoeff_mul_profHat_sq_le`

The squared-profile companion of `Work.OneBodyKin.exists_fsKinCoeff_mul_abs_profHat_le`:

    `∀ δ > 0, ∃ C₀, ∀ C ≥ C₀, ∫_p [‖p‖ − C]₊² · profHat(p)² dp ≤ δ`.

The FS cut-off `fsKinCoeff C r = [r − C]₊²` vanishes for `r ≤ C`, so for `C ≥ 0` the integrand
`fsKinCoeff C ‖p‖ · profHat(p)²` is dominated by `(1 + ‖p‖)² profHat(p)²`, which is integrable
because the bump profile decays like `(1 + ‖p‖)^{-6}` and leaves the integrable weight
`(1 + ‖p‖)^{-10}` in dimension `3`.  As `C → ∞` the integrand converges pointwise to `0`
(`fsKinCoeff C ‖p‖ = 0` once `C ≥ ‖p‖`), so Lebesgue dominated convergence gives the limit `0`
of the integrals, hence the cut-off can be pushed past any `δ > 0`.
-/

namespace Work.OneBodyKin.SecondOrder

open MeasureTheory Filter
open scoped Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **`p ↦ (1 + ‖p‖)² profHat(p)²` is integrable.**  Expanding the square reduces this to the
three integrable weights `profHat² ‖p‖ⁿ`, `n ≤ 2`, of `integrable_profHat_sq_mul_norm_pow`,
which is the dominating function for every `fsKinCoeff`-weighted integral of `profHat²`. -/
lemma integrable_oneAddNorm_sq_mul_profHat_sq :
    MeasureTheory.Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ 2 * (profHat p) ^ 2) := by
  have h2 := Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 2 (le_refl 2)
  have h1 := (Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 1 (by norm_num)).const_mul (2 : ℝ)
  have h0 := Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow 0 (by norm_num)
  refine ((h2.add h1).add h0).congr ?_
  filter_upwards with p
  simp only [Pi.add_apply]
  ring

theorem exists_fsKinCoeff_mul_profHat_sq_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C →
      ∫ p : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 ≤ δ := by
  have hmain : Tendsto (fun C : ℝ =>
      ∫ p : ℝ³, fsKinCoeff C ‖p‖ * (profHat p) ^ 2) atTop (nhds 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
      (F := fun C : ℝ => fun p : ℝ³ => fsKinCoeff C ‖p‖ * (profHat p) ^ 2)
      (f := fun _ => 0)
      (fun p : ℝ³ => (1 + ‖p‖) ^ 2 * (profHat p) ^ 2)
      ?_ ?_ integrable_oneAddNorm_sq_mul_profHat_sq ?_
    · simpa using h
    · -- measurability of every integrand
      exact Filter.Eventually.of_forall fun C =>
        ((((continuous_norm.sub continuous_const).max continuous_const).pow 2).mul
          (Work.OneBodyKin.continuous_profHat.pow 2)).aestronglyMeasurable
    · -- domination by `(1 + ‖p‖)² profHat(p)²` for `C ≥ 0`
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with C hC
      filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (fsKinCoeff_nonneg C ‖p‖) (sq_nonneg _))]
      have h2 : fsKinCoeff C ‖p‖ ≤ (1 + ‖p‖) ^ 2 := by
        rw [fsKinCoeff]
        refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ ?_) 2
        · linarith
        · positivity
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    · -- pointwise convergence to `0`: the cut-off eventually swallows `‖p‖`
      filter_upwards with p
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop ‖p‖] with C hC
      rw [fsKinCoeff_of_le hC, zero_mul]
  have hlt : ∀ᶠ C in atTop, (∫ p : ℝ³, fsKinCoeff C ‖p‖ * (profHat p) ^ 2) < δ :=
    hmain.eventually (isOpen_Iio.mem_nhds hδ)
  obtain ⟨C0, hC0⟩ := eventually_atTop.mp hlt
  exact ⟨C0, fun C hC => le_of_lt (hC0 C hC)⟩

end Work.OneBodyKin.SecondOrder
