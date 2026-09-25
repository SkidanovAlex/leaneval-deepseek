import Mathlib
import Submission.Work.Beltrami.integrable_bI
import Submission.Work.Beltrami.beurlingBound_integrable
import Submission.Work.Beltrami.norm_beurlingIntegrand_le
import Submission.Work.Beltrami.norm_beurlingIntegrand_le_of_holder

namespace Work.Beltrami

open MeasureTheory

noncomputable section

/-!
# Continuity of the Beurling transform along a locally uniformly Hölder sequence

The Beurling transform `beurling f z = -(1/π) ∫ (f ζ - χ(ζ-z) f z)(ζ-z)⁻² dA(ζ)`
(`χ = bumpC`) is the regularised singular integral operator solving `∂ = B ∂̄`.  For the
Schauder theory on a sequence one needs that it is compatible with limits of sequences that are
*uniformly* bounded, uniformly α-Hölder and uniformly supported:

if `u n → f` pointwise, with `‖u n‖ ≤ M`, `‖u n x - u n y‖ ≤ K ‖x-y‖^α` (`α > 0`) and
`u n = 0` outside the ball of radius `R` for every `n`, then `B (u n) z → B f z` for every `z`.

The proof is dominated convergence for the integrands
`w ↦ w⁻² (u n (z+w) - χ w · u n z)`: they converge pointwise to the corresponding integrand of
`f` (pointwise convergence is preserved by the algebraic operations), and they are all dominated
by the *same* integrable function `beurlingBound α K K M R z` — this is exactly the content of
`norm_beurlingIntegrand_le_of_holder` (the α-Hölder form of `norm_beurlingIntegrand_le`).
Note that the same constant `K` is used for `f`: `f` inherits the bound, the Hölder estimate and
the support condition from the sequence `u n`.
-/

theorem tendsto_beurling_of_tendsto {α M K R : ℝ} (hα : 0 < α) (hM : 0 ≤ M) (hK : 0 ≤ K)
    {u : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (huM : ∀ n z, ‖u n z‖ ≤ M)
    (huK : ∀ (n : ℕ) (x y : ℂ), ‖u n x - u n y‖ ≤ K * ‖x - y‖ ^ α)
    (huS : ∀ n z, R < ‖z‖ → u n z = 0)
    (hconv : ∀ z, Filter.Tendsto (fun n => u n z) Filter.atTop (nhds (f z))) :
    ∀ z, Filter.Tendsto (fun n => Work.Beltrami.beurling (u n) z) Filter.atTop
      (nhds (Work.Beltrami.beurling f z)) := by
  intro z
  -- The limit `f` inherits the three uniform conditions.
  have hMf : ∀ y : ℂ, ‖f y‖ ≤ M := fun y =>
    le_of_tendsto_of_tendsto (hconv y).norm tendsto_const_nhds
      (Filter.Eventually.of_forall fun n => huM n y)
  have hKf : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α := fun x y =>
    le_of_tendsto_of_tendsto (((hconv x).sub (hconv y)).norm) tendsto_const_nhds
      (Filter.Eventually.of_forall fun n => huK n x y)
  have hSf : ∀ y : ℂ, R < ‖y‖ → f y = 0 := by
    intro y hy
    refine tendsto_nhds_unique (hconv y) ?_
    rw [show (fun n => u n y) = fun _ => (0 : ℂ) from funext (fun n => huS n y hy)]
    exact tendsto_const_nhds
  -- The integrands are a.e. strongly measurable.
  have hmeas : ∀ n, AEStronglyMeasurable (fun w : ℂ => beurlingIntegrand (u n) z w) volume := by
    intro n
    have hcont : Continuous fun w : ℂ => u n (z + w) - (bumpC w : ℂ) • u n z :=
      ((Work.CR.Flat.Cauchy.continuous_of_holder hα hK (huK n)).comp
          (continuous_const.add continuous_id)).sub
        (bumpC_contDiffC.continuous.smul continuous_const)
    have hm : Measurable fun w : ℂ => (u n (z + w) - (bumpC w : ℂ) • u n z) / (w ^ 2) :=
      hcont.measurable.div (measurable_id.pow_const 2)
    have heq : (fun w : ℂ => beurlingIntegrand (u n) z w)
        = fun w : ℂ => (u n (z + w) - (bumpC w : ℂ) • u n z) / (w ^ 2) := by
      funext w
      rw [beurlingIntegrand, div_eq_mul_inv, smul_eq_mul, mul_comm]
    rw [heq]
    exact hm.aestronglyMeasurable
  -- Dominated convergence for the integrands, with the same majorant for every `n`.
  have hInt : Filter.Tendsto (fun n => ∫ w, beurlingIntegrand (u n) z w) Filter.atTop
      (nhds (∫ w, beurlingIntegrand f z w)) :=
    tendsto_integral_of_dominated_convergence (fun w => beurlingBound α K K M R z w)
      hmeas (beurlingBound_integrable hα z)
      (fun n => Filter.Eventually.of_forall fun w =>
        norm_beurlingIntegrand_le_of_holder hα hM hK (huM n) (huK n) (huS n) (by simp) w)
      (Filter.Eventually.of_forall fun w => by
        have h1 : Filter.Tendsto (fun n => u n (z + w) - (bumpC w : ℂ) • u n z) Filter.atTop
            (nhds (f (z + w) - (bumpC w : ℂ) • f z)) :=
          (hconv (z + w)).sub (tendsto_const_nhds.smul (hconv z))
        have h2 := h1.const_smul ((w ^ 2)⁻¹ : ℂ)
        simpa only [beurlingIntegrand] using h2)
  -- `beurling` is the (translated) integral of `beurlingIntegrand`.
  have hbeur : ∀ n, beurling (u n) z
      = (-(Real.pi)⁻¹ : ℝ) • ∫ w, beurlingIntegrand (u n) z w := by
    intro n
    rw [beurling_eq_translate]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp [beurlingIntegrand, smul_eq_mul, mul_comm])
  have hbeurf : beurling f z = (-(Real.pi)⁻¹ : ℝ) • ∫ w, beurlingIntegrand f z w := by
    rw [beurling_eq_translate]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => by
      simp [beurlingIntegrand, smul_eq_mul, mul_comm])
  simp only [hbeur, hbeurf]
  exact hInt.const_smul ((-(Real.pi)⁻¹ : ℝ))

end

end Work.Beltrami
