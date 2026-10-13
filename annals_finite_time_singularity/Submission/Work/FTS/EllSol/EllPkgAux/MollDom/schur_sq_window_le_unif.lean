import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchurWindowDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchur_sq_le_window
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.schur_sq_window_le
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set

namespace Work.FTS.EllSol.EllPkgAux.MollDom

/-- **The logarithmic Schur bound on the window, uniformly in `z`.**

There is a *single* constant `A > 0` — independent of `z`, namely `2 δ M² + 1` where `M` is a
global bound for the continuous, compactly supported kernel `sKerd δ = deriv (sKer δ)` — such
that for every `z > 0` and every continuous `y`

  `(∫ t, sKerd δ (log z - t) · y t)² ≤ A ∫ t, 1_{|log z - t| ≤ δ} y t²`.

The kernel vanishes off the window `S = [log z - δ, log z + δ]`, where it is bounded by `M`, so
`∫_S (sKerd δ (log z - ·))² ≤ M² |S| = 2 δ M²`; Cauchy–Schwarz on the window
(`zSchur_sq_le_window`) gives the claim with a constant free of `z`. This is the uniform
version of `schur_sq_window_le`, whose constant `1 + ∫_S (sKerd δ (log z - ·))²` is a priori
`z`-dependent (it is in fact independent of `z` by translation invariance with respect to the
logarithmic variable, but it is the kernel bound that makes this explicit and uniform). -/
theorem schur_sq_window_le_unif (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℝ, 0 < z → ∀ y : ℝ → ℝ, Continuous y →
      (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2
        ≤ A * (∫ t : ℝ, if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0) := by
  -- A global bound on the kernel `sKerd δ`, together with its support.
  obtain ⟨M, hMnn, hk, hvan⟩ := exists_sKerd_bound hδ
  refine ⟨2 * δ * M ^ 2 + 1, by nlinarith [sq_nonneg M], ?_⟩
  intro z hz y hy
  -- The window on which the kernel lives.
  set S : Set ℝ := Set.Icc (Real.log z - δ) (Real.log z + δ) with hSdef
  have hSmeas : MeasurableSet S := by rw [hSdef]; exact measurableSet_Icc
  have hScomp : IsCompact S := by rw [hSdef]; exact isCompact_Icc
  have hmem : ∀ t : ℝ, t ∈ S ↔ |Real.log z - t| ≤ δ := by
    intro t
    rw [hSdef, Set.mem_Icc, abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  -- The windowed square of `y`, written as an indicator over `S`.
  have hsquares : (fun t : ℝ => if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0)
      = S.indicator (fun t : ℝ => (y t) ^ 2) := by
    funext t
    rw [Set.indicator_apply]
    by_cases ht : t ∈ S
    · rw [ite_eq_left ((hmem t).mp ht), ite_eq_left ht]
    · rw [ite_eq_right (fun hc => ht ((hmem t).mpr hc)), ite_eq_right ht]
  have hysq_int : MeasureTheory.Integrable
      (fun t : ℝ => if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0) := by
    rw [hsquares]
    exact ((hy.pow 2).continuousOn.integrableOn_compact hScomp).integrable_indicator hSmeas
  -- The windowed datum, written as an indicator over `S`, is a.e.-strongly measurable.
  have hsingle : (fun t : ℝ => if |Real.log z - t| ≤ δ then y t else 0) = S.indicator y := by
    funext t
    rw [Set.indicator_apply]
    by_cases ht : t ∈ S
    · rw [ite_eq_left ((hmem t).mp ht), ite_eq_left ht]
    · rw [ite_eq_right (fun hc => ht ((hmem t).mpr hc)), ite_eq_right ht]
  have hy_aesm : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => if |Real.log z - t| ≤ δ then y t else 0) MeasureTheory.volume := by
    rw [hsingle]
    exact (hy.stronglyMeasurable.indicator hSmeas).aestronglyMeasurable
  -- The uniform Cauchy–Schwarz bound on the window.
  have hmain := zSchur_sq_le_window (δ := δ) (z := z) (M := M) hδ hMnn hk hvan hz
    hysq_int hy_aesm
  have hWnn : 0 ≤ ∫ t : ℝ, if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0 := by
    refine integral_nonneg (fun t => ?_)
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0
  calc (∫ t : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd δ (Real.log z - t) * y t) ^ 2
      ≤ 2 * δ * M ^ 2 * (∫ t : ℝ, if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0) := hmain
    _ ≤ (2 * δ * M ^ 2 + 1) * (∫ t : ℝ, if |Real.log z - t| ≤ δ then (y t) ^ 2 else 0) :=
        mul_le_mul_of_nonneg_right (by linarith) hWnn

end Work.FTS.EllSol.EllPkgAux.MollDom
