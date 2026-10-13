import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.eFam_energy_bound
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.EllipticEst.Honest.HonEnergyAux
import Submission.Work.FTS.GalBasis.cc.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

/-- The Dirichlet eigenfamily grows at most linearly: `|eFam m θ| ≤ 3 (m+1)` on `Iθ`. -/
lemma abs_eFam_le_three (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ 3 * ((m : ℝ) + 1) := by
  rw [Work.Spaces.Iθ] at hθ
  obtain ⟨h0, h1⟩ := hθ
  rcases eq_or_lt_of_le h0 with h0' | h0'
  · rw [← h0', Work.FTS.PhiStar.Series.eFam_zero m, abs_zero]
    positivity
  rcases eq_or_lt_of_le h1 with h1' | h1'
  · rw [h1', Work.FTS.PhiStar.Series.eFam_pi_half m, abs_zero]
    positivity
  · calc |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ Real.sqrt (Work.FTS.PhiStar.Series.EB.Npsi m) :=
          Work.FTS.PhiStar.Series.EB.eFam_abs_le_sqrt_N m ⟨h0', h1'⟩
      _ ≤ 3 * ((m : ℝ) + 1) := by
          have hle : Work.FTS.PhiStar.Series.EB.Npsi m ≤ (3 * ((m : ℝ) + 1)) ^ 2 := by
            have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
            rw [Work.FTS.PhiStar.Series.EB.Npsi]
            nlinarith [hm, sq_nonneg (m : ℝ)]
          calc Real.sqrt (Work.FTS.PhiStar.Series.EB.Npsi m)
              ≤ Real.sqrt ((3 * ((m : ℝ) + 1)) ^ 2) := Real.sqrt_le_sqrt hle
            _ = 3 * ((m : ℝ) + 1) := Real.sqrt_sq (by positivity)

/-- The Gram bound: the `sEta`-weighted `L²` norm of a finite mode sum is bounded by the
`ℓ¹`-type sum `∑ (m+1)|b m|` with constant `9 = 3²`.

The proof is pointwise: `|eFam m θ| ≤ 3(m+1)` on `Iθ`, hence
`|∑_m b m eFam m θ| ≤ ∑_m |b m| · 3(m+1) = 3 S`, so the integrand is dominated by `9 S² σ`. -/
theorem angGram_modeSum {N : ℕ} (b : ℕ → ℝ) :
    (∫ θ in Work.Spaces.Iθ,
        (∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
      ≤ 9 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |b m|) ^ 2 := by
  set S : ℝ := ∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |b m| with hS
  -- the pointwise domination on `Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      (∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      ≤ (9 * S ^ 2) * Work.FTS.EllipticEst.sEta θ := by
    intro θ hθ
    have hs := Work.FTS.EllipticEst.Honest.sEta_nonneg hθ
    have h1 : |∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ 3 * S := by
      calc |∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ ∑ m ∈ Finset.range (N + 1),
              |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ m ∈ Finset.range (N + 1),
              |b m| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| :=
            Finset.sum_congr rfl fun m _ => abs_mul _ _
        _ ≤ ∑ m ∈ Finset.range (N + 1), |b m| * (3 * ((m : ℝ) + 1)) :=
            Finset.sum_le_sum fun m _ =>
              mul_le_mul_of_nonneg_left (abs_eFam_le_three m hθ) (abs_nonneg _)
        _ = 3 * S := by
            rw [hS, Finset.mul_sum]
            exact Finset.sum_congr rfl fun m _ => by ring
    have h2 : (∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
        ≤ 9 * S ^ 2 := by
      have hle := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
      have h3 : (3 * S) ^ 2 = 9 * S ^ 2 := by ring
      rw [h3] at hle
      exact hle
    exact mul_le_mul_of_nonneg_right h2 hs
  -- integrability of the majorant
  have hintG : IntegrableOn
      (fun θ => (9 * S ^ 2) * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Honest.sEta_integrableOn.const_mul _
  -- measurability of the integrand
  have hcont : Continuous
      (fun θ => (∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2) :=
    (continuous_finsetSum _ fun m _ =>
      continuous_const.mul (Work.FTS.PhiStar.Series.continuous_eFam m)).pow 2
  have haesm : AEStronglyMeasurable
      (fun θ => (∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (volume.restrict Work.Spaces.Iθ) :=
    hcont.aestronglyMeasurable.mul
      (Work.FTS.EllipticEst.Honest.sEta_integrableOn.1)
  -- integrability of the integrand
  have hintF : IntegrableOn
      (fun θ => (∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hintG haesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hFnn : 0 ≤ (∑ m ∈ Finset.range (N + 1),
        b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Work.FTS.EllipticEst.sEta θ :=
      mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ)
    rw [Real.norm_eq_abs, abs_of_nonneg hFnn]
    exact hpt θ hθ
  calc (∫ θ in Work.Spaces.Iθ,
        (∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, (9 * S ^ 2) * Work.FTS.EllipticEst.sEta θ :=
        MeasureTheory.setIntegral_mono_on hintF hintG measurableSet_Icc hpt
    _ = 9 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) * S ^ 2 := by
        rw [MeasureTheory.integral_const_mul]; ring
    _ = 9 * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)
          * (∑ m ∈ Finset.range (N + 1), ((m : ℝ) + 1) * |b m|) ^ 2 := by rw [hS]

end Work.FTS.ClassC
