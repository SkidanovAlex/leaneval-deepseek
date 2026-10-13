import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

/-- The angular weight `sEta θ = sin(2θ)^{-η}` is at least `1` on the open slice
`(0, π/2)`: there `0 < sin(2θ) ≤ 1` and `-η ≤ 0`, so `sin(2θ)^{-η} ≥ sin(2θ)^0 = 1`
(`Real.rpow_le_rpow_of_exponent_ge` run backwards). -/
private lemma one_le_sEta_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.sEta θ := by
  have h0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hη : -(Work.Spaces.eta) ≤ (0 : ℝ) := by
    have := Work.Spaces.eta_pos; linarith
  have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1 hη
  simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h

/-- Integrability transfer on the angular slice, weak-hypothesis form: if `g` is only
a.e.-strongly measurable on `(0, π/2)` (no continuity needed) and `g²·sin(2θ)^{-η}` is
integrable on the closed slice `Iθ = [0, π/2]`, then `|g|` is integrable on the open
interval `(0, π/2)`.

Since `η = 99/100 > 0` and `0 < sin(2θ) ≤ 1` on `(0,π/2)`, the weight satisfies `1 ≤ sEta`
there, so `g² ≤ g²·sEta` pointwise; hence `g²` is integrable on `(0,π/2)`.  The endpoints
`{0, π/2}` are a null set, so `Iθ` and `(0,π/2)` carry the same restricted measure and the
integrability hypothesis transports.  Finally `|g| ≤ g² + 1` pointwise and `g² + 1` is
integrable (the slice has finite measure). -/
theorem absIntegrableOfSqMulSeta {g : ℝ → ℝ}
    (hgm : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (h : MeasureTheory.IntegrableOn (fun θ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => |g θ|) (Set.Ioo 0 (Real.pi / 2)) := by
  -- ## Step 0: the two endpoints `{0, π/2}` are a null set, so `Iθ = [0,π/2]` agrees with the
  -- open interval `(0, π/2)` almost everywhere, and the restricted measures coincide.
  have hpair : MeasureTheory.volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro hmem
      rw [Work.Spaces.Iθ, Set.mem_Icc] at hmem
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne hmem.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne hmem.2 (fun hc => hx (Or.inr hc))⟩
    · intro hmem
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at hmem
      exact ⟨le_of_lt hmem.1, le_of_lt hmem.2⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hst
  have hint : MeasureTheory.Integrable
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hms]; exact h
  -- ## Step 1: on `(0, π/2)` the weight satisfies `1 ≤ sEta`, so `g² ≤ g² · sEta` a.e.
  have hsq_int : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine hint.mono' (hgm.pow 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := one_le_sEta_of_mem hθ
    have hsq : 0 ≤ (g θ) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hsq]
    simpa using mul_le_mul_of_nonneg_left h1 hsq
  -- ## Step 2: `|g| ≤ g² + 1` pointwise, and `g² + 1` is integrable (the slice has finite
  -- measure), so `|g|` is integrable on `(0, π/2)`.
  have hmaj : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2 + 1)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hsq_int.add (MeasureTheory.integrable_const (1 : ℝ))
  refine hmaj.mono' hgm.norm ?_
  filter_upwards with θ
  have h1 : |g θ| ≤ (g θ) ^ 2 + 1 := by
    nlinarith [sq_nonneg (|g θ| - 1 / 2), sq_abs (g θ), abs_nonneg (g θ)]
  simpa only [Real.norm_eq_abs, abs_abs] using h1

end Work.FTS.EllipticEst.remov.SourceBound
