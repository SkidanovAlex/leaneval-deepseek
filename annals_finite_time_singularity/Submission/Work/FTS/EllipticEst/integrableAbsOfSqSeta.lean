import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- Integrability transfer on the angular slice: if `g` is continuous on the open interval
`(0, π/2)` and `g²·sin(2θ)^{-η}` is integrable on `Iθ = [0, π/2]`, then `|g|` is integrable on
`Iθ`.  Declaration to be placed in namespace `Work.FTS.EllipticEst` (module
`Submission.Work.FTS.EllipticEst.integrableAbsOfSqSeta`).

Route: `1 ≤ sEta θ` for `θ ∈ (0, π/2)` (`η = 99/100 > 0`, `0 < sin(2θ) ≤ 1`, so
`Real.rpow_le_rpow_of_exponent_ge` gives `sin(2θ)^{-η} ≤ sin(2θ)^0 = 1`), and the endpoints are
a null set, so `g² ≤ g²·sEta` a.e. on `Iθ` — hence `g²` is integrable on `Iθ`
(`Integrable.mono'`, with `AEStronglyMeasurable` of `g²` from
`hg.aestronglyMeasurable measurableSet_Ioo` transferred across the a.e.-equal sets
`Iθ =ᵐ Ioo 0 (π/2)`, e.g. via `Measure.restrict_congr_set` as in `slice_cs_weighted`), and
finally `|g| ≤ g² + 1` pointwise with `g² + 1` integrable on the finite measure space `Iθ`. -/
theorem integrableAbsOfSqSeta {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |g θ|) Work.Spaces.Iθ := by
  -- ## Step 0: the two endpoints `{0, π/2}` are a null set, so `Iθ = [0,π/2]` agrees with the
  -- open interval `(0, π/2)` almost everywhere, and the integrals coincide.
  have hpair : MeasureTheory.volume ({(0 : ℝ), Real.pi / 2} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({(0 : ℝ), Real.pi / 2} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  have hst : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    filter_upwards [hpairab] with x hx
    refine propext ⟨?_, ?_⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc] at h
      rw [Set.mem_Ioo]
      exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
             lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
    · intro h
      rw [Work.Spaces.Iθ, Set.mem_Icc]
      rw [Set.mem_Ioo] at h
      exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hst
  have hint' : MeasureTheory.Integrable
      (fun θ : ℝ => (g θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    rw [← hms]; exact hint
  -- ## Step 1: on `(0, π/2)` the weight satisfies `1 ≤ sEta`, so `g² ≤ g² · sEta` a.e.
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsaesm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hg.aestronglyMeasurable measurableSet_Ioo
  have hsq_int : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    refine hint'.mono' (MeasureTheory.AEStronglyMeasurable.pow hsaesm 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have h1 : 1 ≤ Work.FTS.EllipticEst.sEta θ := by
      have h0 : 0 < Real.sin (2 * θ) := hsinpos θ hθ
      have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have h := Real.rpow_le_rpow_of_exponent_ge h0 hle1
        (show -(Work.Spaces.eta) ≤ (0 : ℝ) by have := Work.Spaces.eta_pos; linarith)
      simpa [Work.FTS.EllipticEst.sEta, Real.rpow_zero] using h
    have hsq : 0 ≤ (g θ) ^ 2 := sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hsq]
    simpa using mul_le_mul_of_nonneg_left h1 hsq
  -- ## Step 2: `|g| ≤ g² + 1` pointwise, and `g² + 1` is integrable (the slice has finite
  -- measure), so `|g|` is integrable on `(0, π/2)`.
  have habs_int : MeasureTheory.Integrable (fun θ : ℝ => |g θ|)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := by
    have hmaj : MeasureTheory.Integrable (fun θ : ℝ => (g θ) ^ 2 + 1)
        (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
      hsq_int.add (MeasureTheory.integrable_const (1 : ℝ))
    refine hmaj.mono' hsaesm.norm ?_
    filter_upwards with θ
    have h1 : |g θ| ≤ (g θ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (|g θ| - 1 / 2), sq_abs (g θ), abs_nonneg (g θ)]
    simpa only [Real.norm_eq_abs, abs_abs] using h1
  -- ## Step 3: transfer back to `Iθ`, which is `(0, π/2)` a.e.
  change MeasureTheory.Integrable (fun θ : ℝ => |g θ|)
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)
  rw [hms]; exact habs_int

end Work.FTS.EllipticEst
