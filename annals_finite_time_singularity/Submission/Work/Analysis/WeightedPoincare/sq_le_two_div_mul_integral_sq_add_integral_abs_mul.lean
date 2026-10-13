import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Analysis.WeightedPoincare

/-- Auxiliary: `R z ^ 2 - R t ^ 2 = ∫ s in t..z, 2 * R s * R' s` for `t ∈ [z/2, z]`,
by the fundamental theorem of calculus. -/
theorem sub_sq_eq_integral_two_mul
    {R R' : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn R (Set.Icc (z / 2) z))
    (hder : ∀ t ∈ Set.Ioo (z / 2) z, HasDerivAt R (R' t) t)
    (hint : IntervalIntegrable (fun t => 2 * R t * R' t) MeasureTheory.volume (z / 2) z) :
    ∀ t ∈ Set.Icc (z / 2) z, R z ^ 2 - R t ^ 2 = ∫ s in t..z, 2 * R s * R' s := by
  have hhalf : (z / 2 : ℝ) ≤ z := by linarith
  intro t ht
  have htz : t ≤ z := ht.2
  have hcont' : ContinuousOn (R ^ 2) (Set.Icc t z) :=
    (hcont.mono (Set.Icc_subset_Icc ht.1 le_rfl)).pow 2
  have hder' : ∀ x ∈ Set.Ioo t z, HasDerivAt (R ^ 2) (2 * R x * R' x) x := by
    intro x hx
    have hx' : x ∈ Set.Ioo (z / 2) z := ⟨lt_of_le_of_lt ht.1 hx.1, hx.2⟩
    have h := (hder x hx').pow 2
    simpa using h
  have hint' : IntervalIntegrable (fun s => 2 * R s * R' s) MeasureTheory.volume t z :=
    hint.mono_set (by
      rw [Set.uIcc_of_le htz, Set.uIcc_of_le hhalf]
      exact Set.Icc_subset_Icc ht.1 le_rfl)
  have hftc := (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htz hcont' hder' hint').symm
  simpa using hftc

theorem sq_le_two_div_mul_integral_sq_add_integral_abs_mul
    {R R' : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn R (Set.Icc (z / 2) z))
    (hder : ∀ t ∈ Set.Ioo (z / 2) z, HasDerivAt R (R' t) t)
    (hint : IntervalIntegrable (fun t => 2 * R t * R' t) MeasureTheory.volume (z / 2) z)
    (hintabs : IntervalIntegrable (fun t => 2 * |R t * R' t|) MeasureTheory.volume (z / 2) z)
    (hintsq : IntervalIntegrable (fun t => R t ^ 2) MeasureTheory.volume (z / 2) z) :
    R z ^ 2 ≤ (2 / z) * (∫ t in (z / 2)..z, R t ^ 2)
      + ∫ t in (z / 2)..z, 2 * |R t * R' t| := by
  set C : ℝ := ∫ t in (z / 2)..z, 2 * |R t * R' t| with hC
  have hhalf : (z / 2 : ℝ) ≤ z := by linarith
  -- pointwise bound `R z ^ 2 ≤ R t ^ 2 + C`
  have hpt : ∀ t ∈ Set.Icc (z / 2) z, R z ^ 2 ≤ R t ^ 2 + C := by
    intro t ht
    have h1 := sub_sq_eq_integral_two_mul hz hcont hder hint t ht
    have hsub' : Set.uIcc t z ⊆ Set.uIcc (z / 2) z := by
      rw [Set.uIcc_of_le ht.2, Set.uIcc_of_le hhalf]
      exact Set.Icc_subset_Icc ht.1 le_rfl
    have h2 : ∫ s in t..z, 2 * R s * R' s ≤ ∫ s in t..z, 2 * |R s * R' s| :=
      intervalIntegral.integral_mono_on ht.2 (hint.mono_set hsub') (hintabs.mono_set hsub')
        (fun x _ => by
          have h : R x * R' x ≤ |R x * R' x| := le_abs_self _
          linarith)
    have h3 : ∫ s in t..z, 2 * |R s * R' s| ≤ C := by
      rw [hC]
      exact intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
        (Filter.Eventually.of_forall (fun x => by positivity)) hintabs
    linarith
  -- integrate the pointwise bound over `[z/2, z]`
  have hconstI : IntervalIntegrable (fun _ : ℝ => R z ^ 2) MeasureTheory.volume (z / 2) z :=
    intervalIntegrable_const
  have hsumI : IntervalIntegrable (fun t : ℝ => R t ^ 2 + C) MeasureTheory.volume (z / 2) z :=
    hintsq.add intervalIntegrable_const
  have key := intervalIntegral.integral_mono_on hhalf hconstI hsumI hpt
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add hintsq intervalIntegrable_const,
    intervalIntegral.integral_const] at key
  have hzd : z - z / 2 = z / 2 := by ring
  rw [hzd, smul_eq_mul, smul_eq_mul] at key
  have key2 : R z ^ 2 ≤ (2 * (∫ t in (z / 2)..z, R t ^ 2) + z * C) / z := by
    rw [le_div_iff₀ hz]
    linarith
  have hfr : (2 * (∫ t in (z / 2)..z, R t ^ 2) + z * C) / z
      = (2 / z) * (∫ t in (z / 2)..z, R t ^ 2) + C := by
    field_simp
  rw [← hfr]
  exact key2

end Work.Analysis.WeightedPoincare
