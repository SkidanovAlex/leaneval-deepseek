import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

open MeasureTheory Set Filter

/-- Elementary pointwise bound: for `z > 0`, `(z²/(1+z)⁴)² = z⁴/(1+z)⁸ ≤ (1+z)^{-4}`,
because `z⁴ ≤ (1+z)⁴`. -/
private theorem rl1_ptwise (z : ℝ) (hz : 0 < z) :
    (z ^ 2 / (1 + z) ^ 4) ^ 2 ≤ (z + 1) ^ (-4 : ℝ) := by
  have hzp : (0 : ℝ) < z + 1 := by linarith
  have hpow : z ^ 4 ≤ (1 + z) ^ 4 := pow_le_pow_left₀ (le_of_lt hz) (by linarith) 4
  have hLHS : (z ^ 2 / (1 + z) ^ 4) ^ 2 = z ^ 4 / (1 + z) ^ 8 := by field_simp
  have hRHS : (z + 1) ^ (-4 : ℝ) = (1 + z) ^ 4 / (1 + z) ^ 8 := by
    rw [show (-4 : ℝ) = -(4 : ℕ) by norm_num, Real.rpow_neg (le_of_lt hzp) (4 : ℕ),
      Real.rpow_natCast]
    field_simp
    ring
  rw [hLHS, hRHS]
  exact div_le_div_of_nonneg_right hpow (by positivity)

/-- `∫_0^∞ (1+z)^{-4} dz = 1/3` (both integrability and value). -/
private theorem rl1_majorant_integral :
    (∫ z in Ioi (0 : ℝ), (z + 1) ^ (-4 : ℝ)) = 1 / 3 := by
  have hMint : IntegrableOn (fun z : ℝ => (z + 1) ^ (-4 : ℝ)) (Ioi (0 : ℝ)) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -4) (c := 0) (m := 1) (by norm_num) (by norm_num)
  have hd : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (t + 1) ^ (-3 : ℝ) / (-3)) ((x + 1) ^ (-4 : ℝ)) x := by
    intro x hx
    have hx1 : x + 1 ≠ 0 := by
      have : (0 : ℝ) ≤ x := hx
      linarith
    have h2 := (((hasDerivAt_id x).add_const (1 : ℝ)).rpow_const (p := (-3 : ℝ))
      (Or.inl hx1)).div_const (-3)
    simp only [id_eq] at h2
    have hnum : (1 * (-3 : ℝ) * (x + 1) ^ ((-3 : ℝ) - 1)) / (-3) = (x + 1) ^ (-4 : ℝ) := by
      rw [show ((-3 : ℝ) - 1) = -4 by norm_num]
      field_simp
    rw [hnum] at h2
    exact h2
  have ht : Tendsto (fun t : ℝ => (t + 1) ^ (-3 : ℝ) / (-3)) atTop (nhds 0) := by
    have h1 : Tendsto (fun t : ℝ => (t + 1) ^ (-3 : ℝ)) atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (y := 3) (by norm_num)).comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
    simpa using h1.div_const (-3)
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' (f := fun t : ℝ => (t + 1) ^ (-3 : ℝ) / (-3))
    (f' := fun x : ℝ => (x + 1) ^ (-4 : ℝ)) (a := (0 : ℝ)) (m := 0) hd hMint ht
  rw [hmain]
  norm_num

theorem BqSqIntegral :
    MeasureTheory.MemLp (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) 2
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
    (∫ z in Set.Ioi (0 : ℝ), (z ^ 2 / (1 + z) ^ 4) ^ 2) ≤ 2 := by
  have hmeas : Measurable (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) := by fun_prop
  have haesm : AEStronglyMeasurable (fun z : ℝ => z ^ 2 / (1 + z) ^ 4)
      (volume.restrict (Ioi (0 : ℝ))) := hmeas.aestronglyMeasurable
  have hMint : IntegrableOn (fun z : ℝ => (z + 1) ^ (-4 : ℝ)) (Ioi (0 : ℝ)) :=
    integrableOn_add_rpow_Ioi_of_lt (a := -4) (c := 0) (m := 1) (by norm_num) (by norm_num)
  have hSqmeas : AEStronglyMeasurable (fun z : ℝ => (z ^ 2 / (1 + z) ^ 4) ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have : Measurable (fun z : ℝ => (z ^ 2 / (1 + z) ^ 4) ^ 2) := by fun_prop
    exact this.aestronglyMeasurable
  have hSqint : Integrable (fun z : ℝ => (z ^ 2 / (1 + z) ^ 4) ^ 2)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine Integrable.mono' hMint hSqmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact rl1_ptwise z hz
  constructor
  · rw [memLp_two_iff_integrable_sq haesm]
    exact hSqint
  · have hval := rl1_majorant_integral
    calc ∫ z in Ioi (0 : ℝ), (z ^ 2 / (1 + z) ^ 4) ^ 2
        ≤ ∫ z in Ioi (0 : ℝ), (z + 1) ^ (-4 : ℝ) :=
          setIntegral_mono_on hSqint hMint measurableSet_Ioi (fun z hz => rl1_ptwise z hz)
      _ = 1 / 3 := hval
      _ ≤ 2 := by norm_num

end Work.FTS.Nonlinear.Pieces.rl1Tools
