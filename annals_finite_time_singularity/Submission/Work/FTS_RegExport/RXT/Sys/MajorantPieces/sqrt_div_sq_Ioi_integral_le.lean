import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS_RegExport.RXT.Sys.MajorantPieces

/-- The majorant weight `√s/(1+s)²` is integrable on `(z, ∞)` and its integral is `≤ 3`,
for every `z ≥ 0`.

The pointwise bound `s^{1/2}/(1+s)² ≤ (1+s)^{-3/2}` (valid since `s ≤ 1+s`) reduces both
statements to the elementary improper integral `∫_z^∞ (1+s)^{-3/2} ds = 2(1+z)^{-1/2} ≤ 2`,
computed by the fundamental theorem of calculus with the antiderivative
`s ↦ -2(1+s)^{-1/2}`. -/
theorem sqrt_div_sq_Ioi_integral_le {z : ℝ} (hz : 0 ≤ z) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) ∧
      (∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) ≤ 3 := by
  have hmeas : Measurable (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) := by measurability
  -- the dominating function `(1+s)^{-3/2}` is integrable on `(z,∞)`
  have hg : IntegrableOn (fun s : ℝ => (1 + s) ^ (-((3 : ℝ) / 2))) (Set.Ioi z) := by
    have h := integrableOn_add_rpow_Ioi_of_lt (a := -((3 : ℝ) / 2)) (c := z)
      (m := (1 : ℝ)) (by norm_num) (by linarith)
    simpa [add_comm] using h
  -- pointwise bound
  have hle : ∀ s ∈ Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ (1 + s) ^ (-((3 : ℝ) / 2)) := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := le_of_lt (lt_of_le_of_lt hz (Set.mem_Ioi.mp hs))
    have h1 : (0 : ℝ) < 1 + s := by linarith
    have hbase : s ^ ((1 : ℝ) / 2) ≤ (1 + s) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hs0 (by linarith) (by norm_num)
    have hinv : (0 : ℝ) ≤ ((1 + s) ^ 2)⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_right hbase hinv
    have hpow : (1 + s) ^ ((1 : ℝ) / 2) * ((1 + s) ^ 2)⁻¹ = (1 + s) ^ (-((3 : ℝ) / 2)) := by
      rw [← Real.rpow_two, ← Real.rpow_neg (le_of_lt h1), ← Real.rpow_add h1]
      congr 1
      norm_num
    calc s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2
        = s ^ ((1 : ℝ) / 2) * ((1 + s) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ (1 + s) ^ ((1 : ℝ) / 2) * ((1 + s) ^ 2)⁻¹ := hmul
      _ = (1 + s) ^ (-((3 : ℝ) / 2)) := hpow
  have hf_int : IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) := by
    refine Integrable.mono' hg hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) ≤ s := le_of_lt (lt_of_le_of_lt hz (Set.mem_Ioi.mp hs))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hle s hs
  -- the exact value of the dominating integral
  have hIntEq : ∫ s in Set.Ioi z, (1 + s) ^ (-((3 : ℝ) / 2)) = 2 * (1 + z) ^ (-((1 : ℝ) / 2)) := by
    have hderiv : ∀ x ∈ Set.Ici z,
        HasDerivAt (fun s : ℝ => -2 * (1 + s) ^ (-((1 : ℝ) / 2))) ((1 + x) ^ (-((3 : ℝ) / 2))) x := by
      intro x hx
      have hxz : z ≤ x := Set.mem_Ici.mp hx
      have hpos : (0 : ℝ) < 1 + x := by linarith
      have hd0 : HasDerivAt (fun s : ℝ => 1 + s) (1 : ℝ) x := by
        simpa using (hasDerivAt_id x).const_add (1 : ℝ)
      have hd1 : HasDerivAt (fun s : ℝ => (1 + s) ^ (-((1 : ℝ) / 2)))
          (1 * (-((1 : ℝ) / 2)) * (1 + x) ^ (-((1 : ℝ) / 2) - 1)) x :=
        hd0.rpow_const (p := -((1 : ℝ) / 2)) (Or.inl (ne_of_gt hpos))
      have hd2 := hd1.const_mul (-2)
      have hexp : -((1 : ℝ) / 2) - 1 = -((3 : ℝ) / 2) := by norm_num
      rw [hexp] at hd2
      convert hd2 using 1
      ring
    have htend : Tendsto (fun s : ℝ => -2 * (1 + s) ^ (-((1 : ℝ) / 2))) atTop (𝓝 0) := by
      have hq : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
      have h1 : Tendsto (fun s : ℝ => (1 + s) ^ (-((1 : ℝ) / 2))) atTop (𝓝 0) := by
        simpa only [Function.comp_def, id_eq] using (tendsto_rpow_neg_atTop hq).comp
          (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
      simpa using h1.const_mul (-2)
    have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hg htend
    simpa using hmain
  refine ⟨hf_int, ?_⟩
  have hmono : ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤
      ∫ s in Set.Ioi z, (1 + s) ^ (-((3 : ℝ) / 2)) :=
    setIntegral_mono_on hf_int hg measurableSet_Ioi hle
  have hfin : (1 + z) ^ (-((1 : ℝ) / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  linarith

end Work.FTS_RegExport.RXT.Sys.MajorantPieces
