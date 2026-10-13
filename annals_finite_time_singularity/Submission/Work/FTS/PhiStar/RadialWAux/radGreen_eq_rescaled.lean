/-
# `radGreen_eq_rescaled` — the rescaled form of the radial Green's function

`radGreen α m c z = K·(z^{-q}·∫₀^z c t^{q-1} + z^{p}·∫_{Ioi z} c t^{-p-1})`, `K = 1/(α(4m+5))`.
Substituting `t = z u` in both integrals (`intervalIntegral.integral_comp_mul_left` on `(0,1)`,
`MeasureTheory.integral_comp_mul_left_Ioi` on `Ioi 1`) turns it into

  `radGreen α m c z = K·(radPhi α m c z + radPsi α m c z)`,

with `radPhi z = ∫₀¹ c(zu)u^{q-1} du` and `radPsi z = ∫_{Ioi 1} c(zu)u^{-p-1} du`.

The two substitution lemmas are proved here for a *general* exponent `s` and a *general* `c`
(no regularity of `c` is needed: both are exact measure-theoretic changes of variables), namely

  `∫ u in (0)..1, c (z*u) * u^s = z^{-(s+1)} · ∫ t in (0)..z, c t * t^s`,
  `∫ u in Ioi 1, c (z*u) * u^s = z^{-(s+1)} · ∫ t in Ioi z, c t * t^s`      (`z > 0`);
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.PhiStar.RadialWAux.Defs
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

/-- Change of variables `t = z u` for the interval integral over `(0,1)`. -/
lemma integral_comp_mul_left_zero_one (f : ℝ → ℝ) {z : ℝ} (hz : z ≠ 0) :
    ∫ u in (0 : ℝ)..1, f (z * u) = z⁻¹ * ∫ t in (0 : ℝ)..z, f t := by
  have h := intervalIntegral.integral_comp_mul_left (f := f) (a := (0 : ℝ)) (b := (1 : ℝ))
    (c := z) hz
  simpa using h

/-- Change of variables `t = z u` for the set integral over `Ioi 1`. -/
lemma integral_comp_mul_left_Ioi_one (f : ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ u in Set.Ioi (1 : ℝ), f (z * u) = z⁻¹ * ∫ t in Set.Ioi z, f t := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi f (1 : ℝ) hz
  simpa using h

/-- The rescaled form of `∫₀^z c t t^s dt`:
`∫ u in (0)..1, c (z*u) * u^s = z^{-(s+1)} · ∫ t in (0)..z, c t * t^s` for `z > 0`. -/
lemma integral_zero_one_rpow (c : ℝ → ℝ) (s : ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ u in (0 : ℝ)..1, c (z * u) * u ^ s
      = z ^ (-(s + 1)) * ∫ t in (0 : ℝ)..z, c t * t ^ s := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hsub := integral_comp_mul_left_zero_one (fun t => c t * t ^ s) hz0
  have hcongr : ∫ u in (0 : ℝ)..1, c (z * u) * (z * u) ^ s
      = ∫ u in (0 : ℝ)..1, z ^ s * (c (z * u) * u ^ s) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 ≤ u := by
      have h1 : u ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
      exact h1.1
    show c (z * u) * (z * u) ^ s = z ^ s * (c (z * u) * u ^ s)
    rw [Real.mul_rpow (le_of_lt hz) hu0]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul] at hsub
  have h1 : z ^ (-s) * z ^ s = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  have h2 : z ^ (-s) * z⁻¹ = z ^ (-(s + 1)) := by
    rw [← Real.rpow_neg_one z, ← Real.rpow_add hz]
    congr 1
    ring
  calc ∫ u in (0 : ℝ)..1, c (z * u) * u ^ s
      = z ^ (-s) * (z ^ s * ∫ u in (0 : ℝ)..1, c (z * u) * u ^ s) := by
        rw [← mul_assoc, h1, one_mul]
    _ = z ^ (-s) * (z⁻¹ * ∫ t in (0 : ℝ)..z, c t * t ^ s) := by rw [hsub]
    _ = z ^ (-(s + 1)) * ∫ t in (0 : ℝ)..z, c t * t ^ s := by
        rw [← mul_assoc, h2]

/-- The rescaled form of `∫_{Ioi z} c t t^s dt`:
`∫ u in Ioi 1, c (z*u) * u^s = z^{-(s+1)} · ∫ t in Ioi z, c t * t^s` for `z > 0`. -/
lemma integral_Ioi_one_rpow (c : ℝ → ℝ) (s : ℝ) {z : ℝ} (hz : 0 < z) :
    ∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ s
      = z ^ (-(s + 1)) * ∫ t in Set.Ioi z, c t * t ^ s := by
  have hsub := integral_comp_mul_left_Ioi_one (fun t => c t * t ^ s) hz
  have hcongr : ∫ u in Set.Ioi (1 : ℝ), c (z * u) * (z * u) ^ s
      = ∫ u in Set.Ioi (1 : ℝ), z ^ s * (c (z * u) * u ^ s) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu1 : (1 : ℝ) < u := hu
    have hu0 : 0 ≤ u := le_of_lt (lt_trans zero_lt_one hu1)
    show c (z * u) * (z * u) ^ s = z ^ s * (c (z * u) * u ^ s)
    rw [Real.mul_rpow (le_of_lt hz) hu0]
    ring
  rw [hcongr, MeasureTheory.integral_const_mul] at hsub
  have h1 : z ^ (-s) * z ^ s = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  have h2 : z ^ (-s) * z⁻¹ = z ^ (-(s + 1)) := by
    rw [← Real.rpow_neg_one z, ← Real.rpow_add hz]
    congr 1
    ring
  calc ∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ s
      = z ^ (-s) * (z ^ s * ∫ u in Set.Ioi (1 : ℝ), c (z * u) * u ^ s) := by
        rw [← mul_assoc, h1, one_mul]
    _ = z ^ (-s) * (z⁻¹ * ∫ t in Set.Ioi z, c t * t ^ s) := by rw [hsub]
    _ = z ^ (-(s + 1)) * ∫ t in Set.Ioi z, c t * t ^ s := by
        rw [← mul_assoc, h2]

theorem radGreen_eq_rescaled {α : ℝ} (hα : 0 < α) (m : ℕ) (c : ℝ → ℝ) :
    ∀ z : ℝ, 0 < z →
      Work.FTS.PhiStar.Radial.radGreen α m c z
        = Work.FTS.PhiStar.RadialWAux.radK α m
            * (Work.FTS.PhiStar.RadialWAux.radPhi α m c z
              + Work.FTS.PhiStar.RadialWAux.radPsi α m c z) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  intro z hz
  have hq := integral_zero_one_rpow c (radQ α m - 1) hz
  have hp := integral_Ioi_one_rpow c (-(radP α m) - 1) hz
  simp only [Work.FTS.PhiStar.Radial.radGreen, radK, radPhi, radPsi] at *
  dsimp only [radQ, radP] at *
  have hexp1 : -(((2 * (m : ℝ) + 5) / α - 1) + 1) = -(2 * (m : ℝ) + 5) / α := by
    rw [sub_add_cancel, neg_div]
  have hexp2 : -(-(2 * (m : ℝ) / α) - 1 + 1) = 2 * (m : ℝ) / α := by
    rw [sub_add_cancel, neg_neg]
  rw [hq, hp, hexp1, hexp2]

end Work.FTS.PhiStar.RadialWAux
