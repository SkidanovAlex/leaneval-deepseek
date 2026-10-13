import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllipticEst.Blocks.DzAgmonDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

noncomputable section

/-- **The integration by parts underlying the compactly supported weighted Agmon inequality.**
For `h` of class `C^∞` on `(0,∞)` vanishing off `[a,b]` with `0 < a`,

  `∫_0^∞ ρ(z)(z h')² = - ∫_0^∞ (d/dz)(ρ z² h') · h`,   `ρ = W2 z = w(z)²`,

both boundary terms `ρ z² h' h` at `0` and at `∞` vanishing because `h` is compactly supported
inside `(0,∞)`.  This is `integral_Ioi_mul_deriv_eq_deriv_mul` with `u = ρ z² h'` and `v = h`. -/
theorem AgmonIBP {h : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ z, z ∉ Set.Icc a b → h z = 0)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi (0 : ℝ))) :
    (∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.Blocks.W2 z * (z * deriv h z) ^ 2)
      = - ∫ z in Set.Ioi (0 : ℝ),
          deriv (fun y : ℝ => Work.FTS.EllipticEst.Blocks.W2 y * y ^ 2 * deriv h y) z
            * h z := by
  have hne : Work.Stability.smoothOrder ≠ 0 := by simp [Work.Stability.smoothOrder]
  -- `ρ` is `C^∞` on `(0,∞)` (closed form `(1+z)⁴/z⁴`)
  have hW2inf : ContDiffOn ℝ Work.Stability.smoothOrder W2 (Set.Ioi (0:ℝ)) := by
    have hform : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z : ℝ => (1 + z) ^ 4 / z ^ 4) (Set.Ioi (0:ℝ)) := by
      apply ContDiffOn.div
      · fun_prop
      · fun_prop
      · intro z hz; exact pow_ne_zero 4 (ne_of_gt hz)
    exact hform.congr (fun z _ => W2_eq z)
  -- `h` is `C^∞`, so is `h'`, so is the coefficient `u := ρ z² h'`
  have hdhinf : ContDiffOn ℝ Work.Stability.smoothOrder (deriv h) (Set.Ioi (0:ℝ)) :=
    hcd.deriv_of_isOpen isOpen_Ioi (by simp [Work.Stability.smoothOrder])
  have hUinf : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun y : ℝ => W2 y * y ^ 2 * deriv h y) (Set.Ioi (0:ℝ)) :=
    (hW2inf.mul (by fun_prop)).mul hdhinf
  have hU1 : ContDiffOn ℝ 1 (fun y : ℝ => W2 y * y ^ 2 * deriv h y) (Set.Ioi (0:ℝ)) :=
    hUinf.of_le (by simp [Work.Stability.smoothOrder])
  -- differentiability of `h` and of `u` on `(0,∞)`
  have hderivAt : ∀ z : ℝ, 0 < z → HasDerivAt h (deriv h z) z := fun z hz =>
    ((hcd.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have huDerivAt : ∀ z : ℝ, 0 < z →
      HasDerivAt (fun y : ℝ => W2 y * y ^ 2 * deriv h y)
        (deriv (fun y : ℝ => W2 y * y ^ 2 * deriv h y) z) z := fun z hz =>
    ((hUinf.differentiableOn hne).differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  -- off the support, `h` vanishes on a neighbourhood, hence so does `h'`
  have hderiv_zero : ∀ z : ℝ, z ∉ Set.Icc a b → deriv h z = 0 := by
    intro z hz
    have hz' : z < a ∨ b < z := by
      simpa only [Set.mem_Icc, not_and_or, not_le] using hz
    rcases hz' with hlt | hgt
    · have hev : h =ᶠ[𝓝 z] fun _ : ℝ => (0:ℝ) := by
        filter_upwards [isOpen_Iio.mem_nhds hlt] with y hy
        exact hsupp y (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hy)
      rw [hev.deriv_eq]; simp
    · have hev : h =ᶠ[𝓝 z] fun _ : ℝ => (0:ℝ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hgt] with y hy
        exact hsupp y (by
          simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hy)
      rw [hev.deriv_eq]; simp
  have hsub : Set.Icc a b ⊆ Set.Ioi (0:ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  have hcontW : ContinuousOn W2 (Set.Icc a b) := hW2inf.continuousOn.mono hsub
  have hcontDh : ContinuousOn (deriv h) (Set.Icc a b) := hdhinf.continuousOn.mono hsub
  have hcontH : ContinuousOn h (Set.Icc a b) := hcd.continuousOn.mono hsub
  have hcontDU : ContinuousOn (deriv (fun y : ℝ => W2 y * y ^ 2 * deriv h y)) (Set.Icc a b) :=
    (hU1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  -- integrability of the two products over `(0,∞)` (both are supported in `[a,b]`)
  have hInt1 : IntegrableOn (fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * deriv h z) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact ((hcontW.mul (continuousOn_id.pow 2)).mul hcontDh).mul hcontDh
    · intro z hz
      rw [hderiv_zero z hz]; ring
  have hInt2 : IntegrableOn (fun z : ℝ =>
      deriv (fun y : ℝ => W2 y * y ^ 2 * deriv h y) z * h z) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_continuousOn_Icc_of_eq_zero_off (a := a) (b := b) ?_ ?_
    · exact hcontDU.mul hcontH
    · intro z hz; rw [hsupp z hz]; ring
  -- the boundary term `u * h = ρ z² h' h` vanishes at both ends
  have hTend0 : Tendsto (fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * h z) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hev : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝[>] (0:ℝ)]
        (fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * h z) := by
      filter_upwards [Ioo_mem_nhdsGT ha] with z hz
      rw [hsupp z (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hz.2)]
      ring
    exact tendsto_const_nhds.congr' hev
  have hTendTop : Tendsto (fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * h z) atTop (𝓝 0) := by
    have hev : (fun _ : ℝ => (0:ℝ)) =ᶠ[atTop]
        (fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * h z) := by
      filter_upwards [eventually_gt_atTop b] with z hz
      rw [hsupp z (by
        simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inr hz)]
      ring
    exact tendsto_const_nhds.congr' hev
  -- integration by parts on `(0,∞)` with `u = ρ z² h'`, `v = h`
  have hkey := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0:ℝ)) (a' := (0:ℝ)) (b' := (0:ℝ))
      (u := fun y : ℝ => W2 y * y ^ 2 * deriv h y)
      (u' := deriv (fun y : ℝ => W2 y * y ^ 2 * deriv h y))
      (v := h) (v' := deriv h)
      huDerivAt hderivAt hInt1 hInt2 hTend0 hTendTop
  rw [show (fun z : ℝ => W2 z * (z * deriv h z) ^ 2)
      = fun z : ℝ => (W2 z * z ^ 2 * deriv h z) * deriv h z from funext fun z => by ring,
    hkey]
  ring

end

end Work.FTS.EllipticEst.Blocks
