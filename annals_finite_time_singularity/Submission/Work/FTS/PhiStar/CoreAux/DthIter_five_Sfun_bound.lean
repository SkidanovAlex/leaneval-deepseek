/-
Copyright: work module for the Elgindi finite-time singularity project.

# The fifth `D_θ`-iterate of `sin(2·)`

The companion of `Work.FTS.H2.DthIter_four_Sfun` / `Work.FTS.H2.abs_DthIter_Sfun_le` at
order `5`.  An explicit computation gives

`D_θ^5 (sin 2·) = sin(2θ) · (32 cos⁵(2θ) − 1856 cos³(2θ) sin²(2θ) + 1952 cos(2θ) sin⁴(2θ))`,

whence `|D_θ^5 (sin 2·)| ≤ 3840` on the open quadrant (and in fact everywhere).  The one
order-`5` bound which the `FlatW`/`F0` calculus of `FTS/PhiStar/CoreAux` consumes.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.H2.STFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real

namespace Work.FTS.PhiStar.CoreAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The derivative of the quartic profile occurring in `D_θ^4(sin 2·)`. -/
theorem deriv_five_Sfun_aux (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')
        * (16 * Real.cos (2 * θ') ^ 4 - 288 * Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2
          + 80 * Real.sin (2 * θ') ^ 4)) θ
      = 2 * Real.cos (2 * θ)
          * (16 * Real.cos (2 * θ) ^ 4 - 288 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2
            + 80 * Real.sin (2 * θ) ^ 4)
        + Real.sin (2 * θ)
          * (-1280 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ)
            + 1792 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 3) := by
  have hA : HasDerivAt (fun θ' : ℝ => 16 * Real.cos (2 * θ') ^ 4)
      (-128 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ)) θ := by
    convert ((Work.FTS.H2.hasDerivAt_cos_two θ).pow 4).const_mul (16 : ℝ) using 1
    ring
  have hB : HasDerivAt
      (fun θ' : ℝ => 288 * (Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2))
      (288 * (-4 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 3
        + 4 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ))) θ := by
    have h := (((Work.FTS.H2.hasDerivAt_cos_two θ).pow 2).mul
      ((Work.FTS.H2.hasDerivAt_sin_two θ).pow 2)).const_mul (288 : ℝ)
    convert h using 1 <;>
      (try funext θ') <;> (try simp only [Pi.pow_apply, Pi.mul_apply]) <;> ring_nf
  have hC : HasDerivAt (fun θ' : ℝ => 80 * Real.sin (2 * θ') ^ 4)
      (640 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 3) θ := by
    convert ((Work.FTS.H2.hasDerivAt_sin_two θ).pow 4).const_mul (80 : ℝ) using 1
    ring
  have hQ : HasDerivAt (fun θ' : ℝ => 16 * Real.cos (2 * θ') ^ 4
      - 288 * Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2
      + 80 * Real.sin (2 * θ') ^ 4)
      (-1280 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ)
        + 1792 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 3) θ := by
    have h := (hA.sub hB).add hC
    convert h using 1 <;>
      (try funext θ') <;>
      (try simp only [Pi.pow_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]) <;> ring_nf
  have hS := Work.FTS.H2.hasDerivAt_sin_two θ
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ')
        * (16 * Real.cos (2 * θ') ^ 4 - 288 * Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2
          + 80 * Real.sin (2 * θ') ^ 4))
      = (fun θ' : ℝ => Real.sin (2 * θ')) * (fun θ' : ℝ => 16 * Real.cos (2 * θ') ^ 4
          - 288 * Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2
          + 80 * Real.sin (2 * θ') ^ 4) := rfl
  rw [hfun, (hS.mul hQ).deriv]

/-- `D_θ^5 (sin 2·)`, explicitly. -/
theorem DthIter_five_Sfun :
    Work.Spaces.DthIter 5 Work.FTS.H2.Sfun
      = fun _ θ => Real.sin (2 * θ)
          * (32 * Real.cos (2 * θ) ^ 5
              - 1856 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
              + 1952 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4) := by
  funext z θ
  rw [show Work.Spaces.DthIter 5 Work.FTS.H2.Sfun
      = Work.Spaces.Dth (Work.Spaces.DthIter 4 Work.FTS.H2.Sfun) from rfl,
    Work.FTS.H2.DthIter_four_Sfun]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => Real.sin (2 * θ')
      * (16 * Real.cos (2 * θ') ^ 4 - 288 * Real.cos (2 * θ') ^ 2 * Real.sin (2 * θ') ^ 2
        + 80 * Real.sin (2 * θ') ^ 4)) θ
      = Real.sin (2 * θ)
          * (32 * Real.cos (2 * θ) ^ 5
              - 1856 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
              + 1952 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4)
  rw [deriv_five_Sfun_aux θ]
  ring

/-- The fifth `D_θ`-iterate of `sin(2·)` is bounded by `3840` on the open quadrant. -/
theorem abs_DthIter_five_Sfun_le (z θ : ℝ) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    |Work.Spaces.DthIter 5 Work.FTS.H2.Sfun z θ| ≤ 3840 := by
  have hs : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
  have hc5 : |Real.cos (2 * θ) ^ 5| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc
  have hc3 : |Real.cos (2 * θ) ^ 3| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hc
  have hs2 : |Real.sin (2 * θ) ^ 2| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs
  have hs4 : |Real.sin (2 * θ) ^ 4| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hs
  have e1 : |(32 : ℝ) * Real.cos (2 * θ) ^ 5| ≤ 32 := by
    rw [abs_mul, show |(32 : ℝ)| = 32 by norm_num]
    nlinarith [hc5]
  have h32 : |Real.cos (2 * θ) ^ 3| * |Real.sin (2 * θ) ^ 2| ≤ 1 := by
    calc |Real.cos (2 * θ) ^ 3| * |Real.sin (2 * θ) ^ 2| ≤ 1 * 1 :=
          mul_le_mul hc3 hs2 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have e2 : |(1856 : ℝ) * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2| ≤ 1856 := by
    rw [show (1856 : ℝ) * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
        = 1856 * (Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2) from by ring,
      abs_mul, show |(1856 : ℝ)| = 1856 by norm_num, abs_mul]
    have h := mul_le_mul_of_nonneg_left h32 (by norm_num : (0:ℝ) ≤ 1856)
    linarith
  have h19 : |Real.cos (2 * θ)| * |Real.sin (2 * θ) ^ 4| ≤ 1 := by
    calc |Real.cos (2 * θ)| * |Real.sin (2 * θ) ^ 4| ≤ 1 * 1 :=
          mul_le_mul hc hs4 (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have e3 : |(1952 : ℝ) * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4| ≤ 1952 := by
    rw [show (1952 : ℝ) * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4
        = 1952 * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4) from by ring,
      abs_mul, show |(1952 : ℝ)| = 1952 by norm_num, abs_mul]
    have h := mul_le_mul_of_nonneg_left h19 (by norm_num : (0:ℝ) ≤ 1952)
    linarith
  have e4 := Work.FTS.H2.abs_sub_le_abs_add ((32 : ℝ) * Real.cos (2 * θ) ^ 5)
    ((1856 : ℝ) * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2)
  have e5 := abs_add_le (((32 : ℝ) * Real.cos (2 * θ) ^ 5
      - (1856 : ℝ) * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2))
    ((1952 : ℝ) * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4)
  have hpoly : |32 * Real.cos (2 * θ) ^ 5
      - 1856 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
      + 1952 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4| ≤ 3840 := by
    linarith
  have hval : Work.Spaces.DthIter 5 Work.FTS.H2.Sfun z θ
      = Real.sin (2 * θ)
          * (32 * Real.cos (2 * θ) ^ 5
              - 1856 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
              + 1952 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4) := by
    rw [DthIter_five_Sfun]
  rw [hval, abs_mul]
  calc |Real.sin (2 * θ)| * |32 * Real.cos (2 * θ) ^ 5
        - 1856 * Real.cos (2 * θ) ^ 3 * Real.sin (2 * θ) ^ 2
        + 1952 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 4|
      ≤ 1 * 3840 :=
        mul_le_mul hs hpoly (abs_nonneg _) (by norm_num)
    _ = 3840 := by norm_num

theorem DthIter_five_Sfun_bound : ∃ M : ℝ, 0 < M ∧ ∀ z θ : ℝ, 0 < θ → θ < Real.pi / 2 → |Work.Spaces.DthIter 5 Work.FTS.H2.Sfun z θ| ≤ M := by
  exact ⟨3840, by norm_num, fun z θ hθ hθ' => abs_DthIter_five_Sfun_le z θ hθ hθ'⟩

end Work.FTS.PhiStar.CoreAux
