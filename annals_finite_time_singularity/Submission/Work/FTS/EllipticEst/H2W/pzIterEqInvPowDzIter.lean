import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceFiber

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open Filter Set

/-!
# `∂_z^n F` in terms of `D_z^n F` for `n ≤ 3`

`D_z = z ∂_z`, so the iterated operators satisfy

* `∂_z F = z⁻¹ D_z F`,
* `∂_z² F = z⁻² (D_z² F − D_z F)`,
* `∂_z³ F = z⁻³ (D_z³ F − 3 D_z² F + 2 D_z F)`.

(These are the inverse-Sirling relations `z^n ∂_z^n = ∑_k s(n,k) D_z^k` for `n ≤ 3`, with
the signed Stirling numbers of the first kind `s(2,·) = (-1,1)`, `s(3,·) = (2,-3,1)`.)

The two `z`-expansions used in the proof are
`D_z²F = z ∂_z F + z² ∂_z²F` and `D_z³F = z ∂_z F + 3z²∂_z²F + z³∂_z³F`, both from the
product rule applied to the `z`-slices (`SmoothOpen.hasDerivAt_slice_pzIter`).
-/

/-- **The second-order expansion** `D_z²F = z ∂_z F + z² ∂_z²F` at an interior point. -/
private theorem DzIter_two_pt {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 F z θ
      = z * Work.Spaces.pzIter 1 F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
  have hg : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 1 F z' θ)
      (Work.Spaces.pzIter 2 F z θ) z := hF.hasDerivAt_slice_pzIter 1 hθ hz
  have hAz : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pzIter 1 F z' θ)
      (Work.Spaces.pzIter 1 F z θ + z * Work.Spaces.pzIter 2 F z θ) z := by
    have h := (hasDerivAt_id z).mul hg
    rw [show (id * fun z' : ℝ => Work.Spaces.pzIter 1 F z' θ)
        = fun z' => z' * Work.Spaces.pzIter 1 F z' θ from by funext z'; rfl] at h
    simpa using h
  rw [show Work.Spaces.DzIter 2 F z θ
        = z * deriv (fun z' : ℝ => z' * Work.Spaces.pzIter 1 F z' θ) z from rfl,
      hAz.deriv]
  ring

/-- **The third-order expansion** `D_z³F = z ∂_z F + 3z²∂_z²F + z³∂_z³F` at an interior
point. -/
private theorem DzIter_three_pt {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 3 F z θ
      = z * Work.Spaces.pzIter 1 F z θ + 3 * (z ^ 2 * Work.Spaces.pzIter 2 F z θ)
        + z ^ 3 * Work.Spaces.pzIter 3 F z θ := by
  -- derivative of the `z`-slice of `z' ↦ z' ∂_zF`
  have hA : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pzIter 1 F z' θ)
      (Work.Spaces.pzIter 1 F z θ + z * Work.Spaces.pzIter 2 F z θ) z := by
    have h := (hasDerivAt_id z).mul (hF.hasDerivAt_slice_pzIter 1 hθ hz)
    rw [show (id * fun z' : ℝ => Work.Spaces.pzIter 1 F z' θ)
        = fun z' => z' * Work.Spaces.pzIter 1 F z' θ from by funext z'; rfl] at h
    simpa using h
  -- derivative of the `z`-slice of `z' ↦ z'² ∂_z²F`
  have hB : HasDerivAt (fun z' : ℝ => z' ^ 2 * Work.Spaces.pzIter 2 F z' θ)
      (2 * z * Work.Spaces.pzIter 2 F z θ + z ^ 2 * Work.Spaces.pzIter 3 F z θ) z := by
    have hp : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have h3 : HasDerivAt (fun z' : ℝ => Work.Spaces.pzIter 2 F z' θ)
        (Work.Spaces.pzIter 3 F z θ) z := hF.hasDerivAt_slice_pzIter 2 hθ hz
    have h := hp.mul h3
    rw [show ((fun z' : ℝ => z' ^ 2) * fun z' : ℝ => Work.Spaces.pzIter 2 F z' θ)
        = fun z' => z' ^ 2 * Work.Spaces.pzIter 2 F z' θ from by funext z'; rfl] at h
    simpa using h
  have hsum : HasDerivAt
      (fun z' : ℝ => z' * Work.Spaces.pzIter 1 F z' θ
        + z' ^ 2 * Work.Spaces.pzIter 2 F z' θ)
      ((Work.Spaces.pzIter 1 F z θ + z * Work.Spaces.pzIter 2 F z θ)
        + (2 * z * Work.Spaces.pzIter 2 F z θ + z ^ 2 * Work.Spaces.pzIter 3 F z θ)) z :=
    hA.add hB
  -- the second-order expansion, as an eventual equality near `z`
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 2 F z' θ)
      =ᶠ[𝓝 z] (fun z' => z' * Work.Spaces.pzIter 1 F z' θ
        + z' ^ 2 * Work.Spaces.pzIter 2 F z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact DzIter_two_pt hF hz' hθ
  calc Work.Spaces.DzIter 3 F z θ
      = z * deriv (fun z' : ℝ => Work.Spaces.DzIter 2 F z' θ) z := rfl
    _ = z * deriv (fun z' : ℝ => z' * Work.Spaces.pzIter 1 F z' θ
          + z' ^ 2 * Work.Spaces.pzIter 2 F z' θ) z := by rw [hev.deriv_eq]
    _ = z * ((Work.Spaces.pzIter 1 F z θ + z * Work.Spaces.pzIter 2 F z θ)
          + (2 * z * Work.Spaces.pzIter 2 F z θ
            + z ^ 2 * Work.Spaces.pzIter 3 F z θ)) := by rw [hsum.deriv]
    _ = z * Work.Spaces.pzIter 1 F z θ + 3 * (z ^ 2 * Work.Spaces.pzIter 2 F z θ)
          + z ^ 3 * Work.Spaces.pzIter 3 F z θ := by ring

theorem pzIterEqInvPowDzIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.pzIter 0 F z θ = Work.Spaces.DzIter 0 F z θ)
      ∧ (Work.Spaces.pzIter 1 F z θ = z⁻¹ * Work.Spaces.DzIter 1 F z θ)
      ∧ (Work.Spaces.pzIter 2 F z θ
          = z⁻¹ ^ 2 * (Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ))
      ∧ (Work.Spaces.pzIter 3 F z θ
          = z⁻¹ ^ 3 * (Work.Spaces.DzIter 3 F z θ - 3 * Work.Spaces.DzIter 2 F z θ
              + 2 * Work.Spaces.DzIter 1 F z θ)) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hD1 : Work.Spaces.DzIter 1 F z θ = z * Work.Spaces.pzIter 1 F z θ := rfl
  have hD2 : Work.Spaces.DzIter 2 F z θ
      = z * Work.Spaces.pzIter 1 F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ :=
    DzIter_two_pt hF hz hθ
  have hD3 : Work.Spaces.DzIter 3 F z θ
      = z * Work.Spaces.pzIter 1 F z θ + 3 * (z ^ 2 * Work.Spaces.pzIter 2 F z θ)
        + z ^ 3 * Work.Spaces.pzIter 3 F z θ :=
    DzIter_three_pt hF hz hθ
  -- the two combinations that occur in the statement
  have hKey2 : Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ
      = z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
    rw [hD2, hD1]; ring
  have hKey3 : Work.Spaces.DzIter 3 F z θ - 3 * Work.Spaces.DzIter 2 F z θ
      + 2 * Work.Spaces.DzIter 1 F z θ = z ^ 3 * Work.Spaces.pzIter 3 F z θ := by
    rw [hD3, hD2, hD1]; ring
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [hD1, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul]
  · rw [hKey2, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hz0, one_pow, one_mul]
  · rw [hKey3, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hz0, one_pow, one_mul]

end Work.FTS.EllipticEst.H2W
