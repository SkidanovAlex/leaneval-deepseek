/-
Copyright: work module for the Elgindi finite-time singularity project.

# Shared bookkeeping for the `∂_θ`-slice estimate `slice_d_bound`

The target `Work.FTS.EllipticEst.Blocks.slice_d_bound` bounds, pointwise on `Iθ = [0, π/2]`,

`(∂_θ u θ)² sin(2θ)^{-η}`  and  `(D_θ^i (∂_θ u) θ)² sin(2θ)^{-γ}`,  `1 ≤ i ≤ K`,

by a universal constant times `slicePhi α K u`, for a smooth slice `u` vanishing at `0` and
`π/2` (`v = sliceV u = u''`, `A = sliceA u = ∫ v² sin(2θ)^{-η}`).

This file collects the elementary facts shared by the several pieces of that proof:

* `sliceV_contDiffAt` — the second derivative of a smooth slice is `C^∞` at every `θ ∈ Iθ`
  (needed for the Leibniz rule `Lop_iter_mul`);
* `gam_lt_two`, `gam_le_two_add_eta` — the numerical bounds `1 < γ ≤ 11/10 < 2` and
  `γ ≤ 2 + η` for `α ∈ (0,1]`, which are exactly the exponent comparisons on `sin(2θ) ∈ [0,1]`
  used everywhere;
* `sin_two_rpow_two_sub_le_thEta`, `sin_two_rpow_two_sub_le_thGam` — the two comparisons
  `sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}` and `sin(2θ)^{2-γ} ≤ sin(2θ)^{-γ}` on `Iθ`;
* `sliceA_nonneg`, `slicePhi_nonneg`, `slicePhi_ge_Vterm`, `slicePhi_ge_gamterm` — the
  dominating function `slicePhi` dominates each of its two kinds of summand.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.sd_lop_iter_sin_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Blocks

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The open neighbourhood of `Iθ` on which a smooth slice is `C^∞` -/

/-- The open interval of `SliceSmooth`: the neighbourhood of the closed angular interval
`Iθ = [0, π/2]` on which a `SliceSmooth` slice is `C^∞`. -/
def sliceNbhd : Set ℝ := Set.Ioo (-1) (Real.pi / 2 + 1)

theorem Iθ_subset_sliceNbhd : Work.Spaces.Iθ ⊆ sliceNbhd := by
  intro x hx
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩

theorem isOpen_sliceNbhd : IsOpen sliceNbhd := isOpen_Ioo

theorem sliceNbhd_mem_nhds {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : sliceNbhd ∈ 𝓝 θ :=
  isOpen_sliceNbhd.mem_nhds (Iθ_subset_sliceNbhd hθ)

/-- `SliceSmooth u` is literally `ContDiffOn ℝ ⊤ u sliceNbhd`. -/
theorem sliceSmooth_iff_contDiffOn (u : ℝ → ℝ) :
    Work.FTS.EllipticEst.SliceSmooth u ↔ ContDiffOn ℝ ⊤ u sliceNbhd :=
  Iff.rfl

/-- The second derivative `sliceV u = u''` of a smooth slice is `C^∞` at every point of the
closed interval `Iθ`, because it is the second derivative of a `C^∞` function on the open
neighbourhood `sliceNbhd ⊇ Iθ`. -/
theorem sliceV_contDiffAt {u : ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SliceSmooth u) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    ContDiffAt ℝ ⊤ (Work.FTS.EllipticEst.sliceV u) θ := by
  have h1 : ContDiffOn ℝ ⊤ (deriv u) sliceNbhd :=
    hsm.deriv_of_isOpen isOpen_sliceNbhd (m := ⊤) (by simp)
  have h2 : ContDiffOn ℝ ⊤ (Work.FTS.EllipticEst.sliceV u) sliceNbhd :=
    h1.deriv_of_isOpen isOpen_sliceNbhd (m := ⊤) (by simp)
  exact h2.contDiffAt (sliceNbhd_mem_nhds hθ)

/-! ## The numerical bounds on `γ = gam α` for `α ∈ (0,1]` -/

theorem gam_lt_two {α : ℝ} (hα : α ≤ 1) : Work.Spaces.gam α < 2 := by
  rw [Work.Spaces.gam]; linarith

theorem gam_le_two_add_eta {α : ℝ} (hα : α ≤ 1) :
    Work.Spaces.gam α ≤ 2 + Work.Spaces.eta := by
  rw [Work.Spaces.gam, Work.Spaces.eta]; linarith

/-! ## The two exponent comparisons on `Iθ`

On `Iθ` one has `0 ≤ sin(2θ) ≤ 1`, so `θ ↦ sin(2θ)^p` is antitone in `p` on the positive
exponents (`sin_two_rpow_le_rpow`).  Since `γ = 1 + α/10 ∈ (1, 11/10]` we have
`2 - γ ∈ [9/10, 1) ⊂ (0, ∞)`, `-η ≤ 2 - γ` (`η = 99/100`, `2 - γ ≥ 9/10 > -η`) and
`-γ ≤ 2 - γ`; hence `sin(2θ)^{2-γ}` is dominated both by `sin(2θ)^{-η}` and by
`sin(2θ)^{-γ}`. -/

theorem sin_two_rpow_two_sub_le_thEta {α θ : ℝ} (h1 : Work.Spaces.gam α < 2)
    (h2 : Work.Spaces.gam α ≤ 2 + Work.Spaces.eta) (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) ≤ Work.FTS.EllipticEst.thEta θ := by
  rw [Work.FTS.EllipticEst.thEta]
  exact Work.FTS.EllipticEst.sin_two_rpow_le_rpow (by linarith) (by linarith) hθ

theorem sin_two_rpow_two_sub_le_thGam {α θ : ℝ} (h1 : Work.Spaces.gam α < 2)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) ≤ Work.FTS.EllipticEst.thGam α θ := by
  rw [Work.FTS.EllipticEst.thGam]
  exact Work.FTS.EllipticEst.sin_two_rpow_le_rpow (by linarith) (by linarith) hθ

/-! ## The dominating function `slicePhi` dominates its summands -/

theorem sliceA_nonneg (u : ℝ → ℝ) : 0 ≤ Work.FTS.EllipticEst.sliceA u := by
  rw [Work.FTS.EllipticEst.sliceA]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Icc
    (fun x hx => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hx))

/-- The sum of the `γ`-weighted terms of `slicePhi` is nonnegative on `Iθ`. -/
theorem slicePhi_sum_nonneg (α : ℝ) (K : ℕ) (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ ∑ m ∈ Finset.Icc 1 K,
      (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ :=
  Finset.sum_nonneg (fun m _ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))

theorem slicePhi_nonneg (α : ℝ) (K : ℕ) (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.slicePhi α K u θ := by
  have hsum := slicePhi_sum_nonneg α K u hθ
  have hA := sliceA_nonneg u
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
  have hC : 0 ≤ Work.FTS.EllipticEst.sliceA u * (Work.FTS.EllipticEst.thEta θ
      + Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
      + Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α)) :=
    mul_nonneg hA (add_nonneg (add_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ)
      (Real.rpow_nonneg hs _)) (Real.rpow_nonneg hs _))
  have hV : 0 ≤ (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
  rw [Work.FTS.EllipticEst.slicePhi]
  linarith

theorem slicePhi_ge_Vterm (α : ℝ) (K : ℕ) (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
      ≤ Work.FTS.EllipticEst.slicePhi α K u θ := by
  have hsum := slicePhi_sum_nonneg α K u hθ
  have hA := sliceA_nonneg u
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
  have hC : 0 ≤ Work.FTS.EllipticEst.sliceA u * (Work.FTS.EllipticEst.thEta θ
      + Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
      + Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α)) :=
    mul_nonneg hA (add_nonneg (add_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ)
      (Real.rpow_nonneg hs _)) (Real.rpow_nonneg hs _))
  rw [Work.FTS.EllipticEst.slicePhi]
  linarith

theorem slicePhi_ge_gamterm (α : ℝ) (K m : ℕ) (u : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hm : m ∈ Finset.Icc 1 K) :
    (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ ≤ Work.FTS.EllipticEst.slicePhi α K u θ := by
  set F : ℕ → ℝ := fun m' => (Work.FTS.EllipticEst.LopIter m' (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
      * Work.FTS.EllipticEst.thGam α θ with hF
  have hle : F m ≤ ∑ m' ∈ Finset.Icc 1 K, F m' :=
    Finset.single_le_sum (f := F)
      (fun m' _ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ)) hm
  have hsum : 0 ≤ ∑ m' ∈ Finset.Icc 1 K, F m' :=
    Finset.sum_nonneg (fun m' _ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))
  have hA := sliceA_nonneg u
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
  have hC : 0 ≤ Work.FTS.EllipticEst.sliceA u * (Work.FTS.EllipticEst.thEta θ
      + Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
      + Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α)) :=
    mul_nonneg hA (add_nonneg (add_nonneg (Work.FTS.EllipticEst.thEta_nonneg hθ)
      (Real.rpow_nonneg hs _)) (Real.rpow_nonneg hs _))
  have hV : 0 ≤ (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thEta_nonneg hθ)
  rw [Work.FTS.EllipticEst.slicePhi, ← hF]
  linarith

end Work.FTS.EllipticEst.Blocks
