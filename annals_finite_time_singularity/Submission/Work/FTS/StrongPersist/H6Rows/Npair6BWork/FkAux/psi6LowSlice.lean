import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkLowAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkSliceSup
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.lowGamSlotIntegrable
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.lowZSliceLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.psi6LowMixedHalf
import Submission.Work.FTS.StrongPersist.H6Row6Gam.gamSliceSup11
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The two halves of the level-`m` slice sum, as integrability statements

These are the a.e.-integrability side conditions needed to apply `MeasureTheory.integral_add`
to the two `Finset.range` sums of `lowSum`.  Each summand of the `γ`-weighted half is
integrable by `lowGamSlotIntegrable` (the `if`-branch being `0`), and each summand of the
`η`-weighted half by `fkSliceSup_slice_integrable`. -/

/-- Integrability of the `γ`-weighted angular half of the level-`m` slice sum. -/
theorem psi6LowMixedHalf_integrable {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {m : ℕ} (hm : m ≤ 2) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (m + 1),
        ∑ j ∈ Finset.range (m + 1),
          if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine MeasureTheory.integrable_finsetSum (Finset.range (m + 1)) (fun i _ => ?_)
  refine MeasureTheory.integrable_finsetSum (Finset.range (m + 1)) (fun j _ => ?_)
  by_cases hc : 1 ≤ i ∧ i + j ≤ m
  · simp only [if_pos hc]
    exact lowGamSlotIntegrable hα hα1 hF hmem hc.1 (by omega) hz
  · simp only [if_neg hc]
    simp

/-- Integrability of the `η`-weighted radial half of the level-`m` slice sum. -/
theorem psi6LowZHalf_integrable {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {m : ℕ} (hm : m ≤ 2) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.Integrable (fun θ : ℝ => ∑ i ∈ Finset.range (m + 1),
        (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
          * (Work.Spaces.mixed i 0 f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine MeasureTheory.integrable_finsetSum (Finset.range (m + 1)) (fun i hi => ?_)
  have hi2 : i ≤ 2 := by
    have := Finset.mem_range.mp hi
    omega
  exact fkSliceSup_slice_integrable hα hF hmem (j := i) (i := 0) (by omega) hz

/-- **The level-`m` `lowSum` slice**, `m ≤ 2`: `∫_θ lowSum α m f z θ ≤ 36 · HkSq α 4 f`.
This is the sum of the two independent halves: the radial one
(`lowZSliceLe`, `≤ 9 · HkSq α 4 f`, `m+1 ≤ 3` slots) and the angular one
(`psi6LowMixedHalf`, `≤ 27 · HkSq α 4 f`). -/
theorem psi6LowSumSliceLe {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {m : ℕ} (hm : m ≤ 2) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, lowSum α m f z θ) ≤ 36 * Work.Spaces.HkSq α 4 f := by
  have hZint := psi6LowZHalf_integrable (α := α) hα hF hmem hm hz
  have hMint := psi6LowMixedHalf_integrable (α := α) hα hα1 hF hmem hm hz
  have hZ := lowZSliceLe (α := α) hα hF hmem hm hz
  have hM := psi6LowMixedHalf (α := α) hα hα1 hF hmem hm hz
  have hsplit : (∫ θ in Work.Spaces.Iθ, lowSum α m f z θ)
      = (∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1),
            (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.mixed i 0 f z θ) ^ 2)
        + ∫ θ in Work.Spaces.Iθ, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) else 0 := by
    unfold lowSum
    exact MeasureTheory.integral_add hZint hMint
  rw [hsplit]
  refine le_trans (add_le_add hZ hM) ?_
  linarith [Work.Spaces.HkSq_nonneg α 4 f]

/-- **The low-level angular slice of `HkIntegrand`, uniformly in `z`.**

For a datum `f` of the open class lying honestly in `ℋ⁴` and `m ≤ 2`, at every `z > 0` the
angular slice of the level-`m` `ℋ`-integrand is bounded by `C · HkSq α 4 f · (w z)²`.

Route: `HkIntegrand α m f z θ = (w z)² · lowSum α m f z θ` a.e. on `Iθ`
(`HkIntegrand_eq_w_sq_mul_lowSum` / `ae_HkIntegrand_eq_w_sq_mul_lowSum` in `fkLowAux`), so
`∫_θ HkIntegrand α m f z θ = (w z)² · ∫_θ lowSum α m f z θ`; splitting the two `Finset.range`
sums of `lowSum` with `MeasureTheory.integral_finsetSum` (the `if`-branches by `by_cases`, the
else-branch being `0`) reduces to the slots: the radial ones `(j,i) = (i,0)` with `i ≤ m` are
`≤ 3 · HkSq α 4 f` by `fkSliceSup_sliceSupGraded` at `k = 4` (its hypothesis `i + 0 + 1 ≤ 4`
holds), integrable by `fkSliceSup_slice_integrable`; the mixed ones (`1 ≤ i`, `i + j ≤ m ≤ 2`,
i.e. only `(j,i) ∈ {(0,1),(1,1),(0,2)}`) are `≤ 3 · HkSq α 4 f` by
`H6Row6Gam.mixed_slice_z_le_three` (its hypothesis `i + j ≤ 3` holds), integrable by
`lowGamSlotIntegrable`. At most `(m+1) + 9 ≤ 12` slots occur, so `C = 36` works. -/
theorem psi6LowSlice : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ (m : ℕ), m ≤ 2 → ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ)
        ≤ C * Work.Spaces.HkSq α 4 f * (Work.Spaces.w z) ^ 2 := by
  refine ⟨36, by norm_num, ?_⟩
  intro α hαmem f hF hmem m hm z hz
  have hα : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hlow := psi6LowSumSliceLe (α := α) hα hα1 hF hmem hm hz
  have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, lowSum α m f z θ := by
    rw [MeasureTheory.integral_congr_ae (ae_HkIntegrand_eq_w_sq_mul_lowSum hα m f z),
      MeasureTheory.integral_const_mul]
  calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z θ)
      = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, lowSum α m f z θ := h1
    _ ≤ (Work.Spaces.w z) ^ 2 * (36 * Work.Spaces.HkSq α 4 f) :=
        mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
    _ = 36 * Work.Spaces.HkSq α 4 f * (Work.Spaces.w z) ^ 2 := by ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
