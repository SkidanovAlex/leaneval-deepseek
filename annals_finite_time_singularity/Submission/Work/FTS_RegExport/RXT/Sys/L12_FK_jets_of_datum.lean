import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_RegExport.RXT.Sys.EPCDefs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Construction.Basic
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.Basic
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.Jets

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12_FK_jets_of_datum` — the `z∂_z`-jets of `L₁₂(F)` and `𝔽K(F)` from the datum hypotheses

`DatumHyp F C` supplies, on the open quadrant `Q0 = (0,∞) × (0,π/2)`, the `C²`-smoothness of
the datum `F`, the pointwise bounds `|D_z^k F| ≤ C` (`k ≤ 2`) and the `L¹`-control
`∫_0^∞ |L12dens F| ≤ C` of the `L₁₂`-density.  From those hypotheses alone the two radial
transforms

* `L₁₂(F)(z) = ∫_z^∞ ∫_θ K(θ)F(s,θ)/s dθ ds`,
* `𝔽K(F)(z)  = ∫_θ F(z,θ)K(θ) dθ`

satisfy the whole order-`≤ 2` jet package: the pointwise bounds `|D_z^j| ≤ 64C⁴` (`j ≤ 2`,
`D_z = z∂_z`), the same for linear combinations, the fundamental-model identity
`D_z L₁₂(F) = -𝔽K(F)`, and the two derivative identities
`∂_z L₁₂(F) = -𝔽K(F)/z`, `∂_z 𝔽K(F)(z) = ∫_θ ∂_zF(z,θ)K(θ) dθ`.

The ingredients live in `L12FKjet.Basic`, `L12FKjet.L12`, `L12FKjet.Jets`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem L12_FK_jets_of_datum :
    ∃ K : ℝ, 0 < K ∧ ∀ (F : ℝ → ℝ → ℝ) (C : ℝ), 1 ≤ C →
      Work.FTS_RegExport.RXT.Sys.DatumHyp F C →
      ∀ z : ℝ, 0 < z →
        (∀ j : ℕ, j ≤ 2 →
          |Work.Elliptic.DzdIter j (Work.Construction.L12 F) z| ≤ K * C ^ 4 ∧
          |Work.Elliptic.DzdIter j (Work.Construction.FK F) z| ≤ K * C ^ 4 ∧
          (∀ a b : ℝ, |Work.Elliptic.DzdIter j (fun z => a * Work.Construction.L12 F z
              + b * Work.Construction.FK F z) z| ≤ (|a| + |b|) * (K * C ^ 4))) ∧
        (Work.Elliptic.DzdIter 1 (Work.Construction.L12 F) z = - Work.Construction.FK F z) ∧
        HasDerivAt (fun z' => Work.Construction.L12 F z') (- (Work.Construction.FK F z) / z) z ∧
        HasDerivAt (fun z' => Work.Construction.FK F z')
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F z θ * Work.Spaces.K θ) z := by
  refine ⟨64, by norm_num, ?_⟩
  intro F C hC1 hD z hz
  have hC : (0 : ℝ) ≤ C := by linarith
  have h2 : ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0 := hD.smooth
  have hb : DatumBnd F C := hD.bnd
  have hbd : ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k F z θ| ≤ C :=
    fun k hk z θ hz' hθ0 hθ1 => hb.DzIter_le hk hz' hθ0 hθ1
  have hint : IntegrableOn (Work.Construction.L12dens F) (Set.Ioi 0) := hD.integrable
  have hmass : (∫ s in Set.Ioi 0, |Work.Construction.L12dens F s|) ≤ C := hD.mass
  -- the derivative of `𝔽K F`, and hence of `Qang F 0 = 𝔽K F`, at every point of `(0,∞)`
  have hFKd : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => Work.Construction.FK F z)
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F u θ * Work.Spaces.K θ) u :=
    fun u hu => lfj_hasDerivAt_FK h2 hbd hC hu
  have hQ0d : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Qang F 0) (Work.Elliptic.Qang F 1 u / u) u := by
    intro u hu
    have h := hFKd u hu
    rw [show (fun z => Work.Construction.FK F z) = Work.Elliptic.Qang F 0 from
      funext fun z => (lfj_Qang_zero_eq_FK F z).symm] at h
    have hval : Work.Elliptic.Qang F 1 u / u
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz F u θ * Work.Spaces.K θ := by
      rw [lfj_Qang_one_eq F u, mul_div_cancel_left₀ _ (ne_of_gt hu)]
    rwa [hval]
  -- the derivative of `L₁₂ F`
  have hL12d : ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => Work.Construction.L12 F z)
      (-(Work.Construction.L12dens F u)) u :=
    fun u hu => lfj_L12_hasDerivAt hint
      (lfj_L12dens_continuousAt ((hQ0d u hu).continuousAt) hu) hu
  -- the derivative of `Qang F 1`
  have hQ1d : ∀ u ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Qang F 1) (Work.Elliptic.Qang F 2 u / u) u :=
    fun u hu => lfj_Qang_one_hasDerivAt h2 hbd hC hu
  -- the eventual identities and their pointwise forms
  have hL12_1e := lfj_DzdIter_one_L12_eq hz hL12d
  have hFK_1e := lfj_DzdIter_one_FK_eq hz hFKd
  have hL12_1 : Work.Elliptic.DzdIter 1 (Work.Construction.L12 F) z
      = - Work.Construction.FK F z := lfj_DzdIter_one_L12 hz (hL12d z hz)
  have hL12_2 : Work.Elliptic.DzdIter 2 (Work.Construction.L12 F) z
      = -(Work.Elliptic.Qang F 1 z) := lfj_DzdIter_two_L12 hL12_1e (hQ0d z hz) hz
  have hFK_1 : Work.Elliptic.DzdIter 1 (Work.Construction.FK F) z
      = Work.Elliptic.Qang F 1 z := lfj_DzdIter_one_FK hz (hFKd z hz)
  have hFK_2 : Work.Elliptic.DzdIter 2 (Work.Construction.FK F) z
      = Work.Elliptic.Qang F 2 z := lfj_DzdIter_two_FK hFK_1e (hQ1d z hz) hz
  -- the jet bounds
  have hQ1b : |Work.Elliptic.Qang F 1 z| ≤ 18 * C :=
    lfj_Qang_abs_le hC hbd (m := 1) (by norm_num) hz
  have hQ2b : |Work.Elliptic.Qang F 2 z| ≤ 18 * C :=
    lfj_Qang_abs_le hC hbd (m := 2) (by norm_num) hz
  have hFK0b : |Work.Construction.FK F z| ≤ 18 * C := by
    rw [← lfj_Qang_zero_eq_FK F z]
    exact lfj_Qang_abs_le hC hbd (m := 0) (by norm_num) hz
  have hL0b : |Work.Construction.L12 F z| ≤ C := lfj_L12_abs_le hint hmass hz
  have hC18 : C ≤ 18 * C := by nlinarith [hC, hC1]
  have hBL : ∀ j : ℕ, j ≤ 2 →
      |Work.Elliptic.DzdIter j (Work.Construction.L12 F) z| ≤ 64 * C ^ 4 := by
    intro j hj
    interval_cases j
    · simpa only [Work.Elliptic.DzdIter_zero] using lfj_le_const hC1 (le_trans hL0b hC18)
    · rw [hL12_1]
      simpa only [abs_neg] using lfj_le_const hC1 hFK0b
    · rw [hL12_2]
      simpa only [abs_neg] using lfj_le_const hC1 hQ1b
  have hBF : ∀ j : ℕ, j ≤ 2 →
      |Work.Elliptic.DzdIter j (Work.Construction.FK F) z| ≤ 64 * C ^ 4 := by
    intro j hj
    interval_cases j
    · simpa only [Work.Elliptic.DzdIter_zero] using lfj_le_const hC1 hFK0b
    · rw [hFK_1]
      exact lfj_le_const hC1 hQ1b
    · rw [hFK_2]
      exact lfj_le_const hC1 hQ2b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    refine ⟨hBL j hj, hBF j hj, ?_⟩
    intro a b
    have hlin := lfj_DzdIter_linear (u := fun w => Work.Construction.L12 F w)
      (v := fun w => Work.Construction.FK F w) (a := a) (b := b) (z := z)
      (hL12d z hz).differentiableAt (hFKd z hz).differentiableAt
      (by filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw; exact (hL12d w hw).differentiableAt)
      (by filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw; exact (hFKd w hw).differentiableAt)
      (hL12_1e.differentiableAt_iff.mpr ((hQ0d z hz).differentiableAt.neg))
      (hFK_1e.differentiableAt_iff.mpr (hQ1d z hz).differentiableAt)
    exact lfj_DzdIter_lin_bound hlin hBL hBF j hj
  · exact hL12_1
  · have hval : -(Work.Construction.FK F z) / z = -(Work.Construction.L12dens F z) := by
      rw [← Work.Construction.mul_L12dens_eq_FK (F := F) (ne_of_gt hz), neg_div,
        mul_div_cancel_left₀ _ (ne_of_gt hz)]
    rw [hval]
    exact hL12d z hz
  · exact hFKd z hz

end Work.FTS_RegExport.RXT.Sys
