import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.MixedUniform
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR)
open Work.FTS.FinalV2 (LimApprox)

set_option autoImplicit false

/-! ## §1 The `g`-part at a fixed horizon `max S 1`

This is `Work.FTS_RegExport.RXT.ftau_DzIter_GR_le` with the horizon `max τ 1` replaced by the
fixed horizon `max S 1` (so that the bound is uniform over `τ ∈ [0,S]`) and with `DynOK'`
replaced by its `LimApprox` half, which is all that `mixed_uniform` uses. -/

lemma ftau_DzIter_GR_le_uniform {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 3)
    {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hA : LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (S : ℝ) {τ : ℝ} (hτS : τ ∈ Set.Icc (0 : ℝ) S) (j : ℕ) (hj : j ≤ 2) (z θ : ℝ)
    (hz : 0 < z) (h1 : 0 < θ) (h2 : θ < Real.pi / 2) :
    |Work.Spaces.DzIter j (slice (GR α g) τ) z θ|
      ≤ 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
        * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα1
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.Q0, Set.mem_prod]; exact ⟨hz, h1, h2⟩
  have hEqOn : Set.EqOn (Function.uncurry (slice (GR α g) τ))
      (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 :=
    fun p hp => ftau_slice_GR_eq hτS.1 hp.1 hp.2.1.le hp.2.2.le
  have hcongr := Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqOn j
  have hstep : Work.Spaces.DzIter j (slice (GR α g) τ) z θ
      = Work.Spaces.DzIter j (slice g τ) z θ := hcongr (x := (z, θ)) hmem
  rw [hstep]
  have hT : 0 < max S 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hτT : τ ∈ Set.Icc (0 : ℝ) (max S 1) := ⟨hτS.1, le_trans hτS.2 (le_max_left _ _)⟩
  have h := mixed_uniform (α := Work.FTS.Regularity.pExp α) hp0 hp1 hA (max S 1) hT
    τ hτT j 0 (by omega) z θ hmem
  simpa only [Work.Spaces.mixed_zero_right] using h

/-! ## §2 The target -/

/-- Pointwise bounds of the first three `D_z`-jets of the profile `F(τ) = F_* + g(τ)` on the
open quadrant, uniformly in `τ ∈ [0,S]`, from `LimApprox` (which supplies `mixed_uniform` for the
`g`-part) and the `C²`-regularity `hc2` of the slices.

PROOF RECIPE (copy `Work.FTS_RegExport.RXT.Ftau_bounds.Ftau_bounds`, whose `hOK : DynOK'` is used
only through `hOK.1.1.c4` and `hOK.2`):

* put `T := max S 1` (`hT : 0 < T`) so `Icc 0 S ⊆ Icc 0 T`;
* the `F_*` part: `ftau_contDiffOn_Fstar_Q0 (pExp_pos hα) (pExp_le_one hα13)` gives `C²` on `Q0`,
  and `ftau_DzIter_Fstar_le hα hα13 hM j hj` (with `M` from
  `Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7`) bounds `|DzIter j F_*| ≤ 10*M`;
* the `g` part: `Work.FTS_RegExport.RXT.MixedUniform.mixed_uniform hα hα1 hA T hT τ hτT j 0 ...`
  gives `|DzIter j (slice g τ) z θ| ≤ 10/√(γ-1) * (C₀ * (pExp α)^2)` for `j ≤ 2`; transfer it to
  `slice (GR α g) τ` with `ftau_slice_GR_eq hτ` (which needs `0 ≤ τ`, `0 < z`, `0 ≤ θ ≤ π/2`) and
  `Work.FTS.H2.DzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0`;
* additivity of `DzIter 1`/`DzIter 2` on the sum: `ftau_DzIter_one_add`/`ftau_DzIter_two_add`,
  whose `ContDiffOn ℝ 1`/`ContDiffOn ℝ 2` inputs for the `g`-part come from `hc2 τ hτ` (transferred
  to `GR` with `Work.FTS.H2.DzIter_congr_of_isOpen`/`ContDiffOn.congr`) and for `F_*` from the
  `F_*`-smoothness above;
* conclude with `abs_add_le` and `C := 10*M + |10/√(γ-1) * (C₀ * (pExp α)^2)|`. -/
theorem Ftau_jets_bounded_of_LimApprox {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (S : ℝ) (hS : 0 < S)
    (hc2 : ∀ τ ∈ Set.Icc (0 : ℝ) S,
      ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
        Work.FTS.EllipticEst.Q0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ z θ| ≤ C ∧
      |Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z θ| ≤ C ∧
      |Work.Spaces.DzIter 2 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) τ) z θ| ≤ C := by
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
  set K : ℝ := 10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) with hK
  refine ⟨10 * M + |K|, ?_, ?_⟩
  · have h10M : 0 ≤ 10 * M := by linarith
    linarith [abs_nonneg K]
  · intro τ hτS z θ hz h1 h2
    have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
    have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
    have hτ : 0 ≤ τ := hτS.1
    have hFc : ContDiffOn ℝ 2
        (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
        Work.FTS.EllipticEst.Q0 :=
      ftau_contDiffOn_Fstar_Q0 hp0 hp1
    have hGc : ContDiffOn ℝ 2
        (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 :=
      (hc2 τ hτS).congr (fun p hp => ftau_slice_GR_eq hτ hp.1 hp.2.1.le hp.2.2.le)
    have hF1 : ContDiffOn ℝ 1
        (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
        Work.FTS.EllipticEst.Q0 := hFc.of_le (by norm_num)
    have hG1 : ContDiffOn ℝ 1
        (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 := hGc.of_le (by norm_num)
    have sp0 : Work.Spaces.DzIter 0
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ := rfl
    have sp1 : Work.Spaces.DzIter 1
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ := by
      change Work.Spaces.DzIter 1 (fun z θ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice (GR α g) τ z θ) z θ
        = Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ
      exact ftau_DzIter_one_add hF1 hG1 z θ hz h1 h2
    have sp2 : Work.Spaces.DzIter 2
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ := by
      change Work.Spaces.DzIter 2 (fun z θ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice (GR α g) τ z θ) z θ
        = Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ
      exact ftau_DzIter_two_add hFc hGc z θ hz h1 h2
    have hF00 : |Work.Spaces.DzIter 0
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      ftau_DzIter_Fstar_le hα hα13 hM 0 (by norm_num) z θ hz h1 h2
    have hF11 : |Work.Spaces.DzIter 1
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      ftau_DzIter_Fstar_le hα hα13 hM 1 (by norm_num) z θ hz h1 h2
    have hF22 : |Work.Spaces.DzIter 2
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      ftau_DzIter_Fstar_le hα hα13 hM 2 (by norm_num) z θ hz h1 h2
    have hG00 : |Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact ftau_DzIter_GR_le_uniform hα hα13 hA S hτS 0 (by norm_num) z θ hz h1 h2
    have hG11 : |Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact ftau_DzIter_GR_le_uniform hα hα13 hA S hτS 1 (by norm_num) z θ hz h1 h2
    have hG22 : |Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact ftau_DzIter_GR_le_uniform hα hα13 hA S hτS 2 (by norm_num) z θ hz h1 h2
    refine ⟨?_, ?_, ?_⟩
    · calc |Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ z θ|
          = |Work.Spaces.DzIter 0
              (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ| := rfl
        _ = |Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| := by rw [sp0]
        _ ≤ |Work.Spaces.DzIter 0 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF00 hG00
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]
    · change |Work.Spaces.DzIter 1
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          ≤ 10 * M + |K|
      calc |Work.Spaces.DzIter 1
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          = |Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| := by rw [sp1]
        _ ≤ |Work.Spaces.DzIter 1 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF11 hG11
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]
    · calc |Work.Spaces.DzIter 2
            (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ|
          = |Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
              + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| := by rw [sp2]
        _ ≤ |Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
              + |Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| := abs_add_le _ _
        _ ≤ 10 * M + K := add_le_add hF22 hG22
        _ ≤ 10 * M + |K| := by linarith [le_abs_self K]

end Work.FTS_RegExport.RXT.Sys
