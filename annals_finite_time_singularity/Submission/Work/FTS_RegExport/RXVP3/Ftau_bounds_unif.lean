import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_RegExport.RXT.Ftau_bounds
import Submission.Work.FTS_RegExport.RXT.MixedUniform
import Submission.Work.FTS_RegExport.RXT.Sys.Ftau_datum_of_LimApprox

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP3.Ftau_bounds_unif` — a fake-time-uniform bound for `F(τ)`

The profile of the strong route is `F(τ) = Ftau (pExp α) (GR α g) τ = F_* + g(τ)` on the open
quadrant, and `Work.FTS_RegExport.RXT.Ftau_bounds.Ftau_bounds` bounds its first three `D_z`-jets
on the open quadrant by `10*M + |K|` (`M` from `FstarJet7`, `K = 10/√(γ-1)·(C₀·(pExp α)²)`), a
constant which is in fact independent of `τ` — but the *statement* of `Ftau_bounds` puts the
existential `∃ C` after the current fake time `τ`, so it cannot be read as a uniform statement.

Here the `∃ C` is taken *before* the quantifier on `τ ≥ 0`.  Every ingredient is already
fake-time-free:

* the radial factor `F_*`: `Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0` for the `C²`-regularity on `Q0` and
  `Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le` with `M` from `FstarJet7` for the `D_z`-jets;
* the `g`-part: `Work.FTS_RegExport.RXT.Sys.ftau_DzIter_GR_le_uniform` (which needs only
  `LimApprox`, i.e. `hOK.2`, and a point `τ ∈ Icc 0 S` — used with `S := τ`), whose bound
  `10/√(γ-1)·(C₀·(pExp α)²)` is the horizon-free one produced by `mixed_uniform`;
* `D_z`-additivity on the sum: `Work.FTS_RegExport.RXT.ftau_DzIter_one_add` / `Work.FTS_RegExport.RXT.ftau_DzIter_two_add`, using that
  `DynOK'` supplies the `C⁴`-regularity of the slices of `g` at *every* `τ ≥ 0`
  (`RegPkgMin.c4`, i.e. `hOK.1.1.c4 τ hτ`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXVP3

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface.RXT (GR)

set_option autoImplicit false

/-- **Uniform bounds for the profile `F(τ) = F_* + g(τ)` and its `D_z`-derivatives.**  On the
open quadrant `F(z,θ) = F_*(z,θ) + g(z,θ,τ)`; the `F_*`-part is bounded by `FstarJet7`
(together with the elementary `|α Γ/c| ≤ 10`), and the `g`-part by `mixed_uniform` at the
horizon `max τ 1`, whose constant is independent of the horizon.  Hence the same constant
`10*M + |K|` works for every `τ ≥ 0`. -/
theorem Ftau_bounds_unif {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
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
  · intro τ hτ z θ hz h1 h2
    have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
    have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
    have hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g := hOK.2
    have hFc : ContDiffOn ℝ 2
        (Function.uncurry (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS_RegExport.RXT.ftau_contDiffOn_Fstar_Q0 hp0 hp1
    have hGc : ContDiffOn ℝ 2
        (Function.uncurry (slice (GR α g) τ)) Work.FTS.EllipticEst.Q0 :=
      ((hOK.1.1.c4 τ hτ).of_le (by norm_num)).congr
        (fun p hp => Work.FTS_RegExport.RXT.ftau_slice_GR_eq hτ hp.1 hp.2.1.le hp.2.2.le)
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
      exact Work.FTS_RegExport.RXT.ftau_DzIter_one_add hF1 hG1 z θ hz h1 h2
    have sp2 : Work.Spaces.DzIter 2
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (GR α g) τ) z θ
        = Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ := by
      change Work.Spaces.DzIter 2 (fun z θ =>
          Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + slice (GR α g) τ z θ) z θ
        = Work.Spaces.DzIter 2 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ
      exact Work.FTS_RegExport.RXT.ftau_DzIter_two_add hFc hGc z θ hz h1 h2
    have hF00 : |Work.Spaces.DzIter 0
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le hα hα13 hM 0 (by norm_num) z θ hz h1 h2
    have hF11 : |Work.Spaces.DzIter 1
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le hα hα13 hM 1 (by norm_num) z θ hz h1 h2
    have hF22 : |Work.Spaces.DzIter 2
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le hα hα13 hM 2 (by norm_num) z θ hz h1 h2
    have hG00 : |Work.Spaces.DzIter 0 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact Work.FTS_RegExport.RXT.Sys.ftau_DzIter_GR_le_uniform hα hα13 hA τ
        ⟨hτ, le_rfl⟩ 0 (by norm_num) z θ hz h1 h2
    have hG11 : |Work.Spaces.DzIter 1 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact Work.FTS_RegExport.RXT.Sys.ftau_DzIter_GR_le_uniform hα hα13 hA τ
        ⟨hτ, le_rfl⟩ 1 (by norm_num) z θ hz h1 h2
    have hG22 : |Work.Spaces.DzIter 2 (slice (GR α g) τ) z θ| ≤ K := by
      rw [hK]
      exact Work.FTS_RegExport.RXT.Sys.ftau_DzIter_GR_le_uniform hα hα13 hA τ
        ⟨hτ, le_rfl⟩ 2 (by norm_num) z θ hz h1 h2
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

end Work.FTS_RegExport.RXVP3
