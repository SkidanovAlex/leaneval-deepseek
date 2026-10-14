import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.PkgK5.SharpAux
import Submission.Work.FTS.EllSol.PkgK5.lzero1_moment_dzIter_sharp
import Submission.Work.FTS.EllSol.PkgK5.tracesK5
import Submission.Work.FTS.StrongGlobal.Transfer

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false
set_option maxHeartbeats 3200000

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta

/-- The endpoint traces of the radial iterates of `X`, under the sharp `A`-honesty
`HkMem α (k+2) (z²∂_z²X)` and the sharp source honesty `HkMem α (k+2) F`, given the two
moment towers (of the unknown up to level `k+3` and of the source up to level `k+1`). -/
theorem traces_of_honest_sharp {α : ℝ} {k : ℕ} {F X : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F X)
    (hAh : Work.Spaces.HkMem α (k + 2)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 X z θ))
    (hFmem : Work.Spaces.HkMem α (k + 2) F)
    (hmom : ∀ i : ℕ, i ≤ k + 3 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i X) z = 0)
    (hmomF : ∀ i : ℕ, i ≤ k + 1 → ∀ z : ℝ, 0 < z →
      Work.Elliptic.Fstar (Work.Spaces.DzIter i F) z = 0) :
    ∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j X z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j X z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hXsm : Work.FTS.EllipticEst.SmoothOpen X :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  intro j hj z hz
  have hsm : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Spaces.DzIter j X z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.remov.ws_contDiffOn_slice (hXsm.DzIter j) hz
  have h2 := secondSlot_dzIter (α := α) (k := k) (F := F) (X := X) hk h j hj hz
  have hu : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.DzIter j X z θ) ^ 2) Iθ := by
    obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta hsm h2
    refine MeasureTheory.Integrable.mono'
      (Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.const_mul (C ^ 2))
      ((aesm_slice_dzIter hXsm j hz).pow 2) ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb' : |Work.Spaces.DzIter j X z θ| ≤ C := (hC θ hθ).2
    have hXs : Work.Spaces.DzIter j X z θ ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb' 2
    have h1 : 1 ≤ sEta θ := Work.FTS.EllipticEst.remov.ws_one_le_sEta hθ
    calc Work.Spaces.DzIter j X z θ ^ 2 ≤ C ^ 2 := hXs
      _ ≤ C ^ 2 * sEta θ := le_mul_of_one_le_right (sq_nonneg C) h1
  have hL := lzero1_energy_dzIter_sharp hk h hAh hFmem j hj hz
  have hmoment := lzero1_moment_dzIter_sharp hk h hAh hFmem hmom hmomF j hj hz
  exact ⟨Work.FTS.EllipticEst.remov.wsSliceLeft hsm h2 hL hmoment,
    Work.FTS.EllipticEst.remov.sliceTendstoRight_fts hsm h2 hL hu⟩

theorem tracesK5_sharp (k : ℕ) (hk : 2 ≤ k) :
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α (k + 2)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      ∀ j : ℕ, j ≤ k + 1 → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j (Work.FTS.EllSol.ellShift α g Φg) z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  intro α g Φg hα hα4 hC hsol hsmo hweak hAh hFmem
  refine traces_of_honest_sharp (F := Work.Elliptic.orthSource g)
    (X := Work.FTS.EllSol.ellShift α g Φg) hk hweak hAh hFmem ?_ ?_
  · exact Fstar_DzIter_le_sharp hk hweak hAh
  · exact fstar_dzIter_source_eq_zero (Work.FTS.EllipticEst.remov.ws_smoothOpen_F hweak)
      hFmem hweak.orthF

end Work.FTS.EllSol.PkgK5
