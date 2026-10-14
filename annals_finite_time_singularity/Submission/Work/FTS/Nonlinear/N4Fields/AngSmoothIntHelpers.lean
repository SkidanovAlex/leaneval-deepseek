import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.tracePi4
import Submission.Work.FTS.StrongPersist.QangSq6
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_pth_poincare =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option maxHeartbeats 800000

/-- The `θ`-derivative of the `θ`-slice of a function smooth on the open quadrant. -/
private lemma hasDerivAt_slice_pth {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (fun θ' : ℝ => F z θ') (Work.Spaces.pth F z θ) θ := by
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => F z θ') θ :=
    ((hF.curry_θ hz).differentiableOn
      (by rw [Work.Stability.smoothOrder]; simp)).differentiableAt
      (isOpen_Ioo.mem_nhds hθ)
  exact hd.hasDerivAt


end Work.FTS.EllSol.EllPkgAux.MollDom
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.Dispatch.weightAlgChi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Dispatch

open Filter Set
open scoped Topology

/-- `iteratedDeriv 2 f` agrees with `deriv (deriv f)`. -/
private lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]





end Work.FTS.EllipticEst.Dispatch
end
-- ===== merged: Submission.Work.FTS.H2.OpenPort.coefTh3_mixed_gain =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.H2.OpenPort

/-- **The `sin(2θ)`-gain of `CoefTh 3`.**  Every mixed derivative `D_z^b D_θ^a f` of a
`C^∞`-datum `f` on the open quadrant with `a ≥ 1` and `a + b ≤ 4` picks up one factor
`sin(2θ)` and is dominated by the flat angular coefficient norm `CoefTh 3 f`.

This combines the σ-gain `Work.FTS.TransportS.flat_mixed_le` (which needs a *uniform* bound
`K` on the mixed derivatives of `∂_θ f` of total order `≤ 3`) with the two facts relating
`CoefThMem 3 f` to the norm `CoefTh 3 f`: a `CoefThMem`-bound is a bound by `supAbsO`
(`Work.FTS.H2.le_supAbsO`), and each `supAbsO` occurring in `CoefTh` is dominated by the
sum itself (`Work.FTS.TransportS.supAbsO_le_coefTh`).  Hence `K := CoefTh 3 f` is admissible
and the conclusion follows. -/
theorem coefTh3_mixed_gain :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      Work.FTS.VocabO.CoefThMem 3 f →
      ∀ (a b : ℕ), 1 ≤ a → a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
        |Work.Spaces.mixed b a f z θ| ≤ C * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.TransportS.flat_mixed_le 3
  refine ⟨C, hCpos, ?_⟩
  intro f hsf hmem a b ha hab z θ hz hθ hθ1
  refine hC f hsf (Work.FTS.VocabO.CoefTh 3 f)
    (Work.FTS.TransportS.coefTh_nonneg 3 f) ?_ a b ha hab z θ hz hθ hθ1
  intro b' i hbi z' θ' hz' hθ' hθ1'
  obtain ⟨K, hK⟩ := hmem b' i hbi
  exact le_trans (Work.FTS.H2.le_supAbsO hz' hθ' hθ1' hK)
    (Work.FTS.TransportS.supAbsO_le_coefTh hbi)

end Work.FTS.H2.OpenPort
end
-- ===== merged: Submission.Work.FTS.Nonlinear.N4Fields.AngSmoothIntHelpers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.N4Fields

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Extracting the angular `C^∞`-data from `SmoothInt` -/


/-- If the uncurried angular profile is `C^∞` on the open quadrant, then the profile itself is
`C^∞` on `(0,π/2)` (evaluate along the line `z = 1`). -/
theorem contDiffOn_ang_of_Q0 {a : ℝ → ℝ}
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioo 0 (Real.pi / 2)) := by
  rw [isOpen_Ioo.contDiffOn_iff]
  intro θ hθ
  have hQ : ((1 : ℝ), θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]
    exact ⟨one_pos, hθ.1, hθ.2⟩
  have h1 : ContDiffAt ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      ((1 : ℝ), θ) :=
    h.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hQ)
  have h2 : ContDiffAt ℝ Work.Stability.smoothOrder (fun θ' : ℝ => ((1 : ℝ), θ')) θ := by
    fun_prop
  exact h1.comp θ h2


/-! ## `SmoothOpen` of an angular multiple -/

/-- Multiplying a `SmoothOpen` function by an angular profile which is `C^∞` on the open
quadrant preserves `SmoothOpen`. -/
theorem smoothOpen_angMul_On {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => a p.2)
      Work.FTS.EllipticEst.Q0)
    {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.SmoothOpen G) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => a θ * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (fun p : ℝ × ℝ => (fun z θ : ℝ => a θ * G z θ) p.1 p.2) Work.FTS.EllipticEst.Q0
  exact ha.mul hG

/-! ## The iterated Leibniz expansion with open-interval smoothness -/

/-- **Leibniz expansion of `D_θ^i` applied to an angular multiple of a `D_z`-iterate**, with
only the *open-interval* smoothness of the profile `a`: for `a` of class `C^∞` on `(0,π/2)`,
`f` smooth on the open quadrant, and `0 < z`, `θ ∈ (0,π/2)`,
`D_θ^i (a(θ) · D_z^j f (z,θ)) = ∑_{m ≤ i} C(i,m) · (L^m a)(θ) · D_θ^{i-m}(D_z^j f)(z,θ)`.
This is `Work.FTS.EllipticEst.Blocks.DthIter_angular_mul_expand` with the analyticity hypothesis
of `a` replaced by `C^∞` on `(0,π/2)` (which is what its proof uses). -/
theorem DthIter_angular_mul_expand_On {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ Work.Stability.smoothOrder a (Set.Ioo 0 (Real.pi / 2)))
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DthIter i (fun z θ => a θ * Work.Spaces.DzIter j f z θ) z θ
      = ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m a θ
          * Work.Spaces.DthIter (i - m) (Work.Spaces.DzIter j f) z θ := by
  have hgOn : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ' => Work.Spaces.DzIter j f z θ') (Set.Ioo 0 (Real.pi / 2)) :=
    (hf.DzIter j).curry_θ hz
  have hmain := Work.FTS.LocData.Lop_iter_mul_eqOn_smooth a
    (fun θ' => Work.Spaces.DzIter j f z θ') (Set.Ioo 0 (Real.pi / 2)) isOpen_Ioo ha hgOn i
  rw [congrFun (Work.Spaces.DthIter_eq_iterate_Lop i
    (fun z θ => a θ * Work.Spaces.DzIter j f z θ) z) θ]
  have hfun : (fun θ' : ℝ => a θ' * Work.Spaces.DzIter j f z θ')
      = a * (fun θ' : ℝ => Work.Spaces.DzIter j f z θ') := rfl
  rw [hfun, hmain hθ]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← congrFun (Work.Spaces.DthIter_eq_iterate_Lop (i - m) (Work.Spaces.DzIter j f) z) θ]
  simp only [Work.FTS.EllipticEst.LopIter]
  ring

end Work.FTS.Nonlinear.N4Fields
end
end
