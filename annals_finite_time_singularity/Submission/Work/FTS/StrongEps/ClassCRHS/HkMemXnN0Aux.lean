import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts
import Submission.Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.Spaces.H_le_Wt
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC
import Submission.Work.FTS.StrongEps.ClassCRHS.N0_split_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Elementary helpers about the `ℋ⁴`-functionals -/

/-- `HkMem` is invariant under negation. -/
theorem mem_neg {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (-f) := by
  obtain ⟨h1, h2⟩ := h
  have hpt : ∀ z θ, Work.Spaces.HkIntegrand α k (-f) z θ
      = Work.Spaces.HkIntegrand α k f z θ :=
    fun z θ => congrFun (congrFun (Work.FTS.EllipticEst.HkIntegrand_neg α k f) z) θ
  constructor
  · intro z hz
    exact (h1 z hz).congr (Filter.Eventually.of_forall (fun θ => (hpt z θ).symm))
  · have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (-f) z θ)
        = (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      funext fun z => MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => hpt z θ)
    rw [hfun]
    exact h2

/-- `HkSq` is invariant under negation. -/
theorem sq_neg {α : ℝ} (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k (-f) = Work.Spaces.HkSq α k f := by
  simp only [Work.Spaces.HkSq]
  rw [Work.FTS.EllipticEst.HkIntegrand_neg α k f]

/-- `Xn` is invariant under negation. -/
theorem Xn_neg {α : ℝ} (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (-f) = Work.FTS.Nonlin.Xn α f := by
  simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
  rw [sq_neg]

/-- **`HkMem α n (D_θ f)`** from `SmoothOpen f` and `HkMem α (n+1) f`. -/
theorem hkMem_Dth_of_smoothOpen {α : ℝ} (hα : 0 < α) (n : ℕ) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (h : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
  Work.FTS.LocData.HkMem_of_majorant α n
    (f := Work.Spaces.Dth f)
    (M := fun z θ => Work.Spaces.HkIntegrand α (n + 1) f z θ)
    ((Work.FTS.EllipticEst.SmoothOpen.Dth hsm).continuousOn_HkIntegrand α n)
    h.1 h.2
    (fun z hz θ hθ => Work.Coercivity.HkIntegrand_Dth_le α hα n f z θ hz hθ)

/-- **Binary additivity of the `ℋ⁴`-membership and the `ℋ⁴`-norm**, with the factor `2`. -/
theorem add2 {α : ℝ} (hα : 0 < α) {u v : ℝ → ℝ → ℝ} {Bu Bv : ℝ}
    (husm : Work.FTS.EllipticEst.SmoothOpen u) (hvsm : Work.FTS.EllipticEst.SmoothOpen v)
    (hu : Work.Spaces.HkMem α 4 u) (hv : Work.Spaces.HkMem α 4 v)
    (bu : Work.FTS.Nonlin.Xn α u ≤ Bu) (bv : Work.FTS.Nonlin.Xn α v ≤ Bv)
    (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv) :
    Work.Spaces.HkMem α 4 (fun z θ => u z θ + v z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => u z θ + v z θ) ≤ 2 * (Bu + Bv) := by
  have hmem : Work.Spaces.HkMem α 4 (fun z θ => u z θ + v z θ) :=
    Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (husm.forall 4) (hvsm.forall 4) hu hv
  refine ⟨hmem, ?_⟩
  have hb := Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα husm hvsm hu hv
  have h1 : Work.FTS.Nonlin.Xn α u ≤ Bu := bu
  have h2 : Work.FTS.Nonlin.Xn α v ≤ Bv := bv
  have h3 : Work.Spaces.HkNorm α 4 u = Work.FTS.Nonlin.Xn α u := rfl
  have h4 : Work.Spaces.HkNorm α 4 v = Work.FTS.Nonlin.Xn α v := rfl
  rw [h3, h4] at hb
  linarith

/-- **`SmoothOpen (z ↦ L₁₂ w z)`** for a datum of the linear class `C` (delivered by the
colleague working on `HkMemXnN0`; see
`Submission/Work/FTS/StrongEps/ClassCRHS/smoothOpen_L12_radial_classC.lean`). -/
theorem smoothOpen_L12_radial_aux {α : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hw : Work.FTS.ClassC.ClassC α w) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
  smoothOpen_L12_radial_classC hα hw

/-! ## The `N₀`-split on the open quadrant -/

/-- **The split of `N₀ α (F_*+w) w` into the seven rows** on the open quadrant (delivered by the
colleague working on `HkMemXnN0`; see
`Submission/Work/FTS/StrongEps/ClassCRHS/N0_split_open.lean`). -/
theorem N0_split_open_aux {α : ℝ} (hα : 0 < α) {w : Work.FTS.Galerkin.Fn}
    (hw : Work.FTS.EllipticEst.SmoothOpen w) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α w) w z θ
        = Work.FTS.Nonlin.N0fix α z θ
          + (Work.FTS.Nonlin.N03g α w z θ
            + (Work.FTS.Nonlin.N04aF α w z θ
              + (Work.FTS.Nonlin.N04bF α w z θ
                + (Work.FTS.Nonlin.N05aF α w z θ
                  + (Work.FTS.Nonlin.N05bF α w z θ
                    + Work.FTS.Nonlin.N06F α w z θ))))) :=
  N0_split_open hα hw

end Work.FTS.StrongEps.ClassCRHS
