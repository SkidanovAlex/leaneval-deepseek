import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR7.Joint.CLM
import Submission.Work.FTS_RegExport.RXR7.Joint.ProfBasic
import Submission.Work.FTS_RegExport.RXR7.Joint.Interior
import Submission.Work.FTS_RegExport.RXR7.Joint.Boundary
import Submission.Work.FTS_RegExport.RXR7.Support.K7cont
import Submission.Work.FTS_RegExport.RXR7.Support.FstarPartCont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## §9  Assembly of the `hFjoint` field -/

/-- Joint continuity of the transport right-hand side `K7` on the slab. -/
theorem K7_contOn_slab {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (μR α Φs E g) (GR α g) (ΦR α Φs E g) S) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => K7 α Φs E g p.1 p.2.1 p.2.2) (R7Slab S) :=
  Work.FTS_RegExport.RXR7.Support.K7cont hS hα hα13 hOK hVP

/-- Joint continuity of the `z`-coordinate of the `F_*`-part. -/
theorem FstarPz_contOn_slab {α : ℝ} {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        p.1 p.2.1) (R7Slab S) := by
  have h2 : ContinuousOn (fun q : ℝ × ℝ =>
      (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) q.1 q.2,
       Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          q.1 q.2)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS_RegExport.RXR7.Support.FstarPartCont (α := α)
  have h3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) (R7Slab S) :=
    (p1.prod p2).continuous.continuousOn
  exact (h2.comp h3 (fun p hp => ⟨hp.1, hp.2.1.1, hp.2.1.2⟩)).fst

/-- Joint continuity of the `θ`-coordinate of the `F_*`-part. -/
theorem FstarPth_contOn_slab {α : ℝ} {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
        p.1 p.2.1) (R7Slab S) := by
  have h2 : ContinuousOn (fun q : ℝ × ℝ =>
      (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) q.1 q.2,
       Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          q.1 q.2)) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS_RegExport.RXR7.Support.FstarPartCont (α := α)
  have h3 : ContinuousOn (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) (R7Slab S) :=
    (p1.prod p2).continuous.continuousOn
  exact (h2.comp h3 (fun p hp => ⟨hp.1, hp.2.1.1, hp.2.1.2⟩)).snd

/-- Joint continuity of the two spatial coordinates of the `F_*`-part. -/
theorem FstarPart_contOn_slab {α : ℝ} {S : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      (Work.Spaces.pz (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          p.1 p.2.1,
       Work.Spaces.pth (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ)
          p.1 p.2.1)) (R7Slab S) :=
  (FstarPz_contOn_slab (α := α) (S := S)).prodMk (FstarPth_contOn_slab (α := α) (S := S))

/-- Joint continuity of the candidate derivative field `ProfD` on the slab. -/
theorem ProfD_contOn_slab {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (μR α Φs E g) (GR α g) (ΦR α Φs E g) S) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ => ProfD α Φs E g p) (R7Slab S) :=
  ProfD_contOn
    (FPz_contOn hS hα hα13 hOK (FstarPart_contOn_slab (α := α) (S := S)).fst)
    (FPt_contOn hS hα hα13 hOK (FstarPart_contOn_slab (α := α) (S := S)).snd)
    (K7_contOn_slab hS hα hα13 hOK hVP)

/-- The profile is differentiable within the slab everywhere, with derivative `ProfD`. -/
theorem profile_hasFDerivWithinAt {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hVP : Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (μR α Φs E g) (GR α g) (ΦR α Φs E g) S)
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Prof α g z θ s) (-(K7 α Φs E g z θ τ)) τ) :
    ∀ x ∈ R7Slab S, HasFDerivWithinAt (fun y : ℝ × ℝ × ℝ => Prof α g y.1 y.2.1 y.2.2)
      (ProfD α Φs E g x) (R7Slab S) x := by
  intro x hx
  by_cases hτ : 0 < x.2.2
  · exact (hasFDerivAt_profD_of_pos hS hα hα13 hOK hEq x hx hτ).hasFDerivWithinAt
  · have h0 : x.2.2 = 0 := le_antisymm (not_lt.mp hτ) hx.2.2.1
    exact hasFDerivWithinAt_profD_of_eq_zero hS hα hα13 hOK
      (K7_contOn_slab hS hα hα13 hOK hVP) hEq x hx h0

end Work.FTS_RegExport.RXR7
