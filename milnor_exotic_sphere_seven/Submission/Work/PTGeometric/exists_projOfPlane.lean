import Mathlib
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.PTGeometric.RieszProj.Defs
import Submission.Work.PTGeometric.ProjOfPlane.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.PTGeometric

open scoped Manifold ContDiff Topology Matrix
open Work.ThomBordism.Grassmann

noncomputable section

/-- The projection onto the plane of a frame, **descended to the oriented Grassmannian**. -/
def projOfPlane (k m : ℕ) : OG k m → Amb (k + m) →L[ℝ] Amb (k + m) :=
  Quotient.lift (s := grassmannSetoid k m) (fun f : Stiefel k m => frameProj f.1)
    (fun f g hfg => by
      obtain ⟨A, rfl⟩ := hfg
      exact (frameProj_soActFun f.1 A).symm)

/-- The value of `projOfPlane` on the class of a frame. -/
theorem projOfPlane_mk (k m : ℕ) (f : Stiefel k m) :
    projOfPlane k m ((Quotient.mk'' f : OG k m)) = frameProj f.1 := by
  unfold projOfPlane
  exact Quotient.lift_mk (s := grassmannSetoid k m) _ _ f

/-- Two frames with the same class in the Grassmannian span the same plane. -/
theorem span_eq_of_mk_eq {k m : ℕ} {f g : Stiefel k m}
    (h : (Quotient.mk'' f : OG k m) = (Quotient.mk'' g : OG k m)) :
    Submodule.span ℝ (Set.range f.1) = Submodule.span ℝ (Set.range g.1) := by
  obtain ⟨A, hA⟩ := Quotient.exact h
  rw [hA]
  show Submodule.span ℝ (Set.range f.1) = Submodule.span ℝ (Set.range (soActFun A.1 f.1))
  exact (span_soActFun_eq A f.1).symm

/-- `memPlane` for the class of a frame: the plane is spanned by the frame. -/
theorem memPlane_mk_iff {k m : ℕ} (f : Stiefel k m) (w : Amb (k + m)) :
    memPlane ((Quotient.mk'' f : OG k m)) w ↔ w ∈ Submodule.span ℝ (Set.range f.1) := by
  constructor
  · rintro ⟨g, hg, hw⟩
    have h : Submodule.span ℝ (Set.range g.1) = Submodule.span ℝ (Set.range f.1) :=
      span_eq_of_mk_eq hg
    rwa [h] at hw
  · intro hw
    exact ⟨f, rfl, hw⟩

theorem continuous_projOfPlane (k m : ℕ) : Continuous (projOfPlane k m) := by
  have hq : Topology.IsQuotientMap (Quotient.mk'' : Stiefel k m → OG k m) :=
    isQuotientMap_quotient_mk' (s := grassmannSetoid k m)
  refine (Topology.IsQuotientMap.continuous_iff hq).mpr ?_
  show Continuous (fun f : Stiefel k m => projOfPlane k m (Quotient.mk'' f))
  have hcomp : (fun f : Stiefel k m => projOfPlane k m (Quotient.mk'' f))
      = fun f => frameProj f.1 := by
    funext f
    exact projOfPlane_mk k m f
  rw [hcomp]
  exact continuous_frameProj

theorem projOfPlane_mem_Gr (k m : ℕ) (P : OG k m) :
    projOfPlane k m P ∈ Gr (k + m) k := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep P
  rw [projOfPlane_mk]
  exact frameProj_mem_Gr f.2

theorem projOfPlane_fixed_iff (k m : ℕ) (P : OG k m) (w : Amb (k + m)) :
    projOfPlane k m P w = w ↔ memPlane P w := by
  obtain ⟨f, rfl⟩ := Quotient.exists_rep P
  rw [projOfPlane_mk, memPlane_mk_iff]
  exact frameProj_fixed_iff f.2 w

end

/-- **The orthogonal projection onto the tautological plane.**  A point of the oriented Grassmannian
`G̃r_k(ℝ^{k+m})` is a `k`-plane; the orthogonal projection onto it is a continuous map into the rank-`k`
orthogonal projections `Gr (k+m) k` of `ℝ^{k+m}`, and it fixes exactly the vectors of the plane
(`memPlane`).  This is the bridge between the Grassmann chapter's incidence description of the
tautological bundle (`memPlane P w`: `w` lies in the plane `P`) and the ambient projection-valued
coordinates `P : M → End(ℝⁿ)` used by `Work.PTGeometric.AmbCharts`/`AmbientCollapseEnd`.

Concretely: for a frame `f` representing `P` put `pr P = ∑ j, (⟨f j, ·⟩) • f j`; it is self-adjoint,
idempotent, of trace `k`, and invariant under the `SO(k)`-action, hence descends to the quotient
`OG k m = Stiefel k m / SO(k)`; the resulting map is continuous, and its fixed point set is its range,
which is exactly the plane, giving the `↔`. -/
theorem exists_projOfPlane (k m : ℕ) :
    ∃ pr : Work.ThomBordism.Grassmann.OG k m →
        EuclideanSpace ℝ (Fin (k + m)) →L[ℝ] EuclideanSpace ℝ (Fin (k + m)),
      Continuous pr ∧ (∀ P, pr P ∈ Work.PTGeometric.Gr (k + m) k) ∧
      (∀ P w, pr P w = w ↔ Work.ThomBordism.Grassmann.memPlane P w) :=
  ⟨projOfPlane k m, continuous_projOfPlane k m, projOfPlane_mem_Gr k m,
    projOfPlane_fixed_iff k m⟩

end Work.PTGeometric
