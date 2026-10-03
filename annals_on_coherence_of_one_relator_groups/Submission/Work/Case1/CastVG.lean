/-
# Casting vertex groups along equalities of vertices

The vertex groups `VertexGroup a` of the free groupoid are indexed by the vertices.  An equality
`h : a = b` of vertices induces an isomorphism `castVG h : VertexGroup a ≃* VertexGroup b` given by
casting the underlying path.  This file collects the properties of this isomorphism which are used
by the small-model construction, notably that it carries the normal closure of the relators of a
presentation into the corresponding normal closure at the other vertex.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.Case1.CastPath
import Submission.Work.ORLocInd.Howie.conjPathHom_mem_relatorNormalClosure

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u v

namespace Work.Case1

open Quiver

variable {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- The homomorphism of vertex groups induced by an equality of vertices: a closed path at `a` is
cast to a closed path at `b`. -/
noncomputable def castVG {a b : V} (h : a = b) :
    Work.ORLocInd.Howie.VertexGroup a →* Work.ORLocInd.Howie.VertexGroup b where
  toFun x := ⟨x.1.cast h h, (PathCast.cast_isReduced x.1 h h).mpr x.2⟩
  map_one' := Subtype.ext (Quiver.Path.cast_nil h)
  map_mul' x y := Subtype.ext (PathCast.cast_pmul x.1 y.1 h h h).symm

@[simp] theorem castVG_coe {a b : V} (h : a = b) (x : Work.ORLocInd.Howie.VertexGroup a) :
    (castVG h x).1 = x.1.cast h h := rfl

theorem castVG_apply {a b : V} (h : a = b) (x : Work.ORLocInd.Howie.VertexGroup a) :
    castVG h x = ⟨x.1.cast h h, (PathCast.cast_isReduced x.1 h h).mpr x.2⟩ := rfl

theorem castVG_self {a : V} (x : Work.ORLocInd.Howie.VertexGroup a) : castVG rfl x = x := by
  apply Subtype.ext
  rw [castVG_coe, Quiver.Path.cast_rfl_rfl]

theorem castVG_trans {a b c : V} (h : a = b) (h' : b = c)
    (x : Work.ORLocInd.Howie.VertexGroup a) :
    castVG h' (castVG h x) = castVG (h.trans h') x := by
  apply Subtype.ext
  rw [castVG_coe, castVG_coe, castVG_coe, Quiver.Path.cast_cast]

theorem castVG_self' {a : V} (h : a = a) (x : Work.ORLocInd.Howie.VertexGroup a) :
    castVG h x = x := by
  rw [Subsingleton.elim h rfl, castVG_self]

theorem castVG_symm_apply {a b : V} (h : a = b) (x : Work.ORLocInd.Howie.VertexGroup a) :
    castVG h.symm (castVG h x) = x := by
  rw [castVG_trans, castVG_self']

theorem castVG_injective {a b : V} (h : a = b) : Function.Injective (castVG h) := by
  intro x y hxy
  apply Subtype.ext
  have h2 := congrArg Subtype.val hxy
  rw [castVG_coe, castVG_coe] at h2
  have h3 : (x.1.cast h h).cast h.symm h.symm = (y.1.cast h h).cast h.symm h.symm := by
    rw [h2]
  rwa [PathCast.cast_cast_symm, PathCast.cast_cast_symm] at h3

/-- The image under `castVG h` of a conjugate of a relator at `a` is a conjugate of the same
relator at `b`. -/
theorem castVG_mem_relatorSet {P : Work.ORLocInd.Howie.Presentation V} {a b : V} (h : a = b) :
    ∀ x ∈ P.relatorSet a, castVG h x ∈ P.relatorNormalClosure b := by
  rintro x ⟨i, δ, hδ, rfl⟩
  refine Subgroup.subset_normalClosure
    ⟨i, δ.cast h rfl, (PathCast.cast_isReduced δ h rfl).mpr hδ, ?_⟩
  apply Subtype.ext
  show (Work.ORLocInd.Howie.pmul δ (Work.ORLocInd.Howie.pmul (P.path i) δ.reverse)).cast h h =
    Work.ORLocInd.Howie.pmul (δ.cast h rfl)
      (Work.ORLocInd.Howie.pmul (P.path i) (δ.cast h rfl).reverse)
  rw [← PathCast.cast_pmul δ (Work.ORLocInd.Howie.pmul (P.path i) δ.reverse) h rfl h,
    ← PathCast.cast_pmul (P.path i) δ.reverse rfl rfl h,
    PathCast.cast_self (P.path i) rfl rfl,
    ← PathCast.cast_reverse δ h rfl]

/-- The normal closure of the relators is carried into the normal closure at the other vertex by
`castVG`. -/
theorem castVG_relatorNormalClosure_le {P : Work.ORLocInd.Howie.Presentation V} {a b : V}
    (h : a = b) :
    (P.relatorNormalClosure a).map (castVG h) ≤ P.relatorNormalClosure b := by
  refine (Subgroup.map_le_iff_le_comap).mpr ?_
  exact Subgroup.normalClosure_le_normal (fun x hx => castVG_mem_relatorSet h x hx)

/-- Pointwise form of `castVG_relatorNormalClosure_le`. -/
theorem castVG_mem_relatorNormalClosure {P : Work.ORLocInd.Howie.Presentation V} {a b : V}
    (h : a = b) {x : Work.ORLocInd.Howie.VertexGroup a}
    (hx : x ∈ P.relatorNormalClosure a) : castVG h x ∈ P.relatorNormalClosure b :=
  castVG_relatorNormalClosure_le (P := P) h (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

end Work.Case1
