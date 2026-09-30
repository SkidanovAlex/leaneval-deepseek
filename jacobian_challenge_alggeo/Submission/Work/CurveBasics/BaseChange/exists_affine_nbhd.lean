import Mathlib
import Submission.Work.CurveBasics.BaseChangeFunctionField
import Submission.Work.CurveBasics.Order.div_inv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.CurveBasics.BaseChange

open Work.CurveBasics

open scoped Classical

/-- A finite set of places of a curve, viewed as a subset of the underlying topological space,
is closed. -/
theorem isClosed_placeImage {k : Type*} [Field k] (C : Curve k) {A : Set C.Place}
    (hA : A.Finite) : IsClosed ((fun Q : C.Place => Q.point) '' A) := by
  have h : ((fun Q : C.Place => Q.point) '' A) = ⋃ Q ∈ A, ({Q.point} : Set C.left) := by
    ext w
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · rintro ⟨Q, hQ, hw⟩; exact ⟨Q, hQ, hw.symm⟩
    · rintro ⟨Q, hQ, hw⟩; exact ⟨Q, hQ, hw.symm⟩
  rw [h]
  exact hA.isClosed_biUnion fun Q _ => Q.isClosed

/-- Every point of a curve has an affine open neighbourhood avoiding a prescribed finite set of
places. -/
theorem exists_affine_nbhd_avoiding {k : Type*} [Field k] (C : Curve k) {A : Set C.Place}
    (hA : A.Finite) {z : C.left} (hz : ∀ Q ∈ A, Q.point ≠ z) :
    ∃ W : C.left.Opens, AlgebraicGeometry.IsAffineOpen W ∧ z ∈ W ∧
      ∀ Q : C.Place, Q.point ∈ W → Q ∉ A := by
  have hcl : IsClosed ((fun Q : C.Place => Q.point) '' A) := isClosed_placeImage C hA
  have hznot : z ∈ ((fun Q : C.Place => Q.point) '' A)ᶜ := by
    rintro ⟨Q, hQ, hQz⟩
    exact hz Q hQ hQz
  have hb : TopologicalSpace.IsTopologicalBasis
      ((↑) '' C.left.affineOpens : Set (Set C.left)) := C.left.isBasis_affineOpens
  obtain ⟨-, ⟨W, hWaff, rfl⟩, hzW, hWU⟩ := hb.exists_subset_of_mem_open hznot hcl.isOpen_compl
  exact ⟨W, hWaff, hzW, fun Q hQW hQA => hWU hQW ⟨Q, hQA, rfl⟩⟩

open Work.CurveBasics in
theorem exists_affine_nbhd {k : Type*} [Field k] {C : Curve k} (x : C.functionField)
    (hx : x ≠ 0) (z : C.left) :
    ∃ W : C.left.Opens, AlgebraicGeometry.IsAffineOpen W ∧ z ∈ W ∧
      (C.RegularOn W x ∨ C.RegularOn W x⁻¹) := by
  classical
  have hpole : {Q : C.Place | C.ordAt x Q < 0}.Finite :=
    (C.finite_support_ordAt x).subset fun Q hQ => ne_of_lt hQ
  have hzero : {Q : C.Place | 0 < C.ordAt x Q}.Finite :=
    (C.finite_support_ordAt x).subset fun Q hQ => ne_of_gt hQ
  by_cases hzpole : ∃ Q : C.Place, C.ordAt x Q < 0 ∧ Q.point = z
  · -- `z` is a pole of `x`, so `x⁻¹` is regular on a small affine neighbourhood of `z`.
    obtain ⟨Q₀, hQ₀ord, hQ₀z⟩ := hzpole
    have hznot : ∀ Q ∈ {Q : C.Place | 0 < C.ordAt x Q}, Q.point ≠ z := by
      intro Q hQ hQz
      have hQQ₀ : Q = Q₀ := Subtype.ext (hQz.trans hQ₀z.symm)
      rw [hQQ₀] at hQ
      simp only [Set.mem_ofPred_eq] at hQ
      linarith
    obtain ⟨W, hWaff, hzW, hW⟩ := exists_affine_nbhd_avoiding C hzero hznot
    refine ⟨W, hWaff, hzW, Or.inr ?_⟩
    intro Q hQW
    have hQnz : Q ∉ {Q : C.Place | 0 < C.ordAt x Q} := hW Q hQW
    have hle : C.ordAt x Q ≤ 0 := by
      by_contra h
      exact hQnz (lt_of_not_ge h)
    rw [show C.ordAt x⁻¹ Q = -C.ordAt x Q from Work.CurveBasics.Order.ordAt_inv C hx Q]
    linarith
  · -- `z` is not a pole of `x`, so `x` is regular on a small affine neighbourhood of `z`.
    have hznot : ∀ Q ∈ {Q : C.Place | C.ordAt x Q < 0}, Q.point ≠ z := by
      intro Q hQ hQz
      exact hzpole ⟨Q, hQ, hQz⟩
    obtain ⟨W, hWaff, hzW, hW⟩ := exists_affine_nbhd_avoiding C hpole hznot
    refine ⟨W, hWaff, hzW, Or.inl ?_⟩
    intro Q hQW
    have hQnp : Q ∉ {Q : C.Place | C.ordAt x Q < 0} := hW Q hQW
    by_contra h
    exact hQnp (lt_of_not_ge h)

end Work.CurveBasics.BaseChange
