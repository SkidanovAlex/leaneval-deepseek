import Mathlib
import Submission.Work.RiemannRoch.Quotients
import Submission.Work.CurveBasics.Linear.finiteDimensional_L

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.RiemannRoch.Linear

universe u

set_option linter.style.haveILetI false

open Work.CurveBasics
open Work.RiemannRoch.Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The diagonal map `K ↪ (Place → K)` is injective: a curve has a place. -/
theorem diagFn_injective (C : Curve k) : Function.Injective (diagFn C) := by
  intro a b h
  have h' : (fun _ : C.Place => a) = fun _ : C.Place => b := h
  exact congrFun h' (Classical.choice (inferInstance : Nonempty C.Place))

/-- The diagonal copy of `h` in the product lies in `A D` exactly when `h ∈ L D`. -/
theorem diagFn_mem_A_iff {C : Curve k} {D : C.Div} {h : C.functionField} :
    diagFn C h ∈ A C D ↔ h ∈ C.L D := by
  show ((diag C h : Adeles C) : C.Place → C.functionField) ∈ A C D ↔ h ∈ C.L D
  exact (mem_Asub (x := diag C h)).symm.trans (diag_mem_Asub_iff (C := C) (D := D))

/-- `L D` is linearly equivalent to `A D ⊓ Kdiag`, via the diagonal embedding. -/
noncomputable def inf_Kdiag_equiv (C : Curve k) (D : C.Div) :
    ↥(C.L D) ≃ₗ[k] ↥(A C D ⊓ Kdiag C) :=
  LinearEquiv.ofBijective
    (((diagFn C).comp (C.L D).subtype).codRestrict (A C D ⊓ Kdiag C) (fun h => by
      rw [Submodule.mem_inf]
      exact ⟨(diagFn_mem_A_iff (C := C) (D := D)).mpr h.2, ⟨h.1, rfl⟩⟩))
    ⟨fun a b hab => Subtype.ext (diagFn_injective C (congrArg Subtype.val hab)),
     fun x => by
      obtain ⟨hxA, hxK⟩ := Submodule.mem_inf.mp x.2
      obtain ⟨g, hg⟩ := (mem_Kdiag (C := C)).mp hxK
      have hgL : g ∈ C.L D := by
        rw [← diagFn_mem_A_iff (C := C) (D := D), hg]
        exact hxA
      exact ⟨⟨g, hgL⟩, Subtype.ext hg⟩⟩

theorem finrank_Lquot {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D E : C.Div}
    (h : D ≤ E) :
    Module.finrank k (Work.RiemannRoch.Curve.Lquot C D E) = C.l E - C.l D := by
  haveI hfinE : FiniteDimensional k ↥(C.L E) := Work.CurveBasics.Linear.finiteDimensional_L C E
  have hLE : C.L D ≤ C.L E := C.L_mono (Work.CurveBasics.Curve.Div.le_iff.mpr h)
  have hMDME : A C D ⊓ Kdiag C ≤ A C E ⊓ Kdiag C :=
    inf_le_inf (A_mono C h) le_rfl
  have eD := inf_Kdiag_equiv C D
  have eE := inf_Kdiag_equiv C E
  haveI hMEfin : Module.Finite k ↥(A C E ⊓ Kdiag C) := Module.Finite.equiv eE
  have hME : Module.finrank k ↥(A C E ⊓ Kdiag C) = C.l E :=
    (LinearEquiv.finrank_eq eE).symm
  have hMD : Module.finrank k ↥(A C D ⊓ Kdiag C) = C.l D :=
    (LinearEquiv.finrank_eq eD).symm
  have hP : Module.finrank k
      ↥((A C D ⊓ Kdiag C).comap (A C E ⊓ Kdiag C).subtype) = C.l D :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hMDME)).trans hMD
  have key := Submodule.finrank_quotient_add_finrank
    (R := k) ((A C D ⊓ Kdiag C).comap (A C E ⊓ Kdiag C).subtype)
  rw [hP, hME] at key
  exact Nat.eq_sub_of_add_eq key

end

end Work.RiemannRoch.Linear
