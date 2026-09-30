import Mathlib
import Submission.Work.RiemannRoch.RR.snake
import Submission.Work.RiemannRoch.RR.finrank_Kquot_eq
import Submission.Work.RiemannRoch.RR.finite_H1
import Submission.Work.RiemannRoch.Aquot.finrank_Aquot
import Submission.Work.RiemannRoch.Linear.finrank_Lquot
import Submission.Work.CurveBasics.Divisor.deg_nonneg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

namespace Work.RiemannRoch.RR

open Work.CurveBasics

/-- An injective linear map `s : W →ₗ V` identifies the relative quotient `N/M`, computed
inside `W`, with the relative quotient `(N.map s)/(M.map s)`, computed inside `V`. -/
noncomputable def relQuot_map_equiv {k : Type u} [Field k] {W V : Type u}
    [AddCommGroup W] [Module k W] [AddCommGroup V] [Module k V]
    (s : W →ₗ[k] V) (hs : Function.Injective s) (M N : Submodule k W) :
    (↥N ⧸ M.comap N.subtype) ≃ₗ[k]
      (↥(N.map s) ⧸ (M.map s).comap (N.map s).subtype) :=
  Submodule.Quotient.equiv (M.comap N.subtype) ((M.map s).comap (N.map s).subtype)
    (Submodule.equivMapOfInjective s hs N) (by
      ext y
      constructor
      · intro hy
        rw [Submodule.mem_map] at hy
        obtain ⟨x, hx, hxy⟩ := hy
        rw [Submodule.mem_comap, Submodule.mem_map]
        exact ⟨(x : W), Submodule.mem_comap.mp hx, congrArg Subtype.val hxy⟩
      · intro hy
        rw [Submodule.mem_comap, Submodule.mem_map] at hy
        obtain ⟨m, hm, hsm⟩ := hy
        obtain ⟨n, hn, hsn⟩ := Submodule.mem_map.mp y.2
        have hmn : m = n := hs (hsm.trans hsn.symm)
        rw [Submodule.mem_map]
        refine ⟨⟨m, by rw [hmn]; exact hn⟩, ?_, ?_⟩
        · rw [Submodule.mem_comap]; exact hm
        · apply Subtype.ext; exact hsm)

/-- The relative quotient `(A(E)+K)/(A(D)+K)` computed inside the adèle space is the same as
`Kquot C D E = (A(E)+K)/(A(D)+K)` computed inside the product `Place → K`. -/
noncomputable def relQuot_sup_diagK_equiv_Kquot {k : Type u} [Field k]
    (C : Work.CurveBasics.Curve k) (D E : C.Div) :
    Work.RiemannRoch.Curve.relQuot (Work.RiemannRoch.Curve.Asub C D ⊔ Work.RiemannRoch.Curve.diagK C)
        (Work.RiemannRoch.Curve.Asub C E ⊔ Work.RiemannRoch.Curve.diagK C)
      ≃ₗ[k] Work.RiemannRoch.Curve.Kquot C D E := by
  have hAsub : ∀ F : C.Div, (Work.RiemannRoch.Curve.Asub C F).map
      (Work.RiemannRoch.Curve.Adeles C).subtype = Work.RiemannRoch.Curve.A C F := by
    intro F
    rw [Work.RiemannRoch.Curve.Asub, Submodule.map_comap_eq, Submodule.range_subtype]
    exact inf_eq_right.mpr (Work.RiemannRoch.Curve.A_le_adeles C F)
  have hdiag : (Work.RiemannRoch.Curve.diagK C).map
      (Work.RiemannRoch.Curve.Adeles C).subtype = Work.RiemannRoch.Curve.Kdiag C := by
    have hc : (Work.RiemannRoch.Curve.Adeles C).subtype.comp (Work.RiemannRoch.Curve.diag C)
        = Work.RiemannRoch.Curve.diagFn C := by
      ext a Q; rfl
    rw [Work.RiemannRoch.Curve.diagK, Work.RiemannRoch.Curve.Kdiag, ← LinearMap.range_comp, hc]
  have hmap : ∀ F : C.Div, (Work.RiemannRoch.Curve.Asub C F ⊔ Work.RiemannRoch.Curve.diagK C).map
      (Work.RiemannRoch.Curve.Adeles C).subtype
        = Work.RiemannRoch.Curve.A C F ⊔ Work.RiemannRoch.Curve.Kdiag C := by
    intro F; rw [Submodule.map_sup, hAsub F, hdiag]
  have e := relQuot_map_equiv (Work.RiemannRoch.Curve.Adeles C).subtype
    (Submodule.subtype_injective _)
    (Work.RiemannRoch.Curve.Asub C D ⊔ Work.RiemannRoch.Curve.diagK C)
    (Work.RiemannRoch.Curve.Asub C E ⊔ Work.RiemannRoch.Curve.diagK C)
  rw [hmap E, hmap D] at e
  exact e

theorem finrank_sup_diagK_quot {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D E : C.Div}
    (h : D ≤ E) :
    FiniteDimensional k
      (Work.RiemannRoch.Curve.relQuot
        (Work.RiemannRoch.Curve.Asub C D ⊔ Work.RiemannRoch.Curve.diagK C)
        (Work.RiemannRoch.Curve.Asub C E ⊔ Work.RiemannRoch.Curve.diagK C)) ∧
    (Module.finrank k
      (Work.RiemannRoch.Curve.relQuot
        (Work.RiemannRoch.Curve.Asub C D ⊔ Work.RiemannRoch.Curve.diagK C)
        (Work.RiemannRoch.Curve.Asub C E ⊔ Work.RiemannRoch.Curve.diagK C)) : ℤ) =
      (C.deg E - C.l E) - (C.deg D - C.l D) := by
  have hleF : (E - D).IsEffective :=
    Curve.Div.le_iff.mpr fun Q => Finsupp.le_def.mp h Q
  have hfin : Module.Finite k
      (Work.RiemannRoch.Curve.relQuot
        (Work.RiemannRoch.Curve.Asub C D ⊔ Work.RiemannRoch.Curve.diagK C)
        (Work.RiemannRoch.Curve.Asub C E ⊔ Work.RiemannRoch.Curve.diagK C)) :=
    finite_sup_quotient (S := Work.RiemannRoch.Curve.Asub C D)
      (T := Work.RiemannRoch.Curve.Asub C E) (K := Work.RiemannRoch.Curve.diagK C)
      (finite_relQuot_Asub C h)
  refine ⟨hfin, ?_⟩
  have he := relQuot_sup_diagK_equiv_Kquot C D E
  have hle : C.l D ≤ C.l E := by
    haveI : Module.Finite k ↥(C.L E) := Work.CurveBasics.Linear.finiteDimensional_L C E
    exact Submodule.finrank_mono (C.L_mono (Curve.Div.le_iff.mpr fun Q => Finsupp.le_def.mp h Q))
  have hsnake := snake C h
  have hcastA : (Module.finrank k (Work.RiemannRoch.Curve.Aquot C D E) : ℤ)
      = C.deg E - C.deg D := by
    rw [Work.RiemannRoch.Aquot.finrank_Aquot C h,
      Int.toNat_of_nonneg (Work.CurveBasics.Divisor.deg_nonneg hleF),
      Work.CurveBasics.Curve.deg_sub]
  have hcastL : (Module.finrank k (Work.RiemannRoch.Curve.Lquot C D E) : ℤ)
      = (C.l E : ℤ) - C.l D := by
    rw [Work.RiemannRoch.Linear.finrank_Lquot C h, Nat.cast_sub hle]
  have hleA : Module.finrank k (Work.RiemannRoch.Curve.Lquot C D E)
      ≤ Module.finrank k (Work.RiemannRoch.Curve.Aquot C D E) :=
    Nat.le.intro hsnake.symm
  have hK : Module.finrank k (Work.RiemannRoch.Curve.Kquot C D E) =
      Module.finrank k (Work.RiemannRoch.Curve.Aquot C D E)
        - Module.finrank k (Work.RiemannRoch.Curve.Lquot C D E) :=
    Nat.eq_sub_of_add_eq (by rw [add_comm]; exact hsnake.symm)
  rw [LinearEquiv.finrank_eq he]
  calc (Module.finrank k (Work.RiemannRoch.Curve.Kquot C D E) : ℤ)
      = (Module.finrank k (Work.RiemannRoch.Curve.Aquot C D E) : ℤ)
          - (Module.finrank k (Work.RiemannRoch.Curve.Lquot C D E) : ℤ) := by
        rw [hK, Nat.cast_sub hleA]
    _ = (C.deg E - C.deg D) - ((C.l E : ℤ) - C.l D) := by rw [hcastA, hcastL]
    _ = (C.deg E - C.l E) - (C.deg D - C.l D) := by ring

end Work.RiemannRoch.RR
