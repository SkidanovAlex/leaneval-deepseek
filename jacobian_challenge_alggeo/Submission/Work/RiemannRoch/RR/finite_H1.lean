import Mathlib
import Submission.Work.RiemannRoch.Quotients
import Submission.Work.RiemannRoch.Aquot.finrank_Aquot

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

namespace Work.RiemannRoch.RR

open Work.CurveBasics

/-! ## Auxiliary module lemmas

These are pure linear-algebra facts about quotients of `k`-modules used to assemble the
finiteness of `H1 C D` from the finiteness of `H1 C 0` and of the one-step quotients
`A(E)/A(D)`. -/

/-- If `P ≤ Q` are submodules of a `k`-module `X`, `X ⧸ Q` is finite and `Q ⧸ (P ⊓ Q)` is
finite, then `X ⧸ P` is finite (extension of a finite module by a finite submodule). -/
theorem finite_quotient_of_le {k : Type u} [Field k] {X : Type u} [AddCommGroup X] [Module k X]
    (P Q : Submodule k X) (h : P ≤ Q)
    (hQ : Module.Finite k (X ⧸ Q))
    (hPQ : Module.Finite k (Q ⧸ Submodule.comap Q.subtype P)) :
    Module.Finite k (X ⧸ P) := by
  have hN : Module.Finite k (Submodule.map P.mkQ Q) := by
    have hker : LinearMap.ker (P.mkQ.comp Q.subtype) = Submodule.comap Q.subtype P := by
      ext x
      simp [LinearMap.mem_ker, Submodule.mem_comap]
    have hrange : LinearMap.range (P.mkQ.comp Q.subtype) = Submodule.map P.mkQ Q := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have e := LinearMap.quotKerEquivRange (P.mkQ.comp Q.subtype)
    rw [hker, hrange] at e
    exact Module.Finite.equiv e
  haveI : Module.Finite k (Submodule.map P.mkQ Q) := hN
  haveI : Module.Finite k ((X ⧸ P) ⧸ Submodule.map P.mkQ Q) :=
    Module.Finite.equiv (Submodule.quotientQuotientEquivQuotient P Q h).symm
  exact Module.Finite.of_submodule_quotient (Submodule.map P.mkQ Q)

/-- For `S ≤ T` submodules of a `k`-module `X` and any submodule `K`, the quotient
`(T ⊔ K)/(S ⊔ K)` is finite whenever `T ⧸ (S ⊓ T)` is finite: it is a quotient of `T/(S ⊓ T)`. -/
theorem finite_sup_quotient {k : Type u} [Field k] {X : Type u} [AddCommGroup X] [Module k X]
    {S T K : Submodule k X}
    (hfin : Module.Finite k (T ⧸ Submodule.comap T.subtype S)) :
    Module.Finite k (↥(T ⊔ K) ⧸ Submodule.comap (T ⊔ K).subtype (S ⊔ K)) := by
  set R : Submodule k ↥(T ⊔ K) :=
    Submodule.comap (T ⊔ K).subtype (S ⊔ K) with hR
  let θ : ↥T →ₗ[k] ↥(T ⊔ K) ⧸ R :=
    R.mkQ.comp (Submodule.inclusion le_sup_left)
  have hθt : ∀ x : ↥T, θ x = R.mkQ (⟨(x : X), Submodule.mem_sup_left x.2⟩ : ↥(T ⊔ K)) := by
    intro x; rfl
  have hker : θ.ker = Submodule.comap T.subtype (S ⊔ K) := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    rw [hθt x, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hR, Submodule.mem_comap]
    rfl
  have hsurj : Function.Surjective θ := by
    intro y
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective R y
    obtain ⟨t, ht, k, hk, htk⟩ := Submodule.mem_sup.mp q.2
    refine ⟨⟨t, ht⟩, ?_⟩
    have hq : q = (⟨t, Submodule.mem_sup_left ht⟩ : ↥(T ⊔ K))
        + ⟨k, Submodule.mem_sup_right hk⟩ := by
      ext; exact htk.symm
    rw [hθt ⟨t, ht⟩, hq, map_add]
    have hk0 : R.mkQ (⟨k, Submodule.mem_sup_right hk⟩ : ↥(T ⊔ K)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hR, Submodule.mem_comap]
      exact Submodule.mem_sup_right hk
    rw [hk0, add_zero]
  haveI : Module.Finite k (↥T ⧸ θ.ker) := by
    have hle : Submodule.comap T.subtype S ≤ θ.ker := by
      rw [hker]; exact Submodule.comap_mono le_sup_left
    refine Module.Finite.of_surjective
      (Submodule.mapQ (Submodule.comap T.subtype S) θ.ker LinearMap.id ?_) ?_
    · rw [Submodule.comap_id]; exact hle
    · intro y
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective θ.ker y
      exact ⟨Submodule.Quotient.mk x, by rw [Submodule.mapQ_apply]; rfl⟩
  have hrange : θ.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  haveI : Module.Finite k ↥θ.range := Module.Finite.equiv (LinearMap.quotKerEquivRange θ)
  exact Module.Finite.equiv ((LinearEquiv.ofEq θ.range ⊤ hrange).trans Submodule.topEquiv)

/-- The adelic quotient `A(E)/A(D)` is finite dimensional for `D ≤ E`, with dimension
`deg (E - D)`; here we only record finiteness. -/
theorem finite_Aquot_of_le {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D E : C.Div}
    (h : D ≤ E) : Module.Finite k (Work.RiemannRoch.Curve.Aquot C D E) := by
  have hF : Work.CurveBasics.Curve.Div.IsEffective (E - D) :=
    Work.CurveBasics.Curve.Div.le_iff.mpr fun Q => Finsupp.le_def.mp h Q
  have hrank := Work.RiemannRoch.Aquot.rank_Aquot_add C D (E - D) hF
  rw [add_sub_cancel D E] at hrank
  have hlt : Module.rank k (Work.RiemannRoch.Curve.Aquot C D E) < Cardinal.aleph0 := by
    rw [hrank]; exact Cardinal.natCast_lt_aleph0
  exact Module.rank_lt_aleph0_iff.mp hlt

/-- The quotient `A(E)/A(D)` of adèles with poles bounded by `E` modulo those bounded by `D`,
computed inside the adèle ring, is canonically the same as the quotient of the lattice
`A(E)` by `A(D)` used in `Aquot`. -/
noncomputable def relQuot_Asub_equiv_Aquot {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (D E : C.Div) :
    Work.RiemannRoch.Curve.relQuot (Work.RiemannRoch.Curve.Asub C D)
      (Work.RiemannRoch.Curve.Asub C E) ≃ₗ[k] Work.RiemannRoch.Curve.Aquot C D E := by
  let e : ↥(Work.RiemannRoch.Curve.Asub C E) ≃ₗ[k] ↥(Work.RiemannRoch.Curve.A C E) :=
    { toFun := fun x => ⟨x.1.1, Work.RiemannRoch.Curve.mem_Asub.mp x.2⟩
      invFun := fun y => ⟨⟨y.1, Work.RiemannRoch.Curve.A_le_adeles C E y.2⟩,
        Work.RiemannRoch.Curve.mem_Asub.mpr y.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl
      map_smul' := fun c x => Subtype.ext rfl }
  have hmap : Submodule.map e.toLinearMap
      ((Work.RiemannRoch.Curve.Asub C D).comap (Work.RiemannRoch.Curve.Asub C E).subtype)
      = (Work.RiemannRoch.Curve.A C D).comap (Work.RiemannRoch.Curve.A C E).subtype := by
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Submodule.mem_comap] at hx ⊢
      exact Work.RiemannRoch.Curve.mem_Asub.mp hx
    · intro hy
      rw [Submodule.mem_comap] at hy
      refine ⟨e.symm y, ?_, by simp⟩
      rw [Submodule.mem_comap, Work.RiemannRoch.Curve.mem_Asub]
      exact hy
  exact Submodule.Quotient.equiv _ _ e hmap

theorem finite_relQuot_Asub {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) {D E : C.Div}
    (h : D ≤ E) :
    Module.Finite k (Work.RiemannRoch.Curve.relQuot (Work.RiemannRoch.Curve.Asub C D)
      (Work.RiemannRoch.Curve.Asub C E)) := by
  have hfin := finite_Aquot_of_le C h
  have he := relQuot_Asub_equiv_Aquot C D E
  haveI := hfin
  exact Module.Finite.equiv he.symm


/-- The positive part `D⁺` of a divisor: `D⁺ Q = max 0 (D Q)`.  It is an effective divisor
dominating `D`. -/
noncomputable def divPos {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} (D : C.Div) :
    C.Div := D.mapRange (fun n : ℤ => max 0 n) (by simp)

@[simp]
theorem divPos_apply {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} (D : C.Div)
    (Q : C.Place) : divPos D Q = max 0 (D Q) := Finsupp.mapRange_apply

theorem le_divPos {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} (D : C.Div) :
    D ≤ divPos D :=
  Finsupp.le_def.mpr fun Q => by rw [divPos_apply]; exact le_max_right 0 (D Q)

theorem zero_le_divPos {k : Type u} [Field k] {C : Work.CurveBasics.Curve k} (D : C.Div) :
    (0 : C.Div) ≤ divPos D :=
  Finsupp.le_def.mpr fun Q => by
    rw [divPos_apply, Finsupp.zero_apply]; exact le_max_left 0 (D Q)

theorem finite_H1 {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (h : Work.RiemannRoch.Curve.HasFiniteGenus C) (D : C.Div) :
    Module.Finite k (Work.RiemannRoch.Curve.H1 C D) := by
  haveI h0 : Module.Finite k (Work.RiemannRoch.Curve.H1 C 0) := h
  set E : C.Div := divPos D with hE
  have hDE : D ≤ E := by
    rw [Finsupp.le_def]; intro Q
    rw [hE, divPos_apply]; exact le_max_right 0 (D Q)
  have h0E : (0 : C.Div) ≤ E := by
    rw [Finsupp.le_def]; intro Q
    rw [hE, divPos_apply, Finsupp.zero_apply]
    exact le_max_left 0 (D Q)
  have hAsubDE : Work.RiemannRoch.Curve.Asub C D ≤ Work.RiemannRoch.Curve.Asub C E :=
    Submodule.comap_mono (Work.RiemannRoch.Curve.A_mono C hDE)
  have hAsub0E : Work.RiemannRoch.Curve.Asub C 0 ≤ Work.RiemannRoch.Curve.Asub C E :=
    Submodule.comap_mono (Work.RiemannRoch.Curve.A_mono C h0E)
  have hEfin : Module.Finite k (Work.RiemannRoch.Curve.H1 C E) := by
    have hPQ : Work.RiemannRoch.Curve.Asub C 0 ⊔ Work.RiemannRoch.Curve.diagK C
        ≤ Work.RiemannRoch.Curve.Asub C E ⊔ Work.RiemannRoch.Curve.diagK C :=
      sup_le_sup hAsub0E le_rfl
    refine Module.Finite.of_surjective
      (Submodule.mapQ (Work.RiemannRoch.Curve.Asub C 0 ⊔ Work.RiemannRoch.Curve.diagK C)
        (Work.RiemannRoch.Curve.Asub C E ⊔ Work.RiemannRoch.Curve.diagK C) LinearMap.id ?_) ?_
    · rw [Submodule.comap_id]; exact hPQ
    · intro y
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
      exact ⟨Submodule.Quotient.mk x, by rw [Submodule.mapQ_apply]; rfl⟩
  have hrel : Module.Finite k (Work.RiemannRoch.Curve.relQuot (Work.RiemannRoch.Curve.Asub C D)
      (Work.RiemannRoch.Curve.Asub C E)) := finite_relQuot_Asub C hDE
  have hPQ2 : Work.RiemannRoch.Curve.Asub C D ⊔ Work.RiemannRoch.Curve.diagK C
      ≤ Work.RiemannRoch.Curve.Asub C E ⊔ Work.RiemannRoch.Curve.diagK C :=
    sup_le_sup hAsubDE le_rfl
  have hsup := finite_sup_quotient (S := Work.RiemannRoch.Curve.Asub C D)
    (T := Work.RiemannRoch.Curve.Asub C E) (K := Work.RiemannRoch.Curve.diagK C) hrel
  exact finite_quotient_of_le (Work.RiemannRoch.Curve.Asub C D ⊔ Work.RiemannRoch.Curve.diagK C)
    (Work.RiemannRoch.Curve.Asub C E ⊔ Work.RiemannRoch.Curve.diagK C) hPQ2 hEfin hsup

end Work.RiemannRoch.RR
