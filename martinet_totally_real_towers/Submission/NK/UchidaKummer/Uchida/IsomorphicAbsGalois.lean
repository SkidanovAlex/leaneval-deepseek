import Mathlib
import Submission.NK.UchidaKummer.Uchida.ModuleData

set_option linter.style.haveILetI false

namespace NK.UchidaKummer

/-!
# Isomorphic number fields have isomorphic absolute Galois groups

Let `e : K₁ ≃+* K₂` be a ring isomorphism of fields.  Every separable closure `K₁'` of `K₁` can
be regarded as a separable closure of `K₂` through `e`, and conversely; hence the Galois groups
`Gal(K₁'/K₁)` and `Gal(K₂'/K₂)` are isomorphic.  This is the elementary input the Uchida
strategy needs: the absolute Galois group is an invariant of the field up to isomorphism.

(This file is a copy, inside `NK.UchidaKummer`, of the proof written for the delegated lemma
`NK.Uchida.hasIsomorphicAbsGalois_of_ringEquiv`.)

The two general lemmas below do the work.  `algEquivCongrOfAlgebraMap` identifies the automorphism
groups of `E` over two algebra structures whose structure maps differ by a ring isomorphism `e` of
the bases; `hasIsomorphicAbsGalois_of_ringEquiv` uses `Algebra.IsSeparable.iff_of_equiv_equiv`
(Mathlib) to transfer separability of `K₂'` over `K₂` to separability of `K₂'` over `K₁` along `e`,
and then `IsSepClosure.equiv` to compare the two separable closures.
-/

/-- **Automorphism groups over two algebra structures on the same field.**

If the two algebra structures are related by a ring isomorphism `e` of the base rings, through
`algebraMap k₁ E = (algebraMap k₂ E).comp e`, then the two automorphism groups coincide: an
`E ≃ₐ[k₁] E` is the same thing as an `E ≃ₐ[k₂] E` (the underlying ring equivalence is unchanged). -/
def algEquivCongrOfAlgebraMap {k₁ k₂ E : Type*} [Field k₁] [Field k₂] [Field E]
    [Algebra k₁ E] [Algebra k₂ E] (e : k₁ ≃+* k₂)
    (h : ∀ x : k₁, algebraMap k₁ E x = algebraMap k₂ E (e x)) :
    (E ≃ₐ[k₁] E) ≃* (E ≃ₐ[k₂] E) where
  toFun σ :=
    { toRingEquiv := σ.toRingEquiv
      commutes' := fun b => by
        have hb : algebraMap k₂ E b = algebraMap k₁ E (e.symm b) := by
          rw [h (e.symm b), e.apply_symm_apply]
        rw [hb]
        exact σ.commutes (e.symm b) }
  invFun τ :=
    { toRingEquiv := τ.toRingEquiv
      commutes' := fun a => by
        rw [h a]
        exact τ.commutes (e a) }
  left_inv σ := by ext x; rfl
  right_inv τ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

/-- Isomorphic number fields have isomorphic absolute Galois groups (in the sense of
`NK.UchidaKummer.HasIsomorphicAbsGalois`, which quantifies over all choices of separable closure). -/
theorem hasIsomorphicAbsGalois_of_ringEquiv {K₁ K₂ : Type*} [Field K₁] [NumberField K₁]
    [Field K₂] [NumberField K₂] (e : K₁ ≃+* K₂) :
    NK.UchidaKummer.HasIsomorphicAbsGalois K₁ K₂ := by
  intro K₁' _ _ _ K₂' _ _ _
  -- Regard `K₂'` as a `K₁`-algebra by pulling back scalars along `e`.
  let φ : K₁ →+* K₂' := (algebraMap K₂ K₂').comp e.toRingHom
  letI : Algebra K₁ K₂' := φ.toAlgebra
  -- `K₂'` is still separable over the new base `K₁` (`Algebra.IsSeparable.iff_of_equiv_equiv`),
  -- so it is a separable closure of `K₁`.
  have hsep : Algebra.IsSeparable K₁ K₂' :=
    (Algebra.IsSeparable.iff_of_equiv_equiv e (RingEquiv.refl K₂') (by ext x; rfl)).mpr
      (inferInstance : Algebra.IsSeparable K₂ K₂')
  haveI : IsSepClosure K₁ K₂' :=
    ⟨(inferInstance : IsSepClosure K₂ K₂').sep_closed, hsep⟩
  -- Both `K₁'` and `K₂'` are separable closures of `K₁`, and conjugating by a `K₁`-algebra
  -- isomorphism between them identifies the `K₁`-automorphism groups; the second factor then
  -- replaces `K₁`-linearity by `K₂`-linearity.
  exact ⟨(AlgEquiv.autCongr (IsSepClosure.equiv K₁ K₁' K₂')).trans
    (algEquivCongrOfAlgebraMap e (fun x => rfl))⟩

end NK.UchidaKummer
