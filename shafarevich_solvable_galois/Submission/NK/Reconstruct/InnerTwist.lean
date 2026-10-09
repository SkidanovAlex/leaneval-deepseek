import Submission.NK.Reconstruct.Transport
import Submission.NeukirchUchida.Conjugation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The obstruction to the existence of a realizing `σ`, and the inner-twist reduction

The reconstruction step of Neukirch–Uchida asks for a field isomorphism
`σ : K₂' ≃+* K₁'` with `MapsBase` such that `Conjugates σ ϕ`, i.e.
`ϕ g = σ⁻¹ ∘ g ∘ σ` for every `g : Gal(K₁'/K₁)`.

Once *some* `MapsBase` isomorphism `σ₀ : K₂' ≃+* K₁'` is known — equivalently, once the *base
field* isomorphism between the number fields is known (the "weak" Neukirch–Uchida theorem) — the
freedom in `σ` is right multiplication by an element of `Gal(K₂'/K₂)`, and the obstruction to
realizing `ϕ` is the automorphism

  `β := Φ_{σ₀} ∘ ϕ⁻¹ : Gal(K₂'/K₂) ≃* Gal(K₂'/K₂)`,  where  `Φ_{σ₀} := conjHomEquiv hσ₀`.

This file proves the two halves of the resulting equivalence:

* `conjugates_trans_of_conj_normal` — **if `β` is inner** (`β = MulAut.conj k`), then
  `σ := σ₀ ∘ k` realizes `ϕ`: `Conjugates (k.toRingEquiv.trans σ₀) ϕ`, with no hypothesis on `ϕ`
  beyond the existence of `σ₀`;  the realizing isomorphism is exhibited explicitly, so the deep
  input of the reconstruction is *exactly* the vanishing of the class of `β` in
  `Out(Gal(K₂'/K₂))`.
* `trans_eq_conj_of_conjugates` — conversely, if `σ = σ₀ ∘ k` (for `k ∈ Gal(K₂'/K₂)`) realizes
  `ϕ`, then `β = MulAut.conj k`.

Reference: J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, XII §12.2;
S. Shimizu, arXiv:2009.10431, §4.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

section MapsBaseTrans

variable (σ₀ : K₂' ≃+* K₁')
  (hσ₀ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀)

include hσ₀

/-- **Composition with an element of `Gal(K₂'/K₂)` on the right preserves `MapsBase`.** -/
theorem mapsBase_trans (k : Gal(K₂'/K₂)) :
    Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂')
      (k.toRingEquiv.trans σ₀) := by
  rw [Submission.NeukirchUchida.MapsBase] at hσ₀ ⊢
  ext y
  constructor
  · intro hy
    rcases Subring.mem_map.mp hy with ⟨x, hx, hxy⟩
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp hx
    rw [← ha] at hxy
    have hxy' : σ₀ (algebraMap K₂ K₂' a) = y := by
      change (k.toRingEquiv.trans σ₀) (algebraMap K₂ K₂' a) = y at hxy
      rw [RingEquiv.trans_apply,
        show k.toRingEquiv (algebraMap K₂ K₂' a) = algebraMap K₂ K₂' a
          from k.commutes a] at hxy
      exact hxy
    rw [← hxy', ← hσ₀]
    exact Subring.mem_map.mpr ⟨algebraMap K₂ K₂' a, ⟨a, rfl⟩, rfl⟩
  · intro hy
    rw [← hσ₀] at hy
    rcases Subring.mem_map.mp hy with ⟨x, hx, hxy⟩
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp hx
    rw [← ha] at hxy
    refine Subring.mem_map.mpr ⟨algebraMap K₂ K₂' a, ⟨a, rfl⟩, ?_⟩
    change (k.toRingEquiv.trans σ₀) (algebraMap K₂ K₂' a) = y
    rw [RingEquiv.trans_apply,
      show k.toRingEquiv (algebraMap K₂ K₂' a) = algebraMap K₂ K₂' a from k.commutes a]
    exact hxy

end MapsBaseTrans

/-- **The inner-twist reduction.**  Let `σ₀ : K₂' ≃+* K₁'` be a base-field mapping isomorphism
with conjugation isomorphism `Φ_{σ₀} = conjHomEquiv hσ₀`, and let `k ∈ Gal(K₂'/K₂)`.  If the
obstruction `β := Φ_{σ₀} ∘ ϕ⁻¹` is the inner automorphism `MulAut.conj k`, then `σ := σ₀ ∘ k` is a
base-field mapping isomorphism inducing `ϕ`: `Conjugates (k.toRingEquiv.trans σ₀) ϕ`.

This is the precise sense in which the deep existence half of Neukirch–Uchida reduces to the
vanishing of the class of `β` in `Out(Gal(K₂'/K₂))` once the base fields are known to be
isomorphic. -/
theorem conjugates_trans_of_conj_normal {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {σ₀ : K₂' ≃+* K₁'}
    {hσ₀ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀}
    (k : Gal(K₂'/K₂))
    (h : ϕ.symm.trans (Submission.NeukirchUchida.conjHomEquiv hσ₀) = MulAut.conj k) :
    Submission.NeukirchUchida.Conjugates (k.toRingEquiv.trans σ₀) ϕ := by
  refine ⟨mapsBase_trans σ₀ hσ₀ k, fun g => ?_⟩
  have hpt : ∀ u : Gal(K₂'/K₂),
      Submission.NeukirchUchida.conjHomEquiv hσ₀ (ϕ.symm u) = k * u * k⁻¹ := by
    intro u
    have := DFunLike.congr_fun h u
    simpa [MulEquiv.trans_apply, MulAut.conj_apply] using this
  have hg : Submission.NeukirchUchida.conjHomEquiv hσ₀ g = k * (ϕ g) * k⁻¹ := by
    simpa using hpt (ϕ g)
  have key : ∀ x : K₂', (Submission.NeukirchUchida.conjHomEquiv hσ₀ g) (k x) = k ((ϕ g) x) := by
    intro x
    rw [hg]
    simp [AlgEquiv.mul_apply]
  have hconj : ∀ y : K₂', (Submission.NeukirchUchida.conjHomEquiv hσ₀ g) (k y)
      = σ₀.symm (g (σ₀ (k y))) := by
    intro y
    change (Submission.NeukirchUchida.conj hσ₀ g) (k y) = σ₀.symm (g (σ₀ (k y)))
    rw [Submission.NeukirchUchida.conj_apply]
  ext x
  have hmain : ((k.toRingEquiv.trans σ₀).trans
      (g.toRingEquiv.trans (k.toRingEquiv.trans σ₀).symm)) x = (ϕ g : K₂' ≃+* K₂') x := by
    calc ((k.toRingEquiv.trans σ₀).trans (g.toRingEquiv.trans (k.toRingEquiv.trans σ₀).symm)) x
        = (k.toRingEquiv.trans σ₀).symm (g ((k.toRingEquiv.trans σ₀) x)) := by
          simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
      _ = k.symm (σ₀.symm (g (σ₀ (k x)))) := by
          simp only [RingEquiv.symm_trans_apply, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
            AlgEquiv.toRingEquiv_symm]
      _ = k.symm ((Submission.NeukirchUchida.conjHomEquiv hσ₀ g) (k x)) := by
          rw [show σ₀.symm (g (σ₀ (k x)))
            = (Submission.NeukirchUchida.conjHomEquiv hσ₀ g) (k x) from (hconj x).symm]
      _ = (ϕ g : K₂' ≃+* K₂') x := by
          rw [key]
          exact k.symm_apply_apply ((ϕ g) x)
  exact hmain.symm

/-- **The converse of the inner-twist reduction for the tautological twist.**  If `σ = σ₀ ∘ k`
with `k ∈ Gal(K₂'/K₂)` induces `ϕ`, then the obstruction `Φ_{σ₀} ∘ ϕ⁻¹` is `MulAut.conj k`.

Combined with `conjugates_trans_of_conj_normal`, for the twist family `σ = σ₀ ∘ k` the condition
`Conjugates σ ϕ` is equivalent to the innerness of `β`. -/
theorem trans_eq_conj_of_conjugates {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {σ₀ : K₂' ≃+* K₁'}
    {hσ₀ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀}
    (k : Gal(K₂'/K₂))
    (h : Submission.NeukirchUchida.Conjugates (k.toRingEquiv.trans σ₀) ϕ) :
    ϕ.symm.trans (Submission.NeukirchUchida.conjHomEquiv hσ₀) = MulAut.conj k := by
  have key : ∀ (g : Gal(K₁'/K₁)) (y : K₂'),
      (Submission.NeukirchUchida.conjHomEquiv hσ₀ g) y = k ((ϕ g : K₂' ≃+* K₂') (k⁻¹ y)) := by
    intro g y
    have hconj : ∀ x : K₂', (Submission.NeukirchUchida.conjHomEquiv hσ₀ g) (k x)
        = σ₀.symm (g (σ₀ (k x))) := by
      intro x
      change (Submission.NeukirchUchida.conj hσ₀ g) (k x) = σ₀.symm (g (σ₀ (k x)))
      rw [Submission.NeukirchUchida.conj_apply]
    have h2 : ∀ x : K₂', (Submission.NeukirchUchida.conjHomEquiv hσ₀ g) (k x)
        = k ((ϕ g : K₂' ≃+* K₂') x) := by
      intro x
      have h1 : (ϕ g : K₂' ≃+* K₂') x
          = k.symm ((Submission.NeukirchUchida.conjHomEquiv hσ₀ g) (k x)) := by
        rw [h.2 g]
        simp only [RingEquiv.trans_apply, RingEquiv.symm_trans_apply, AlgEquiv.coe_ringEquiv,
          AlgEquiv.toRingEquiv_symm]
        rw [hconj x]
      rw [h1, k.apply_symm_apply]
    simpa using h2 (k⁻¹ y)
  refine MulEquiv.ext fun u => AlgEquiv.ext fun x => ?_
  rw [MulEquiv.trans_apply, MulAut.conj_apply, key (ϕ.symm u) x, ϕ.apply_symm_apply]
  simp [AlgEquiv.mul_apply]

end NK.Reconstruct

namespace NK.Reconstruct

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The existence form of the inner-twist reduction.**  If a base-field mapping isomorphism
`σ₀ : K₂' ≃+* K₁'` is known and the obstruction `Φ_{σ₀} ∘ ϕ⁻¹` is inner, then `ϕ` is induced by a
field isomorphism: `∃ σ, Conjugates σ ϕ`.

This is the form to compare with the target `Submission.NeukirchUchida.exists_sigma`: after the
weak half of Neukirch–Uchida (a base-field isomorphism) and the vanishing of the explicit
obstruction class, the conclusion follows. -/
theorem exists_conjugates_of_conj_normal {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {σ₀ : K₂' ≃+* K₁'}
    {hσ₀ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀}
    (k : Gal(K₂'/K₂))
    (h : ϕ.symm.trans (Submission.NeukirchUchida.conjHomEquiv hσ₀) = MulAut.conj k) :
    ∃ σ : K₂' ≃+* K₁', Submission.NeukirchUchida.Conjugates σ ϕ :=
  ⟨k.toRingEquiv.trans σ₀, conjugates_trans_of_conj_normal k h⟩

/-- **The obstruction vanishes exactly when `ϕ` is induced by a field isomorphism** (in the
presence of a base-field mapping isomorphism `σ₀`): given any `k ∈ Gal(K₂'/K₂)`, the twist
`σ = σ₀ ∘ k` induces `ϕ` if and only if the obstruction `Φ_{σ₀} ∘ ϕ⁻¹` equals `MulAut.conj k`.

Together with the fact that every `MapsBase` isomorphism of the separable closures restricts to an
isomorphism of the base fields, this exhibits the deep input of the reconstruction as the
vanishing of a single cohomological obstruction in `Out(Gal(K₂'/K₂))`. -/
theorem conjugates_twist_iff {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {σ₀ : K₂' ≃+* K₁'}
    {hσ₀ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ₀}
    (k : Gal(K₂'/K₂)) :
    Submission.NeukirchUchida.Conjugates (k.toRingEquiv.trans σ₀) ϕ ↔
      ϕ.symm.trans (Submission.NeukirchUchida.conjHomEquiv hσ₀) = MulAut.conj k :=
  ⟨trans_eq_conj_of_conjugates k, conjugates_trans_of_conj_normal k⟩

end NK.Reconstruct
