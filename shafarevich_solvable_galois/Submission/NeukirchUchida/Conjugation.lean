import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsSepClosed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Conjugation machinery for the Neukirch–Uchida theorem

The theorem (Cohomology of Number Fields, XII, Thm 12.2.1) asserts that every
homeomorphic isomorphism `ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)` of absolute Galois
groups of number fields is induced by a *unique* field isomorphism
`σ : K₂' ≃+* K₁'` mapping the embedded copy of `K₂` onto the embedded copy of
`K₁`, in the sense that `ϕ g = σ⁻¹ ∘ g ∘ σ` for every `g ∈ Gal(K₁'/K₁)`
(`= σ.trans (g.toRingEquiv.trans σ.symm)`, where `RingEquiv.trans e₁ e₂`
acts as `e₂ ∘ e₁`).

This file develops the *elementary half* of that correspondence, valid for
arbitrary fields: given such a `σ`, the map
`g ↦ σ.trans (g.toRingEquiv.trans σ.symm)` lands in `Gal(K₂'/K₂)` (i.e. the
conjugate fixes the embedded base field) and acts as `x ↦ σ⁻¹ (g (σ x))`.
All statements here are fully proved; the deep *existence* half of (12.2.1)
is a separate (open) milestone.

-/

namespace Submission.NeukirchUchida

open scoped Topology

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']

/-- The pair of embeddings `i₁ : K₁ →+* K₁'`, `i₂ : K₂ →+* K₂'` lets us speak
about the embedded copies of the base fields.  `MapsBase i₁ i₂ σ` says that the
ring isomorphism `σ : K₂' ≃+* K₁'` maps the embedded copy of `K₂` (via `i₂`)
onto the embedded copy of `K₁` (via `i₁`). -/
def MapsBase (i₁ : K₁ →+* K₁') (i₂ : K₂ →+* K₂') (σ : K₂' ≃+* K₁') : Prop :=
  i₂.range.map σ.toRingHom = i₁.range

/-- A purely algebraic fact about subrings: mapping by a ring equivalence and
then by its inverse reproduces the original subring. -/
lemma subring_map_symm_of_map_eq {A B : Type*} [Ring A] [Ring B] (e : A ≃+* B)
    (S : Subring A) (T : Subring B) (h : S.map (e : A →+* B) = T) :
    T.map (e.symm : B →+* A) = S := by
  rw [← h]
  ext x
  constructor
  · intro hx
    rcases (Subring.mem_map.mp hx) with ⟨y, hy, hyx⟩
    rcases (Subring.mem_map.mp hy) with ⟨z, hz, hzy⟩
    have hxz : x = z := by
      calc
        x = e.symm y := hyx.symm
        _ = e.symm (e z) := congrArg (fun w => e.symm w) hzy.symm
        _ = z := e.symm_apply_apply z
    simpa [hxz]
  · intro hx
    refine Subring.mem_map.mpr ⟨e x, ?_, ?_⟩
    · exact Subring.mem_map.mpr ⟨x, hx, rfl⟩
    · simp

/-- If `σ` maps the embedded `K₂` onto the embedded `K₁`, then its inverse
maps the embedded `K₁` back onto the embedded `K₂`. -/
lemma mapsBase_symm (i₁ : K₁ →+* K₁') (i₂ : K₂ →+* K₂') {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase i₁ i₂ σ) : i₁.range.map σ.symm.toRingHom = i₂.range := by
  exact subring_map_symm_of_map_eq σ i₂.range i₁.range hσ

/-- If `σ` maps the embedded `K₂` onto the embedded `K₁`, then elements of
`i₂(K₂)` are sent into `i₁(K₁)`. -/
lemma mapsBase_mem (i₁ : K₁ →+* K₁') (i₂ : K₂ →+* K₂') {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase i₁ i₂ σ) {x : K₂'} (hx : x ∈ i₂.range) : σ x ∈ i₁.range := by
  rw [← hσ]
  exact Subring.mem_map.mpr ⟨x, hx, rfl⟩

/-- Dually: elements of `i₁(K₁)` are pulled back into `i₂(K₂)`. -/
lemma mapsBase_mem_symm (i₁ : K₁ →+* K₁') (i₂ : K₂ →+* K₂') {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase i₁ i₂ σ) {x : K₁'} (hx : x ∈ i₁.range) : σ.symm x ∈ i₂.range := by
  rw [← mapsBase_symm i₁ i₂ hσ]
  exact Subring.mem_map.mpr ⟨x, hx, rfl⟩

section TheoremScenario

variable [Algebra K₁ K₁'] [Algebra K₂ K₂']

/-- An automorphism of `K₁'` over `K₁` fixes the embedded copy of `K₁`
pointwise. -/
lemma algEquiv_fixes_base_range (g : Gal(K₁'/K₁)) {x : K₁'}
    (hx : x ∈ (algebraMap K₁ K₁').range) : g x = x := by
  rcases hx with ⟨a, rfl⟩
  exact g.commutes a

/-- The conjugate of an element of `Gal(K₁'/K₁)` by `σ` (namely
`x ↦ σ⁻¹ (g (σ x))`) fixes the embedded `K₂` pointwise, provided `σ` maps the
base field onto the base field. -/
lemma conj_fixes_base {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (g : Gal(K₁'/K₁)) :
    ∀ x : K₂', x ∈ (algebraMap K₂ K₂').range →
      (σ.trans (g.toRingEquiv.trans σ.symm)) x = x := by
  intro x hx
  calc
    (σ.trans (g.toRingEquiv.trans σ.symm)) x = σ.symm (g (σ x)) := by
      simp only [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv]
    _ = σ.symm (σ x) := by
      congr 1
      exact algEquiv_fixes_base_range g
        (mapsBase_mem (algebraMap K₁ K₁') (algebraMap K₂ K₂') hσ hx)
    _ = x := σ.symm_apply_apply x

/-- Conjugation by `σ` sends `Gal(K₁'/K₁)` into `Gal(K₂'/K₂)` when `σ` maps
base fields to base fields. -/
noncomputable def conj {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (g : Gal(K₁'/K₁)) :
    Gal(K₂'/K₂) :=
  AlgEquiv.ofRingEquiv (f := σ.trans (g.toRingEquiv.trans σ.symm)) (by
    intro a
    exact conj_fixes_base hσ g (algebraMap K₂ K₂' a) ⟨a, rfl⟩)

/-- The underlying ring equivalence of the conjugate is exactly the
`RingEquiv.trans` expression from the statement of the theorem. -/
lemma conj_toRingEquiv {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (g : Gal(K₁'/K₁)) :
    (conj hσ g : K₂' ≃+* K₂') = σ.trans (g.toRingEquiv.trans σ.symm) := rfl

/-- The conjugate acts as `x ↦ σ⁻¹ (g (σ x))`. -/
lemma conj_apply {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (g : Gal(K₁'/K₁)) (x : K₂') :
    conj hσ g x = σ.symm (g (σ x)) := by
  change (σ.trans (g.toRingEquiv.trans σ.symm)) x = σ.symm (g (σ x))
  simp only [RingEquiv.trans_apply]
  rfl

/-- Conjugation by `σ` is a group homomorphism `Gal(K₁'/K₁) →* Gal(K₂'/K₂)`. -/
noncomputable def conjHom {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    Gal(K₁'/K₁) →* Gal(K₂'/K₂) where
  toFun := conj hσ
  map_one' := by
    ext x
    simp [conj_apply]
  map_mul' g h := by
    ext x
    simp [conj_apply]


/-- Reindexing `mapsBase_symm` at the level of `MapsBase`. -/
lemma mapsBase_symm_alg {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    MapsBase (algebraMap K₂ K₂') (algebraMap K₁ K₁') σ.symm := by
  unfold MapsBase
  exact mapsBase_symm (algebraMap K₁ K₁') (algebraMap K₂ K₂') hσ

/-- For a base-field-mapping `σ`, conjugation by `σ` gives a group
isomorphism `Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)`, whose inverse is conjugation by
`σ.symm`.  This is the easy half of the correspondence of CoNF XII §2:
the map `α ↦ α∗` (with `α = σ⁻¹`, cf. the introduction of this file). -/
noncomputable def conjHomEquiv {σ : K₂' ≃+* K₁'}
    (hσ : MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    Gal(K₁'/K₁) ≃* Gal(K₂'/K₂) where
  toFun := fun g => conj hσ g
  invFun := fun g => conj (mapsBase_symm_alg hσ) g
  left_inv g := by
    ext x
    rw [conj_apply, conj_apply]
    simp
  right_inv g := by
    ext x
    rw [conj_apply, conj_apply]
    simp
  map_mul' g h := (conjHom hσ).map_mul g h

/-- The condition on `σ : K₂' ≃+* K₁'` from the statement of the theorem,
spelled with `MapsBase` plus the conjugation formula. -/
def Conjugates (σ : K₂' ≃+* K₁') (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) : Prop :=
  MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ ∧
    ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)

end TheoremScenario

end Submission.NeukirchUchida
