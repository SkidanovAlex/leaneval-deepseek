import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NeukirchUchida.FieldTransport
import Submission.NeukirchUchida.Local.Transitivity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Continuity of the conjugation homomorphism `Gal(K₁'/K₁) →* Gal(K₂'/K₂)`

Let `σ : K₂' ≃+* K₁'` be a ring isomorphism mapping the embedded copy of `K₂` onto the
embedded copy of `K₁` (`MapsBase`).  `Submission.NeukirchUchida.conjHom` is the group
homomorphism `g ↦ σ⁻¹ ∘ g ∘ σ` from `Gal(K₁'/K₁)` to `Gal(K₂'/K₂)`.

The goal of this file is `NK.NeukirchUchida.continuous_conjHom`: conjugation by `σ` is
continuous for the Krull topologies.  This is the statement that the elementary half of the
Neukirch–Uchida correspondence is a morphism of profinite groups.

## Strategy

The Krull topology has a fundamental system of neighbourhoods of the identity given by the
fixing subgroups `Gal(K₁'/F)` for `F/K₁` finite dimensional.  A homomorphism of topological
groups is continuous as soon as it is continuous at `1`, and continuity at `1` may be checked
on this neighbourhood basis.  So the heart of the proof is:

**if `E ⊆ K₂'` is an intermediate field of finite degree over `K₂`, then `σ '' E` is an
intermediate field of finite degree over `K₁`.**

The field `σ '' E` is the `imageField` defined below; the finiteness is the content of
`imageField_finiteDimensional`: the ring hierarchy `E → σ '' E` is semilinear over the ring
isomorphism `baseEquiv hσ : K₂ ≃+* K₁` induced by `σ`, so a finite generating set of `E`
over `K₂` is one for `σ '' E` over `K₁` (`Submodule.FG.map` for semilinear maps, transported
along the semilinear map `E →ₛₗ[baseEquiv hσ] imageField hσ E`).

-/

namespace NK.NeukirchUchida

open Submission.NeukirchUchida

open scoped Topology

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [Algebra K₁ K₁'] [Algebra K₂ K₂'] {σ : K₂' ≃+* K₁'}

section BaseEquiv

/-- The ring homomorphism `K₂ →+* (algebraMap K₁ K₁').range`, `a ↦ σ (algebraMap K₂ K₂' a)`,
which exists because `σ` carries the embedded copy of `K₂` into that of `K₁`. -/
noncomputable def baseHomAux
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    K₂ →+* (algebraMap K₁ K₁').range :=
  RingHom.codRestrict (σ.toRingHom.comp (algebraMap K₂ K₂')) (algebraMap K₁ K₁').range
    (fun a => Submission.NeukirchUchida.mapsBase_mem (algebraMap K₁ K₁') (algebraMap K₂ K₂') hσ
      ⟨a, rfl⟩)

lemma baseHomAux_apply
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (a : K₂) :
    ((baseHomAux hσ a : (algebraMap K₁ K₁').range) : K₁') = σ (algebraMap K₂ K₂' a) := rfl

lemma baseHomAux_injective
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    Function.Injective (baseHomAux hσ) := by
  intro a b hab
  have h1 : σ (algebraMap K₂ K₂' a) = σ (algebraMap K₂ K₂' b) := by
    simpa only [baseHomAux_apply] using congrArg Subtype.val hab
  exact (algebraMap K₂ K₂').injective (σ.injective h1)

lemma baseHomAux_surjective
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    Function.Surjective (baseHomAux hσ) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ (algebraMap K₂ K₂').range.map σ.toRingHom := by
    rw [hσ]; exact hy
  obtain ⟨x, hx, hxy⟩ := Subring.mem_map.mp hy'
  obtain ⟨a, rfl⟩ := hx
  refine ⟨a, Subtype.ext ?_⟩
  rw [baseHomAux_apply]
  exact hxy

/-- The ring isomorphism `K₁ ≃+* (algebraMap K₁ K₁').range` inverse to `algebraMap`. -/
noncomputable def baseRangeEquiv : K₁ ≃+* (algebraMap K₁ K₁').range :=
  RingEquiv.ofBijective (algebraMap K₁ K₁').rangeRestrict
    ⟨fun x y h => (algebraMap K₁ K₁').injective (congrArg Subtype.val h),
     fun y => by
       obtain ⟨a, ha⟩ := RingHom.mem_range.mp y.2
       exact ⟨a, Subtype.ext ha⟩⟩

/-- **The isomorphism of base fields induced by `σ`**: the unique `σ₀ : K₂ ≃+* K₁` with
`σ (algebraMap K₂ K₂' a) = algebraMap K₁ K₁' (σ₀ a)` for all `a : K₂`. -/
noncomputable def baseEquiv
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    K₂ ≃+* K₁ :=
  (RingEquiv.ofBijective (baseHomAux hσ)
    ⟨baseHomAux_injective hσ, baseHomAux_surjective hσ⟩).trans baseRangeEquiv.symm

/-- The defining property of `baseEquiv`. -/
lemma baseEquiv_spec
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (a : K₂) :
    algebraMap K₁ K₁' (baseEquiv hσ a) = σ (algebraMap K₂ K₂' a) := by
  have h : baseRangeEquiv (baseEquiv hσ a) = baseHomAux hσ a := by
    rw [baseEquiv, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
    exact RingEquiv.ofBijective_apply (baseHomAux hσ) _ a
  exact congrArg Subtype.val h

/-- `baseEquiv_spec` with the scalar of the semilinear structure made explicit. -/
lemma baseEquiv_spec'
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (a : K₂) :
    algebraMap K₁ K₁' ((baseEquiv hσ : K₂ →+* K₁) a) = σ (algebraMap K₂ K₂' a) :=
  baseEquiv_spec hσ a

end BaseEquiv

section ImageField

/-- **The image of a finite intermediate field under `σ`.**  If `E ⊆ K₂'` is an intermediate
field of `K₂`, then `σ '' E` contains `algebraMap K₁ K₁'` (because `σ` maps the base fields
onto each other) and is a subfield of `K₁'`, hence an intermediate field of `K₁`. -/
noncomputable def imageField
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (E : IntermediateField K₂ K₂') : IntermediateField K₁ K₁' where
  carrier := σ '' (E : Set K₂')
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, E.mul_mem ha hb, by rw [map_mul]⟩
  one_mem' := ⟨1, E.one_mem, by rw [map_one]⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, E.add_mem ha hb, by rw [map_add]⟩
  zero_mem' := ⟨0, E.zero_mem, by rw [map_zero]⟩
  algebraMap_mem' := by
    intro a
    have ha : algebraMap K₁ K₁' a ∈ (algebraMap K₂ K₂').range.map σ.toRingHom := by
      rw [hσ]; exact ⟨a, rfl⟩
    obtain ⟨x, hx, hxa⟩ := Subring.mem_map.mp ha
    obtain ⟨b, rfl⟩ := hx
    exact ⟨algebraMap K₂ K₂' b, E.algebraMap_mem b, hxa⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, E.inv_mem ha, by rw [map_inv₀]⟩

lemma mem_imageField
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (E : IntermediateField K₂ K₂') {x : K₁'} :
    x ∈ imageField hσ E ↔ ∃ y ∈ E, σ y = x := Iff.rfl

/-- **Finiteness of the image field**: `σ '' E` is finite dimensional over `K₁` whenever `E`
is finite dimensional over `K₂`.  This is the technical heart of the continuity statement.

The map `E → imageField hσ E`, `x ↦ σ x`, is additive and semilinear over the ring
isomorphism `baseEquiv hσ : K₂ ≃+* K₁` (by `baseEquiv_spec`), so it is a
`σ`-semilinear map; it is surjective, and images of finitely generated modules under
semilinear maps are finitely generated (`Submodule.FG.map`). -/
lemma imageField_finiteDimensional
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (E : IntermediateField K₂ K₂') [FiniteDimensional K₂ E] :
    FiniteDimensional K₁ (imageField hσ E) := by
  let f : E → imageField hσ E := fun x => ⟨σ (x : K₂'), ⟨x, x.2, rfl⟩⟩
  have hf_add : ∀ x y : E, f (x + y) = f x + f y := by
    intro x y
    apply Subtype.ext
    change σ ((x + y : E) : K₂') = σ (x : K₂') + σ (y : K₂')
    rw [show ((x + y : E) : K₂') = (x : K₂') + (y : K₂') by
        rw [IntermediateField.coe_add], map_add]
  have hf_smul : ∀ (a : K₂) (x : E), f (a • x) = (baseEquiv hσ : K₂ →+* K₁) a • f x := by
    intro a x
    apply Subtype.ext
    rw [SetLike.val_smul]
    change σ ((a • x : E) : K₂') =
      ((baseEquiv hσ : K₂ →+* K₁) a) • (σ (x : K₂') : K₁')
    simp only [Algebra.smul_def]
    rw [IntermediateField.coe_mul, IntermediateField.coe_algebraMap_apply]
    rw [map_mul, baseEquiv_spec']
  let φ : E →ₛₗ[(baseEquiv hσ : K₂ →+* K₁)] imageField hσ E :=
    { toFun := f, map_add' := hf_add, map_smul' := hf_smul }
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨x, hxE, hxs⟩ := y.2
    exact ⟨⟨x, hxE⟩, Subtype.ext hxs⟩
  have hfgE : (⊤ : Submodule K₂ E).FG := ‹FiniteDimensional K₂ E›.fg_top
  have hrange : Submodule.map φ (⊤ : Submodule K₂ E) = ⊤ := by
    rw [← LinearMap.range_eq_map, LinearMap.range_eq_top]
    exact hsurj
  have hfgF : (⊤ : Submodule K₁ (imageField hσ E)).FG := by
    rw [← hrange]
    exact Submodule.FG.map φ hfgE
  exact Module.Finite.of_fg_top hfgF

end ImageField

section Continuity

/-- The neighbourhood computation: conjugation by `σ` sends the fixing subgroup of
`imageField hσ E` into the fixing subgroup of `E`. -/
lemma conj_mem_fixingSubgroup
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (E : IntermediateField K₂ K₂') {g : Gal(K₁'/K₁)}
    (hg : g ∈ (imageField hσ E).fixingSubgroup) :
    Submission.NeukirchUchida.conjHom hσ g ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  intro y hy
  show Submission.NeukirchUchida.conj hσ g y = y
  rw [Submission.NeukirchUchida.conj_apply, hg (σ y) ⟨y, hy, rfl⟩, σ.symm_apply_apply]

end Continuity

/-- **Continuity of conjugation.**  For a ring isomorphism `σ : K₂' ≃+* K₁'` mapping the
embedded copy of `K₂` onto that of `K₁`, the induced group homomorphism
`conjHom hσ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)` is continuous for the Krull topologies. -/
theorem continuous_conjHom {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    Continuous (Submission.NeukirchUchida.conjHom hσ : Gal(K₁'/K₁) → Gal(K₂'/K₂)) := by
  refine continuous_of_continuousAt_one (Submission.NeukirchUchida.conjHom hσ) ?_
  rw [ContinuousAt, (Submission.NeukirchUchida.conjHom hσ).map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff K₂ K₂'] at hU
  obtain ⟨E, _hEfin, hEU⟩ := hU
  rw [krullTopology_mem_nhds_one_iff K₁ K₁']
  refine ⟨imageField hσ E, imageField_finiteDimensional hσ E, ?_⟩
  intro g hg
  exact hEU (conj_mem_fixingSubgroup hσ E hg)

end NK.NeukirchUchida
