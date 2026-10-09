import Mathlib
import Submission.NK.Reconstruct.Transport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finite-dimensionality of the transported level `σ(L)`

Let `K₁`, `K₂` be number fields with separable closures `K₁'`, `K₂'`, and let
`σ : K₂' ≃+* K₁'` be a ring isomorphism carrying the embedded copy of `K₂` onto the
embedded copy of `K₁` (`Submission.NeukirchUchida.MapsBase`).  For an intermediate field
`L ⊆ K₂'` the *transported level* `sigmaLevel σ hσ L = σ(L)` is an intermediate field of
`K₁'/K₁`.  The main result of this file, `finiteDimensional_sigmaLevel`, says that `σ(L)`
is finite over `K₁` as soon as `L` is finite over `K₂`.

The mathematical content is that `σ` restricts to a *semilinear* isomorphism
`↥(σ L) ≃ ↥L` over the ring isomorphism `K₁ ≃+* K₂` induced by `σ` on the two base fields,
and that finite generation of a module is preserved by such an equivalence.  Both ingredients
are supplied here: `sigmaBaseRingEquiv` constructs the base-field isomorphism out of `hσ`, and
`module_finite_of_ringEquiv_semilinear` is the transfer lemma for finitely generated modules.
-/

namespace NK.Reconstruct

open scoped Pointwise

/-! ## Transfer of finite generation along a semilinear equivalence of modules -/

/-- **Finite generation transfers along a semilinear equivalence of modules.**

If `f : M ≃+ N` is an additive equivalence intertwining the `R`-action on `M` with the
`S`-action on `N` through a ring isomorphism `e : R ≃+* S` (`f (r • m) = e r • f m`), and `N`
is finitely generated over `S`, then `M` is finitely generated over `R`. -/
theorem module_finite_of_ringEquiv_semilinear {R S M N : Type*} [Semiring R] [Semiring S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
    (e : R ≃+* S) (f : M ≃+ N) (h : ∀ (r : R) (m : M), f (r • m) = e r • f m)
    (hf : Module.Finite S N) : Module.Finite R M := by
  have hfg : (⊤ : Submodule S N).FG := Module.Finite.fg_top
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  refine Module.Finite.of_fg_top (Submodule.fg_iff_exists_fin_generating_family.mpr
    ⟨n, fun i => f.symm (s i), ?_⟩)
  refine le_antisymm le_top ?_
  intro m _
  have hm : f m ∈ Submodule.span S (Set.range s) := by rw [hs]; trivial
  have key : f.symm (f m) ∈ Submodule.span R (Set.range fun i => f.symm (s i)) := by
    refine Submodule.span_induction (s := Set.range s)
      (p := fun y _ => f.symm y ∈ Submodule.span R (Set.range fun i => f.symm (s i)))
      ?_ ?_ ?_ ?_ hm
    · rintro y ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · simp
    · intro y z hy hz ihy ihz
      rw [map_add]
      exact Submodule.add_mem _ ihy ihz
    · intro c y hy ihy
      have hcy : f.symm (c • y) = e.symm c • f.symm y := by
        apply f.injective
        rw [AddEquiv.apply_symm_apply, h, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      rw [hcy]
      exact Submodule.smul_mem _ _ ihy
  simpa using key

/-! ## The ring isomorphism `K₁ ≃+* K₂` induced on the base fields -/

section BaseRingEquiv

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [Algebra K₁ K₁'] [Algebra K₂ K₂']

/-- An element of the embedded copy of `K₁` has, under `σ.symm`, a preimage in the embedded
copy of `K₂`: the defining property of `Submission.NeukirchUchida.MapsBase`. -/
lemma sigmaBase_exists_symm {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (a : K₁) :
    ∃ b : K₂, algebraMap K₂ K₂' b = σ.symm (algebraMap K₁ K₁' a) :=
  Submission.NeukirchUchida.mapsBase_mem_symm _ _ hσ ⟨a, rfl⟩

/-- Dually, an element of the embedded copy of `K₂` has, under `σ`, a preimage in the embedded
copy of `K₁`. -/
lemma sigmaBase_exists {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (b : K₂) :
    ∃ a : K₁, algebraMap K₁ K₁' a = σ (algebraMap K₂ K₂' b) :=
  Submission.NeukirchUchida.mapsBase_mem _ _ hσ ⟨b, rfl⟩

/-- The element of `K₂` corresponding to `a : K₁`, characterized by
`algebraMap K₂ K₂' (sigmaBaseMapFun σ hσ a) = σ.symm (algebraMap K₁ K₁' a)`. -/
noncomputable def sigmaBaseMapFun (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (a : K₁) : K₂ :=
  (sigmaBase_exists_symm hσ a).choose

/-- The defining property of `sigmaBaseMapFun`. -/
lemma sigmaBaseMapFun_spec (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (a : K₁) :
    algebraMap K₂ K₂' (sigmaBaseMapFun σ hσ a) = σ.symm (algebraMap K₁ K₁' a) :=
  (sigmaBase_exists_symm hσ a).choose_spec

/-- The inverse correspondence: the element of `K₁` corresponding to `b : K₂`. -/
noncomputable def sigmaBaseInvFun (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (b : K₂) : K₁ :=
  (sigmaBase_exists hσ b).choose

/-- The defining property of `sigmaBaseInvFun`. -/
lemma sigmaBaseInvFun_spec (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (b : K₂) :
    algebraMap K₁ K₁' (sigmaBaseInvFun σ hσ b) = σ (algebraMap K₂ K₂' b) :=
  (sigmaBase_exists hσ b).choose_spec

/-- **The ring isomorphism `K₁ ≃+* K₂` induced by a base-field-mapping `σ`.**

It is the unique ring isomorphism making the diagram with `σ.symm` and the embeddings of the
base fields commute: for `a : K₁`, `sigmaBaseRingEquiv σ hσ a` is the element `b : K₂` with
`algebraMap K₂ K₂' b = σ.symm (algebraMap K₁ K₁' a)`. -/
noncomputable def sigmaBaseRingEquiv (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) :
    K₁ ≃+* K₂ where
  toFun := sigmaBaseMapFun σ hσ
  invFun := sigmaBaseInvFun σ hσ
  left_inv a := by
    apply RingHom.injective (algebraMap K₁ K₁')
    rw [sigmaBaseInvFun_spec, sigmaBaseMapFun_spec, RingEquiv.apply_symm_apply]
  right_inv b := by
    apply RingHom.injective (algebraMap K₂ K₂')
    rw [sigmaBaseMapFun_spec, sigmaBaseInvFun_spec, RingEquiv.symm_apply_apply]
  map_mul' a b := by
    apply RingHom.injective (algebraMap K₂ K₂')
    simp only [map_mul, sigmaBaseMapFun_spec]
  map_add' a b := by
    apply RingHom.injective (algebraMap K₂ K₂')
    simp only [map_add, sigmaBaseMapFun_spec]

/-- The characterizing property of the base-field isomorphism. -/
@[simp] lemma sigmaBaseRingEquiv_apply_map (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ) (a : K₁) :
    algebraMap K₂ K₂' (sigmaBaseRingEquiv σ hσ a) = σ.symm (algebraMap K₁ K₁' a) :=
  sigmaBaseMapFun_spec σ hσ a

end BaseRingEquiv

/-! ## The transported level is finite over `K₁` -/

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The isomorphism of transported levels is semilinear over the base-field isomorphism.**

The ring isomorphism `sigmaLevelEquiv σ hσ L : ↥(σ L) ≃+* ↥L` (which is the restriction of
`σ.symm`) intertwines the `K₁`-action on `↥(σ L)` with the `K₂`-action on `↥L` through the
base-field isomorphism `sigmaBaseRingEquiv σ hσ : K₁ ≃+* K₂`:

`sigmaLevelEquiv σ hσ L (a • x) = sigmaBaseRingEquiv σ hσ a • sigmaLevelEquiv σ hσ L x`. -/
lemma sigmaLevelEquiv_smul (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₂ K₂') (a : K₁)
    (x : ↥(NK.Reconstruct.sigmaLevel σ hσ L)) :
    (NK.Reconstruct.sigmaLevelEquiv σ hσ L) (a • x) =
      sigmaBaseRingEquiv σ hσ a • (NK.Reconstruct.sigmaLevelEquiv σ hσ L) x := by
  apply Subtype.ext
  conv_rhs => rw [IntermediateField.coe_smul, Algebra.smul_def,
    NK.Reconstruct.sigmaLevelEquiv_apply, sigmaBaseRingEquiv_apply_map]
  conv_lhs => rw [NK.Reconstruct.sigmaLevelEquiv_apply, IntermediateField.coe_smul,
    Algebra.smul_def, map_mul]

/-- **The transported level `σ(L)` is finite-dimensional over `K₁` when `L` is finite over
`K₂`.**

Indeed `sigmaLevelEquiv σ hσ L : ↥(σ L) ≃+* ↥L` is semilinear over the base-field isomorphism
`sigmaBaseRingEquiv σ hσ : K₁ ≃+* K₂` (`sigmaLevelEquiv_smul`), so finite generation transfers
along it by `module_finite_of_ringEquiv_semilinear`. -/
theorem finiteDimensional_sigmaLevel {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁']
    [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] (σ : K₂' ≃+* K₁')
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (L : IntermediateField K₂ K₂') [FiniteDimensional K₂ L] :
    FiniteDimensional K₁ (NK.Reconstruct.sigmaLevel σ hσ L) := by
  have hsem : ∀ (r : K₁) (m : ↥(NK.Reconstruct.sigmaLevel σ hσ L)),
      (NK.Reconstruct.sigmaLevelEquiv σ hσ L).toAddEquiv (r • m) =
        sigmaBaseRingEquiv σ hσ r •
          (NK.Reconstruct.sigmaLevelEquiv σ hσ L).toAddEquiv m := by
    intro a x
    change (NK.Reconstruct.sigmaLevelEquiv σ hσ L) (a • x) =
      sigmaBaseRingEquiv σ hσ a • (NK.Reconstruct.sigmaLevelEquiv σ hσ L) x
    exact sigmaLevelEquiv_smul σ hσ L a x
  exact module_finite_of_ringEquiv_semilinear (sigmaBaseRingEquiv σ hσ)
    (NK.Reconstruct.sigmaLevelEquiv σ hσ L).toAddEquiv hsem inferInstance

end NK.Reconstruct
