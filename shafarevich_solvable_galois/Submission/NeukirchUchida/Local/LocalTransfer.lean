import Mathlib.Topology.Connected.Separation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.NeukirchUchida.Local.LocalGalois
import Submission.NeukirchUchida.Local.Restriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of decomposition groups: the local side

Let `M / K` be a finite Galois extension of number fields and `L` an intermediate field, normal
over `K`.  For a finite place `w` of `M` there is by `Local/Restriction.lean` a
restriction homomorphism of decomposition groups

`D_w ≤ Gal(M/K) → D_{w|_L} ≤ Gal(L/K)`,

and by `Local/LocalGalois.lean` both groups are identified with the corresponding *local* Galois
groups `Gal(M_w/K_p)` and `Gal(L_{w|_L}/K_p)`.

The main result of this file, `decompositionToAdicCompletion_adicCompletionMap_placeUnder`, shows
that these identifications are compatible: the extension of `σ ∈ D_w` to the completion `M_w`,
restricted to the image of `L_{w|_L}`, is exactly the extension of the restriction `σ|_L` of `σ`
to `L`.  In other words the diagram

```
D_w            --→ D_{w|_L}
 ↓ ≅                  ↓ ≅
Gal(M_w/K_p)   --→ Gal(L_{w|_L}/K_p)
```

commutes.  This is what makes the decomposition groups of the finite levels of a separable
closure into a *projective system* whose limit is the decomposition group of a place of the
separable closure, and eventually the local Galois group `Gal(K̄_𝔭/K_𝔭)`
(Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter XII).
-/

open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Submission.NeukirchUchida.Local

section Instances

variable {K M : Type*} [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]

/-- A finite normal extension of a number field inside a second number field is Galois.  This is
the instance form of `Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero`, restricted to
intermediate fields. -/
instance instIsGaloisIntermediateFieldOfNormal (L : IntermediateField K M) [Normal K L] :
    IsGalois K ↥L :=
  Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero

/-- **The place `w` of `M` lies over the place `w|_L` of `L` below it.** -/
theorem placeUnder_liesOver (L : IntermediateField K M) [Normal K L]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) :
    w.asIdeal.LiesOver (placeUnder (K := K) L w).asIdeal :=
  ⟨by rw [placeUnder_asIdeal, Ideal.under_def]⟩

/-- The place `w|_L` of `L` lies over the place `p` of `K` if `w` does. -/
theorem placeUnder_liesOver' (L : IntermediateField K M) [Normal K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) (h : w.asIdeal.LiesOver p.asIdeal) :
    (placeUnder (K := K) L w).asIdeal.LiesOver p.asIdeal := by
  haveI := h
  exact liesOver_placeUnder L w p

/-- **Restriction of decomposition groups to an intermediate field.** The decomposition group of
`w` in `Gal(M/K)` maps into the decomposition group of the place `w|_L` below `w`. -/
noncomputable def decompositionRestrict (L : IntermediateField K M) [Normal K L]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) :
    decompositionSubgroup (K := K) w →*
      decompositionSubgroup (K := K) (placeUnder (K := K) L w) where
  toFun σ := ⟨AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ.1,
    restrictNormalHom_mem_decompositionSubgroup L w σ.1 σ.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := by
    intro σ τ
    apply Subtype.ext
    simp

@[simp]
theorem decompositionRestrict_apply (L : IntermediateField K M) [Normal K L]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (σ : decompositionSubgroup (K := K) w) :
    ((decompositionRestrict (K := K) L w) σ).1 =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ.1 := rfl

end Instances

/-! ## Compatibility with the extension to completions -/

section Compatibility

variable {K M : Type*} [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]

/-- **Compatibility of the extension to the completion with restriction to an intermediate
field.**

Extending `σ ∈ D_w ≤ Gal(M/K)` to the completion `M_w` and then restricting along the canonical
embedding `L_{w|_L} ↪ M_w` gives the same map as first restricting `σ` to `D_{w|_L}` and
extending to `L_{w|_L}`. -/
theorem decompositionToAdicCompletion_adicCompletionMap_placeUnder
    (L : IntermediateField K M) [Normal K L]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M))
    (σ : decompositionSubgroup (K := K) w)
    (y : (placeUnder (K := K) L w).adicCompletion ↥L) :
    decompositionToAdicCompletion (K := K) (L := M) w σ
        (Commons.RingTheory.Henselian.adicCompletionMap (placeUnder (K := K) L w) w
          (placeUnder_liesOver (K := K) L w) y) =
      Commons.RingTheory.Henselian.adicCompletionMap (placeUnder (K := K) L w) w
        (placeUnder_liesOver (K := K) L w)
        (decompositionToAdicCompletion (K := K) (L := ↥L) (placeUnder (K := K) L w)
          ((decompositionRestrict (K := K) L w) σ) y) := by
  have hdense : DenseRange
      (algebraMap ↥L ((placeUnder (K := K) L w).adicCompletion ↥L)) :=
    IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 ↥L) ↥L
      (placeUnder (K := K) L w)
  have hEq : (fun y : (placeUnder (K := K) L w).adicCompletion ↥L =>
        decompositionToAdicCompletion (K := K) (L := M) w σ
          (Commons.RingTheory.Henselian.adicCompletionMap (placeUnder (K := K) L w) w
            (placeUnder_liesOver (K := K) L w) y)) =
      (fun y : (placeUnder (K := K) L w).adicCompletion ↥L =>
        Commons.RingTheory.Henselian.adicCompletionMap (placeUnder (K := K) L w) w
          (placeUnder_liesOver (K := K) L w)
          (decompositionToAdicCompletion (K := K) (L := ↥L) (placeUnder (K := K) L w)
            ((decompositionRestrict (K := K) L w) σ) y)) := by
    refine DenseRange.equalizer hdense ?_ ?_ ?_
    · exact (continuous_decompositionToAdicCompletion (K := K) (L := M) w σ).comp
        (Commons.RingTheory.Henselian.adicCompletionMap_continuous _ _ _)
    · exact (Commons.RingTheory.Henselian.adicCompletionMap_continuous _ _ _).comp
        (continuous_decompositionToAdicCompletion (K := K) (L := ↥L)
          (placeUnder (K := K) L w) ((decompositionRestrict (K := K) L w) σ))
    · funext x
      simp only [Function.comp_apply]
      have hx : algebraMap ↥L ((placeUnder (K := K) L w).adicCompletion ↥L) x =
          (x : (placeUnder (K := K) L w).adicCompletion ↥L) := rfl
      rw [hx]
      rw [Commons.RingTheory.Henselian.adicCompletionMap_apply (placeUnder (K := K) L w) w
        (placeUnder_liesOver (K := K) L w) x]
      rw [decompositionToAdicCompletion_coe (K := K) (L := M) w σ (algebraMap ↥L M x)]
      rw [decompositionToAdicCompletion_coe (K := K) (L := ↥L) (placeUnder (K := K) L w)
        ((decompositionRestrict (K := K) L w) σ) x]
      rw [Commons.RingTheory.Henselian.adicCompletionMap_apply (placeUnder (K := K) L w) w
        (placeUnder_liesOver (K := K) L w)]
      rw [decompositionRestrict_apply]
      rw [← AlgEquiv.restrictNormal_commutes (χ := σ.1) (K₂ := M) ↥L x]
      rfl
  exact congr_fun hEq y

/-! ## The restriction map on the local Galois groups -/

/-- **Restriction of a `K_p`-automorphism of `M_w` to the subfield `L_{w|_L}`.**

Because the identification `D_w ≃* Gal(M_w/K_p)` is an isomorphism, and the restriction
`D_w → D_{w|_L}` is a group homomorphism, the composite identification

`Gal(M_w/K_p) ≃ D_w → D_{w|_L} ≃ Gal(L_{w|_L}/K_p)`

gives the restriction map of the projective system of local Galois groups.  Its concrete meaning
is recorded in `localRestrict_adicCompletionMap`. -/
noncomputable def localRestrict
    (L : IntermediateField K M) [Normal K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) (h : w.asIdeal.LiesOver p.asIdeal) :
    letI := adicCompletionAlgebra (K := K) (L := M) p w h
    letI := adicCompletionAlgebra (K := K) (L := ↥L) p (placeUnder (K := K) L w)
      (placeUnder_liesOver' (K := K) L p w h)
    (w.adicCompletion M ≃ₐ[p.adicCompletion K] w.adicCompletion M) →*
      ((placeUnder (K := K) L w).adicCompletion ↥L ≃ₐ[p.adicCompletion K]
        (placeUnder (K := K) L w).adicCompletion ↥L) :=
  letI := adicCompletionAlgebra (K := K) (L := M) p w h
  letI := adicCompletionAlgebra (K := K) (L := ↥L) p (placeUnder (K := K) L w)
    (placeUnder_liesOver' (K := K) L p w h)
  ((decompositionSubgroupMulEquivLocalGalois (K := K) (L := ↥L) p
      (placeUnder (K := K) L w) (placeUnder_liesOver' (K := K) L p w h)).toMonoidHom).comp
    ((decompositionRestrict (K := K) L w).comp
      (decompositionSubgroupMulEquivLocalGalois (K := K) (L := M) p w h).symm.toMonoidHom)

@[simp]
theorem localRestrict_apply_decompositionSubgroupMulEquiv
    (L : IntermediateField K M) [Normal K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) (h : w.asIdeal.LiesOver p.asIdeal)
    (σ : decompositionSubgroup (K := K) w) :
    localRestrict (K := K) L p w h
        (decompositionSubgroupMulEquivLocalGalois (K := K) (L := M) p w h σ) =
      decompositionSubgroupMulEquivLocalGalois (K := K) (L := ↥L) p
        (placeUnder (K := K) L w) (placeUnder_liesOver' (K := K) L p w h)
        ((decompositionRestrict (K := K) L w) σ) := by
  simp only [localRestrict, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

/-- **Concrete description of the restriction map on the local Galois groups.**

An element `τ` of `Gal(M_w/K_p)` restricts to the unique `K_p`-automorphism `ρ` of `L_{w|_L}`
with `ρ(y) = τ(y)` for `y ∈ L_{w|_L}` (where both sides are viewed in `M_w` via the canonical
embedding). -/
theorem localRestrict_adicCompletionMap
    (L : IntermediateField K M) [Normal K L]
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) (h : w.asIdeal.LiesOver p.asIdeal)
    (σ : decompositionSubgroup (K := K) w)
    (y : (placeUnder (K := K) L w).adicCompletion ↥L) :
    letI := adicCompletionAlgebra (K := K) (L := M) p w h
    letI := adicCompletionAlgebra (K := K) (L := ↥L) p (placeUnder (K := K) L w)
      (placeUnder_liesOver' (K := K) L p w h)
    Commons.RingTheory.Henselian.adicCompletionMap (placeUnder (K := K) L w) w
        (placeUnder_liesOver (K := K) L w)
        ((localRestrict (K := K) L p w h)
          (decompositionSubgroupMulEquivLocalGalois (K := K) (L := M) p w h σ) y) =
      (decompositionSubgroupMulEquivLocalGalois (K := K) (L := M) p w h σ)
        (Commons.RingTheory.Henselian.adicCompletionMap (placeUnder (K := K) L w) w
          (placeUnder_liesOver (K := K) L w) y) := by
  letI := adicCompletionAlgebra (K := K) (L := M) p w h
  letI := adicCompletionAlgebra (K := K) (L := ↥L) p (placeUnder (K := K) L w)
    (placeUnder_liesOver' (K := K) L p w h)
  rw [localRestrict_apply_decompositionSubgroupMulEquiv]
  exact (decompositionToAdicCompletion_adicCompletionMap_placeUnder L w σ y).symm

end Compatibility

end Submission.NeukirchUchida.Local
