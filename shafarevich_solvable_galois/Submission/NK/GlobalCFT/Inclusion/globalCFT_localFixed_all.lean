import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Connected.Separation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The fixed field of a decomposition group at a single place

For `L / K` a finite Galois extension of number fields and a place `w` of `L` over a place `v` of
`K`, the decomposition group `D_w` acts on the local field `L_w` through the canonical local
isomorphisms `Place.localRingEquiv σ w : L_w ≃+* L_{σ w}`.  This file proves the local fixed field
theorem: a unit of `L_w` fixed by the whole decomposition group comes from a unit of `K_v`:

`∃ a : K_vˣ, Place.localAlgebraMapUnits w v h a = y`.

The archimedean case is handled with the Mathlib description of the completion of a number field
at an infinite place as `ℝ` or `ℂ` (`NumberField.InfinitePlace.Completion.extensionEmbedding` and
friends), the nonarchimedean case with the identification of the adjoint action of the
decomposition group with the local Galois group
(`Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois`).

## Main results

* `NK.GlobalCFT.Inclusion.glp_localFixed_mem_range`
* `NK.GlobalCFT.Inclusion.glp_local_fixed_of_fixed_idele`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Inclusion

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### Transport lemmas for the local fields

The local field `L_v` is a `match` on the place `v`, so equalities of places have to be
transported along; these lemmas record that this transport is compatible with the underlying
elements of units and with the values of idèles. -/

lemma glp_units_cast_val {a b : Place L} (h : a = b) (u : (Place.localField L a)ˣ) :
    ((h ▸ u : (Place.localField L b)ˣ)).val = (h ▸ u.val : Place.localField L b) := by
  cases h; rfl

lemma glp_cast_cast {a b : Place L} (h : a = b) (z : Place.localField L b) :
    (h ▸ (h.symm ▸ z : Place.localField L a) : Place.localField L b) = z := by
  cases h; rfl

lemma glp_idele_transport {K : Type*} [Field K] [NumberField K] (x : 𝕀[K])
    {a b : Place K} (h : a = b) : x b = h ▸ x a := by
  cases h; rfl

/-! ### The two descriptions of the Galois action on the finite places -/

/-- The automorphism of `𝓞 L` induced by `σ` is the restriction of `σ` to the ring of
integers. -/
lemma glp_ringOfIntegersEquiv_eq_galRestrict (σ : L ≃ₐ[K] L) :
    Place.ringOfIntegersEquiv σ = galRestrict (𝓞 K) K L (𝓞 L) σ := by
  ext x
  exact (algebraMap_galRestrict_apply (𝓞 K) σ x).symm

variable [FiniteDimensional K L] [IsGalois K L]

/-- `NK.GlobalCFT`'s action on the finite places of `L` agrees with the commons' one. -/
lemma glp_smulHeightOneSpectrum_eq_of_mem_decompositionSubgroup {q : HeightOneSpectrum (𝓞 L)}
    {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q) :
    Place.smulHeightOneSpectrum σ q = q := by
  apply HeightOneSpectrum.ext
  rw [Place.smulHeightOneSpectrum_asIdeal, glp_ringOfIntegersEquiv_eq_galRestrict]
  exact Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_map_eq hσ

/-- An element of the decomposition group of `q` fixes the place `Place.ofFinite q`. -/
lemma glp_smul_ofFinite_of_mem_decompositionSubgroup {q : HeightOneSpectrum (𝓞 L)}
    {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q) :
    σ • Place.ofFinite q = Place.ofFinite q := by
  rw [Place.smul_ofFinite, glp_smulHeightOneSpectrum_eq_of_mem_decompositionSubgroup hσ]

/-- The local isomorphism `Place.localRingEquiv` and the commons' action
`decompositionToAdicCompletion` of the decomposition group on the `q`-adic completion agree:
both are "apply `σ`", hence they are continuous and agree on the dense image of `L`. -/
lemma glp_localRingEquiv_eq_cast_decompositionToAdicCompletion {q : HeightOneSpectrum (𝓞 L)}
    (σ : L ≃ₐ[K] L)
    (hσD : σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q)
    (hσ : σ • Place.ofFinite q = Place.ofFinite q) (x : q.adicCompletion L) :
    Place.localRingEquiv σ (Place.ofFinite q) x =
      (hσ.symm ▸ (Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion
        (K := K) q ⟨σ, hσD⟩ x) : Place.localField L (σ • Place.ofFinite q)) := by
  have hdense : DenseRange (algebraMap L (Place.localField L (Place.ofFinite q))) :=
    Galois.denseRange_algebraMap_localField (Place.ofFinite q)
  have hcont₁ : Continuous (fun x : Place.localField L (Place.ofFinite q) =>
      Place.localRingEquiv σ (Place.ofFinite q) x) :=
    Galois.continuous_localRingEquiv σ _
  have hcont₂ : Continuous (fun x : Place.localField L (Place.ofFinite q) =>
      (hσ.symm ▸ (Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion
        (K := K) q ⟨σ, hσD⟩ x) : Place.localField L (σ • Place.ofFinite q))) :=
    Galois.continuous_localField_cast hσ.symm
      (Commons.NumberTheory.NumberField.Completion.continuous_decompositionToAdicCompletion
        (K := K) q ⟨σ, hσD⟩)
  have hfun : (fun x : Place.localField L (Place.ofFinite q) =>
        Place.localRingEquiv σ (Place.ofFinite q) x) =
      (fun x : Place.localField L (Place.ofFinite q) =>
        (hσ.symm ▸ (Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion
          (K := K) q ⟨σ, hσD⟩ x) : Place.localField L (σ • Place.ofFinite q))) := by
    refine DenseRange.equalizer hdense hcont₁ hcont₂ ?_
    funext z
    simp only [Function.comp_apply]
    rw [Place.localRingEquiv_algebraMap, Galois.globalCFT_algebraMap_eq_coe,
      Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion_coe,
      ← Galois.globalCFT_algebraMap_eq_coe, ← Galois.localField_cast_algebraMap]
  exact congrFun hfun x

/-- The canonical local units map at finite places, in the form of `adicCompletionMap`. -/
lemma glp_localAlgebraMapUnits_ofFinite {q : HeightOneSpectrum (𝓞 L)} {Q : HeightOneSpectrum (𝓞 K)}
    (h : q.asIdeal.LiesOver Q.asIdeal) :
    Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q)
        (Place.liesOver_ofFinite h) =
      Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q h).toMonoidHom := by
  ext u
  simp only [Place.localAlgebraMapUnits, Units.coe_map]
  rw [dif_pos h, Units.coe_map]

end NK.GlobalCFT.Inclusion

namespace NK.GlobalCFT.Inclusion

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The local fixed field theorem at a finite place.**  Let `q | Q` be a nonarchimedean place
of `L` over a nonarchimedean place of `K`.  A unit of `L_q` which is fixed by the whole
decomposition group `D_q` (acting through the canonical isomorphisms `Place.localRingEquiv`) is
the image of a unit of `K_Q` under the canonical local map. -/
theorem glp_localFixed_finite {q : HeightOneSpectrum (𝓞 L)} {Q : HeightOneSpectrum (𝓞 K)}
    (h : q.asIdeal.LiesOver Q.asIdeal)
    (y : (Place.localField L (Place.ofFinite q))ˣ)
    (hy : ∀ σ : L ≃ₐ[K] L, ∀ (hσ : σ • Place.ofFinite q = Place.ofFinite q),
      Units.map (Place.localRingEquiv σ (Place.ofFinite q)).toMonoidHom y = hσ.symm ▸ y) :
    ∃ a : (Place.localField K (Place.ofFinite Q))ˣ,
      Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q)
        (Place.liesOver_ofFinite h) a = y := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q h
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q h
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q h
  -- ## Step 1: `y` is fixed by the whole local Galois group `Gal(L_q / K_Q)`
  have hfix : ∀ τ : (q.adicCompletion L) ≃ₐ[Q.adicCompletion K] (q.adicCompletion L),
      τ y.val = y.val := by
    intro τ
    obtain ⟨σ, hστ⟩ :=
      (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
        Q q h).surjective τ
    rw [← hστ,
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe]
    change (Commons.NumberTheory.NumberField.Completion.decompositionToLocalGaloisFun Q q h σ :
      q.adicCompletion L → q.adicCompletion L) y.val = y.val
    rw [Commons.NumberTheory.NumberField.Completion.decompositionToLocalGaloisFun_apply]
    have hplace : σ.1 • Place.ofFinite q = Place.ofFinite q :=
      glp_smul_ofFinite_of_mem_decompositionSubgroup σ.2
    have hyσ : Units.map (Place.localRingEquiv σ.1 (Place.ofFinite q)).toMonoidHom y =
        (hplace.symm ▸ y : (Place.localField L (σ.1 • Place.ofFinite q))ˣ) := hy σ.1 hplace
    have hcongr : Place.localRingEquiv σ.1 (Place.ofFinite q) y.val =
        ((hplace.symm ▸ y : (Place.localField L (σ.1 • Place.ofFinite q))ˣ)).val :=
      congrArg (fun u : (Place.localField L (σ.1 • Place.ofFinite q))ˣ => u.val) hyσ
    have hT : ((hplace.symm ▸ y : (Place.localField L (σ.1 • Place.ofFinite q))ˣ)).val =
        (hplace.symm ▸ y.val : Place.localField L (σ.1 • Place.ofFinite q)) :=
      glp_units_cast_val hplace.symm y
    have hcmp := glp_localRingEquiv_eq_cast_decompositionToAdicCompletion (K := K) (q := q) σ.1 σ.2
      hplace y.val
    have key : (hplace.symm ▸
          (Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion
            (K := K) q ⟨σ.1, σ.2⟩ y.val) : Place.localField L (σ.1 • Place.ofFinite q)) =
        (hplace.symm ▸ y.val : Place.localField L (σ.1 • Place.ofFinite q)) := by
      rw [← hcmp, ← hT]
      exact hcongr
    have hfinal : Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion
        (K := K) q σ y.val = y.val := by
      have hh := congrArg
        (fun w => (hplace ▸ w : Place.localField L (Place.ofFinite q))) key
      simpa only [glp_cast_cast hplace] using hh
    exact hfinal
  -- ## Step 2: fixed points of a Galois extension lie in the base field
  have hmem : ∀ u : (q.adicCompletion L)ˣ,
      (∀ τ : (q.adicCompletion L) ≃ₐ[Q.adicCompletion K] (q.adicCompletion L),
        τ u.val = u.val) →
      ∃ a : Q.adicCompletion K, algebraMap (Q.adicCompletion K) (q.adicCompletion L) a = u.val := by
    intro u hu
    have : u.val ∈ (⊥ : IntermediateField (Q.adicCompletion K) (q.adicCompletion L)) := by
      rw [← IsGalois.fixedField_top (F := Q.adicCompletion K) (E := q.adicCompletion L)]
      rw [IntermediateField.mem_fixedField_iff]
      intro τ _
      exact hu τ
    exact IntermediateField.mem_bot.mp this
  obtain ⟨a₀, ha₀⟩ := hmem y hfix
  have hfix_inv : ∀ τ : (q.adicCompletion L) ≃ₐ[Q.adicCompletion K] (q.adicCompletion L),
      τ (y⁻¹).val = (y⁻¹).val := by
    intro τ
    rw [Units.val_inv_eq_inv_val, map_inv₀, hfix τ]
  obtain ⟨a₁, ha₁⟩ := hmem y⁻¹ hfix_inv
  -- ## Step 3: `a₀` is a unit mapping to `y`
  have hinj : Function.Injective (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) := by
    rw [Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra_algebraMap]
    exact Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective Q q h
  have h₁ : a₀ * a₁ = 1 := by
    apply hinj
    rw [map_mul, ha₀, ha₁, map_one, Units.val_inv_eq_inv_val]
    exact mul_inv_cancel₀ (Units.ne_zero y)
  have h₂ : a₁ * a₀ = 1 := by
    apply hinj
    rw [map_mul, ha₁, ha₀, map_one, Units.val_inv_eq_inv_val]
    exact inv_mul_cancel₀ (Units.ne_zero y)
  refine ⟨⟨a₀, a₁, h₁, h₂⟩, ?_⟩
  have hmain : Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom
      (⟨a₀, a₁, h₁, h₂⟩ : (Q.adicCompletion K)ˣ) = y := by
    apply Units.ext
    rw [Units.coe_map]
    exact ha₀
  have hmap : Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q)
      (Place.liesOver_ofFinite h) =
      Units.map (algebraMap (Q.adicCompletion K) (q.adicCompletion L)).toMonoidHom := by
    rw [glp_localAlgebraMapUnits_ofFinite h]
    rfl
  simpa only [hmap] using hmain

end NK.GlobalCFT.Inclusion
