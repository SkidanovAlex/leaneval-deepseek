import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Connected.Separation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local fixed points at a finite place

Let `L / K` be a finite Galois extension of number fields, `q` a nonarchimedean place of `L` lying
over the nonarchimedean place `Q` of `K`.  The decomposition group `D_q = {σ | σ • q = q} ≤
Gal(L/K)` acts on the local field `L_q` through the canonical local isomorphisms
`Place.localRingEquiv σ q : L_q ≃+* L_{σ q}`, and the Galois group of the local extension
`L_q / K_Q` is exactly the decomposition group (the commons lemma
`decompositionSubgroupMulEquivLocalGalois`).

Consequently the units of `L_q` fixed by the decomposition group are precisely the units coming
from `K_Q`: if `y ∈ L_qˣ` is fixed by every `σ ∈ D_q` then `y` lies in the image of the canonical
local map `K_Qˣ →* L_qˣ`.  This is the local input for the computation of the fixed points of the
idèle class group under `Gal(L/K)` (Neukirch–Schmidt–Wingberg, Chapter XII).

## Main result

* `NK.GlobalCFT.Galois.globalCFT_localFixed_finite`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### Transport of local fields along equalities of places

The local field `L_v` is defined by a `match` on the place `v`, so equalities of places have to be
transported along.  These elementary lemmas record how this transport interacts with the
underlying elements of the unit group and with itself. -/

/-- Transporting a unit of a local field along an equality of places commutes with the transport of
its underlying element. -/
lemma place_units_cast_val {a b : Place L} (h : a = b) (u : (Place.localField L a)ˣ) :
    ((h ▸ u : (Place.localField L b)ˣ)).val = (h ▸ u.val : Place.localField L b) := by
  cases h; rfl

/-- The transport along `h` followed by the transport along `h.symm` is the identity. -/
lemma place_cast_cast {a b : Place L} (h : a = b) (z : Place.localField L b) :
    (h ▸ (h.symm ▸ z : Place.localField L a) : Place.localField L b) = z := by
  cases h; rfl

/-- The automorphism of `𝓞 L` induced by `σ : Gal(L/K)` is the restriction of `σ` to the ring of
integers; here this is spelled out for Mathlib's `galRestrict`. -/
lemma ringOfIntegersEquiv_eq_galRestrict (σ : L ≃ₐ[K] L) :
    Place.ringOfIntegersEquiv σ = galRestrict (𝓞 K) K L (𝓞 L) σ := by
  ext x
  exact (algebraMap_galRestrict_apply (𝓞 K) σ x).symm

variable [FiniteDimensional K L] [IsGalois K L]

/-- The action of `Gal(L/K)` on the finite places of `L` used in the commons (`placeSmul`) agrees
with the one used in `NK.GlobalCFT` (`Place.smulHeightOneSpectrum`). -/
lemma smulHeightOneSpectrum_eq_of_mem_decompositionSubgroup
    {q : HeightOneSpectrum (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q) :
    Place.smulHeightOneSpectrum σ q = q := by
  apply HeightOneSpectrum.ext
  rw [Place.smulHeightOneSpectrum_asIdeal, ringOfIntegersEquiv_eq_galRestrict]
  exact Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_map_eq hσ

/-- An element of the decomposition group of `q` fixes the place `Place.ofFinite q`. -/
lemma smul_ofFinite_of_mem_decompositionSubgroup
    {q : HeightOneSpectrum (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q) :
    σ • Place.ofFinite q = Place.ofFinite q := by
  rw [Place.smul_ofFinite, smulHeightOneSpectrum_eq_of_mem_decompositionSubgroup hσ]

/-! ### The action of the decomposition group on the local field

The `NK.GlobalCFT` action `Place.localRingEquiv` and the commons action
`decompositionToAdicCompletion` of the decomposition group on the `q`-adic completion are both
"apply `σ`", hence equal: both are continuous and they agree on the dense image of `L`. -/

lemma localRingEquiv_eq_cast_decompositionToAdicCompletion
    {q : HeightOneSpectrum (𝓞 L)} (σ : L ≃ₐ[K] L)
    (hσD : σ ∈ Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) q)
    (hσ : σ • Place.ofFinite q = Place.ofFinite q) (x : q.adicCompletion L) :
    Place.localRingEquiv σ (Place.ofFinite q) x =
      (hσ.symm ▸ (Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion
        (K := K) q ⟨σ, hσD⟩ x) : Place.localField L (σ • Place.ofFinite q)) := by
  have hdense : DenseRange (algebraMap L (Place.localField L (Place.ofFinite q))) :=
    denseRange_algebraMap_localField (Place.ofFinite q)
  have hcont₁ : Continuous (fun x : Place.localField L (Place.ofFinite q) =>
      Place.localRingEquiv σ (Place.ofFinite q) x) := continuous_localRingEquiv σ _
  have hcont₂ : Continuous (fun x : Place.localField L (Place.ofFinite q) =>
      (hσ.symm ▸ (Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion
        (K := K) q ⟨σ, hσD⟩ x) : Place.localField L (σ • Place.ofFinite q))) :=
    continuous_localField_cast hσ.symm
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
    rw [Place.localRingEquiv_algebraMap]
    rw [globalCFT_algebraMap_eq_coe]
    rw [Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion_coe]
    rw [← globalCFT_algebraMap_eq_coe]
    rw [← localField_cast_algebraMap]
  exact congrFun hfun x

/-- The canonical local units map `K_Qˣ →* L_qˣ` at the finite places `q | Q`, in the form of the
commons' `adicCompletionMap`. -/
lemma localAlgebraMapUnits_ofFinite {q : HeightOneSpectrum (𝓞 L)} {Q : HeightOneSpectrum (𝓞 K)}
    (h : q.asIdeal.LiesOver Q.asIdeal) :
    Place.localAlgebraMapUnits (Place.ofFinite q) (Place.ofFinite Q)
        (Place.liesOver_ofFinite h) =
      Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q h).toMonoidHom := by
  ext u
  simp only [Place.localAlgebraMapUnits, Units.coe_map]
  rw [dif_pos h]
  rw [Units.coe_map]

end NK.GlobalCFT.Galois

namespace NK.GlobalCFT.Galois

open NK.GlobalCFT

theorem globalCFT_localFixed_finite {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)}
    {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h : q.asIdeal.LiesOver Q.asIdeal)
    (y : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q))ˣ)
    (hy : ∀ σ : L ≃ₐ[K] L,
      ∀ (hσ : σ • NK.GlobalCFT.Place.ofFinite q = NK.GlobalCFT.Place.ofFinite q),
      Units.map (NK.GlobalCFT.Place.localRingEquiv σ
        (NK.GlobalCFT.Place.ofFinite q)).toMonoidHom y = hσ.symm ▸ y) :
    ∃ a : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))ˣ,
      NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite Q)
        (NK.GlobalCFT.Place.liesOver_ofFinite h) a = y := by
  classical
  -- The `K_Q`-algebra structure on `L_q` making `L_q / K_Q` a finite Galois extension.
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q h
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q h
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q h
  -- ## Step 1: `y` is fixed by the whole local Galois group `Gal(L_q / K_Q)`.
  have hfix : ∀ τ : (q.adicCompletion L) ≃ₐ[Q.adicCompletion K] (q.adicCompletion L),
      τ y.val = y.val := by
    intro τ
    obtain ⟨σ, hστ⟩ :=
      (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
        Q q h).surjective τ
    rw [← hστ,
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe]
    change Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion
      (K := K) q σ y.val = y.val
    -- `σ` is an element of the decomposition group of `q`.
    have hplace : σ.1 • Place.ofFinite q = Place.ofFinite q :=
      smul_ofFinite_of_mem_decompositionSubgroup σ.2
    have hyσ := hy σ.1 hplace
    have hcongr := congrArg
      (fun u : (Place.localField L (σ.1 • Place.ofFinite q))ˣ => u.val) hyσ
    have hT := place_units_cast_val hplace.symm y
    have hcmp :=
      localRingEquiv_eq_cast_decompositionToAdicCompletion (K := K) σ.1 σ.2 hplace y.val
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
      simpa only [place_cast_cast hplace] using hh
    exact hfinal
  -- ## Step 2: fixed points of a Galois extension lie in the base field.
  have hmem : ∀ u : (q.adicCompletion L)ˣ,
      (∀ τ : (q.adicCompletion L) ≃ₐ[Q.adicCompletion K] (q.adicCompletion L), τ u.val = u.val) →
      ∃ a : Q.adicCompletion K,
        algebraMap (Q.adicCompletion K) (q.adicCompletion L) a = u.val := by
    intro u hu
    have hbot : u.val ∈ (⊥ : IntermediateField (Q.adicCompletion K) (q.adicCompletion L)) := by
      rw [← IsGalois.fixedField_top (F := Q.adicCompletion K) (E := q.adicCompletion L)]
      rw [IntermediateField.mem_fixedField_iff]
      intro τ _
      exact hu τ
    exact IntermediateField.mem_bot.mp hbot
  obtain ⟨a₀, ha₀⟩ := hmem y hfix
  have hfix_inv : ∀ τ : (q.adicCompletion L) ≃ₐ[Q.adicCompletion K] (q.adicCompletion L),
      τ (y⁻¹).val = (y⁻¹).val := by
    intro τ
    rw [Units.val_inv_eq_inv_val, map_inv₀, hfix τ]
  obtain ⟨a₁, ha₁⟩ := hmem y⁻¹ hfix_inv
  -- ## Step 3: `a₀` is a unit and maps to `y`.
  have hinj : Function.Injective
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L)) := by
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
  rw [localAlgebraMapUnits_ofFinite h]
  refine Units.ext ?_
  rw [Units.coe_map]
  exact ha₀

end NK.GlobalCFT.Galois
