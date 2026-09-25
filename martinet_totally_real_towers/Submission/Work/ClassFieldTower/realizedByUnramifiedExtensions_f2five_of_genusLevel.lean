import Mathlib
import Submission.Work.ClassFieldTower.WallShrunk
import Submission.Work.ClassFieldTower.ProTwoGenus
import Submission.Work.ClassFieldTower.ProTwoDefs
import Submission.Work.ClassFieldTower.five_le_of_surjective_zmodTwo_five

/-!
# Every finite `2`-quotient of `(𝔽₂)^5` is realized by an unramified extension

The genus level `HasGenusLevel F` supplies a finite unramified Galois extension `L₀/F` whose
Galois group has exponent `2` and order `2^5`.  Since a finite abelian group of exponent `2` and
order `2^5` is `(𝔽₂)^5`, the Galois group of `L₀/F` is isomorphic to `F2five`; and every finite
`2`-quotient of `F2five` is the Galois group of a subextension of `L₀/F`, which is again
unramified over `F` because the relative different is trivial.

The tool that makes the last step work is

* `differentIdeal_eq_top_of_intermediateField`: the relative different of a subextension of an
  extension with trivial relative different is trivial.  This is the tower formula
  `differentIdeal_eq_differentIdeal_mul_differentIdeal` together with the fact that the extension
  of a proper ideal along an integral ring extension `𝓞 L → 𝓞 L₀` is proper
  (`Ideal.map_eq_top_iff`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **Unramifiedness passes to intermediate fields.**

If `E/F` is an extension of number fields with trivial relative different (`𝔡(E/F) = (1)`) and
`L` is an intermediate field, then `𝔡(L/F) = (1)`.  Equivalently: a subextension of an extension
that is unramified at every finite prime is unramified at every finite prime.

Proof: the transitivity of the different ideal gives
`𝔡(E/F) = 𝔡(E/L) · 𝔡(L/F)·𝓞 E`; as `𝔡(E/F) = ⊤` and both factors are contained in the second
one, the extension `𝔡(L/F)·𝓞 E` is the unit ideal of `𝓞 E`.  The ring map `𝓞 L → 𝓞 E` is
injective and integral, so an ideal whose extension is the unit ideal is itself the unit ideal
(`Ideal.map_eq_top_iff`). -/
private theorem differentIdeal_eq_top_of_intermediateField {F E : Type*} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    (L : IntermediateField F E) (h : differentIdeal (𝓞 F) (𝓞 E) = ⊤) :
    differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤ := by
  -- transitivity of the different ideal, over the tower `𝓞 F ⊆ 𝓞 ↥L ⊆ 𝓞 E`
  have htower := differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 F) (𝓞 ↥L) (𝓞 E)
  -- the extension of `𝔡(L/F)` to `𝓞 E` is the unit ideal
  have hmap : Ideal.map (algebraMap (𝓞 ↥L) (𝓞 E)) (differentIdeal (𝓞 F) (𝓞 ↥L)) = ⊤ := by
    rw [h] at htower
    exact top_le_iff.mp ((le_of_eq htower).trans Ideal.mul_le_right)
  -- an ideal of `𝓞 ↥L` whose extension to the integral extension `𝓞 E` is the unit ideal is
  -- itself the unit ideal
  exact (Ideal.map_eq_top_iff (algebraMap (𝓞 ↥L) (𝓞 E))
    (FaithfulSMul.algebraMap_injective _ _) (fun x => Algebra.IsIntegral.isIntegral x)).mp hmap

/-- Every finite `2`-quotient of `(𝔽₂)^5` (i.e. of `F2five = Fin 5 → Multiplicative (ZMod 2)`) is
the Galois group of a finite unramified Galois extension of `F`, whenever `F` has a genus level
(`HasGenusLevel F`: an unramified finite Galois extension with exponent-`2` Galois group of order
`2^5`).

Proof strategy: let `h` give `L₀/F` unramified, finite dimensional, Galois, with `σ² = 1` for all
`σ ∈ Gal(L₀/F)` and `Nat.card (L₀ ≃ₐ[F] L₀) = 2^5`.  The commons lemma
`Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card`
(composed with `piMulEquivZmodTwo 5`) gives `e : (L₀ ≃ₐ[F] L₀) ≃* F2five`.  Given `N : Subgroup F2five`
(any subgroup, all are normal as `F2five` is abelian) take `H := N.comap e`, `L := fixedField H ⊆ L₀`.
Then `L/F` is finite dimensional, `IsGalois F ↥L` (`IntermediateField.of_fixedField_normal_subgroup`),
`differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤` (subextension of an unramified extension: use
`Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx` together with
`Ideal.ramificationIdx_tower` / `ramificationIdx_below_dvd`, or the tower formula
`differentIdeal_eq_differentIdeal_mul_differentIdeal`), and
`Gal(L/F) ≅ Gal(L₀/F) ⧸ H ≅ F2five ⧸ N` (via `AlgEquiv.restrictNormalHom` +
`IntermediateField.fixingSubgroup_fixedField` + `QuotientGroup.congr` with `e`). -/
theorem realizedByUnramifiedExtensions_f2five_of_genusLevel {F : Type} [Field F] [NumberField F]
    (h : HasGenusLevel F) : RealizedByUnramifiedExtensions F F2five := by
  classical
  obtain ⟨L₀, iL, iNL, iAL, hfd, hgal, hdiff, hexp, hcard⟩ := h
  letI : Field L₀ := iL
  letI : NumberField L₀ := iNL
  letI : Algebra F L₀ := iAL
  letI : FiniteDimensional F L₀ := hfd
  letI : IsGalois F L₀ := hgal
  -- a finite group of exponent `2` is commutative
  haveI : Fintype (L₀ ≃ₐ[F] L₀) := AlgEquiv.fintype F L₀
  haveI : IsMulCommutative (L₀ ≃ₐ[F] L₀) :=
    IsMulCommutative.of_comm (fun a b => commute_of_sq_eq_one hexp a b)
  -- `Gal(L₀/F) ≃* (ℤ/2)^5`, i.e. `≃* F2five`
  obtain ⟨e₀⟩ :=
    Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
      (G := L₀ ≃ₐ[F] L₀) hexp hcard
  let e : (L₀ ≃ₐ[F] L₀) ≃* F2five := e₀.trans (piMulEquivZmodTwo 5).symm
  intro N hN _ _
  -- the subgroup of `Gal(L₀/F)` cut out by `N`
  let H : Subgroup (L₀ ≃ₐ[F] L₀) := N.comap e
  haveI hHn : (Subgroup.comap (e : (L₀ ≃ₐ[F] L₀) →* F2five) N).Normal :=
    hN.comap (e : (L₀ ≃ₐ[F] L₀) →* F2five)
  -- the corresponding subextension, which is unramified over `F`
  let L : IntermediateField F L₀ := IntermediateField.fixedField H
  refine ⟨↥L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact differentIdeal_eq_top_of_intermediateField L hdiff
  · -- `Gal(L/F) ≃ Gal(L₀/F) ⧸ H ≃ F2five ⧸ N`
    refine ⟨((IsGalois.normalAutEquivQuotient H).symm).trans (QuotientGroup.congr H N e ?_)⟩
    rw [Subgroup.map_comap_eq, e.range_eq_top, top_inf_eq]

end Work.ClassFieldTower
