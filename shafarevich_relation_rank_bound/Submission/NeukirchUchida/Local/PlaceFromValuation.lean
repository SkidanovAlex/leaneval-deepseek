import Submission.NeukirchUchida.Local.LocalTransfer
import Submission.NeukirchUchida.Local.InfiniteDecomposition
import Submission.Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_valuationSubring
import Submission.Commons.FieldTheory.Galois.mem_stabilizer_valuationSubring_iff_forall_restrict
import Submission.Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
import Submission.Commons.RingTheory.Valuation.valuationSubringAtPrime_injective
import Submission.Commons.RingTheory.Valuation.comap_inclusion_comap_eq
import Submission.Commons.RingTheory.Valuation.algebraMap_mem_valuationSubringAtPrime

/-!
# The finite place attached to a valuation subring

Let `K` be a number field, `p` a finite place of `K`, `K'` a (possibly infinite) extension of `K`
and `A` a valuation subring of `K'` whose restriction to `K` is the valuation ring `𝒪_𝔭` of `p`.
Then for every finite Galois intermediate field `L ⊆ K'` the intersection `A ∩ L` is the valuation
ring of a finite place `w_L` of `L`, and the stabiliser of `A ∩ L` in `Gal(L/K)` is the
decomposition group of `w_L`.

This is the passage from the "place of the infinite extension" (a valuation subring of `K'`) to
the finite places `w_L` whose decomposition groups form the projective system computing the
decomposition group of `A` (Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter II
and Chapter XII §1).

## Main results

* `valuationSubringAtPrime_ne_top` : `𝒪_𝔭 ≠ K`;
* `restrictValuationSubring_ne_top` : `A ∩ L ≠ L`;
* `heightOneSpectrum_valuation_placeSmul` : the valuation of `σ • w` at `σ x` is that of `w` at
  `x`;
* `mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup` : the stabiliser of the
  valuation ring of `w` in `Gal(L/K)` is the decomposition group of `w`.
-/

open scoped NumberField Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Submission.NeukirchUchida.Local

section Generic

variable {K : Type*} [Field K] [NumberField K]

/-- **The valuation ring of a finite place of a number field is not the whole field.** -/
theorem valuationSubringAtPrime_ne_top (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p ≠ ⊤ := by
  intro h
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.valuationSubring_eq_top_iff] at h
  exact h inferInstance

end Generic

section Restrict

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

/-- The restriction of a valuation subring of `K'` to the base field is not everything if the
restriction to the intermediate field `L` is not everything. -/
theorem comap_algebraMap_eq_top_of_comap_eq_top {A : ValuationSubring K'}
    {L : IntermediateField K K'} (h : A.comap (algebraMap ↥L K') = ⊤) :
    A.comap (algebraMap K K') = ⊤ := by
  have key : ∀ x : K, algebraMap K K' x ∈ A := by
    intro x
    have h1 : algebraMap K ↥L x ∈ A.comap (algebraMap ↥L K') := by
      rw [h]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap] at h1
    rw [IsScalarTower.algebraMap_apply K ↥L K']
    exact h1
  refine SetLike.ext fun x => ?_
  rw [ValuationSubring.mem_comap]
  exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => key x⟩

variable (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- If the restriction of `A` to `K` is the valuation ring at `p`, then `A` does not contain `K`. -/
theorem comap_algebraMap_ne_top (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    A.comap (algebraMap K K') ≠ ⊤ := by
  rw [hA]
  exact valuationSubringAtPrime_ne_top p

/-- **The intersection of `A` with a finite intermediate field is not the whole field.** -/
theorem restrictValuationSubring_ne_top (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') : A.comap (algebraMap ↥L K') ≠ ⊤ := by
  intro h
  exact comap_algebraMap_ne_top p A hA (comap_algebraMap_eq_top_of_comap_eq_top h)

end Restrict

/-! ## The valuation of `σ • w` -/

section Vall

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The valuation of the place `σ • w` at `σ x` is the valuation of `w` at `x`.** -/
theorem heightOneSpectrum_valuation_placeSmul (σ : Gal(L/K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (x : L) :
    IsDedekindDomain.HeightOneSpectrum.valuation L (placeSmul σ w) (σ x) =
      IsDedekindDomain.HeightOneSpectrum.valuation L w x :=
  Commons.RingTheory.DedekindDomain.valuation_map_of_map_eq
    (R := 𝓞 L) (K := L)
    (galRestrict (𝓞 K) K L (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) σ.toRingEquiv
    (fun r => (algebraMap_galRestrict_apply (𝓞 K) σ r).symm)
    w (placeSmul σ w) (placeSmul_asIdeal σ w) x

/-- **The stabiliser of the valuation ring of a finite place is its decomposition group.** -/
theorem mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (σ : Gal(L/K)) :
    σ ∈ MulAction.stabilizer (Gal(L/K))
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w) ↔
      σ ∈ decompositionSubgroup (K := K) w := by
  have hmem : ∀ y : L, (y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w ↔
      IsDedekindDomain.HeightOneSpectrum.valuation L w y ≤ 1) := by
    intro y
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
      Valuation.mem_valuationSubring_iff]
  constructor
  · intro h
    rw [MulAction.mem_stabilizer_iff] at h
    have hstab : ∀ y : L,
        (y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w ↔
          σ y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w) := by
      intro y
      have hy : σ y ∈ σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w ↔
          σ⁻¹ • (σ y) ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w :=
        ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      rw [h] at hy
      simpa using hy.symm
    rw [mem_decompositionSubgroup]
    refine IsDedekindDomain.HeightOneSpectrum.eq_of_valuation_isEquiv_valuation (K := L) ?_
    rw [Valuation.isEquiv_iff_val_le_one]
    intro y
    obtain ⟨x, rfl⟩ := σ.surjective y
    rw [heightOneSpectrum_valuation_placeSmul σ w x]
    exact (hmem x).symm.trans ((hstab x).trans (hmem (σ x)))
  · intro h
    rw [mem_decompositionSubgroup] at h
    rw [MulAction.mem_stabilizer_iff]
    refine SetLike.ext fun y => ?_
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have hkey : IsDedekindDomain.HeightOneSpectrum.valuation L w (σ⁻¹ • y) =
        IsDedekindDomain.HeightOneSpectrum.valuation L w y := by
      have h2 := heightOneSpectrum_valuation_placeSmul (K := K) σ w (σ⁻¹ • y)
      rw [h] at h2
      simpa using h2.symm
    have hy : σ⁻¹ • y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w ↔
        IsDedekindDomain.HeightOneSpectrum.valuation L w (σ⁻¹ • y) ≤ 1 := hmem _
    have hy' : y ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L w ↔
        IsDedekindDomain.HeightOneSpectrum.valuation L w y ≤ 1 := hmem _
    rw [hy, hy', hkey]

end Vall


/-! ## Number field instances for finite intermediate fields -/

section NumberFieldInstances

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

/-- A finite-dimensional extension of a number field is finite dimensional over `ℚ`. -/
instance instFiniteDimensionalRatIntermediateField (L : IntermediateField K K')
    [FiniteDimensional K L] : FiniteDimensional ℚ ↥L :=
  Module.Finite.trans K ↥L

/-- A finite-dimensional extension of a number field is a number field. -/
instance instNumberFieldIntermediateField (L : IntermediateField K K')
    [FiniteDimensional K L] : NumberField ↥L := NumberField.mk

end NumberFieldInstances

/-! ## The finite place of an intermediate field -/

section Place

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

/-- A finite normal intermediate field of a characteristic zero extension is Galois over the base
field (instance form of `Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero`). -/
instance instIsGaloisIntermediateFieldOfNormalOfFinite {K K' : Type*} [Field K] [Field K']
    [Algebra K K'] [CharZero K] (L : IntermediateField K K') [FiniteDimensional K L]
    [Normal K L] : IsGalois K ↥L :=
  Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero

/-- **The ring of integers of a finite intermediate field is contained in `A ∩ L`** whenever `A`
contains the image of `𝓞 K`.  Indeed `𝓞 L` is the integral closure of `𝓞 K` in `L` and a
valuation subring of a field is integrally closed. -/
theorem ringOfIntegers_le_comap_algebraMap (A : ValuationSubring K')
    (L : IntermediateField K K') [FiniteDimensional K L]
    (hA : ∀ x : 𝓞 K, algebraMap K K' (algebraMap (𝓞 K) K x) ∈ A) :
    ∀ x : 𝓞 ↥L, algebraMap (𝓞 ↥L) ↥L x ∈ A.comap (algebraMap ↥L K') := by
  refine Commons.NumberTheory.NumberField.ringOfIntegers_le_valuationSubring
    (K := K) (L := ↥L) (A := A.comap (algebraMap ↥L K')) ?_
  intro x
  rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply K ↥L K']
  exact hA x

/-- **The finite place of `L` cut out by the valuation subring `A` of `K'`.** -/
theorem exists_place_of_comap_eq (A : ValuationSubring K')
    (hAne : A.comap (algebraMap K K') ≠ ⊤)
    (hA : ∀ x : 𝓞 K, algebraMap K K' (algebraMap (𝓞 K) K x) ∈ A)
    (L : IntermediateField K K') [FiniteDimensional K L] :
    ∃ w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L),
      A.comap (algebraMap ↥L K') =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L w := by
  refine Commons.RingTheory.Valuation.exists_heightOneSpectrum_eq_valuationSubringAtPrime
    (A.comap (algebraMap ↥L K')) ?_ (ringOfIntegers_le_comap_algebraMap A L hA)
  intro h
  exact hAne (comap_algebraMap_eq_top_of_comap_eq_top h)

/-- **The restriction of an element of the decomposition group of a place of `K'` is in the
decomposition group of the induced place of every finite normal intermediate field.**

This is the compatibility of the projective system of finite-level decomposition groups at the
level of places: the place `w` of `L` is the one cut out by `A`. -/
theorem restrictNormalHom_mem_decompositionSubgroup_of_mem_stabilizer
    {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsGalois K K']
    (A : ValuationSubring K') (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L))
    (hw : A.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L w)
    (σ : Gal(K'/K)) (hσ : σ ∈ MulAction.stabilizer (Gal(K'/K)) A) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := K') ↥L σ ∈ decompositionSubgroup (K := K) w := by
  have h1 := (Commons.FieldTheory.Galois.mem_stabilizer_valuationSubring_iff_forall_restrict
      A σ).mp hσ L
  rw [hw] at h1
  exact (mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup w
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') ↥L σ)).mp h1

end Place


/-! ## The decomposition group of a place of a separable closure -/

section Limit

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

/-- The image of the ring of integers of the base field is contained in `A`, when `A` restricts to
the valuation ring of `p` on `K`. -/
theorem algebraMap_mem_of_comap_eq (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    ∀ x : 𝓞 K, algebraMap K K' (algebraMap (𝓞 K) K x) ∈ A := by
  intro x
  rw [← ValuationSubring.mem_comap, hA]
  exact Commons.RingTheory.Valuation.algebraMap_mem_valuationSubringAtPrime p x

/-- `A` does not contain `K` when it restricts to the valuation ring of `p`. -/
theorem comap_ne_top_of_eq (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    A.comap (algebraMap K K') ≠ ⊤ := by
  rw [hA]
  exact valuationSubringAtPrime_ne_top p

/-- **The finite place of a finite intermediate field cut out by the place `A` of `K'`.** -/
noncomputable def placeOf (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] :
    IsDedekindDomain.HeightOneSpectrum (𝓞 ↥L) :=
  Classical.choose (exists_place_of_comap_eq A (comap_ne_top_of_eq p A hA)
    (algebraMap_mem_of_comap_eq p A hA) L)

/-- The defining property of `placeOf`: it is the finite place whose valuation ring is the
intersection of `A` with the intermediate field. -/
theorem comap_eq_valuationSubringAtPrime_placeOf
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] :
    A.comap (algebraMap ↥L K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L (placeOf p A hA L) :=
  Classical.choose_spec (exists_place_of_comap_eq A (comap_ne_top_of_eq p A hA)
    (algebraMap_mem_of_comap_eq p A hA) L)

/-- The prime of `𝓞 K` below the place `w_L` induced by `A`. -/
noncomputable def primeBelow (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
  ⟨(placeOf p A hA L).asIdeal.under (𝓞 K), inferInstance,
    Ideal.under_ne_bot (𝓞 K) (placeOf p A hA L).ne_bot⟩

theorem primeBelow_asIdeal (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] :
    (primeBelow p A hA L).asIdeal = (placeOf p A hA L).asIdeal.under (𝓞 K) := rfl

/-- The induced finite place `w_L` lies over `primeBelow`. -/
theorem placeOf_liesOver_primeBelow (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] :
    (placeOf p A hA L).asIdeal.LiesOver (primeBelow p A hA L).asIdeal := ⟨rfl⟩

/-- **The induced place `w_L` lies over the prime `p` of the base field.**

Consequently the local Galois groups in `decompositionSubgroup_placeOf_mulEquiv_localGalois` are
extensions of the completion `K_p` of the base field at `p`. -/
theorem primeBelow_eq (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] :
    primeBelow p A hA L = p := by
  have hnat := Commons.RingTheory.Valuation.comap_valuationSubringAtPrime (K := K) (L := ↥L)
    (primeBelow p A hA L) (placeOf p A hA L) (placeOf_liesOver_primeBelow p A hA L)
  have hw := comap_eq_valuationSubringAtPrime_placeOf p A hA L
  have hcomp : (A.comap (algebraMap ↥L K')).comap (algebraMap K ↥L) =
      A.comap (algebraMap K K') := by
    refine SetLike.ext fun x => ?_
    simp only [ValuationSubring.mem_comap]
    rw [IsScalarTower.algebraMap_apply K ↥L K']
  have key : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K (primeBelow p A hA L) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p := by
    rw [← hnat, ← hw]
    exact hcomp.trans hA
  exact Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (R := 𝓞 K) (K := K) key


/-- **The induced finite place `w_L` lies over `p`.** -/
theorem placeOf_liesOver (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] :
    (placeOf p A hA L).asIdeal.LiesOver p.asIdeal := by
  have h1 : (placeOf p A hA L).asIdeal.under (𝓞 K) = p.asIdeal := by
    rw [← primeBelow_asIdeal p A hA L, primeBelow_eq p A hA L]
  exact ⟨h1.symm⟩

variable [IsGalois K K']

/-- **The decomposition group of a place of a separable closure is the projective limit of the
decomposition groups of its restrictions to the finite normal intermediate fields.**

This is the precise statement that the decomposition group `D_A ≤ Gal(K'/K)` of the place `A` is
the inverse limit of the finite groups `D_{w_L} ≅ Gal(L_{w_L}/K_p)`. -/
theorem mem_stabilizer_iff_forall_mem_decompositionSubgroup
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (σ : Gal(K'/K)) :
    σ ∈ MulAction.stabilizer (Gal(K'/K)) A ↔
      ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L],
        AlgEquiv.restrictNormalHom (F := K) (K₁ := K') ↥L σ ∈
          decompositionSubgroup (K := K) (placeOf p A hA L) := by
  constructor
  · intro hσ L hLfin hLnorm
    haveI := hLfin
    haveI := hLnorm
    have h1 := (Commons.FieldTheory.Galois.restrictNormalHom_smul_comap_eq_of_smul_eq
      A σ ((MulAction.mem_stabilizer_iff).mp hσ) L)
    rw [comap_eq_valuationSubringAtPrime_placeOf p A hA L] at h1
    exact (mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup _ _).mp
      ((MulAction.mem_stabilizer_iff).mpr h1)
  · intro h
    rw [MulAction.mem_stabilizer_iff]
    have key : ∀ y : K', y ∈ A ↔ σ y ∈ A := by
      intro y
      set L₀ : IntermediateField K K' := IntermediateField.adjoin K ({y} : Set K')
      haveI hL₀ : FiniteDimensional K L₀ :=
        IntermediateField.adjoin.finiteDimensional (IsGalois.integral K y)
      set L : IntermediateField K K' := IntermediateField.normalClosure K L₀ K'
      haveI hLn : Normal K L := inferInstance
      haveI hLf : FiniteDimensional K L := inferInstance
      have hyL₀ : y ∈ L₀ := IntermediateField.mem_adjoin_simple_self K y
      have hyL : y ∈ L := IntermediateField.le_normalClosure L₀ hyL₀
      have hσyL : σ y ∈ L := by
        have hg : σ y ∈ (σ.toAlgHom.comp L₀.val).fieldRange := ⟨⟨y, hyL₀⟩, by simp⟩
        exact AlgHom.fieldRange_le_normalClosure (σ.toAlgHom.comp L₀.val) hg
      have hL := h L
      rw [mem_decompositionSubgroup] at hL
      have hL' := (mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
        (placeOf p A hA L)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') ↥L σ)).mpr hL
      rw [MulAction.mem_stabilizer_iff] at hL'
      have hplace : A.comap (algebraMap ↥L K') =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L (placeOf p A hA L) :=
        comap_eq_valuationSubringAtPrime_placeOf p A hA L
      constructor
      · intro hyA
        have hx : (⟨y, hyL⟩ : ↥L) ∈ A.comap (algebraMap ↥L K') := by
          rw [ValuationSubring.mem_comap, IntermediateField.algebraMap_apply]
          exact hyA
        rw [hplace] at hx
        have hs := ValuationSubring.smul_mem_pointwise_smul
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') ↥L σ) (⟨y, hyL⟩ : ↥L)
          (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L (placeOf p A hA L)) hx
        rw [hL'] at hs
        rw [← hplace, ValuationSubring.mem_comap, IntermediateField.algebraMap_apply,
          AlgEquiv.smul_def, AlgEquiv.restrictNormalHom_apply] at hs
        simpa using hs
      · intro hσyA
        have hx : (⟨σ y, hσyL⟩ : ↥L) ∈ A.comap (algebraMap ↥L K') := by
          rw [ValuationSubring.mem_comap, IntermediateField.algebraMap_apply]
          exact hσyA
        rw [hplace] at hx
        have hmem : (⟨σ y, hσyL⟩ : ↥L) ∈
            (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') ↥L σ) •
              (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L
                (placeOf p A hA L)) := by
          rw [hL']; exact hx
        have hτ := (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
          (g := AlgEquiv.restrictNormalHom (F := K) (K₁ := K') ↥L σ)
          (S := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L
            (placeOf p A hA L))).mp hmem
        have h3 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') ↥L σ)⁻¹ •
              (⟨σ y, hσyL⟩ : ↥L) = (⟨y, hyL⟩ : ↥L) := by
          apply Subtype.ext
          rw [AlgEquiv.smul_def, ← map_inv, AlgEquiv.restrictNormalHom_apply]
          simp
        rw [h3, ← hplace, ValuationSubring.mem_comap, IntermediateField.algebraMap_apply] at hτ
        simpa using hτ
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have hk := key (σ⁻¹ • x)
    simpa [AlgEquiv.smul_def] using hk

/-- **The decomposition group of a place as an inverse limit of finite quotients.**

The stabiliser of `A` in `Gal(K'/K)` is the intersection of the preimages of the finite-level
decomposition groups `D_{w_L}`; equivalently, since `Gal(K'/K)` is the inverse limit of the finite
groups `Gal(L/K)`, it is the inverse limit of the `D_{w_L}` along the restriction maps. -/
theorem stabilizer_eq_iInf_decompositionSubgroup
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p) :
    MulAction.stabilizer (Gal(K'/K)) A =
      ⨅ (L : IntermediateField K K') (_ : FiniteDimensional K L) (_ : Normal K L),
        (decompositionSubgroup (K := K) (placeOf p A hA L)).comap
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') ↥L) := by
  refine Subgroup.ext fun σ => ?_
  simp only [Subgroup.mem_iInf]
  exact mem_stabilizer_iff_forall_mem_decompositionSubgroup p A hA σ

/-- **The finite-level decomposition groups in the inverse limit are local Galois groups.**

For every finite normal intermediate field `L`, the finite-level decomposition group appearing in
`stabilizer_eq_iInf_decompositionSubgroup` is canonically isomorphic to the local Galois group of
the completion of `L` at the induced place `w_L` over the completion of `K` at the prime below
`w_L`. -/
noncomputable def decompositionSubgroup_placeOf_mulEquiv_localGalois
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] :
    letI := adicCompletionAlgebra (primeBelow p A hA L) (placeOf p A hA L)
      (placeOf_liesOver_primeBelow p A hA L)
    decompositionSubgroup (K := K) (placeOf p A hA L) ≃*
      ((placeOf p A hA L).adicCompletion ↥L ≃ₐ[(primeBelow p A hA L).adicCompletion K]
        (placeOf p A hA L).adicCompletion ↥L) :=
  letI := adicCompletionAlgebra (primeBelow p A hA L) (placeOf p A hA L)
    (placeOf_liesOver_primeBelow p A hA L)
  decompositionSubgroupMulEquivLocalGalois (K := K) (L := ↥L)
    (primeBelow p A hA L) (placeOf p A hA L) (placeOf_liesOver_primeBelow p A hA L)

/-- **The finite-level decomposition groups in the inverse limit are local Galois groups over
`K_p`.**

This is `decompositionSubgroup_placeOf_mulEquiv_localGalois` with the prime below `w_L` identified
with `p` by `primeBelow_eq`. -/
noncomputable def decompositionSubgroup_placeOf_mulEquiv_localGalois_self
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] :
    letI := adicCompletionAlgebra p (placeOf p A hA L) (placeOf_liesOver p A hA L)
    decompositionSubgroup (K := K) (placeOf p A hA L) ≃*
      ((placeOf p A hA L).adicCompletion ↥L ≃ₐ[p.adicCompletion K]
        (placeOf p A hA L).adicCompletion ↥L) :=
  letI := adicCompletionAlgebra p (placeOf p A hA L) (placeOf_liesOver p A hA L)
  decompositionSubgroupMulEquivLocalGalois (K := K) (L := ↥L)
    p (placeOf p A hA L) (placeOf_liesOver p A hA L)


end Limit


/-! ## Compatibility of the induced places along a tower -/

section Tower

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']

theorem comap_inclusion_comap_eq {L L₀ : IntermediateField K K'} (h : L₀ ≤ L)
    (A : ValuationSubring K') :
    (A.comap (algebraMap ↥L K')).comap (IntermediateField.inclusion h) =
      A.comap (algebraMap ↥L₀ K') :=
  Commons.RingTheory.Valuation.comap_inclusion_comap_eq h A

/-- **The finite places induced by a place of `K'` are compatible along the tower.** -/
theorem restrictValuationSubringAtPrime_placeOf
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    {L₀ L : IntermediateField K K'} (h : L₀ ≤ L) [FiniteDimensional K L₀]
    [FiniteDimensional K L] :
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L (placeOf p A hA L)).comap
        (IntermediateField.inclusion h) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥L₀ (placeOf p A hA L₀) := by
  rw [← comap_eq_valuationSubringAtPrime_placeOf p A hA L,
    ← comap_eq_valuationSubringAtPrime_placeOf p A hA L₀]
  exact comap_inclusion_comap_eq h A

end Tower


end Submission.NeukirchUchida.Local
