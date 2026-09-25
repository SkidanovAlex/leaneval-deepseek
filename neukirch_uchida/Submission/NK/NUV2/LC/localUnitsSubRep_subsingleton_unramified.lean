import Mathlib
import Submission.NK.HassePrinciple.LocalUnitsSub
import Submission.NK.GlobalCFTdeep.Herbrand.localUnitsUnitsEquiv
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_localUnitSubRep_of_ramificationIdx_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.hOne_localUnitSubRep_of_ramificationIdx_eq_one
import Submission.NK.CFTLib.tateCohomology_neg_one_idele_of_isUnramified
import Submission.NK.GlobalCFTdeep.Shared

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.NUV2.LC

open scoped NumberField
open CategoryTheory

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The prime of `𝓞 K` lying under a prime of `𝓞 L`. -/
noncomputable def lieUnder (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) :=
  ⟨q.asIdeal.under (NumberField.RingOfIntegers K),
    Ideal.IsPrime.under (NumberField.RingOfIntegers K) q.asIdeal,
    Ideal.under_ne_bot (NumberField.RingOfIntegers K) q.ne_bot⟩

theorem lieUnder_liesOver (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    q.asIdeal.LiesOver (lieUnder (K := K) q).asIdeal :=
  Ideal.LiesOver.mk rfl

/-! ## The coefficient-ring transfer for `H²`, at the level of `Subsingleton` -/

/-- The cocycle-level coefficient transfer: the class of a 2-cocycle in `H²` is zero over `k` if
and only if it is zero over `k'`, because both the cocycle and the coboundary conditions involve
only the `G`-action and the additive structure. -/
theorem H2π_eq_zero_transfer_cocycles {k k' G V : Type} [CommRing k] [CommRing k'] [Group G]
    [AddCommGroup V] [Module k V] [Module k' V] [DistribMulAction G V]
    [SMulCommClass G k V] [SMulCommClass G k' V]
    (z : ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k G V))) :
    (ConcreteCategory.hom (groupCohomology.H2π (Rep.ofDistribMulAction k G V))) z = 0 ↔
      (ConcreteCategory.hom (groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) z = 0 := by
  have h1 := groupCohomology.H2π_eq_zero_iff (A := Rep.ofDistribMulAction k G V) z
  have h2 := groupCohomology.H2π_eq_zero_iff (A := Rep.ofDistribMulAction k' G V) z
  exact h1.trans h2.symm

/-- **The coefficient-ring transfer for `H²`**: if `V` carries both a `k`-module and a `k'`-module
structure compatible with the same `G`-action and the second cohomology over `k` is trivial, then
so is the second cohomology over `k'`. -/
theorem subsingleton_groupCohomology_two_coeffTransfer
    {k k' G V : Type} [CommRing k] [CommRing k'] [Group G]
    [AddCommGroup V] [Module k V] [Module k' V] [DistribMulAction G V]
    [SMulCommClass G k V] [SMulCommClass G k' V]
    (h : Subsingleton (groupCohomology (Rep.ofDistribMulAction k G V) 2)) :
    Subsingleton (groupCohomology (Rep.ofDistribMulAction k' G V) 2) := by
  refine ⟨fun a b => ?_⟩
  have hsurj : Function.Surjective (⇑(groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨za, rfl⟩ := hsurj a
  obtain ⟨zb, rfl⟩ := hsurj b
  have key : ∀ z : ↥(groupCohomology.cocycles₂ (Rep.ofDistribMulAction k' G V)),
      (ConcreteCategory.hom (groupCohomology.H2π (Rep.ofDistribMulAction k' G V))) z = 0 := by
    intro z
    exact (H2π_eq_zero_transfer_cocycles (k := k) (k' := k') z).mp (h.elim _ 0)
  rw [key za, key zb]

/-! ## The two actions on the local units agree -/

/-- The action of the Hasse–Brauer–Noether decomposition group on the local units and the action
of the `NK.GlobalCFTdeep` decomposition group agree on underlying local units. -/
theorem hasse_smul_coe_eq (w : NK.GlobalCFT.Place L)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w) (u : ↥(NK.GlobalCFT.Place.localUnits L w)) :
    ((σ • u : ↥(NK.GlobalCFT.Place.localUnits L w)) :
        (NK.GlobalCFT.Place.localField L w)ˣ) =
      (((⟨σ.1, σ.2⟩ : NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w) • u :
        ↥(NK.GlobalCFT.Place.localUnits L w)) : (NK.GlobalCFT.Place.localField L w)ˣ) := by
  rw [NK.GlobalCFTdeep.coe_smul_localUnitSubRep]
  exact NK.GlobalCFTdeep.localUnitsEquiv_apply_eq (K := K) w σ
    (u : (NK.GlobalCFT.Place.localField L w)ˣ)

/-- The two representations of the decomposition group on the local units (over `ℤ`, with the two
different action instances) have the same action on the underlying elements. -/
theorem hasse_rho_eq_global (w : NK.GlobalCFT.Place L)
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) w)
    (x : Additive ↥(NK.GlobalCFT.Place.localUnits L w)) :
    (Rep.ofDistribMulAction ℤ (MulAction.stabilizer (L ≃ₐ[K] L) w)
        (Additive ↥(NK.GlobalCFT.Place.localUnits L w))).ρ σ x =
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L) w).ρ
        (⟨σ.1, σ.2⟩ : NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w) x := by
  rw [Rep.ofDistribMulAction_ρ_apply_apply, NK.GlobalCFTdeep.localUnitSubRep_ρ_apply]
  exact Subtype.ext (hasse_smul_coe_eq (K := K) (L := L) w σ (Additive.toMul x))

/-! ## The bridge from the `GlobalCFTdeep` representation to the `HassePrinciple` one -/

/-- **Vanishing of `H²` of the local units transfers from the `NK.GlobalCFTdeep`
representation to the `NK.HassePrinciple` one.**  Both representations have the same underlying
module `↥(Place.localUnits L w)`, the same (equivalent) group, and the same action on underlying
elements; only the coefficient ring and the formal instance of the action differ. -/
theorem subsingleton_hasse_of_subsingleton_global (w : NK.GlobalCFT.Place L)
    (h : Subsingleton (groupCohomology
      (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L) w) 2)) :
    Subsingleton (groupCohomology
      (NK.HassePrinciple.localUnitsSubRep (K := K) (L := L) w) 2) := by
  let M1 : Rep ℤ (MulAction.stabilizer (L ≃ₐ[K] L) w) :=
    Rep.ofDistribMulAction ℤ (MulAction.stabilizer (L ≃ₐ[K] L) w)
      (Additive ↥(NK.GlobalCFT.Place.localUnits L w))
  let M2 : Rep ℤ (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w) :=
    NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L) w
  let ψ : MulAction.stabilizer (L ≃ₐ[K] L) w ≃*
      NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w := MulEquiv.refl _
  have hρ : ∀ g : MulAction.stabilizer (L ≃ₐ[K] L) w, M1.ρ g = M2.ρ (ψ g) := by
    intro g
    have hg : (ψ g : NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w)
        = ⟨g.1, g.2⟩ := rfl
    rw [hg]
    ext x
    exact hasse_rho_eq_global (K := K) (L := L) w g x
  have hrep : M1 = Rep.res ψ.toMonoidHom M2 := by
    change Rep.of (Representation.ofDistribMulAction ℤ (MulAction.stabilizer (L ≃ₐ[K] L) w)
      (Additive ↥(NK.GlobalCFT.Place.localUnits L w))) = Rep.res ψ.toMonoidHom M2
    rw [show Rep.res ψ.toMonoidHom M2 = Rep.of (M2.ρ.comp ψ.toMonoidHom) from rfl]
    refine congrArg Rep.of ?_
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro x
    exact DFunLike.congr_fun (hρ g) x
  haveI hsub : Subsingleton (groupCohomology M2 2) := h
  have hM1 : Subsingleton (groupCohomology M1 2) := by
    have hiso : groupCohomology M1 2 ≅ groupCohomology M2 2 := by
      rw [hrep]
      exact groupCohomology.mapIso (G := MulAction.stabilizer (L ≃ₐ[K] L) w)
        (H := NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) w) ψ
        (LinearEquiv.refl ℤ M2.V) (by intro g; rfl) 2
    exact ⟨fun a b => (Iso.toLinearEquiv hiso).injective
      (Subsingleton.elim ((Iso.toLinearEquiv hiso) a) ((Iso.toLinearEquiv hiso) b))⟩
  exact subsingleton_groupCohomology_two_coeffTransfer (k := ℤ)
    (k' := NK.HassePrinciple.CoeffInt) hM1

/-! ## Vanishing of `H²` for the `GlobalCFTdeep` representation -/

/-- `H²` of the local units at an unramified finite place vanishes, in the
`NK.GlobalCFTdeep` vocabulary: the decomposition group is cyclic (the local extension is
unramified), so `H² = Ĥ⁰` by periodicity, and `Ĥ⁰` is trivial because every invariant unit is a
norm. -/
theorem subsingleton_globalLocalUnitSubRep_of_ramificationIdx_eq_one
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    Subsingleton (groupCohomology (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) 2) := by
  let Q := lieUnder (K := K) q
  have hq : q.asIdeal.LiesOver Q.asIdeal := lieUnder_liesOver (K := K) q
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hmod : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : Fintype (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    AlgEquiv.fintype (Q.adicCompletion K) (q.adicCompletion L)
  haveI hfin : Fintype (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) :=
    Fintype.ofEquiv (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois Q q hq).symm.toEquiv
  have hloc_cyc : IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
      Q q hq hunr
  haveI hcyc : IsCyclic (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) :=
    (MulEquiv.isCyclic (NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois Q q hq)).mpr hloc_cyc
  have h0 : NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) = 1 :=
    NK.GlobalCFTdeep.Herbrand.hZero_localUnitSubRep_eq_one_of_ramificationIdx_eq_one Q q hq hunr
  letI : CommGroup (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q))
  have hper :=
    Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
      g hg (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
        (NK.GlobalCFT.Place.ofFinite q))
  have hcard : Nat.card (groupCohomology (NK.GlobalCFTdeep.localUnitSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) 2) = 1 := by
    rw [hper, ← NK.GlobalCFTdeep.hZero_def]
    exact h0
  exact (Nat.card_eq_one_iff_unique.mp hcard).1

/-! ## The requested lemma -/

theorem localUnitsSubRep_subsingleton_unramified {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    Subsingleton (groupCohomology (NK.HassePrinciple.localUnitsSubRep (K := K) (L := L)
      (NK.GlobalCFT.Place.ofFinite q)) 2) :=
  subsingleton_hasse_of_subsingleton_global (K := K) (L := L) (NK.GlobalCFT.Place.ofFinite q)
    (subsingleton_globalLocalUnitSubRep_of_ramificationIdx_eq_one (K := K) (L := L) q hunr)

end NK.NUV2.LC
