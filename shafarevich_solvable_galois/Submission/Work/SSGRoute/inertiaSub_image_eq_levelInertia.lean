import Mathlib
import Submission.Work.SSGRoute.H2locAux.Defs
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.levelInertia_defs
import Submission.Work.SSGRoute.primeOfLevel_mem_iff_k
import Submission.Work.SSGRoute.ringOfIntegers_mem_of_isFinPlace_k
import Submission.Work.SSGRoute.valuation_sub_lt_one_of_isTrivialAtLevel
import Submission.NK.ResidueFrob.exists_inertia_of_isTrivialOnResidueAtLevel
import Submission.NK.ResidueFrob.exists_mem_decompositionGroup_restrictNormalHom_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped Pointwise NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## Helper lemmas -/

/-- **Membership in the level inertia is equivalent to triviality on the level residue field.**
(Stated privately here to keep this module independent of the modules that state it publicly.) -/
private theorem mem_inertia_levelPrime_iff_isTrivialAtLevel'
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (B : ValuationSubring Ω) (hB : B.comap (algebraMap k Ω) ≠ ⊤)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] [NumberField ↥L]
    (g : Ω ≃ₐ[k] Ω) :
    AlgEquiv.restrictNormalHom L g ∈
        Ideal.inertia (↥L ≃ₐ[k] ↥L) (levelPrime k Ω B hB L).asIdeal ↔
      IsTrivialAtLevel k Ω B hB L g := by
  rw [IsTrivialAtLevel, NK.FrobeniusBridge.IsTrivialOnResidueAtLevel, AddSubgroup.mem_inertia]
  refine forall_congr' fun x => ?_
  have hsmul : (AlgEquiv.restrictNormalHom L g) • x =
      galRestrict (NumberField.RingOfIntegers k) k ↥L (NumberField.RingOfIntegers ↥L)
        (AlgEquiv.restrictNormalHom L g) x := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [algebraMap_galRestrict_apply, algebraMap.smul']
    rfl
  rw [hsmul]
  exact Iff.rfl

/-- **All finite levels together exhaust `A`.**  If `σ` acts trivially on the maximal ideal of
`A` at the elements of every finite normal level, then it acts trivially on the whole maximal
ideal of `A`. -/
private theorem val_sub_lt_one_of_all_levels
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω)
    (h : ∀ (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] [NumberField ↥L],
      ∀ y : Ω, y ∈ L → y ∈ A → A.valuation (σ y - y) < 1)
    {x : Ω} (hx : x ∈ A) : A.valuation (σ x - x) < 1 := by
  have hxint : IsIntegral k x := IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic x)
  haveI : Normal k Ω := inferInstance
  let L₀ : IntermediateField k Ω := IntermediateField.adjoin k {x}
  haveI : Nonempty (L₀ →ₐ[k] Ω) := ⟨L₀.val⟩
  haveI hL₀ : FiniteDimensional k L₀ := IntermediateField.adjoin.finiteDimensional hxint
  let L : IntermediateField k Ω := IntermediateField.normalClosure k L₀ Ω
  haveI hLfin : FiniteDimensional k L := normalClosure.is_finiteDimensional k L₀ Ω
  haveI hLnorm : Normal k L := inferInstance
  haveI hLnf : NumberField ↥L :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L
  have hxL : x ∈ L :=
    IntermediateField.le_normalClosure L₀
      (IntermediateField.subset_adjoin k ({x} : Set Ω) (Set.mem_singleton x))
  exact h L x hxL hx

/-- **An inertia element of the place `A` acts trivially modulo the prime on every finite
level.** -/
private theorem isTrivialAtLevel_of_isInertia
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M]
    (σ : Ω ≃ₐ[k] Ω) (hσ : SSGRoute.IsInertia k A σ) :
    IsTrivialAtLevel k Ω A hA M σ := by
  haveI hSep : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  obtain ⟨hσD, hσv⟩ := hσ
  intro x
  rw [primeOfLevel_mem_iff_k k Ω A hA M]
  have hyA : ((x : ↥M) : Ω) ∈ A :=
    ringOfIntegers_mem_of_isFinPlace_k k Ω A hA M x
  have hval : A.valuation (σ ((x : ↥M) : Ω) - ((x : ↥M) : Ω)) < 1 := hσv _ hyA
  have hmap : algebraMap (𝓞 ↥M) Ω
      (galRestrict (𝓞 k) k ↥M (𝓞 ↥M) (AlgEquiv.restrictNormalHom M σ) x - x)
      = σ ((x : ↥M) : Ω) - ((x : ↥M) : Ω) := by
    have h1 : algebraMap (𝓞 ↥M) Ω
        (galRestrict (𝓞 k) k ↥M (𝓞 ↥M) (AlgEquiv.restrictNormalHom M σ) x)
        = σ ((x : ↥M) : Ω) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 ↥M) ↥M Ω,
        algebraMap_galRestrict_apply (A := 𝓞 k) (K := k) (L := ↥M) (B := 𝓞 ↥M)
          (AlgEquiv.restrictNormalHom M σ) x]
      exact AlgEquiv.restrictNormalHom_apply M σ x
    have h2 : algebraMap (𝓞 ↥M) Ω x = ((x : ↥M) : Ω) := rfl
    rw [map_sub, h1, h2]
  rw [hmap]
  exact hval

/-- **The image of the place inertia in a finite level is the level inertia.**

`k` a number field, `Ω` an algebraic closure, `A` a finite place of `Ω` over `k`, `M/k` a finite
normal level.  Then the image of the inertia subgroup `Work.SSGRoute.inertiaSub k Ω A ≤ G_k`
under the restriction `AlgEquiv.restrictNormalHom M : G_k →* Gal(M/k)` is exactly the level
inertia `Work.SSGRoute.levelInertiaOf k Ω A hA M`, i.e. the inertia subgroup of `Gal(M/k)` at the
prime of `𝓞 M` below `A`.

* `⊆`: an inertia element of `A` acts trivially modulo `𝔪_A`, hence its restriction acts
  trivially modulo `P` on `𝓞 M` (compare `B.valuation` on `Ω` with the `P`-adic valuation on
  `↥M`; `NK.Reconstruct.primeOfLevel_spec` identifies `A.comap (algebraMap ↥M Ω)` with
  `valuationSubringAtPrime ↥M P`, and `Work.SSGRoute.valuation_sub_lt_one_of_isTrivialAtLevel`
  transfers the condition the other way).  One needs `𝓞 M ⊆ A ∩ M`
  (`Work.SSGRoute.ringOfIntegers_mem_of_isFinPlace_k`).
* `⊇`: the surjectivity of "place inertia ↠ level inertia": if `g ∈ D_A` acts trivially on the
  residue field of the level `M`, then `g` agrees on `M` with an inertia element of `A`.  This is
  `NK.ResidueFrob.exists_inertia_of_isTrivialOnResidueAtLevel` (arbitrary number field and
  separable closure), which produces `δ ∈ D_A` fixing `M` pointwise with `δ * g` acting trivially
  at every finite level, hence `δ * g ∈ I_A`; one must first lift `τ ∈ Ideal.inertia` to some
  `g ∈ D_A` with `g|_M = τ`
  (`Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq`, as used in
  `Submission/Work/SSGRoute/decomp_mod_inertia_cyclic.lean`), and use
  `Work.SSGRoute.mem_levelSub_iff` / `valuation_sub_lt_one_of_all_levels`.

Useful on disk: `Work.SSGRoute.mem_levelSub_iff`, `Work.SSGRoute.levelSub_eq_preimage`,
`NK.ResidueFrob.exists_inertia_of_isTrivialOnResidueAtLevel`,
`Submission/Work/SSGRoute/decomp_mod_inertia_cyclic.lean` (same surjectivity, for the decomposition
group), `Submission/Work/SSGRoute/levelSub_commutator_and_generator.lean` (private lemmas
`mem_inertia_iff_isTrivialAtLevel`, `map_restrictNormalHom_decomp_eq_stabilizer`). -/
theorem inertiaSub_image_eq_levelInertia
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    (Work.SSGRoute.inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom M) =
      Work.SSGRoute.levelInertiaOf k Ω A hA M := by
  classical
  haveI hSep : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  have hRHS : Work.SSGRoute.levelInertiaOf k Ω A hA M =
      Ideal.inertia (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal := rfl
  apply le_antisymm
  · rintro τ hτ
    obtain ⟨σ, hσ, hστ⟩ := Subgroup.mem_map.mp hτ
    rw [← hστ, hRHS]
    exact (mem_inertia_levelPrime_iff_isTrivialAtLevel' k Ω A hA M σ).mpr
      (isTrivialAtLevel_of_isInertia k Ω A hA M σ
        ((Work.SSGRoute.mem_inertiaSub k Ω A σ).mp hσ))
  · intro τ hτ
    rw [hRHS] at hτ
    -- lift `τ` to `G_k`
    obtain ⟨g, hgτ⟩ : ∃ g : Ω ≃ₐ[k] Ω, AlgEquiv.restrictNormalHom M g = τ :=
      ⟨τ.liftNormal Ω, by
        rw [show AlgEquiv.restrictNormalHom M (τ.liftNormal Ω) =
          (τ.liftNormal Ω).restrictNormal ↥M from rfl]
        exact AlgEquiv.restrict_liftNormal (K₁ := ↥M) (E := Ω) τ⟩
    have hgmem : AlgEquiv.restrictNormalHom M g ∈
        Ideal.inertia (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal := by
      rw [hgτ]; exact hτ
    have htrivg : IsTrivialAtLevel k Ω A hA M g :=
      (mem_inertia_levelPrime_iff_isTrivialAtLevel' k Ω A hA M g).mp hgmem
    -- pass to an element of `D_A` with the same restriction
    obtain ⟨h, hh, hhres⟩ :=
      NK.ResidueFrob.exists_mem_decompositionGroup_restrictNormalHom_eq ⟨A, hA⟩ M htrivg
    have htrivh : IsTrivialAtLevel k Ω A hA M h := by
      unfold Work.SSGRoute.IsTrivialAtLevel NK.FrobeniusBridge.IsTrivialOnResidueAtLevel
        at htrivg ⊢
      intro x
      have h2 := htrivg x
      rw [← hhres] at h2
      exact h2
    -- correct `h` by an element fixing `M` pointwise
    obtain ⟨δ, hδ, hδ1, hδtriv⟩ :=
      NK.ResidueFrob.exists_inertia_of_isTrivialOnResidueAtLevel ⟨A, hA⟩ M h hh htrivh
    have hδh : δ * h ∈ SSGRoute.decomp k A := Subgroup.mul_mem _ hδ hh
    have hval : ∀ y : Ω, y ∈ A → A.valuation ((δ * h) y - y) < 1 := by
      intro y hy
      refine val_sub_lt_one_of_all_levels k Ω A (δ * h) ?_ hy
      intro N hN1 hN2 hN3 y' hyN hyA
      exact valuation_sub_lt_one_of_isTrivialAtLevel A hA N (δ * h) hδh
        (hδtriv N) hyN hyA
    have hmem : δ * h ∈ inertiaSub k Ω A :=
      (Work.SSGRoute.mem_inertiaSub k Ω A (δ * h)).mpr ⟨hδh, hval⟩
    refine Subgroup.mem_map.mpr ⟨δ * h, hmem, ?_⟩
    rw [map_mul, hδ1, one_mul, hhres, hgτ]

end Work.SSGRoute
