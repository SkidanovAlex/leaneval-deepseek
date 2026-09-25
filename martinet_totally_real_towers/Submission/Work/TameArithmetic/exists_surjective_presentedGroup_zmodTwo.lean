import Mathlib
import Submission.Work.TameArithmetic.Defs
import Submission.Commons.NumberTheory.NumberField.exists_multiquadratic_totallyReal_unramifiedOutside
import Submission.Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card

/-!
# The maximal tame pro-`2` extension of `ℚ` has `(ℤ/2)^5` as a quotient

`Work.TameArithmetic.exists_surjective_presentedGroup_zmodTwo`: for a maximal tame pro-`2` extension
`K` of `ℚ` (for `S = {17, 41, 73, 89, 97}`, `Work.TameArithmetic.IsMaximalTamePro2 K`) and any
pro-`2` presentation `P` of `Γ = Gal(K/ℚ)` with five generators, the abstract group
`presentedGroup P = FreeGroup (Fin 5) ⧸ ⟪rel⟫` presented by `P` admits a surjection onto
`(ℤ/2)^5`, written as `Fin 5 → Multiplicative (ZMod 2)`.

The mathematics:

* the multiquadratic field `M = ℚ(√17, √41, √73, √89, √97)` is a finite Galois, totally real,
  pro-`2` extension of `ℚ` whose different is supported over `S`
  (`Commons.NumberTheory.NumberField.exists_multiquadratic_totallyReal_unramifiedOutside`), so by
  the universal property of `K` it embeds into `K`, with `Gal(M/ℚ) ≅ (ℤ/2)^5`;
* writing `L` for the image of `M` in `K`, restriction of automorphisms gives a homomorphism
  `Γ → Gal(L/ℚ) ≅ (ℤ/2)^5`, which is continuous for the Krull topology and surjective;
* the image of the presentation map `FreeGroup (Fin 5) → Γ` is `H = closure (range gen)`, a dense
  subgroup of `Γ` (`P.dense`), and the closure of a dense subgroup maps onto every finite quotient
  of `Γ` (`DenseRange.topologicalClosure_map_subgroup`, the target being discrete because `L/ℚ` is
  finite). Hence the composite `presentedGroup P ≅ H → Gal(L/ℚ)` is surjective.
-/

namespace Work.TameArithmetic

open scoped Classical

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The `n`-fold product of copies of `ZMod 2`, written multiplicatively on the outside
(`Multiplicative (Fin n → ZMod 2)`) resp. pointwise (`Fin n → Multiplicative (ZMod 2)`): the two
are the same functions with the same pointwise multiplication. -/
def piZModTwoMulEquiv (n : ℕ) :
    Multiplicative (Fin n → ZMod 2) ≃* (Fin n → Multiplicative (ZMod 2)) where
  toFun x := fun i => Multiplicative.ofAdd (x.toAdd i)
  invFun y := Multiplicative.ofAdd (fun i => (y i).toAdd)
  left_inv x := by ext i; simp
  right_inv y := by ext i; simp
  map_mul' x y := by ext i; simp

/-- Every element of `Multiplicative (Fin n → ZMod 2)` is an involution. -/
lemma zModTwo_pi_sq (n : ℕ) (y : Multiplicative (Fin n → ZMod 2)) : y ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_pow, toAdd_one, two_nsmul]
  funext i
  exact CharTwo.add_self_eq_zero (y.toAdd i)

/-- `Multiplicative (Fin n → ZMod 2)` is commutative. -/
lemma zModTwo_pi_comm (n : ℕ) (a b : Multiplicative (Fin n → ZMod 2)) : a * b = b * a := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, add_comm]

theorem exists_surjective_presentedGroup_zmodTwo {K : Type} [Field K] [Algebra ℚ K] [IsGalois ℚ K]
    (hmax : Work.TameArithmetic.IsMaximalTamePro2 K)
    (P : Work.TameArithmetic.TamePro2Presentation K) :
    ∃ f : Work.TameArithmetic.presentedGroup P →* (Fin 5 → Multiplicative (ZMod 2)),
      Function.Surjective f := by
  classical
  obtain ⟨_, huniv, _⟩ := hmax
  -- 1. the multiquadratic field `M = ℚ(√17, √41, √73, √89, √97)` and its embedding into `K`
  obtain ⟨M, iF, iNF, iTR, iG, hfr, ⟨eM⟩, hsupp⟩ :=
    Commons.NumberTheory.NumberField.exists_multiquadratic_totallyReal_unramifiedOutside
      primesS primesS_prime primesS_mod_eight
  letI : Field M := iF
  letI : NumberField M := iNF
  letI : IsGalois ℚ M := iG
  haveI : NumberField.IsTotallyReal M := iTR
  -- `M/ℚ` is a pro-`2`, `S`-tame, infinite-place-unramified extension of `ℚ`
  have hpg : IsPGroup 2 (M ≃ₐ[ℚ] M) := by
    refine IsPGroup.of_card (n := 5) ?_
    rw [Nat.card_congr eM.toEquiv, primesS_card]
    norm_num
  have hunr : IsUnramifiedAtInfinitePlaces ℚ M := by
    refine ⟨fun w => ?_⟩
    rw [NumberField.InfinitePlace.IsUnramified]
    exact (NumberField.IsTotallyReal.mult_eq _).trans (NumberField.IsTotallyReal.mult_eq w).symm
  obtain ⟨φ, -⟩ := huniv M hpg hsupp hunr
  -- 2. the image `L` of `M` in `K`, as an intermediate field
  let L : IntermediateField ℚ K := φ.fieldRange
  letI : Algebra ℚ ↥L := L.algebra'
  haveI : FiniteDimensional ℚ ↥L := Module.Finite.equiv (AlgHom.equivFieldRange φ).toLinearEquiv
  have hgalL : IsGalois ℚ ↥L := IsGalois.of_algEquiv (AlgHom.equivFieldRange φ)
  haveI : Normal ℚ ↥L := hgalL.to_normal
  haveI : DiscreteTopology Gal(↥L/ℚ) := krullTopology_discreteTopology_of_finiteDimensional ℚ ↥L
  -- 3. `Gal(L/ℚ) ≃ (Fin 5 → Multiplicative (ZMod 2))`
  have eTot : Gal(↥L/ℚ) ≃* Multiplicative (Fin primesS.card → ZMod 2) :=
    (AlgEquiv.autCongr (AlgHom.equivFieldRange φ)).symm.trans eM
  haveI : IsMulCommutative Gal(↥L/ℚ) :=
    IsMulCommutative.of_comm fun a b => eTot.injective (by
      rw [map_mul, map_mul]
      exact zModTwo_pi_comm _ _ _)
  have hsqL : ∀ x : Gal(↥L/ℚ), x ^ 2 = 1 := fun x =>
    eTot.injective (by rw [map_pow, map_one]; exact zModTwo_pi_sq _ (eTot x))
  have hcardL : Nat.card Gal(↥L/ℚ) = 2 ^ 5 := by
    rw [Nat.card_congr eTot.toEquiv, primesS_card]
    simp
  obtain ⟨eL⟩ :=
    Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
      (k := 5) hsqL hcardL
  have efin : Gal(↥L/ℚ) ≃* (Fin 5 → Multiplicative (ZMod 2)) := eL.trans (piZModTwoMulEquiv 5)
  -- 4. the dense finitely generated subgroup `H = closure (range gen) ≤ Γ` surjects onto the
  -- finite quotient `Gal(L/ℚ)`
  let fL : Gal(K/ℚ) →* Gal(↥L/ℚ) := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := K) ↥L
  have hdenseRange : ((FreeGroup.lift P.gen).range).topologicalClosure = ⊤ := by
    rw [FreeGroup.range_lift_eq_closure]
    exact P.dense
  have hmapTop : Subgroup.map fL (FreeGroup.lift P.gen).range = ⊤ := by
    have h := DenseRange.topologicalClosure_map_subgroup
      (InfiniteGalois.restrictNormalHom_continuous L)
      (AlgEquiv.restrictNormalHom_surjective K).denseRange hdenseRange
    have hle : (Subgroup.map fL (FreeGroup.lift P.gen).range).topologicalClosure
        ≤ Subgroup.map fL (FreeGroup.lift P.gen).range :=
      Subgroup.topologicalClosure_minimal _ le_rfl (isClosed_discrete _)
    rw [h] at hle
    exact le_antisymm le_top hle
  -- 5. the surjection out of the presented group
  let F' : FreeGroup (Fin 5) →* Gal(↥L/ℚ) := fL.comp (FreeGroup.lift P.gen)
  have hF'range : F'.range = ⊤ := by
    rw [MonoidHom.range_comp]
    exact hmapTop
  have hker : Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin 5))) ≤ MonoidHom.ker F' := by
    rw [← P.ker_eq]
    intro x hx
    simp only [MonoidHom.mem_ker] at hx ⊢
    show fL ((FreeGroup.lift P.gen) x) = 1
    rw [hx, map_one]
  let lift : presentedGroup P →* Gal(↥L/ℚ) :=
    QuotientGroup.lift (Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin 5)))) F' hker
  have hsurjLift : Function.Surjective lift := by
    intro y
    have hy : y ∈ F'.range := by rw [hF'range]; trivial
    obtain ⟨x, rfl⟩ := hy
    exact ⟨QuotientGroup.mk x, QuotientGroup.lift_mk _ hker x⟩
  exact ⟨(efin : Gal(↥L/ℚ) →* (Fin 5 → Multiplicative (ZMod 2))).comp lift,
    efin.surjective.comp hsurjLift⟩

end Work.TameArithmetic
