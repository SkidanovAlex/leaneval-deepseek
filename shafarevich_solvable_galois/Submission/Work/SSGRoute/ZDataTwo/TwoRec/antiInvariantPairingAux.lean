import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.antiInvariantDichotomy
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup_right
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.killsInertia_of_unit_notTwo
import Submission.Work.SSGRoute.ZConstruction.exists_finset_covering_notUnit
import Submission.Work.SSGRoute.ZConstruction.LevelKHilbert
import Submission.Work.SSGRoute.ZConstruction.DichotomyKills
import Submission.Work.SSGRoute.ZConstruction.HCharMulSq
import Submission.Work.SSGRoute.PinnedTwin.oPairAtPairEqZero
import Submission.Work.SSGRoute.NodeS37.coprimeOfPrimeRepresentative
import Submission.Work.SSGRoute.ZConstruction.OThetaLocalNorm
import Submission.Work.SSGRoute.NodeS35.kills_inertia_conjUnit
import Submission.Work.SSGRoute.H9.oPairAt_swapTwo
import Submission.Work.SSGRoute.NodeS37.oPairAt_smul_conj
import Submission.Work.SSGRoute.P2Nat.oPairAt_smul_conj
import Submission.Work.SSGRoute.ZDataTwo.isLocalNorm_of_kills_inertia
import Submission.Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero
import Submission.Work.SSGRoute.H9.swCount_conjUnit
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.PlaceValBridge
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.exists_coprime_representative_two
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.killsLocalGroup_of_one_unit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary lemmas for the anti-invariant p. 16 computation

This file collects the *sorry-free* helper library that the p. 16 diagonal computation
(`TwoRec.pinnedValue_diagonal_proved`) and its satellite lemmas use:

* orbit cancellation of an involution in `ZMod 2` (`sum_involution_zmodTwo`);
* the invariance of `oPairGlob` under replacing a place by a `K`-conjugate one
  (`oPairGlob_eq_of_gesKConj`), i.e. its dependence only on the prime of `↥K` below the place;
* the insensitivity of `oPairAt` to multiplying either argument by a class whose Kummer cochain
  kills the local group (`oPairAt_mul_left/right_of_killsLocalGroup`);
* `conjUnit` of a chosen lift as `Units.map` of the automorphism;
* the trivial pairing of two units at a place where `2` is a unit
  (`oPairGlob_eq_zero_of_units`);
* elementary bookkeeping for the sibling place and for the prime `placeSmul ρ 𝔭`.

Nothing here uses `sorry`, and nothing depends on the (still open) main theorem.
-/

open scoped Pointwise NumberField

namespace Work.SSGRoute.ZDataTwo.TwoRec

open _root_.SSGRoute

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-! ## Orbit sums in `ZMod 2` -/

/-- **Sum over the orbits of an involution, in `ZMod 2`.**  If `σ` is an involution of the finite set
`F` and `g` is constant on the two-element orbits, the sum of `g` over `F` is the sum over the
`σ`-fixed points. -/
theorem sum_involution_zmodTwo {α : Type*} [DecidableEq α] (σ : α → α) (F : Finset α)
    (g : α → ZMod 2)
    (hσ : ∀ x ∈ F, σ (σ x) = x) (hF : ∀ x ∈ F, σ x ∈ F)
    (hg : ∀ x ∈ F, σ x ≠ x → g (σ x) = g x) :
    F.sum g = (F.filter (fun x => σ x = x)).sum g := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun x => σ x = x) g
  have hN : (F.filter (fun x => ¬ (σ x = x))).sum g = 0 := by
    refine Finset.sum_involution (s := F.filter (fun x => ¬ (σ x = x))) (f := g)
      (fun x _ => σ x) ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨haF, haN⟩ := Finset.mem_filter.mp ha
      rw [hg a haF (fun h => haN h)]
      rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
    · intro a ha _
      exact (Finset.mem_filter.mp ha).2
    · intro a ha
      obtain ⟨haF, haN⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨hF a haF, fun h => haN (h.symm.trans (hσ a haF))⟩
    · intro a ha
      exact hσ a (Finset.mem_filter.mp ha).1
  rw [hN, add_zero] at hsplit
  exact hsplit.symm

/-! ## `oPairGlob` depends only on the prime below the place -/

/-- **The local pairing depends only on the prime of `↥K` below the place.**  Two `K`-conjugate
finite places give the same value of `oPairGlob`. -/
theorem oPairGlob_eq_of_gesKConj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (α β : (↥K)ˣ)
    (A B : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hB : SSGRoute.IsFinPlace k B)
    (h : Work.SSGRoute.gesKConj K A B) :
    Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA α β
      = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hB α β := by
  have hcomap : A.comap (algebraMap ↥K Ω) = B.comap (algebraMap ↥K Ω) :=
    Work.SSGRoute.ZConstruction.comap_eq_of_gesKConj (K := K) h
  have hp : Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) A hA
      = Work.SSGRoute.ZDataMup.LTRecFamHonest.hPrimeBelow (K := K) B hB := by
    apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
    rw [← Submission.NeukirchUchida.primeOf_spec (K₁ := ↥K) (K₁' := Ω) A
        (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA),
      ← Submission.NeukirchUchida.primeOf_spec (K₁ := ↥K) (K₁' := Ω) B
        (Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := B) hB), hcomap]
  by_cases hα : α ∈ NK.LocalAnabelian.powSubgroup 2 ↥K
  · rw [Work.SSGRoute.H9.oPairGlob_eq_zero_of_mem_powSubgroup_fst (K := K) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α β A hA hα,
      Work.SSGRoute.H9.oPairGlob_eq_zero_of_mem_powSubgroup_fst (K := K) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α β B hB hα]
  · rw [Work.SSGRoute.ZConstruction.oPairGlob_eq_finPair (K := K) (k := k) (Ω := Ω) ζ hζ hζK A hA α β hα,
      Work.SSGRoute.ZConstruction.oPairGlob_eq_finPair (K := K) (k := k) (Ω := Ω) ζ hζ hζK B hB α β hα,
      hp]

/-- The two `oPairAt`/`oPairGlob` encodings agree. -/
theorem oPairAt_eq_oPairGlob_two {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (α β : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA α β :=
  Work.SSGRoute.P2Nat.oPairAt_eq_oPairGlob_aux (K := K) ζ hζ hζK α β A hA

/-! ## Insensitivity of `oPairAt` to locally trivial factors -/

/-- **Insensitivity of the local pairing to a locally trivial factor in its first argument.** -/
theorem oPairAt_mul_left_of_killsLocalGroup {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (u a β : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hkill : ∀ v ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ u v = 0) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (u * a))
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) := by
  classical
  have hcoc : ∀ c : (↥K)ˣ,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ c ∈ Work.SSGRoute.lcCocycles 2 k Ω K
        (ZMod 2) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
    intro c
    exact ⟨Work.SSGRoute.isCocycleOn_mono (SSGRoute.res k K) inf_le_right
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ c),
      Work.SSGRoute.isLocConstOn_mono inf_le_right
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ c)⟩
  have h0 : Work.SSGRoute.toClass 2 k Ω K (ZMod 2) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ u) = 0 :=
    Work.SSGRoute.ZConstruction.toClass_eq_zero_of_eq_zero_on (A := A) _
      (fun v hv => hkill v hv)
  unfold Work.SSGRoute.ZDataMup.OddForm.oPairAt
  congr 1
  rw [Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK u a,
    Work.SSGRoute.toClass_add 2 k Ω K (ZMod 2) _ (hcoc u) (hcoc a), h0, zero_add]

/-- **Insensitivity of the local pairing to a locally trivial factor in its second argument.** -/
theorem oPairAt_mul_right_of_killsLocalGroup {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (α u b : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hkill : ∀ v ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ u v = 0) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (u * b))
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b) := by
  classical
  have hcoc : ∀ c : (↥K)ˣ,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ c ∈ Work.SSGRoute.lcCocycles 2 k Ω K
        (ZMod 2) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
    intro c
    exact ⟨Work.SSGRoute.isCocycleOn_mono (SSGRoute.res k K) inf_le_right
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ c),
      Work.SSGRoute.isLocConstOn_mono inf_le_right
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ c)⟩
  have h0 : Work.SSGRoute.toClass 2 k Ω K (ZMod 2) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ u) = 0 :=
    Work.SSGRoute.ZConstruction.toClass_eq_zero_of_eq_zero_on (A := A) _
      (fun v hv => hkill v hv)
  unfold Work.SSGRoute.ZDataMup.OddForm.oPairAt
  congr 1
  rw [Work.SSGRoute.nodeKummerCocharZMod_mul K ζ hζ hζK u b,
    Work.SSGRoute.toClass_add 2 k Ω K (ZMod 2) _ (hcoc u) (hcoc b), h0, zero_add]

/-! ## The sibling place -/

/-- The `σ`-sibling of a finite place is a finite place. -/
theorem siblingPlace_isFinPlace {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] {Q : ValuationSubring Ω} (hQ : SSGRoute.IsFinPlace k Q)
    (σ : K ≃ₐ[k] K) :
    SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.siblingPlace K σ Q) :=
  (SSGRoute.isFinPlace_smul_iff Q (Work.SSGRoute.ZDataMup.galLift K σ)).mpr hQ

/-- The `↥K`-trace of the `galLift K σ`-translate of a place is the `σ`-translate of the trace. -/
theorem comap_galLift_smul_place {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) (Q : ValuationSubring Ω) :
    (Work.SSGRoute.ZDataMup.galLift K σ • Q).comap (algebraMap ↥K Ω)
      = σ • (Q.comap (algebraMap ↥K Ω)) := by
  ext x
  have hpt : (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ • (algebraMap ↥K Ω x)
      = algebraMap ↥K Ω (σ⁻¹ • x) := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def]
    rw [← Work.SSGRoute.algebraMap_restrictNormalHom (K := K)
      ((Work.SSGRoute.ZDataMup.galLift K σ)⁻¹) x]
    congr 1
    rw [map_inv, Work.SSGRoute.ZDataMup.galLift_spec]
  rw [ValuationSubring.mem_comap]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rw [ValuationSubring.mem_comap, hpt]

/-- The prime of `𝓞 ↥K` below the `galLift K σ`-translate of a place is the `σ`-translate of the
prime below it. -/
theorem oddPrime_galLift_smul_place {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (σ : K ≃ₐ[k] K) (Q : ValuationSubring Ω) (hQ : SSGRoute.IsFinPlace k Q)
    (hQ' : SSGRoute.IsFinPlace k (Work.SSGRoute.ZDataMup.galLift K σ • Q)) :
    Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
        (Work.SSGRoute.ZDataMup.galLift K σ • Q) hQ' =
      Commons.NumberTheory.NumberField.Completion.placeSmul σ
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQ) := by
  apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
  rw [← Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
        (K := k) (L := ↥K) (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQ)
        (Commons.NumberTheory.NumberField.Completion.placeSmul σ
          (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQ)) σ
        (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal σ
          (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) Q hQ))]
  rw [← Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := Q) hQ,
      ← Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K)
        (A := Work.SSGRoute.ZDataMup.galLift K σ • Q) hQ']
  exact comap_galLift_smul_place (K := K) σ Q

/-- `conjUnit` of a chosen lift is `Units.map` of the automorphism. -/
theorem conjUnit_galLift_eq_unitsMap {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) (b : (↥K)ˣ) :
    Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) b =
      Units.map σ.toRingEquiv.toMonoidHom b := by
  apply Units.ext
  rw [Work.SSGRoute.H9.conjUnit, Units.coe_map, Work.SSGRoute.ZDataMup.galLift_spec,
    Units.coe_map]
  rfl

/-- `conjUnit` of a chosen lift acts on the underlying element through the automorphism. -/
theorem conjUnit_galLift_apply {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    (σ : K ≃ₐ[k] K) (b : (↥K)ˣ) :
    (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K σ) b : ↥K) =
      σ (b : ↥K) := by
  rw [Work.SSGRoute.H9.conjUnit, Units.coe_map, Work.SSGRoute.ZDataMup.galLift_spec]
  rfl

/-! ## Two units pair trivially at an odd place -/

/-- **Two units at a place where `2` is a unit pair trivially.**  Both Kummer levels are unramified
at a non-dyadic prime, so both classes are unit classes, and units pair trivially.

(This is the private lemma `oPairGlob_units_eq_zero` of `TwoRec/antiInvariantDichotomy.lean`,
restated publicly for reuse.) -/
theorem oPairGlob_eq_zero_of_units {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (a u : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h2 : ¬ A.valuation (2 : Ω) < 1)
    (ha : A.valuation (algebraMap ↥K Ω (a : ↥K)) = 1)
    (hu : A.valuation (algebraMap ↥K Ω (u : ↥K)) = 1) :
    Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        hA a u = 0 := by
  classical
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  haveI : IsAlgClosure ↥K Ω := ⟨inferInstance, inferInstance⟩
  by_cases hsq : a ∈ NK.LocalAnabelian.powSubgroup 2 ↥K
  · exact Work.SSGRoute.H9.oPairGlob_eq_zero_of_mem_powSubgroup_fst (K := K) (k := k) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) hζ' a u A hA hsq
  · haveI hfdL : FiniteDimensional ↥K
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_finiteDimensional (Ω := Ω) (K := K) (p := 2)
        (⟨ζ, hζK⟩ : ↥K) hζ' a
    haveI hgalL : IsGalois ↥K
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isGalois (Ω := Ω) (K := K) (p := 2)
        (⟨ζ, hζK⟩ : ↥K) hζ' a
    haveI hnfL : NumberField
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) :=
      Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_numberField (Ω := Ω) (K := K) (p := 2)
        (⟨ζ, hζK⟩ : ↥K) hζ' a
    obtain ⟨hc, hy⟩ := Work.SSGRoute.H9.hLevel_quadratic_data (K := K) (Ω := Ω)
      (⟨ζ, hζK⟩ : ↥K) hζ' a hsq
    -- the Kummer character of the unit `a` kills the inertia of `A` over `↥K`
    have ha_inertia : ∀ σ : Ω ≃ₐ[↥K] Ω, SSGRoute.IsInertia ↥K A σ →
        Work.SSGRoute.kummerChar (K := ↥K) (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' a σ = 0 := by
      intro σ hσ
      rw [← Work.SSGRoute.ZDataTwo.kummerCharZMod_two_eq_kummerChar (k := k) (Ω := Ω) K
        (⟨ζ, hζK⟩ : ↥K) hζ' a σ]
      exact Work.SSGRoute.kummerCharZMod_eq_zero_of_isInertia_of_unit k Ω K 2
        (⟨ζ, hζK⟩ : ↥K) hζ' A h2 a ha σ hσ
    -- `u` is a unit at the prime of `↥K` below `A`
    have hprime_unit :
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).valuation ↥K (u : ↥K) = 1 := by
      have h1 : (A.comap (algebraMap ↥K Ω)).valuation (u : ↥K) = 1 :=
        (Work.SSGRoute.GrunwaldEscapeCore.comap_valuation_eq_one_iff A u).mp hu
      rw [Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hA] at h1
      exact (Work.SSGRoute.EscapeCoreLib.valuationSubringAtPrime_valuation_eq_one_iff
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) (u : ↥K)).mp h1
    -- the value of the completion image of `u` is a square in the value group (it is `1`)
    have hsqval : ∃ y : ((Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion
          ↥K)ˣ,
        Valued.v (R := (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion ↥K)
            (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap ↥K
              ((Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion ↥K) (u : ↥K))
          = (Valued.v (R := (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion
                ↥K) (Γ₀ := WithZero (Multiplicative ℤ)) (y : _)) ^ 2 := by
      refine ⟨1, ?_⟩
      rw [show Valued.v (R := (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion
              ↥K) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap ↥K
              ((Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).adicCompletion ↥K) (u : ↥K))
          = (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA).valuation ↥K (u : ↥K) from
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ (u : ↥K),
        hprime_unit]
      simp
    have hisnorm : NK.NUV2.LC.IsLocalNorm ↥K
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a) u
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)) :=
      Work.SSGRoute.ZDataTwo.isLocalNorm_of_kills_inertia_of_sq_val (k := ↥K) (Ω := Ω)
        A (Work.SSGRoute.ZDataMup.OddForm.oddFinPlace (K := K) hA)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hA)
        (⟨ζ, hζK⟩ : ↥K) hζ' a u
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a)
        hc hy ha_inertia hsqval
    refine (Work.SSGRoute.H9.oPairGlob_eq_zero_iff_mem_localNormSubgroup (K := K) (k := k)
      (Ω := Ω) (⟨ζ, hζK⟩ : ↥K) hζ' a u A hA hsq).mpr ?_
    exact (Work.HilbertSymbolGeneral.isLocalNorm_iff_localNormSubgroup (K := ↥K)
      (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) a)) u
      (NK.GlobalCFT.Place.ofFinite
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA))).mp hisnorm

/-! ## Counts, supports and places over a prime -/

/-- For a finite place `A` and the prime `𝔭` of `𝓞 ↥K` below it, a unit `y ∈ ↥K` is a unit at `A`
exactly when it is a unit at `𝔭` (i.e. has zero `𝔭`-adic count). -/
theorem valuation_ne_one_iff_count_ne_zero {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [NumberField ↥K]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) (y : (↥K)ˣ) :
    A.valuation (algebraMap ↥K Ω (y : ↥K)) ≠ 1 ↔
      FractionalIdeal.count ↥K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (y : ↥K)) ≠ 0 :=
  (Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero A 𝔭 h𝔭 y).not

/-- `spanSingleton` does not see the sign of its generator. -/
theorem spanSingleton_neg {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : K) :
    FractionalIdeal.spanSingleton (nonZeroDivisors R) (-x)
      = FractionalIdeal.spanSingleton (nonZeroDivisors R) x := by
  rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
  exact ⟨-1, by simp [Units.smul_def]⟩

/-- **The count of the `ρ`-conjugate unit at `𝔭` is the count of `y` at `ρ𝔭`.** -/
theorem count_conjUnit_eq_count_placeSmul {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (y : (↥K)ˣ)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    FractionalIdeal.count ↥K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (((Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) y : (↥K)ˣ) : ↥K)))
      = FractionalIdeal.count ↥K
          (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭)
          (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
            (y : ↥K)) := by
  have h := Work.SSGRoute.NodeS37.count_placeSmul_eq_count (L := ↥K) ρ y
    (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭)
  rw [placeSmul_placeSmul (K := ↥K) ρ hρ2 𝔭] at h
  rwa [← conjUnit_galLift_eq_unitsMap (K := K) ρ y] at h

/-- **The support of a `ρ`-invariant (or anti-invariant) class is `ρ`-stable.** -/
theorem count_ne_zero_iff_count_placeSmul_ne_zero {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (y : (↥K)ˣ)
    (hy : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) y = y
      ∨ Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) y = -y)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    FractionalIdeal.count ↥K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (y : ↥K)) ≠ 0 ↔
      FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (y : ↥K)) ≠ 0 := by
  have h := count_conjUnit_eq_count_placeSmul (K := K) ρ hρ2 y 𝔭
  rcases hy with hy | hy
  · rw [hy] at h
    exact Iff.of_eq (congrArg (fun z => z ≠ 0) h)
  · rw [hy] at h
    have hcoe : ((-y : (↥K)ˣ) : ↥K) = -((y : ↥K)) := rfl
    rw [hcoe, spanSingleton_neg] at h
    exact Iff.of_eq (congrArg (fun z => z ≠ 0) h)

/-- A place over a prime, and its defining property. -/
theorem exists_finPlace_over_prime {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
      A.comap (algebraMap ↥K Ω)
        = IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
  Work.SSGRoute.ZConstruction.exists_isFinPlace_comap_valuationSubringAtPrime 𝔭

/-! ## The `count`/valuation dictionary in the `< 1` and `≤ 1` forms -/

/-- **The `𝔭`-adic count of a unit is positive exactly when its `𝔭`-adic value is `< 1`.** -/
theorem count_pos_iff_valuation_lt_one {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (y : Kˣ) :
    0 < FractionalIdeal.count K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          (y : K)) ↔
      (IsDedekindDomain.HeightOneSpectrum.valuation K 𝔭) (y : K) < 1 := by
  rw [Work.SSGRoute.GrunwaldEscapeCore.val_eq_exp_neg_count (K := K) 𝔭 (Units.ne_zero y)]
  rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from rfl, WithZero.exp,
    WithZero.exp, WithZero.coe_lt_coe, Multiplicative.ofAdd_lt]
  omega

/-- **The `𝔭`-adic count of a unit is nonnegative exactly when its `𝔭`-adic value is `≤ 1`.** -/
theorem count_nonneg_iff_valuation_le_one {K : Type} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (y : Kˣ) :
    0 ≤ FractionalIdeal.count K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers K))
          (y : K)) ↔
      (IsDedekindDomain.HeightOneSpectrum.valuation K 𝔭) (y : K) ≤ 1 := by
  rw [Work.SSGRoute.GrunwaldEscapeCore.val_eq_exp_neg_count (K := K) 𝔭 (Units.ne_zero y)]
  rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (0 : ℤ) from rfl, WithZero.exp,
    WithZero.exp, WithZero.coe_le_coe, Multiplicative.ofAdd_le]
  omega

/-- **The place-level form of `count_pos_iff_valuation_lt_one`.** -/
theorem count_pos_iff_place_valuation_lt_one {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [NumberField ↥K]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) (y : (↥K)ˣ) :
    0 < FractionalIdeal.count ↥K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (y : ↥K)) ↔
      A.valuation (algebraMap ↥K Ω (y : ↥K)) < 1 :=
  (count_pos_iff_valuation_lt_one (K := ↥K) 𝔭 y).trans
    (place_valuation_lt_one_iff A 𝔭 h𝔭 (y : ↥K)).symm

/-- **The place-level form of `count_nonneg_iff_valuation_le_one`.** -/
theorem count_nonneg_iff_place_valuation_le_one {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [NumberField ↥K]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) (y : (↥K)ˣ) :
    0 ≤ FractionalIdeal.count ↥K 𝔭
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (y : ↥K)) ↔
      A.valuation (algebraMap ↥K Ω (y : ↥K)) ≤ 1 :=
  (count_nonneg_iff_valuation_le_one (K := ↥K) 𝔭 y).trans
    (place_valuation_le_one_iff A 𝔭 h𝔭 (y : ↥K)).symm

/-- **`2` is a unit at a place where it is not in the maximal ideal.** -/
theorem valuation_two_eq_one_of_not_lt_one {Ω : Type} [Field Ω] (A : ValuationSubring Ω)
    (h2 : ¬ A.valuation (2 : Ω) < 1) : A.valuation (2 : Ω) = 1 := by
  refine le_antisymm ?_ (not_lt.mp h2)
  rw [ValuationSubring.valuation_le_one_iff]
  have hh : (2 : Ω) = 1 + 1 := by norm_num
  rw [hh]
  exact A.add_mem 1 1 A.one_mem A.one_mem

/-! ## The local units at a prime where the anti-invariant switch is not a unit -/

/-- **At a place whose prime is neither `𝔮` nor `ρ𝔮`, where the anti-invariant switch
`X = z - ρz` is not a unit, both `z` and `ρz` are units and `X` lies in the maximal ideal.**

The hypotheses are exactly the divisor structure of `z = b·y²` (`z` integral, its support
disjoint from that of `ρz`) at the prime `𝔭` of `B`. -/
theorem localUnits_of_count_X_ne_zero {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (z X a : (↥K)ˣ)
    (hX : (X : ↥K) = (z : ↥K)
      - (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z : ↥K))
    (ha : (2 : ↥K) * (a : ↥K) = (z : ↥K)
      + (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z : ↥K))
    (hzint : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      0 ≤ FractionalIdeal.count ↥K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (z : ↥K)))
    (hcop : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      FractionalIdeal.count ↥K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (z : ↥K)) ≠ 0 →
      FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ P)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (z : ↥K)) = 0)
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (h2 : ¬ B.valuation (2 : Ω) < 1)
    (hXc : FractionalIdeal.count ↥K (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (X : ↥K)) ≠ 0) :
    B.valuation (algebraMap ↥K Ω (z : ↥K)) = 1 ∧
      B.valuation (algebraMap ↥K Ω
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z : ↥K)) = 1 ∧
      B.valuation (algebraMap ↥K Ω (a : ↥K)) = 1 ∧
      B.valuation (algebraMap ↥K Ω (X : ↥K)) < 1 := by
  classical
  set 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K) :=
    Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB with h𝔭def
  have h𝔭 : B.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
    Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) hB
  set rz : (↥K)ˣ := Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z with hrzdef
  -- integrality of the conjugate
  have hrzint : ∀ P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      0 ≤ FractionalIdeal.count ↥K P (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (rz : ↥K)) := by
    intro P
    rw [hrzdef, count_conjUnit_eq_count_placeSmul (K := K) ρ hρ2 z P]
    exact hzint _
  -- `X` is integral at `B`
  have hzle : B.valuation (algebraMap ↥K Ω (z : ↥K)) ≤ 1 :=
    (count_nonneg_iff_place_valuation_le_one B 𝔭 h𝔭 z).mp (hzint 𝔭)
  have hrzle : B.valuation (algebraMap ↥K Ω (rz : ↥K)) ≤ 1 :=
    (count_nonneg_iff_place_valuation_le_one B 𝔭 h𝔭 rz).mp (hrzint 𝔭)
  have hXle : B.valuation (algebraMap ↥K Ω (X : ↥K)) ≤ 1 := by
    have hsub : algebraMap ↥K Ω (X : ↥K)
        = algebraMap ↥K Ω (z : ↥K) - algebraMap ↥K Ω (rz : ↥K) := by
      rw [hX, map_sub]
    rw [hsub]
    exact le_trans (Valuation.map_sub _ _ _) (max_le hzle hrzle)
  have hXlt : B.valuation (algebraMap ↥K Ω (X : ↥K)) < 1 :=
    lt_of_le_of_ne hXle fun h1 =>
      hXc ((Work.SSGRoute.GrunwaldEscapeCore.valuation_eq_one_iff_count_eq_zero B 𝔭 h𝔭 X).mp h1)
  -- `z` is a unit
  have hzunit : B.valuation (algebraMap ↥K Ω (z : ↥K)) = 1 := by
    refine le_antisymm hzle (not_lt.mp ?_)
    intro hlt
    have hcz : FractionalIdeal.count ↥K 𝔭 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (z : ↥K)) ≠ 0 :=
      ne_of_gt ((count_pos_iff_place_valuation_lt_one B 𝔭 h𝔭 z).mpr hlt)
    have hrzlt : B.valuation (algebraMap ↥K Ω (rz : ↥K)) < 1 := by
      have hle : B.valuation (algebraMap ↥K Ω (rz : ↥K))
          ≤ max (B.valuation (algebraMap ↥K Ω (z : ↥K)))
              (B.valuation (algebraMap ↥K Ω (X : ↥K))) := by
        have hsub : algebraMap ↥K Ω (rz : ↥K)
            = algebraMap ↥K Ω (z : ↥K) - algebraMap ↥K Ω (X : ↥K) := by
          rw [← map_sub]
          congr 1
          rw [hX]; ring
        rw [hsub]
        exact Valuation.map_sub _ _ _
      exact lt_of_le_of_lt hle (max_lt hlt hXlt)
    have hcrz : FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (z : ↥K)) ≠ 0 := by
      rw [← count_conjUnit_eq_count_placeSmul (K := K) ρ hρ2 z 𝔭]
      rw [← hrzdef]
      exact ne_of_gt ((count_pos_iff_place_valuation_lt_one B 𝔭 h𝔭 rz).mpr hrzlt)
    exact hcrz (hcop 𝔭 hcz)
  -- `ρz` is a unit
  have hrzunit_all : B.valuation (algebraMap ↥K Ω (rz : ↥K)) = 1 := by
    refine le_antisymm hrzle (not_lt.mp ?_)
    intro hlt
    have hczlt : B.valuation (algebraMap ↥K Ω (z : ↥K)) < 1 := by
      have hle : B.valuation (algebraMap ↥K Ω (z : ↥K))
          ≤ max (B.valuation (algebraMap ↥K Ω (rz : ↥K)))
              (B.valuation (algebraMap ↥K Ω (X : ↥K))) := by
        have hsum : algebraMap ↥K Ω (z : ↥K)
            = algebraMap ↥K Ω (rz : ↥K) + algebraMap ↥K Ω (X : ↥K) := by
          rw [← map_add]
          congr 1
          rw [hX]; ring
        rw [hsum]
        exact Valuation.map_add _ _ _
      exact lt_of_le_of_lt hle (max_lt hlt hXlt)
    have hcz : FractionalIdeal.count ↥K 𝔭 (FractionalIdeal.spanSingleton
        (nonZeroDivisors (NumberField.RingOfIntegers ↥K)) (z : ↥K)) ≠ 0 :=
      ne_of_gt ((count_pos_iff_place_valuation_lt_one B 𝔭 h𝔭 z).mpr hczlt)
    have hcrz : FractionalIdeal.count ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭)
        (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
          (z : ↥K)) ≠ 0 := by
      rw [← count_conjUnit_eq_count_placeSmul (K := K) ρ hρ2 z 𝔭]
      rw [← hrzdef]
      exact ne_of_gt ((count_pos_iff_place_valuation_lt_one B 𝔭 h𝔭 rz).mpr hlt)
    exact hcrz (hcop 𝔭 hcz)
  -- `a` is a unit
  have h2val : B.valuation (2 : Ω) = 1 := valuation_two_eq_one_of_not_lt_one B h2
  have haval : B.valuation (algebraMap ↥K Ω (a : ↥K)) = 1 := by
    have hA2 : (2 : Ω) * algebraMap ↥K Ω (a : ↥K)
        = algebraMap ↥K Ω (z : ↥K) + algebraMap ↥K Ω (rz : ↥K) := by
      have h := congrArg (algebraMap ↥K Ω) ha
      rw [hrzdef] at h
      simpa only [map_mul, map_add, map_ofNat] using h
    refine le_antisymm ?_ (not_lt.mp ?_)
    · have h := Valuation.map_add (B.valuation) (algebraMap ↥K Ω (z : ↥K))
          (algebraMap ↥K Ω (rz : ↥K))
      rw [← hA2] at h
      rw [Valuation.map_mul, h2val, one_mul] at h
      exact le_trans h (max_le (le_of_eq hzunit) (le_of_eq hrzunit_all))
    · intro hlt
      have hsumlt : B.valuation (algebraMap ↥K Ω (z : ↥K) + algebraMap ↥K Ω (rz : ↥K)) < 1 := by
        rw [← hA2, Valuation.map_mul, h2val, one_mul]
        exact hlt
      have hsublt : B.valuation (algebraMap ↥K Ω (z : ↥K) - algebraMap ↥K Ω (rz : ↥K)) < 1 := by
        have hsub : algebraMap ↥K Ω (z : ↥K) - algebraMap ↥K Ω (rz : ↥K)
            = algebraMap ↥K Ω (X : ↥K) := by
          rw [← map_sub]
          congr 1
          rw [hX]
        rw [hsub]
        exact hXlt
      have h2zlt : B.valuation (algebraMap ↥K Ω ((2 : ↥K) * (z : ↥K))) < 1 := by
        have hsum2 : algebraMap ↥K Ω ((2 : ↥K) * (z : ↥K))
            = (algebraMap ↥K Ω (z : ↥K) + algebraMap ↥K Ω (rz : ↥K))
              + (algebraMap ↥K Ω (z : ↥K) - algebraMap ↥K Ω (rz : ↥K)) := by
          rw [map_mul, map_ofNat]
          ring
        rw [hsum2]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hsumlt hsublt)
      have h2z : B.valuation (algebraMap ↥K Ω ((2 : ↥K) * (z : ↥K))) = 1 := by
        rw [map_mul, map_ofNat, Valuation.map_mul, h2val, one_mul, hzunit]
      exact absurd h2z (ne_of_lt h2zlt)
  exact ⟨hzunit, hrzunit_all, haval, hXlt⟩

/-! ## Pairing bookkeeping at the sibling -/

/-- In `ZMod 2`, a sum vanishing forces equality of the two terms. -/
theorem zmod_two_eq_of_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  have hneg : (-1 : ZMod 2) = 1 := by decide
  have hx : x = -y := add_eq_zero_iff_eq_neg.mp h
  rw [hx, ← neg_one_mul, hneg, one_mul]

/-- **Symmetry of the local pairing of two Kummer cochains.** -/
theorem oPairAt_comm_aux {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (α β : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α) := by
  rw [oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK α β A hA,
    Work.SSGRoute.H9.oPairGlob_comm_two (K := K) (⟨ζ, hζK⟩ : ↥K)
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) α β A hA,
    ← oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK β α A hA]

/-- **The local pairing of two Kummer cochains only depends on the `K`-class of the place.** -/
theorem oPairAt_eq_of_gesKConj_place {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (α β : (↥K)ˣ)
    (A B : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hB : SSGRoute.IsFinPlace k B)
    (h : Work.SSGRoute.gesKConj K A B) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) B hB
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) := by
  rw [oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK α β A hA,
    oPairGlob_eq_of_gesKConj (K := K) (k := k) (Ω := Ω) ζ hζ hζK α β A B hA hB h,
    ← oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK α β B hB]

/-- **The reduction `χ_{ρz} ↔ χ_a` at a place where the switch `X = z - ρz` is a non-unit.** -/
theorem oPairAt_mul_left_rz_eq_mul_left_a {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1) (z rz X a : (↥K)ˣ)
    (hrz : rz = Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z)
    (hX : (X : ↥K) = (z : ↥K) - (rz : ↥K))
    (ha : (2 : ↥K) * (a : ↥K) = (z : ↥K) + (rz : ↥K))
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (h2 : ¬ B.valuation (2 : Ω) < 1)
    (hrzB : B.valuation (algebraMap ↥K Ω (rz : ↥K)) = 1)
    (haB : B.valuation (algebraMap ↥K Ω (a : ↥K)) = 1)
    (hXB : B.valuation (algebraMap ↥K Ω (X : ↥K)) < 1) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) B hB
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) B hB
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ a)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) := by
  -- `ρz / a` is a `1`-unit at `B`
  have hunit : B.valuation (algebraMap ↥K Ω ((rz * a⁻¹ : (↥K)ˣ) : ↥K)) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, Valuation.map_mul,
      Valuation.map_inv, hrzB, haB, inv_one, mul_one]
  have ht : B.valuation (algebraMap ↥K Ω (((rz * a⁻¹ : (↥K)ˣ) : ↥K) - 1)) < 1 := by
    have h2val : B.valuation (2 : Ω) = 1 := valuation_two_eq_one_of_not_lt_one B h2
    -- `2 * (ρz - a) = -X`
    have h2sub : (2 : ↥K) * ((rz : ↥K) - (a : ↥K)) = -(X : ↥K) := by
      calc (2 : ↥K) * ((rz : ↥K) - (a : ↥K)) = 2 * (rz : ↥K) - 2 * (a : ↥K) := by ring
        _ = 2 * (rz : ↥K) - ((z : ↥K) + (rz : ↥K)) := by rw [← ha]
        _ = (rz : ↥K) - (z : ↥K) := by ring
        _ = -((X : ↥K)) := by rw [hX]; ring
    have hvalsub : B.valuation (algebraMap ↥K Ω ((rz : ↥K) - (a : ↥K))) < 1 := by
      have hv : B.valuation (algebraMap ↥K Ω ((2 : ↥K) * ((rz : ↥K) - (a : ↥K)))) < 1 := by
        rw [h2sub]
        simpa only [map_neg, Valuation.map_neg] using hXB
      rw [map_mul, map_ofNat, Valuation.map_mul, h2val, one_mul] at hv
      exact hv
    have hcoe : ((rz * a⁻¹ : (↥K)ˣ) : ↥K) - 1 = ((rz : ↥K) - (a : ↥K)) * (a : ↥K)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val,
        show ((rz : ↥K) - (a : ↥K)) * (a : ↥K)⁻¹ = (rz : ↥K) * (a : ↥K)⁻¹ - 1 from by
          rw [sub_mul, mul_inv_cancel₀ (Units.ne_zero a)]]
    rw [hcoe]
    simp only [map_mul, map_inv₀, Valuation.map_mul, Valuation.map_inv, haB, inv_one, mul_one]
    exact hvalsub
  have hkill : ∀ v ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (rz * a⁻¹) v = 0 :=
    Work.SSGRoute.ZDataTwo.TwoRec.killsLocalGroup_of_one_unit (K := K) ζ hζ hζK (rz * a⁻¹) B hB
      h2 hunit ht
  have h := oPairAt_mul_left_of_killsLocalGroup (K := K) ζ hζ hζK (rz * a⁻¹) a X B hB hkill
  rwa [show (rz * a⁻¹) * a = rz from by group] at h

/-- **The sibling term of the p. 16 computation.**  The pairing of the stage class with its
conjugate at the sibling is the pairing of the switch with the conjugate of the normalised
representative. -/
theorem oPairAt_sibling_eq_oPairGlob_antiInvariant {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (ρ : K ≃ₐ[k] K) (hρ2 : ρ ^ 2 = 1)
    (b z y rz X : (↥K)ˣ) (hzy : z = b * (y * y))
    (hrz : rz = Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z)
    (hX : (X : ↥K) = (z : ↥K) - (rz : ↥K))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hA2 : ¬ A.valuation (2 : Ω) < 1)
    (hzA : A.valuation (algebraMap ↥K Ω (z : ↥K)) = 1)
    (hXA : A.valuation (algebraMap ↥K Ω (X : ↥K)) = 1)
    (hρzA : A.valuation (algebraMap ↥K Ω (rz : ↥K)) < 1) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) b))
      = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA
        rz X := by
  classical
  set rb : (↥K)ˣ := Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) b with hrbdef
  -- the cochains of `z` and `ρz` agree with those of `b` and `ρb`
  have hχz : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ z
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b := by
    rw [hzy]
    funext ψ
    by_cases hψ : ψ ∈ K.fixingSubgroup
    · exact Work.SSGRoute.ZConstruction.nodeKummerCocharZMod_mul_sq (K := K) ζ hζ hζK b y ψ hψ
    · rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := b * (y * y)) hψ,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := b) hψ]
  have hrz_eq : rz = rb * (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) y
      * Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) y) := by
    rw [hrz, hrbdef, hzy, Work.SSGRoute.H9.conjUnit_mul, Work.SSGRoute.H9.conjUnit_mul]
  have hχrz : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz
      = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rb := by
    rw [hrz_eq]
    funext ψ
    by_cases hψ : ψ ∈ K.fixingSubgroup
    · exact Work.SSGRoute.ZConstruction.nodeKummerCocharZMod_mul_sq (K := K) ζ hζ hζK rb
        (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) y) ψ hψ
    · rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := rb * (Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) y
            * Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) y)) hψ,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod_of_notMem (K := K) (ζ := ζ) (hζK := hζK)
          (hζ := hζ) (β := rb) hψ]
  -- `X / z` is a `1`-unit at `A`
  have hunit : A.valuation (algebraMap ↥K Ω ((X * z⁻¹ : (↥K)ˣ) : ↥K)) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, Valuation.map_mul,
      Valuation.map_inv, hXA, hzA, inv_one, mul_one]
  have ht : A.valuation (algebraMap ↥K Ω (((X * z⁻¹ : (↥K)ˣ) : ↥K) - 1)) < 1 := by
    have hcoe : ((X * z⁻¹ : (↥K)ˣ) : ↥K) - 1 = ((X : ↥K) - (z : ↥K)) * (z : ↥K)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val,
        show ((X : ↥K) - (z : ↥K)) * (z : ↥K)⁻¹ = (X : ↥K) * (z : ↥K)⁻¹ - 1 from by
          rw [sub_mul, mul_inv_cancel₀ (Units.ne_zero z)]]
    have hXs : (X : ↥K) - (z : ↥K) = -(rz : ↥K) := by rw [hX]; ring
    rw [hcoe, hXs]
    simp only [map_mul, map_neg, map_inv₀, Valuation.map_mul, Valuation.map_neg,
      Valuation.map_inv, hzA, inv_one, mul_one]
    exact hρzA
  have hkill : ∀ v ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (X * z⁻¹) v = 0 :=
    Work.SSGRoute.ZDataTwo.TwoRec.killsLocalGroup_of_one_unit (K := K) ζ hζ hζK (X * z⁻¹) A hA
      hA2 hunit ht
  have hred : Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ z) := by
    have h := oPairAt_mul_right_of_killsLocalGroup (K := K) ζ hζ hζK rz (X * z⁻¹) z A hA hkill
    rwa [show (X * z⁻¹) * z = X from by group] at h
  calc Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ b)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rb)
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ z)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz) := by
        rw [← hχz, ← hχrz]
    _ = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ z) :=
        oPairAt_comm_aux (K := K) (k := k) (Ω := Ω) ζ hζ hζK z rz A hA
    _ = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ rz)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ X) := hred.symm
    _ = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hA
        rz X := oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK rz X A hA

/-- **The split pair of primes contributes zero.**  For a place `B` whose prime is not `ρ`-fixed
(the switch `X = z - ρz` being a non-unit there, `2` a unit, and `z`, `ρz`, `a = (z+ρz)/2` units),
the local term at `B` equals the one at `galLift K ρ • B`; in `ZMod 2` the two terms of the pair
therefore cancel. -/
theorem oPairGlob_antiInvariant_eq_galLift_smul {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (ρ : K ≃ₐ[k] K) (hρ1 : ρ ≠ 1) (hρ2 : ρ ^ 2 = 1)
    (z rz X a : (↥K)ˣ)
    (hrz : rz = Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) z)
    (hX : (X : ↥K) = (z : ↥K) - (rz : ↥K))
    (ha : (2 : ↥K) * (a : ↥K) = (z : ↥K) + (rz : ↥K))
    (hafix : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) a = a)
    (hXanti : Work.SSGRoute.H9.conjUnit (Work.SSGRoute.ZDataMup.galLift K ρ) X = -X)
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (hB2 : ¬ B.valuation (2 : Ω) < 1)
    (hB2' : ¬ (Work.SSGRoute.ZDataMup.galLift K ρ • B).valuation (2 : Ω) < 1)
    (hrzB : B.valuation (algebraMap ↥K Ω (rz : ↥K)) = 1)
    (haB : B.valuation (algebraMap ↥K Ω (a : ↥K)) = 1)
    (hXB : B.valuation (algebraMap ↥K Ω (X : ↥K)) < 1)
    (hrzB' : (Work.SSGRoute.ZDataMup.galLift K ρ • B).valuation (algebraMap ↥K Ω (rz : ↥K)) = 1)
    (haB' : (Work.SSGRoute.ZDataMup.galLift K ρ • B).valuation (algebraMap ↥K Ω (a : ↥K)) = 1)
    (hXB' : (Work.SSGRoute.ZDataMup.galLift K ρ • B).valuation (algebraMap ↥K Ω (X : ↥K)) < 1) :
    Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) hB
        rz X
      = Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        ((SSGRoute.isFinPlace_smul_iff B (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hB) rz X := by
  rw [← oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK rz X B hB,
    ← oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK rz X
      (Work.SSGRoute.ZDataMup.galLift K ρ • B)
      ((SSGRoute.isFinPlace_smul_iff B (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hB),
    oPairAt_mul_left_rz_eq_mul_left_a (K := K) (k := k) (Ω := Ω) ζ hζ hζK ρ hρ2 z rz X a hrz
      hX ha B hB hB2 hrzB haB hXB,
    oPairAt_mul_left_rz_eq_mul_left_a (K := K) (k := k) (Ω := Ω) ζ hζ hζK ρ hρ2 z rz X a hrz
      hX ha (Work.SSGRoute.ZDataMup.galLift K ρ • B)
      ((SSGRoute.isFinPlace_smul_iff B (Work.SSGRoute.ZDataMup.galLift K ρ)).mpr hB)
      hB2' hrzB' haB' hXB']
  exact zmod_two_eq_of_add_eq_zero
    (Work.SSGRoute.PinnedTwin.oPairAtPairEqZero (K := K) (k := k) (Ω := Ω) ζ hζ hζK ρ hρ1 hρ2 a X
      hafix hXanti B hB hB2 haB)

open scoped Classical

/-- The `count` of a height-one prime, regarded as a fractional ideal, at a place `P`. -/
theorem count_asIdeal_eq {K : Type} [Field K] [NumberField K]
    (𝔮 P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FractionalIdeal.count K P
        ((𝔮.asIdeal : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers K)) K))
      = (if P = 𝔮 then (1 : ℤ) else 0) := by
  classical
  by_cases h : P = 𝔮
  · rw [h, if_pos rfl, FractionalIdeal.count_self]
  · rw [if_neg h, FractionalIdeal.count_maximal_coprime K P (fun hh => h hh.symm)]

/-- **A positive `𝔭`-adic count forces the place valuation to be `< 1`.** -/
theorem valuation_lt_one_of_count_pos {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    {K : IntermediateField k Ω} [NumberField ↥K]
    (A : ValuationSubring Ω)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭) (y : (↥K)ˣ)
    (h : 0 < FractionalIdeal.count ↥K 𝔭
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (y : ↥K))) :
    A.valuation (algebraMap ↥K Ω (y : ↥K)) < 1 :=
  (count_pos_iff_place_valuation_lt_one A 𝔭 h𝔭 y).mp h

/-- **The place is dyadic exactly when the prime below it divides `2`.** -/
theorem place_two_lt_one_iff_count_pos {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B) :
    B.valuation (2 : Ω) < 1 ↔ 0 < FractionalIdeal.count ↥K
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB)
      (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers ↥K))
        (2 : ↥K)) := by
  rw [show (2 : Ω) = algebraMap ↥K Ω ((Units.mk0 (2 : ↥K) (by norm_num) : (↥K)ˣ) : ↥K) from by
    rw [show ((Units.mk0 (2 : ↥K) (by norm_num) : (↥K)ˣ) : ↥K) = (2 : ↥K) from rfl,
      map_ofNat (algebraMap ↥K Ω) 2]]
  exact (count_pos_iff_place_valuation_lt_one B
    (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) B hB)
    (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := B) hB)
    (Units.mk0 (2 : ↥K) (by norm_num))).symm

/-- **The `ρ`-translate of the valuation ring at `𝔭` is the one at `placeSmul ρ 𝔭`.** -/
theorem smul_valuationSubringAtPrime_eq {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (ρ : K ≃ₐ[k] K)
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K)) :
    ρ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K
        (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭) :=
  Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict 𝔭
    (Commons.NumberTheory.NumberField.Completion.placeSmul ρ 𝔭) ρ
    (Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal ρ 𝔭)

/-- **`oPairGlob` and `oPairAt` agree, independently of the proof of finiteness of the place.** -/
theorem oPairGlob_eq_oPairAt_proof_irrel {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (α β : (↥K)ˣ)
    (A : ValuationSubring Ω) (h1 h2 : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.ZDataMup.OddForm.oPairGlob (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        (hA := h1) α β
      = Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        A h2
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) := by
  rw [← oPairAt_eq_oPairGlob_two (K := K) ζ hζ hζK α β A h1]

end Work.SSGRoute.ZDataTwo.TwoRec
