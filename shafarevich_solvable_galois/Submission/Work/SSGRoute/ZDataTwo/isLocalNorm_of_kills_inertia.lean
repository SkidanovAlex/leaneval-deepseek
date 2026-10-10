import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZDataTwo.InertiaCriterion
import Submission.Work.SSGRoute.ZDataTwo.Mu2Assembly
import Submission.Work.SSGRoute.ZDataTwo.ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.SSGRoute.ZDataTwo

open scoped NumberField IntermediateField
open IsDedekindDomain

/-!
# The excluded finite places contribute a local norm

At a finite place `B` of `Ω` with `B ∤ 2` at which both Kummer characters of `α` and `β` kill the
inertia, `β` is a local norm at the prime `Q` of `k` below `B` from the quadratic extension
`L = k(√α)`.

The argument splits into two local statements:

* the inertia-killing of `α` says that the Kummer field `k(√α) ⊆ Ω` is fixed pointwise by the
  inertia of `B`, hence is unramified at `Q` (`levelPrime_data_of_isInertia_fixing`);
* the inertia-killing of `β` says the same for `k(√β)`; reading the square root of `β` in the
  completion of `k(√β)` shows that the image of `β` in `k_Q` has a *square* valuation
  (`exists_sq_val_completion_of_kills_inertia_self`).

Together with the unramified norm criterion `isLocalNorm_of_unramified_of_val_pow` (with the
inertia degree `f ∈ {1,2}` and the corresponding `f`-th power witness) this gives `β ∈ N_{L_Q/k_Q}`;
the transport to the abstract `L` goes through
`finPair_eq_zero_iff_isLocalNorm`, both extensions having the same local Hilbert pairing.
-/

section Main

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- The prime of `k` below the finite place `B` is the prime `Q` attached to `B` by the
`valuationSubringAtPrime` datum. -/
lemma primeBelow_eq_of_valuationSubringAtPrime_eq (B : ValuationSubring Ω)
    (hB : SSGRoute.IsFinPlace k B)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q) :
    primeBelow k Ω B hB = Q :=
  Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := k) (by
    rw [← primeBelow_spec k Ω B hB]; exact hQ)

/-- The prime of `k` below a place of `Ω`, in the two spellings used in the workspace. -/
lemma primeOf_eq_primeBelow (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B) :
    Submission.NeukirchUchida.primeOf B hB = primeBelow k Ω B hB := by
  haveI : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  refine Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := k) ?_
  rw [← Submission.NeukirchUchida.primeOf_spec B hB, ← primeBelow_spec k Ω B hB]

/-- The prime of the level `L` below `B` lies over the prime `Q` of `k` below `B`. -/
lemma levelPrime_liesOver (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L] [NumberField ↥L] :
    (Work.SSGRoute.levelPrime k Ω B hB L).asIdeal.LiesOver Q.asIdeal := by
  haveI : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  have h := NK.ResidueFrob.primeOfLevel_liesOver (K := k) (K' := Ω)
    (⟨B, hB⟩ : NK.FrobeniusBridge.FinitePlaceOf k Ω) L
  rw [primeOf_eq_primeBelow (k := k) (Ω := Ω) B hB,
    primeBelow_eq_of_valuationSubringAtPrime_eq (k := k) (Ω := Ω) B hB Q hQ] at h
  simpa only [Work.SSGRoute.levelPrime] using h

/-- **The ramification datum of a level whose inertia is fixed.**  If every inertia element of the
place `B` fixes a finite Galois level `L` of degree `≤ 2`, then the prime of `𝓞 L` below `B` is
unramified over the prime of `k` below `B`, and its inertia degree is at most `2`. -/
lemma levelPrime_data_of_isInertia_fixing (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (L : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    (hfix : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → σ ∈ L.fixingSubgroup)
    (hfin : Module.finrank k ↥L ≤ 2) :
    (Work.SSGRoute.levelPrime k Ω B hB L).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers k) = 1 ∧
      (Work.SSGRoute.levelPrime k Ω B hB L).asIdeal.inertiaDeg
        (NumberField.RingOfIntegers k) ≤ 2 := by
  have hunr : ¬ SSGRoute.IsRamifiedIn k L B := fun ⟨σ, hσI, hσ⟩ => hσ (hfix σ hσI)
  have he : (Work.SSGRoute.levelPrime k Ω B hB L).asIdeal.ramificationIdx
      (NumberField.RingOfIntegers k) = 1 :=
    ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn k Ω L B hB hunr
  refine ⟨he, ?_⟩
  have hlies : (Work.SSGRoute.levelPrime k Ω B hB L).asIdeal.LiesOver
      (Submission.NeukirchUchida.primeOf B hB).asIdeal := by
    haveI : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
    have h := NK.ResidueFrob.primeOfLevel_liesOver (K := k) (K' := Ω)
      (⟨B, hB⟩ : NK.FrobeniusBridge.FinitePlaceOf k Ω) L
    simpa only [Work.SSGRoute.levelPrime] using h
  have hcard :=
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := k) (L := ↥L) (Submission.NeukirchUchida.primeOf B hB)
      (Work.SSGRoute.levelPrime k Ω B hB L) hlies
  have hle :=
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
      (K := k) (L := ↥L) (Submission.NeukirchUchida.primeOf B hB)
      (Work.SSGRoute.levelPrime k Ω B hB L) hlies
  rw [he, one_mul] at hcard
  omega

/-- An element of the abstract quadratic extension `L = k(√α)` shows that `α` is not a square in
`k`. -/
lemma not_square_of_sq_root {K E : Type} [Field K] [Field E] [Algebra K E] (α : Kˣ) (y : E)
    (hy1 : y * y = algebraMap K E (α : K)) (hy2 : y ∉ Set.range (algebraMap K E)) :
    ∀ d : K, d * d ≠ (α : K) := by
  intro d hd
  have hsq : y * y = algebraMap K E d * algebraMap K E d := by
    rw [hy1, ← map_mul, hd]
  have hzero : (y - algebraMap K E d) * (y + algebraMap K E d) = 0 := by
    rw [sub_mul, mul_add, mul_add, hsq]
    ring
  rcases mul_eq_zero.mp hzero with h | h
  · exact hy2 ⟨d, (sub_eq_zero.mp h).symm⟩
  · exact hy2 ⟨-d, by rw [map_neg]; exact (eq_neg_iff_add_eq_zero.mpr h).symm⟩

/-- **The even-valuation input for `β`.**  If the Kummer character of `β` kills the inertia at the
finite place `B` lying over `Q`, then the image of `β` in `k_Q` is a square in the value group: the
Kummer field `k(√β)` is unramified at `Q`, and the square root of `β` inside it computes the
valuation of `β` as a square. -/
lemma exists_sq_val_completion_of_kills_inertia_self (B : ValuationSubring Ω)
    (hB : SSGRoute.IsFinPlace k B)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (β : kˣ)
    (hb : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ →
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ β σ = 0) :
    ∃ y : (Q.adicCompletion k)ˣ,
      Valued.v (R := Q.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap k (Q.adicCompletion k) (β : k)) =
        (Valued.v (R := Q.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
          (y : Q.adicCompletion k)) ^ 2 := by
  classical
  -- the Kummer field `k(√β)`, quadratic by construction
  set zΩ : Ω := ((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) β : Ωˣ) : Ω) with hzΩ
  have hroot : zΩ * zΩ = algebraMap k Ω (β : k) := by
    rw [hzΩ, ← pow_two, ← Units.val_pow_eq_pow_val, Work.SSGRoute.kummerSqrt_pow, Units.coe_map]
    try rfl
  set Lβ : IntermediateField k Ω := IntermediateField.adjoin k {zΩ} with hLβ
  haveI hnormal : Normal k Lβ := by
    rw [hLβ]
    exact (NK.NUV2.LC.adjoinSq_normal_finrank_le (K := k) (L := Ω) zΩ (β : k) hroot).1
  haveI hfd : FiniteDimensional k Lβ := by
    rw [hLβ]
    exact (NK.NUV2.LC.adjoinSq_normal_finrank_le (K := k) (L := Ω) zΩ (β : k) hroot).2.1
  haveI hgal : IsGalois k Lβ := isGalois_iff.mpr ⟨inferInstance, hnormal⟩
  haveI hnf : NumberField ↥Lβ :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) Lβ
  -- every inertia element of `B` fixes the Kummer field of `β`
  have hfix : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → σ ∈ Lβ.fixingSubgroup := by
    intro σ hσ
    rw [hLβ]
    refine mem_fixingSubgroup_adjoin_simple zΩ σ ?_
    exact (Work.SSGRoute.kummerChar_eq_zero_iff_apply_sqrt (K := k) (Ω := Ω) ζ hζ β σ).mp
      (hb σ hσ)
  have hunr : ¬ SSGRoute.IsRamifiedIn k Lβ B := fun ⟨σ, hσI, hσ⟩ => hσ (hfix σ hσI)
  -- the prime of `𝓞 ↥Lβ` below `B`
  set qL : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥Lβ) :=
    Work.SSGRoute.levelPrime k Ω B hB Lβ with hqL
  have he : qL.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    rw [hqL]
    exact ramificationIdx_levelPrime_eq_one_of_not_isRamifiedIn k Ω Lβ B hB hunr
  have hpb : primeBelow k Ω B hB = Q :=
    primeBelow_eq_of_valuationSubringAtPrime_eq B hB Q hQ
  have hliesB : (Work.SSGRoute.levelPrime k Ω B hB Lβ).asIdeal.LiesOver
      (Submission.NeukirchUchida.primeOf B hB).asIdeal := by
    haveI : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
    have h := NK.ResidueFrob.primeOfLevel_liesOver (K := k) (K' := Ω)
      (⟨B, hB⟩ : NK.FrobeniusBridge.FinitePlaceOf k Ω) Lβ
    simpa only [Work.SSGRoute.levelPrime] using h
  have hliesQ : qL.asIdeal.LiesOver Q.asIdeal := by
    rw [hqL]
    rw [← hpb]
    rw [← primeOf_eq_primeBelow (k := k) (Ω := Ω) B hB]
    exact hliesB
  -- the square root of `β` inside `Lβ` and its image in the completion
  have hzmem : zΩ ∈ Lβ := by
    rw [hLβ]
    exact IntermediateField.mem_adjoin_simple_self k zΩ
  have hzsq : (⟨zΩ, hzmem⟩ : ↥Lβ) ^ 2 = algebraMap k ↥Lβ (β : k) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow]
    change zΩ ^ 2 = algebraMap k Ω (β : k)
    rw [pow_two]
    exact hroot
  set x : qL.adicCompletion ↥Lβ :=
    algebraMap ↥Lβ (qL.adicCompletion ↥Lβ) ⟨zΩ, hzmem⟩ with hx
  have hx2 : x ^ 2 = ((algebraMap k ↥Lβ (β : k)) : qL.adicCompletion ↥Lβ) := by
    rw [hx, ← map_pow, hzsq]
    try rfl
  have hZ : (Commons.RingTheory.Henselian.adicCompletionMap Q qL hliesQ)
        (algebraMap k (Q.adicCompletion k) (β : k)) =
      ((algebraMap k ↥Lβ (β : k)) : qL.adicCompletion ↥Lβ) :=
    Commons.RingTheory.Henselian.adicCompletionMap_apply Q qL hliesQ (β : k)
  -- a unit of `k_Q` with the valuation of `x`
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_surjective k Q
    (Valued.v (R := qL.adicCompletion ↥Lβ) (Γ₀ := WithZero (Multiplicative ℤ)) x)
  have hva : Valued.v (R := Q.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap k (Q.adicCompletion k) a) =
      Valued.v (R := qL.adicCompletion ↥Lβ) (Γ₀ := WithZero (Multiplicative ℤ)) x :=
    (Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq Q a).trans ha
  have hx0 : x ≠ 0 := by
    intro h
    have h2 : ((algebraMap k ↥Lβ (β : k)) : qL.adicCompletion ↥Lβ) = 0 := by
      rw [← hx2, h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have h3 : algebraMap k ↥Lβ (β : k) = 0 :=
      (algebraMap ↥Lβ (qL.adicCompletion ↥Lβ)).injective h2
    exact (Units.ne_zero β) ((algebraMap k ↥Lβ).injective (by simpa using h3))
  have ha0 : a ≠ 0 := by
    intro h0
    refine (Valuation.ne_zero_iff (Valued.v (R := qL.adicCompletion ↥Lβ)
      (Γ₀ := WithZero (Multiplicative ℤ)))).mpr hx0 ?_
    rw [← ha, h0]
    exact map_zero _
  refine ⟨Units.map ((algebraMap k (Q.adicCompletion k)).toMonoidHom) (Units.mk0 a ha0), ?_⟩
  have htval : Valued.v (R := Q.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
      ((Units.map ((algebraMap k (Q.adicCompletion k)).toMonoidHom) (Units.mk0 a ha0) :
        (Q.adicCompletion k)ˣ) : Q.adicCompletion k) =
      Valued.v (R := qL.adicCompletion ↥Lβ) (Γ₀ := WithZero (Multiplicative ℤ)) x := by
    rw [Units.coe_map, Units.val_mk0]
    exact hva
  -- the value of `β` is the square of the value of `x`
  have step1 : Valued.v (R := qL.adicCompletion ↥Lβ) (Γ₀ := WithZero (Multiplicative ℤ))
      ((Commons.RingTheory.Henselian.adicCompletionMap Q qL hliesQ)
        (algebraMap k (Q.adicCompletion k) (β : k))) =
      (Valued.v (R := qL.adicCompletion ↥Lβ) (Γ₀ := WithZero (Multiplicative ℤ)) x) ^ 2 := by
    rw [hZ, ← hx2, map_pow]
    try rfl
  have step2 : Valued.v (R := Q.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap k (Q.adicCompletion k) (β : k)) =
      (Valued.v (R := qL.adicCompletion ↥Lβ) (Γ₀ := WithZero (Multiplicative ℤ)) x) ^ 2 := by
    rw [← step1,
      Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q qL hliesQ
        (algebraMap k (Q.adicCompletion k) (β : k)),
      he, pow_one]
    try rfl
  rw [htval]
  exact step2

end Main

section Assembly

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [IsAlgClosed Ω]

/-- **The assembly.**  Given the even-valuation input for `β` in the completion `k_Q`, `β` is a
local norm at `Q` from any quadratic extension `L = k(√α)` in which the Kummer character of `α`
kills the inertia of `B`. -/
theorem isLocalNorm_of_kills_inertia_of_sq_val
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (α β : kˣ)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (h2 : Nat.card (L ≃ₐ[k] L) = 2)
    (hy : ∃ y : L, y * y = algebraMap k L (α : k) ∧ y ∉ Set.range (algebraMap k L))
    (ha : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ →
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α σ = 0)
    (hsq : ∃ y : (Q.adicCompletion k)ˣ,
      Valued.v (R := Q.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap k (Q.adicCompletion k) (β : k)) =
        (Valued.v (R := Q.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
          (y : Q.adicCompletion k)) ^ 2) :
    NK.NUV2.LC.IsLocalNorm k L β (NK.GlobalCFT.Place.ofFinite Q) := by
  classical
  -- `α` is not a square in `k`
  have hnsq : ∀ d : k, d * d ≠ (α : k) := by
    obtain ⟨y, hy1, hy2⟩ := hy
    exact not_square_of_sq_root α y hy1 hy2
  -- the Kummer field `k(√α)` of `α`
  obtain ⟨hgal, hcard, hyK⟩ := kummerField_quadratic k Ω α hnsq
  have hrootα : (((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω)) *
      (((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω)) = algebraMap k Ω (α : k) := by
    rw [← pow_two, ← Units.val_pow_eq_pow_val, Work.SSGRoute.kummerSqrt_pow, Units.coe_map]
    try rfl
  haveI hfdK : FiniteDimensional k ↥(kummerField k Ω α) := by
    rw [kummerField]
    exact (NK.NUV2.LC.adjoinSq_normal_finrank_le (K := k) (L := Ω)
      (((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω)) (α : k) hrootα).2.1
  haveI : IsGalois k ↥(kummerField k Ω α) := hgal
  haveI : NumberField ↥(kummerField k Ω α) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω)
      (kummerField k Ω α)
  have hfix : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ →
      σ ∈ (kummerField k Ω α).fixingSubgroup := by
    intro σ hσ
    refine mem_fixingSubgroup_adjoin_simple
      (((Work.SSGRoute.kummerSqrt (K := k) (Ω := Ω) α : Ωˣ) : Ω)) σ ?_
    exact (Work.SSGRoute.kummerChar_eq_zero_iff_apply_sqrt (K := k) (Ω := Ω) ζ hζ α σ).mp
      (ha σ hσ)
  have hfin : Module.finrank k ↥(kummerField k Ω α) ≤ 2 := by
    rw [← IsGalois.card_aut_eq_finrank k ↥(kummerField k Ω α)]
    omega
  -- the prime of `𝓞 ↥(k(√α))` below `B`
  set qK : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(kummerField k Ω α)) :=
    Work.SSGRoute.levelPrime k Ω B hB (kummerField k Ω α) with hqK
  obtain ⟨he₀, hf0⟩ := levelPrime_data_of_isInertia_fixing B hB (kummerField k Ω α) hfix hfin
  have he : qK.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
    rw [hqK]
    exact he₀
  have hf2le : qK.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) ≤ 2 := by
    rw [hqK]
    exact hf0
  have hLies : qK.asIdeal.LiesOver Q.asIdeal := by
    rw [hqK]
    exact levelPrime_liesOver B hB Q hQ (kummerField k Ω α)
  -- the inertia degree is `1` or `2`
  have hfpos : 0 < qK.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    have hcard2 :=
      Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        (K := k) (L := ↥(kummerField k Ω α)) Q qK hLies
    haveI hfinmod : Module.Finite (Q.adicCompletion k)
        (qK.adicCompletion ↥(kummerField k Ω α)) :=
      Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q qK hLies
    have hpos : 0 < Module.finrank (Q.adicCompletion k)
        (qK.adicCompletion ↥(kummerField k Ω α)) := Module.finrank_pos
    rw [he, one_mul] at hcard2
    omega
  -- the `f`-th power value witness of the unramified norm criterion
  have hdiv : ∃ y : (Q.adicCompletion k)ˣ,
      Valued.v (R := Q.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap k (Q.adicCompletion k) (β : k)) =
        (Valued.v (R := Q.adicCompletion k) (Γ₀ := WithZero (Multiplicative ℤ))
          (y : Q.adicCompletion k)) ^
          (qK.asIdeal.inertiaDeg (NumberField.RingOfIntegers k)) := by
    rcases eq_or_ne (qK.asIdeal.inertiaDeg (NumberField.RingOfIntegers k)) 1 with hf1 | hf1
    · refine ⟨Units.map ((algebraMap k (Q.adicCompletion k)).toMonoidHom) β, ?_⟩
      rw [hf1, pow_one, Units.coe_map]
      try rfl
    · have hfeq : qK.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 2 := by omega
      obtain ⟨y, hyv⟩ := hsq
      exact ⟨y, by rw [hfeq]; exact hyv⟩
  have hloc : NK.NUV2.LC.IsLocalNorm k ↥(kummerField k Ω α) β
      (NK.GlobalCFT.Place.ofFinite Q) :=
    isLocalNorm_of_unramified_of_val_pow Q qK hLies he β hdiv
  -- the local Hilbert symbol of `α` and `β` at `Q` vanishes
  have hpb : primeBelow k Ω B hB = Q :=
    primeBelow_eq_of_valuationSubringAtPrime_eq B hB Q hQ
  have h0 : finPair k (primeBelow k Ω B hB) α β = 0 :=
    (finPair_eq_zero_iff_isLocalNorm k Ω ζ hζ B hB α β ↥(kummerField k Ω α) hcard hyK).mpr (by
      rw [hpb]
      exact hloc)
  -- and so `β` is a local norm for the abstract `L` as well
  have h1 := (finPair_eq_zero_iff_isLocalNorm k Ω ζ hζ B hB α β L h2 hy).mp h0
  rwa [hpb] at h1

end Assembly

/-- **The excluded finite places contribute a local norm.**  At a finite place `B` of `Ω` with
`B ∤ 2` at which both Kummer characters kill the inertia, `β` is a local norm at the prime `Q` of
`k` below `B` from the quadratic extension `L = k(√α)`. -/
theorem isLocalNorm_of_kills_inertia {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (B : ValuationSubring Ω) (hB : SSGRoute.IsFinPlace k B)
    (h2B : ¬ B.valuation (2 : Ω) < 1)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : B.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k Q)
    (ζ : k) (hζ : IsPrimitiveRoot ζ 2) (α β : kˣ)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (h2 : Nat.card (L ≃ₐ[k] L) = 2)
    (hy : ∃ y : L, y * y = algebraMap k L (α : k) ∧ y ∉ Set.range (algebraMap k L))
    (ha : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ →
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ α σ = 0)
    (hb : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ →
      Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ β σ = 0) :
    NK.NUV2.LC.IsLocalNorm k L β (NK.GlobalCFT.Place.ofFinite Q) :=
  isLocalNorm_of_kills_inertia_of_sq_val B hB Q hQ ζ hζ α β L h2 hy ha
    (exists_sq_val_completion_of_kills_inertia_self B hB Q hQ ζ hζ β hb)

end Work.SSGRoute.ZDataTwo
