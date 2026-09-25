import Mathlib
import Submission.NK.CFTLib.ARL.Cyclic
import Submission.NK.CFTLib.ARL.count_idealOf_normIdeleHom

/-!
# The relative norm of a fractional ideal of `L` over `K`

The relative norm `N_{L/K} A` of a fractional ideal `A` of `𝓞 L`, defined through its `𝔭`-adic
exponent vector `relNormExp A 𝔭 = ∑_{𝔓 | 𝔭} f(𝔓/𝔭) · v_𝔓(A)`, packaged as a homomorphism
`relNormUnit` on the group of fractional ideals.  The main point for
`NK.CFTLib.ARL.index_principalRay_sup_normIdeals_le` is `relNormUnit_mem_normIdeals`: the
relative norm of a fractional ideal which is a local unit away from `m` lies in the norm group
`NK.CFTLib.ARL.normIdeals K L m`, and `idealOf_normIdeleHom`: the ideal of an idèlic norm is the
relative norm of the ideal of the idèle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.ARL

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-! ## The relative norm of a fractional ideal, by its exponent vector -/

/-- The exponent of the relative norm of a fractional ideal of `L` at the prime `𝔭` of `K`:
`∑_{𝔓 | 𝔭} f(𝔓/𝔭) · v_𝔓(A)`. -/
noncomputable def relNormExp (A : FractionalIdeal (𝓞 L)⁰ L)
    (𝔭 : HeightOneSpectrum (𝓞 K)) : ℤ :=
  ∑ 𝔓 ∈ Place.primesOverFinite (K := K) (L := L) 𝔭,
    ((𝔓.asIdeal.inertiaDeg (𝓞 K) : ℤ) * FractionalIdeal.count L 𝔓 A)

/-- The relative norm of a *fractional* ideal `A` of `L`, defined by its `𝔭`-adic exponent vector
`relNormExp A`. -/
noncomputable def relNormFI (A : FractionalIdeal (𝓞 L)⁰ L) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K),
    (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (relNormExp (K := K) (L := L) A 𝔭)

/-- Only finitely many primes of `K` occur in the exponent vector of `relNormFI`. -/
lemma relNormExp_eventually_zero (A : FractionalIdeal (𝓞 L)⁰ L) :
    ∀ᶠ 𝔭 : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      relNormExp (K := K) (L := L) A 𝔭 = 0 := by
  classical
  set S : Set (HeightOneSpectrum (𝓞 L)) := {𝔓 | FractionalIdeal.count L 𝔓 A ≠ 0} with hS
  have hSfin : S.Finite := by
    simpa [hS] using Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := L) A)
  have hsub : {𝔭 : HeightOneSpectrum (𝓞 K) | relNormExp (K := K) (L := L) A 𝔭 ≠ 0} ⊆
      (fun 𝔓 : HeightOneSpectrum (𝓞 L) => 𝔓.under (𝓞 K)) '' S := by
    intro 𝔭 h𝔭
    obtain ⟨𝔓, h𝔓mem, h𝔓ne⟩ : ∃ 𝔓 ∈ Place.primesOverFinite (K := K) (L := L) 𝔭,
        ((𝔓.asIdeal.inertiaDeg (𝓞 K) : ℤ) * FractionalIdeal.count L 𝔓 A) ≠ 0 := by
      by_contra h
      push Not at h
      exact h𝔭 (Finset.sum_eq_zero h)
    have hlies : 𝔓.asIdeal.LiesOver 𝔭.asIdeal :=
      (Place.mem_primesOverFinite (K := K) (L := L)).mp h𝔓mem
    refine (Set.mem_image _ S 𝔭).mpr ⟨𝔓, ?_, ?_⟩
    · rw [hS]
      exact fun h0 => h𝔓ne (by rw [h0, mul_zero])
    · exact HeightOneSpectrum.ext hlies.over.symm
  rw [Filter.eventually_cofinite]
  exact (hSfin.image (fun 𝔓 : HeightOneSpectrum (𝓞 L) => 𝔓.under (𝓞 K))).subset hsub

/-- The `𝔭`-adic exponent of `relNormFI A` is `relNormExp A 𝔭`. -/
lemma count_relNormFI (A : FractionalIdeal (𝓞 L)⁰ L) (𝔭 : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K 𝔭 (relNormFI (K := K) (L := L) A) =
      relNormExp (K := K) (L := L) A 𝔭 :=
  FractionalIdeal.count_finprod K 𝔭 _ (relNormExp_eventually_zero (K := K) (L := L) A)

/-- `relNormFI A` is nonzero. -/
lemma relNormFI_ne_zero (A : FractionalIdeal (𝓞 L)⁰ L) :
    relNormFI (K := K) (L := L) A ≠ 0 := by
  unfold relNormFI
  apply finprod_ne_zero
  intro 𝔭
  apply zpow_ne_zero
  rw [FractionalIdeal.coeIdeal_ne_zero]
  exact 𝔭.ne_bot

/-- The exponent vector is additive in the fractional ideal. -/
lemma relNormExp_mul {A B : FractionalIdeal (𝓞 L)⁰ L} (hA : A ≠ 0) (hB : B ≠ 0) :
    relNormExp (K := K) (L := L) (A * B) = relNormExp (K := K) (L := L) A +
      relNormExp (K := K) (L := L) B := by
  funext 𝔭
  simp only [relNormExp, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun 𝔓 _ => by
    rw [FractionalIdeal.count_mul L 𝔓 hA hB, mul_add]

/-- `relNormFI` is multiplicative. -/
lemma relNormFI_mul {A B : FractionalIdeal (𝓞 L)⁰ L} (hA : A ≠ 0) (hB : B ≠ 0) :
    relNormFI (K := K) (L := L) (A * B) =
      relNormFI (K := K) (L := L) A * relNormFI (K := K) (L := L) B := by
  refine IdeleClassGroup.fractionalIdeal_eq_of_count_eq (relNormFI_ne_zero _)
    (mul_ne_zero (relNormFI_ne_zero _) (relNormFI_ne_zero _)) fun 𝔭 => ?_
  rw [count_relNormFI, FractionalIdeal.count_mul K 𝔭 (relNormFI_ne_zero _) (relNormFI_ne_zero _),
    count_relNormFI, count_relNormFI, relNormExp_mul hA hB]
  rfl


/-! ## The relative norm of integral ideals -/

/-- `relNormFI` of the unit fractional ideal. -/
lemma relNormFI_one :
    relNormFI (K := K) (L := L) (1 : FractionalIdeal (𝓞 L)⁰ L) = 1 := by
  refine IdeleClassGroup.fractionalIdeal_eq_of_count_eq (relNormFI_ne_zero _) one_ne_zero
    fun 𝔭 => ?_
  rw [count_relNormFI, relNormExp, FractionalIdeal.count_one]
  simp [FractionalIdeal.count_one]

/-- `relNormFI` of a power. -/
lemma relNormFI_pow (A : FractionalIdeal (𝓞 L)⁰ L) (hA : A ≠ 0) (n : ℕ) :
    relNormFI (K := K) (L := L) (A ^ n) = relNormFI (K := K) (L := L) A ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, relNormFI_one]
  | succ n ih => rw [pow_succ, relNormFI_mul (pow_ne_zero _ hA) hA, ih, pow_succ]

open UniqueFactorizationMonoid in
/-- `relNormFI` of a prime ideal of `𝓞 L` is the relative norm of that prime. -/
lemma relNormFI_prime (𝔓 : HeightOneSpectrum (𝓞 L)) :
    relNormFI (K := K) (L := L) (𝔓.asIdeal : FractionalIdeal (𝓞 L)⁰ L) =
      ((Ideal.relNorm (𝓞 K) 𝔓.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  haveI : 𝔓.asIdeal.IsPrime := 𝔓.isPrime
  haveI : 𝔓.asIdeal.IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime 𝔓.ne_bot 𝔓.isPrime
  have hqprime : (𝔓.asIdeal.under (𝓞 K)).IsPrime := inferInstance
  have hqne : 𝔓.asIdeal.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) 𝔓.ne_bot
  haveI : (𝔓.asIdeal.under (𝓞 K)).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hqne hqprime
  haveI : 𝔓.asIdeal.LiesOver (𝔓.asIdeal.under (𝓞 K)) := ⟨rfl⟩
  refine IdeleClassGroup.fractionalIdeal_eq_of_count_eq (relNormFI_ne_zero _) ?_ fun 𝔭 => ?_
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    exact fun h => 𝔓.ne_bot ((Ideal.relNorm_eq_bot_iff).mp h)
  · have hcount : ∀ 𝔔 : HeightOneSpectrum (𝓞 L),
        FractionalIdeal.count L 𝔔 (𝔓.asIdeal : FractionalIdeal (𝓞 L)⁰ L) =
          if 𝔓 = 𝔔 then 1 else 0 := fun 𝔔 => FractionalIdeal.count_maximal L 𝔔 𝔓
    have hsum : (∑ 𝔔 ∈ Place.primesOverFinite (K := K) (L := L) 𝔭,
        ((𝔔.asIdeal.inertiaDeg (𝓞 K) : ℤ) * FractionalIdeal.count L 𝔔
          (𝔓.asIdeal : FractionalIdeal (𝓞 L)⁰ L))) =
        ∑ 𝔔 ∈ Place.primesOverFinite (K := K) (L := L) 𝔭,
          (if 𝔓 = 𝔔 then (𝔔.asIdeal.inertiaDeg (𝓞 K) : ℤ) else 0) :=
      Finset.sum_congr rfl fun 𝔔 _ => by
        rw [hcount 𝔔]
        by_cases h : 𝔓 = 𝔔 <;> simp [h]
    rw [count_relNormFI, relNormExp, hsum, Finset.sum_ite_eq,
      Ideal.relNorm_eq_pow_of_isMaximal 𝔓.asIdeal (𝔓.asIdeal.under (𝓞 K)),
      FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow]
    change (if 𝔓 ∈ Place.primesOverFinite (K := K) (L := L) 𝔭 then
        (𝔓.asIdeal.inertiaDeg (𝓞 K) : ℤ) else 0) =
      (𝔓.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        FractionalIdeal.count K 𝔭 (↑((𝔓.under (𝓞 K)).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
    rw [FractionalIdeal.count_maximal]
    have hmem : 𝔓 ∈ Place.primesOverFinite (K := K) (L := L) 𝔭 ↔ 𝔓.under (𝓞 K) = 𝔭 := by
      rw [Place.mem_primesOverFinite]
      constructor
      · intro h
        exact HeightOneSpectrum.ext h.over.symm
      · intro h
        exact ⟨by rw [← h, HeightOneSpectrum.under_asIdeal]⟩
    by_cases h : 𝔓 ∈ Place.primesOverFinite (K := K) (L := L) 𝔭
    · rw [if_pos h, if_pos (hmem.mp h), mul_one]
    · rw [if_neg h, if_neg (fun hh => h (hmem.mpr hh)), mul_zero]

open UniqueFactorizationMonoid in
/-- `relNormFI` of an integral ideal is its relative norm. -/
lemma relNormFI_coeIdeal (𝔟 : Ideal (𝓞 L)) (h𝔟 : 𝔟 ≠ ⊥) :
    relNormFI (K := K) (L := L) (𝔟 : FractionalIdeal (𝓞 L)⁰ L) =
      ((Ideal.relNorm (𝓞 K) 𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  revert h𝔟
  refine UniqueFactorizationMonoid.induction_on_prime
    (P := fun 𝔟 : Ideal (𝓞 L) => 𝔟 ≠ ⊥ → relNormFI (K := K) (L := L)
      (𝔟 : FractionalIdeal (𝓞 L)⁰ L) =
        ((Ideal.relNorm (𝓞 K) 𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) 𝔟 ?_ ?_ ?_
  · intro h
    exact absurd Ideal.zero_eq_bot h
  · intro x hx _
    rw [Ideal.isUnit_iff.mp hx, FractionalIdeal.coeIdeal_top, Ideal.relNorm_top,
      FractionalIdeal.coeIdeal_top, relNormFI_one]
  · intro a p ha hpprime iha hpa
    have hpbot : p ≠ ⊥ := fun h => hpa (by rw [h, ← Ideal.zero_eq_bot, zero_mul,
      Ideal.zero_eq_bot])
    have habot : a ≠ ⊥ := fun h => ha (h.trans Ideal.zero_eq_bot.symm)
    have hpp : p.IsPrime := (Ideal.prime_iff_isPrime hpbot).mp hpprime
    have hpne : (p : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 := fun h =>
      hpbot ((FractionalIdeal.coeIdeal_eq_zero).mp h)
    have hane : (a : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 := fun h =>
      habot ((FractionalIdeal.coeIdeal_eq_zero).mp h)
    rw [FractionalIdeal.coeIdeal_mul, relNormFI_mul hpne hane,
      relNormFI_prime ⟨p, hpp, hpbot⟩, iha habot,
      map_mul (Ideal.relNorm (𝓞 K)) p a, FractionalIdeal.coeIdeal_mul]


/-! ## The units of fractional ideals, and the norm subgroup -/

/-- The unit of the group of fractional ideals of `L` associated with a prime ideal. -/
noncomputable def primeUnit (𝔓 : HeightOneSpectrum (𝓞 L)) : (FractionalIdeal (𝓞 L)⁰ L)ˣ :=
  Units.mk0 ((𝔓.asIdeal : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)
    (by rw [FractionalIdeal.coeIdeal_ne_zero]; exact 𝔓.ne_bot)

@[simp] lemma primeUnit_val (𝔓 : HeightOneSpectrum (𝓞 L)) :
    ((primeUnit 𝔓 : (FractionalIdeal (𝓞 L)⁰ L)ˣ) : FractionalIdeal (𝓞 L)⁰ L) =
      ((𝔓.asIdeal : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) := rfl

/-- `relNormFI` as a homomorphism of the groups of fractional ideals. -/
noncomputable def relNormUnit :
    (FractionalIdeal (𝓞 L)⁰ L)ˣ →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun A := Units.mk0 (relNormFI (K := K) (L := L) (A : FractionalIdeal (𝓞 L)⁰ L))
    (relNormFI_ne_zero _)
  map_one' := by
    apply Units.ext
    simp [relNormFI_one]
  map_mul' A B := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul]
    exact relNormFI_mul A.ne_zero B.ne_zero

/-- The norm of a prime is the relative norm ideal. -/
lemma relNormUnit_primeUnit (𝔓 : HeightOneSpectrum (𝓞 L)) :
    relNormUnit (K := K) (L := L) (primeUnit 𝔓) =
      Units.mk0 (((Ideal.relNorm (𝓞 K) 𝔓.asIdeal : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K)) (by
          rw [FractionalIdeal.coeIdeal_ne_zero]
          exact fun h => 𝔓.ne_bot ((Ideal.relNorm_eq_bot_iff).mp h)) := by
  apply Units.ext
  simp only [Units.val_mk0, primeUnit_val]
  exact relNormFI_prime 𝔓

/-- **The relative norm of a fractional ideal which is a local unit outside `m` lies in the norm
group `𝔑(m)`.**  This is the ideal-theoretic content of the identity
`idealOf (N_{L/K} y) = relNorm (idealOf y)`. -/
lemma relNormUnit_mem_normIdeals (m : ℕ) {A : (FractionalIdeal (𝓞 L)⁰ L)ˣ}
    (hA : ∀ 𝔓 : HeightOneSpectrum (𝓞 L), (m : 𝓞 L) ∈ 𝔓.asIdeal →
      FractionalIdeal.count L 𝔓 (A : FractionalIdeal (𝓞 L)⁰ L) = 0) :
    relNormUnit (K := K) (L := L) A ∈ normIdeals K L m := by
  classical
  set S : Finset (HeightOneSpectrum (𝓞 L)) :=
    (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := L)
      (A : FractionalIdeal (𝓞 L)⁰ L))).toFinset with hS
  have hSmem : ∀ 𝔓, 𝔓 ∈ S ↔ FractionalIdeal.count L 𝔓 (A : FractionalIdeal (𝓞 L)⁰ L) ≠ 0 :=
    fun 𝔓 => Set.Finite.mem_toFinset _
  have hsupp : Function.mulSupport (fun 𝔓 : HeightOneSpectrum (𝓞 L) =>
      ((𝔓.asIdeal : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) ^
        FractionalIdeal.count L 𝔓 (A : FractionalIdeal (𝓞 L)⁰ L)) ⊆ ↑S := by
    intro 𝔓 h𝔓
    exact (hSmem 𝔓).mpr fun h0 => h𝔓 (by simp only [h0, zpow_zero])
  have hfac : (∏ 𝔓 ∈ S, (primeUnit 𝔓) ^
      FractionalIdeal.count L 𝔓 (A : FractionalIdeal (𝓞 L)⁰ L)) = A := by
    apply Units.ext
    rw [Units.coe_prod]
    simp only [primeUnit_val, Units.val_zpow_eq_zpow_val]
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp]
    exact FractionalIdeal.finprod_heightOneSpectrum_factorization' L A.ne_zero
  rw [← hfac, map_prod]
  refine Subgroup.prod_mem _ fun 𝔓 h𝔓 => ?_
  rw [map_zpow]
  refine Subgroup.zpow_mem _ ?_ _
  refine Subgroup.subset_closure ⟨⟨𝔓.asIdeal, 𝔓.ne_bot, ?_⟩, ?_⟩
  · intro 𝔭 h𝔭 hdvd
    haveI : 𝔓.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime 𝔓.ne_bot 𝔓.isPrime
    haveI : 𝔭.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime 𝔭.ne_bot 𝔭.isPrime
    have hle : 𝔓.asIdeal ≤ 𝔭.asIdeal := Ideal.dvd_iff_le.mp hdvd
    have heq : 𝔓.asIdeal = 𝔭.asIdeal :=
      Ideal.IsMaximal.eq_of_le ‹𝔓.asIdeal.IsMaximal›
        (Ideal.IsMaximal.ne_top ‹𝔭.asIdeal.IsMaximal›) hle
    exact (hSmem 𝔓).mp h𝔓 (hA 𝔓 (heq.symm ▸ h𝔭))
  · rw [relNormUnit_primeUnit]



/-! ## Auxiliary arithmetic lemmas -/

/-- The ideal of the idèlic norm is the relative norm of the ideal of the idèle. -/
theorem idealOf_normIdeleHom (y : Idele L) :
    Idele.idealOf (Idele.normIdeleHom K L y) =
      relNormFI (K := K) (L := L) (Idele.idealOf y) := by
  refine IdeleClassGroup.fractionalIdeal_eq_of_count_eq (Idele.idealOf_ne_zero _)
    (relNormFI_ne_zero _) fun 𝔭 => ?_
  rw [count_relNormFI, relNormExp]
  exact (count_idealOf_normIdeleHom (K := K) (L := L) y 𝔭).trans
    (Finset.sum_congr rfl fun 𝔓 _ => by rw [Idele.count_idealOf])


end NK.CFTLib.ARL
