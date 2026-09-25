import Mathlib
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Units.isProP_principalUnits

open scoped WithZero

namespace NK.TameStructureDeep.Tame

set_option linter.style.haveILetI false

/-- A nonzero element of `ℤᵐ⁰` that is an `ℓ^K`-th power for every `K` is `1`: the element has
finite "exponent" `WithZero.log α`, which is divisible by `ℓ^K` for every `K`. -/
private theorem eq_one_of_forall_pow_eq {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {α : ℤᵐ⁰} (hα : α ≠ 0)
    (h : ∀ K : ℕ, ∃ β : ℤᵐ⁰, β ^ (ℓ ^ K) = α) : α = 1 := by
  set e : ℤ := WithZero.log α with he
  have hdiv : ∀ K : ℕ, ((ℓ : ℤ) ^ K) ∣ e := by
    intro K
    obtain ⟨β, hβ⟩ := h K
    have hlog : (ℓ : ℤ) ^ K * WithZero.log β = e := by
      have h1 := congrArg WithZero.log hβ
      rw [WithZero.log_pow, nsmul_eq_mul, Nat.cast_pow] at h1
      rw [← he] at h1
      exact h1
    rw [← hlog]
    exact dvd_mul_right _ _
  obtain ⟨K, hK⟩ : ∃ K : ℕ, |e| < (ℓ : ℤ) ^ K := by
    refine ⟨e.natAbs + 1, ?_⟩
    have h2 : (e.natAbs : ℤ) < (2 : ℤ) ^ (e.natAbs + 1) := by
      have h' : e.natAbs < 2 ^ (e.natAbs + 1) := by
        have := Nat.lt_two_pow_self (n := e.natAbs + 1)
        omega
      exact_mod_cast h'
    have h3 : (2 : ℤ) ^ (e.natAbs + 1) ≤ (ℓ : ℤ) ^ (e.natAbs + 1) :=
      pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hℓ) _
    calc |e| = (e.natAbs : ℤ) := (Int.natCast_natAbs e).symm
      _ < (2 : ℤ) ^ (e.natAbs + 1) := h2
      _ ≤ (ℓ : ℤ) ^ (e.natAbs + 1) := h3
  have he0 : e = 0 := Int.eq_zero_of_abs_lt_dvd (hdiv K) hK
  rw [← WithZero.exp_log hα, ← he, he0, WithZero.exp_zero]

/-- The image of a principal unit `z ∈ U¹ = 1 + 𝔪` of `𝒪_κ` under `κ → E` lies in a discrete
valuation ring `A` of `E`.  Indeed `U¹` is `ℓ`-divisible for every prime `ℓ` different from the
residue characteristic (`exists_pow_eq_of_mem_principalUnits`), so the value of `f z` under the
valuation of `A` is an `ℓ^K`-th power for every `K`, hence (in the value group `ℤᵐ⁰`) equal to
`1`. -/
private theorem principalUnits_algebraMap_mem {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (𝔭.adicCompletion K) E]
    (A : ValuationSubring E) [IsDiscreteValuationRing A]
    (z : NK.LocalInputs.principalUnits K 𝔭) :
    algebraMap (𝔭.adicCompletion K) E
      (((z : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
        𝔭.adicCompletion K) ∈ A := by
  -- the discrete valuation of `A`
  let vA : Valuation E ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation E
  have hvA : vA.valuationSubring = A := by
    ext x
    rw [Valuation.mem_valuationSubring_iff]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := A) (K := E) h
      exact ha ▸ a.2
    · intro hx
      have := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
        (K := E) (IsDiscreteValuationRing.maximalIdeal A) ⟨x, hx⟩
      simpa [vA] using this
  -- a prime `ℓ` different from the residue characteristic
  obtain ⟨ℓ, hℓge, hℓprime⟩ := Nat.exists_infinite_primes (resCharAt 𝔭 + 1)
  have hℓne : ℓ ≠ resCharAt 𝔭 := by omega
  have hℓ2 : 2 ≤ ℓ := hℓprime.two_le
  have hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
      (resCharAt 𝔭) := NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  have hpprime : (resCharAt 𝔭).Prime :=
    NK.TameStructureDeep.Units.prime_of_charP_residueField 𝔭 hchar
  -- `z` is an `ℓ^N`-th power in `U¹` for every `N`
  have hiter : ∀ N : ℕ, ∃ w : ↥(NK.LocalInputs.principalUnits K 𝔭), w ^ (ℓ ^ N) = z := by
    intro N
    induction N with
    | zero => exact ⟨z, by simp⟩
    | succ N ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨w', hw'⟩ :=
        NK.TameStructureDeep.Units.exists_pow_eq_of_mem_principalUnits 𝔭
          hchar hpprime hℓprime hℓne w
      exact ⟨w', by rw [pow_succ', pow_mul, hw', hw]⟩
  -- its value is `1`
  have hval : vA (algebraMap (𝔭.adicCompletion K) E
      (((z : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
        𝔭.adicCompletion K)) = 1 := by
    refine eq_one_of_forall_pow_eq hℓ2 ?_ ?_
    · rw [Valuation.ne_zero_iff]
      intro h0
      have hz0 : ((z : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) = 0 := by
        refine Subtype.ext ?_
        show (((z : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
          𝔭.adicCompletion K) = 0
        apply (algebraMap (𝔭.adicCompletion K) E).injective
        simpa using h0
      exact (z : (𝔭.adicCompletionIntegers K)ˣ).ne_zero hz0
    · intro N
      obtain ⟨w, hw⟩ := hiter N
      refine ⟨vA (algebraMap (𝔭.adicCompletion K) E
        (((w : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
          𝔭.adicCompletion K)), ?_⟩
      have hw' : (((w : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
            𝔭.adicCompletion K) ^ (ℓ ^ N)
          = (((z : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
            𝔭.adicCompletion K) := by
        have := congrArg (fun t : ↥(NK.LocalInputs.principalUnits K 𝔭) =>
          (((t : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
            𝔭.adicCompletion K)) hw
        simpa using this
      rw [← Valuation.map_pow, ← map_pow, hw']
  rw [← hvA, Valuation.mem_valuationSubring_iff]
  rw [hval]

theorem dvr_comap_eq_adicCompletionIntegers {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {E : Type*} [Field E] [Algebra (𝔭.adicCompletion K) E]
    [Algebra.IsAlgebraic (𝔭.adicCompletion K) E]
    (A : ValuationSubring E) [IsDiscreteValuationRing A] :
    A.comap (algebraMap (𝔭.adicCompletion K) E) = 𝔭.adicCompletionIntegers K := by
  classical
  -- `A` is a proper valuation subring, since it is a discrete valuation ring
  have hAne : A ≠ ⊤ := by
    intro htop
    rw [ValuationSubring.eq_top_iff] at htop
    obtain ⟨x, hxm, hx0⟩ := (Submodule.ne_bot_iff (IsLocalRing.maximalIdeal A)).mp
      (IsDiscreteValuationRing.not_a_field A)
    refine htop ((Valuation.isNontrivial_iff_exists_lt_one A.valuation).mpr
      ⟨(x : E), ?_, ?_⟩)
    · exact fun h0 => hx0 (Subtype.ext h0)
    · exact (ValuationSubring.valuation_lt_one_iff A x).mp hxm
  -- hence so is its contraction `R = A ∩ κ`
  have hRne : A.comap (algebraMap (𝔭.adicCompletion K) E) ≠ ⊤ := fun h =>
    hAne (Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top A
      (inferInstance : Algebra.IsAlgebraic (𝔭.adicCompletion K) E) h)
  -- every unit of `𝒪_κ` maps into `A`
  have hunits : ∀ u : (𝔭.adicCompletionIntegers K)ˣ,
      algebraMap (𝔭.adicCompletion K) E ((u : 𝔭.adicCompletionIntegers K) :
        𝔭.adicCompletion K) ∈ A := by
    intro u
    haveI hfin : Finite (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
      NK.TameStructureDeep.Units.finite_residueField_adicCompletionIntegers 𝔭
    letI hft : Fintype (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) :=
      Fintype.ofFinite _
    have hq2 : 2 ≤ Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    -- `u ^ (#k - 1)` is a principal unit
    have hmem : u ^ (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) - 1) ∈
        NK.LocalInputs.principalUnits K 𝔭 := by
      rw [NK.LocalInputs.principalUnits, MonoidHom.mem_ker]
      have hcard : Fintype.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))ˣ =
          Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) - 1 := by
        rw [Fintype.card_units, Nat.card_eq_fintype_card]
      rw [← hcard, MonoidHom.map_pow]
      exact pow_card_eq_one
    have h1 : (algebraMap (𝔭.adicCompletion K) E
        ((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) ^
          (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) - 1) ∈ A := by
      have h := principalUnits_algebraMap_mem 𝔭 A ⟨u ^ _, hmem⟩
      have h2 : ((((⟨u ^ _, hmem⟩ : ↥(NK.LocalInputs.principalUnits K 𝔭)) :
            (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
            𝔭.adicCompletion K)
          = (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
            𝔭.adicCompletion K) ^
            (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) - 1) := by
        simp only [Units.val_pow_eq_pow_val]
        exact Subring.coe_pow _ _ _
      rw [h2, map_pow] at h
      exact h
    -- hence `f u` is integral over `A`, so lies in `A`
    have hInt : IsIntegral A ((algebraMap (𝔭.adicCompletion K) E
        ((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) ^
          (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) - 1)) := by
      have h := isIntegral_algebraMap (R := A) (A := E) (x := ⟨_, h1⟩)
      simpa using h
    have hInt2 : IsIntegral A (algebraMap (𝔭.adicCompletion K) E
        ((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) :=
      IsIntegral.of_pow (by omega) hInt
    haveI hIC : IsIntegrallyClosedIn ↥A.toSubring E :=
      Subring.isIntegrallyClosedIn_iff.mpr fun z hz =>
        LocalSubring.mem_of_isMax_of_isIntegral A.isMax_toLocalSubring hz
    exact Subring.isIntegrallyClosedIn_iff.mp hIC hInt2
  -- a uniformiser of `𝒪_κ`, and the residue characteristic
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible (𝔭.adicCompletionIntegers K)
  have hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
      (resCharAt 𝔭) := NK.Mine.charP_ringChar_residueField_adicCompletion 𝔭
  have hp0unit : ¬ IsUnit ((resCharAt 𝔭 : ℕ) : 𝔭.adicCompletionIntegers K) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have h0 : IsLocalRing.residue (𝔭.adicCompletionIntegers K)
        ((resCharAt 𝔭 : ℕ) : 𝔭.adicCompletionIntegers K) = 0 := by
      rw [map_natCast]
      exact CharP.cast_eq_zero _ _
    simpa using h0
  have hp0ne : ((resCharAt 𝔭 : ℕ) : 𝔭.adicCompletionIntegers K) ≠ 0 :=
    (Nat.cast_ne_zero).mpr (NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭).ne_zero
  obtain ⟨n₀, u₀, hu₀⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0ne hπirr
  have hn₀ : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hu₀
      exact hp0unit (hu₀ ▸ u₀.isUnit)
    · exact h
  -- `π` maps into `A`
  have hpi : algebraMap (𝔭.adicCompletion K) E
      ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) ∈ A := by
    let vA : Valuation E ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal A).valuation E
    have hvA : vA.valuationSubring = A := by
      ext x
      rw [Valuation.mem_valuationSubring_iff]
      constructor
      · intro h
        obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one (A := A) (K := E) h
        exact ha ▸ a.2
      · intro hx
        have := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
          (K := E) (IsDiscreteValuationRing.maximalIdeal A) ⟨x, hx⟩
        simpa [vA] using this
    have hmem_iff : ∀ x : E, vA x ≤ 1 ↔ x ∈ A := fun x => by
      rw [← hvA, Valuation.mem_valuationSubring_iff]
    -- the value relation coming from `resCharAt 𝔭 = u₀ * π ^ n₀`
    have hrel : vA (algebraMap (𝔭.adicCompletion K) E
          (((resCharAt 𝔭 : ℕ) : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) =
        vA (algebraMap (𝔭.adicCompletion K) E
          ((u₀ : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) *
        (vA (algebraMap (𝔭.adicCompletion K) E
          ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K))) ^ n₀ := by
      have hcast : algebraMap (𝔭.adicCompletion K) E
            (((resCharAt 𝔭 : ℕ) : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) =
          algebraMap (𝔭.adicCompletion K) E
              ((u₀ : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) *
            (algebraMap (𝔭.adicCompletion K) E
              ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) ^ n₀ := by
        have h := congrArg (fun t : 𝔭.adicCompletionIntegers K =>
          algebraMap (𝔭.adicCompletion K) E (t : 𝔭.adicCompletion K)) hu₀
        simpa using h
      rw [hcast, map_mul, map_pow]
    -- the value of `u₀` is `1`
    have hu0val : vA (algebraMap (𝔭.adicCompletion K) E
        ((u₀ : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) = 1 := by
      have hXY : (↑u₀ : 𝔭.adicCompletionIntegers K) *
          (↑(u₀⁻¹) : 𝔭.adicCompletionIntegers K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hprod : vA (algebraMap (𝔭.adicCompletion K) E
            ((u₀ : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K))
          * vA (algebraMap (𝔭.adicCompletion K) E
            (((u₀⁻¹ : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
              𝔭.adicCompletion K)) = 1 := by
        rw [← Valuation.map_mul, ← map_mul, ← Subring.coe_mul, hXY, Subring.coe_one, map_one,
          Valuation.map_one]
      have hle1 : vA (algebraMap (𝔭.adicCompletion K) E
          ((u₀ : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) ≤ 1 :=
        (hmem_iff _).mpr (hunits u₀)
      have hle2 : (vA (algebraMap (𝔭.adicCompletion K) E
          ((u₀ : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)))⁻¹ ≤ 1 := by
        have hu0inv : vA (algebraMap (𝔭.adicCompletion K) E
              (((u₀⁻¹ : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
                𝔭.adicCompletion K))
            = (vA (algebraMap (𝔭.adicCompletion K) E
              ((u₀ : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)))⁻¹ :=
          eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)
        rw [← hu0inv]
        exact (hmem_iff _).mpr (hunits u₀⁻¹)
      have hpos : 0 < vA (algebraMap (𝔭.adicCompletion K) E
          ((u₀ : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) := by
        rw [Valuation.pos_iff]
        intro h0
        have h1 : (((u₀ : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
            𝔭.adicCompletion K) = 0 :=
          (algebraMap (𝔭.adicCompletion K) E).injective (by simpa using h0)
        exact u₀.ne_zero (Subtype.ext h1)
      exact le_antisymm hle1 ((inv_le_one₀ hpos).mp hle2)
    -- the value of `resCharAt 𝔭` is at most `1`
    have hp0le : vA (algebraMap (𝔭.adicCompletion K) E
        (((resCharAt 𝔭 : ℕ) : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) ≤ 1 := by
      refine (hmem_iff _).mpr ?_
      rw [show algebraMap (𝔭.adicCompletion K) E
          ((((resCharAt 𝔭 : ℕ) : 𝔭.adicCompletionIntegers K)) : 𝔭.adicCompletion K) =
          ((resCharAt 𝔭 : ℕ) : E) from map_natCast _ _]
      exact natCast_mem (s := A) _
    -- conclude the value of `π`
    have h3 : (vA (algebraMap (𝔭.adicCompletion K) E
        ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K))) ^ n₀ ≤ 1 := by
      have h4 := hp0le
      rw [hrel, hu0val, one_mul] at h4
      exact h4
    have : vA (algebraMap (𝔭.adicCompletion K) E
        ((π : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K)) ≤ 1 := by
      by_contra hcon
      rw [not_le] at hcon
      exact absurd h3 (not_le.mpr (one_lt_pow₀ hcon (by omega)))
    exact (hmem_iff _).mp this
  -- finally `𝒪_κ ≤ R`
  have hle : 𝔭.adicCompletionIntegers K ≤ A.comap (algebraMap (𝔭.adicCompletion K) E) := by
    intro x hx
    rw [ValuationSubring.mem_comap]
    by_cases hx0 : x = 0
    · rw [hx0, map_zero]
      exact A.zero_mem
    · have hxO : (⟨x, hx⟩ : 𝔭.adicCompletionIntegers K) ≠ 0 := fun h =>
        hx0 (by simpa using congrArg Subtype.val h)
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hxO hπirr
      have hcast : x = ((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) *
          (((π : 𝔭.adicCompletionIntegers K)) : 𝔭.adicCompletion K) ^ n := by
        have h := congrArg (fun t : 𝔭.adicCompletionIntegers K => (t : 𝔭.adicCompletion K)) hu
        rw [show ((⟨x, hx⟩ : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) = x from rfl] at h
        simpa using h
      rw [hcast, map_mul, map_pow]
      exact mul_mem (hunits u) (pow_mem hpi n)
  rcases ValuationSubring.eq_self_or_eq_top_of_le (A := 𝔭.adicCompletionIntegers K)
      (B := A.comap (algebraMap (𝔭.adicCompletion K) E)) hle with h | h
  · exact h.symm
  · exact absurd h hRne

end NK.TameStructureDeep.Tame
