import Mathlib
import Submission.Work.Kummer.Defs
import Submission.Work.SSGRoute.LocalFieldArith.Prelude
import Submission.Work.SSGRoute.LocalFieldArith.principalUnits_deep_mem_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero
open IsDedekindDomain

namespace Work.SSGRoute.LocalFieldArith

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- `Work.Kummer.nthPowerSubgroup` is the range of the `p`-th power monoid homomorphism. -/
theorem nthPowerSubgroup_eq_range_powMonoidHom (p : ℕ) (G : Type*) [CommGroup G] :
    Work.Kummer.nthPowerSubgroup p G = (powMonoidHom p : G →* G).range := by
  apply le_antisymm
  · intro x hx
    rw [Work.Kummer.mem_nthPowerSubgroup] at hx
    obtain ⟨y, hy⟩ := hx
    rw [MonoidHom.mem_range]
    exact ⟨y, by rw [powMonoidHom_apply]; exact hy⟩
  · intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨y, hy⟩ := hx
    rw [Work.Kummer.mem_nthPowerSubgroup]
    exact ⟨y, by rw [powMonoidHom_apply] at hy; exact hy⟩

private theorem exists_exp_neg_val_prime (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (p : ℕ) [Fact p.Prime] :
    ∃ e : ℕ, (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
        ((p : ℕ) : 𝔭.adicCompletion K) = WithZero.exp (-(e : ℤ)) := by
  have hp : p.Prime := Fact.out
  have hchar : CharZero (𝔭.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion 𝔭
  have hnat_val : ∀ n : ℕ, (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
      ((n : ℕ) : 𝔭.adicCompletion K) ≤ 1 := by
    intro n; induction n with
    | zero => rw [Nat.cast_zero, Valuation.map_zero]; exact zero_le
    | succ k ih =>
      rw [Nat.cast_succ]
      refine Valuation.map_add_le _ ih ?_
      rw [Valuation.map_one]
  have hne : ((p : ℕ) : 𝔭.adicCompletion K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hvalne : (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
      ((p : ℕ) : 𝔭.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  set m : ℤ := WithZero.log ((Valued.v :
      Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
      ((p : ℕ) : 𝔭.adicCompletion K)) with hm
  have hexpm : (Valued.v : Valuation (𝔭.adicCompletion K) (WithZero (Multiplicative ℤ)))
      ((p : ℕ) : 𝔭.adicCompletion K) = WithZero.exp m := by
    rw [hm]; exact (WithZero.exp_log hvalne).symm
  have hmle : m ≤ 0 := by
    have h : WithZero.exp m ≤ WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_zero, ← hexpm]; exact hnat_val p
    exact WithZero.exp_le_exp.mp h
  refine ⟨m.natAbs, ?_⟩
  have hcast : (((m.natAbs : ℕ) : ℤ)) = -m := Int.ofNat_natAbs_of_nonpos hmle
  rw [hexpm, hcast]
  congr 1
  ring

private theorem natCard_unitGroup_quot_pow_eq {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (p : ℕ) :
    Nat.card ((𝔭.adicCompletionIntegers K).unitGroup ⧸
        (powMonoidHom p : (𝔭.adicCompletionIntegers K).unitGroup →*
          (𝔭.adicCompletionIntegers K).unitGroup).range) =
      Nat.card ((𝔭.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom p : (𝔭.adicCompletionIntegers K)ˣ →*
          (𝔭.adicCompletionIntegers K)ˣ).range) := by
  have he : ((powMonoidHom p : (𝔭.adicCompletionIntegers K).unitGroup →*
        (𝔭.adicCompletionIntegers K).unitGroup).range).map
        (ValuationSubring.unitGroupMulEquiv (𝔭.adicCompletionIntegers K)) =
      (powMonoidHom p : (𝔭.adicCompletionIntegers K)ˣ →*
        (𝔭.adicCompletionIntegers K)ˣ).range := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨k, hk, hkx⟩ := hx
      rw [MonoidHom.mem_range] at hk ⊢
      obtain ⟨g, hg⟩ := hk
      refine ⟨ValuationSubring.unitGroupMulEquiv _ g, ?_⟩
      have hgk : g ^ p = k := by simpa only [powMonoidHom_apply] using hg
      rw [powMonoidHom_apply, ← map_pow, hgk]
      exact hkx
    · intro hx
      rw [MonoidHom.mem_range] at hx
      obtain ⟨k, hk⟩ := hx
      rw [Subgroup.mem_map]
      refine ⟨(ValuationSubring.unitGroupMulEquiv _).symm (k ^ p), ?_, ?_⟩
      · rw [MonoidHom.mem_range]
        exact ⟨(ValuationSubring.unitGroupMulEquiv _).symm k, by
          simp only [powMonoidHom_apply]
          rw [← map_pow]⟩
      · rw [← hk, powMonoidHom_apply]
        exact MulEquiv.apply_symm_apply _ _
  have hidx : ((powMonoidHom p : (𝔭.adicCompletionIntegers K).unitGroup →*
        (𝔭.adicCompletionIntegers K).unitGroup).range).index =
      ((powMonoidHom p : (𝔭.adicCompletionIntegers K)ˣ →*
        (𝔭.adicCompletionIntegers K)ˣ).range).index := by
    rw [← he, Subgroup.index_map_equiv]
  exact hidx

/-- **The `p`-power quotient of `κˣ` is `p` times that of `𝒪_κˣ`.**

Every unit of `κ = 𝔭.adicCompletion K` is `u · ϖ ^ m` with `u : 𝒪_κˣ` and `m : ℤ`
(`exists_units_mul_uniformizer_zpow_adicCompletion`), i.e. `κˣ ⧸ 𝒪_κˣ ≅ ℤ`; the `p`-th powers of
`κˣ` correspond to `(𝒪_κˣ)^p` together with `pℤ`, so `κˣ ⧸ (κˣ)^p ≅ (𝒪_κˣ ⧸ (𝒪_κˣ)^p) × ℤ/pℤ`.

This is the `Nat.card` form; it is proved exactly as in
`NK.LocalInputs.PowerQuotient.natCard_KummerGroup_eq_pow_of_principalUnits`, whose step 2 is the
same computation, but without any hypothesis on `p` relative to the residue characteristic. -/
theorem natCard_units_adicCompletion_quot_pow_eq_mul
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (p : ℕ) (hp : p.Prime) :
    Nat.card ((𝔭.adicCompletion K)ˣ ⧸
        (powMonoidHom p : (𝔭.adicCompletion K)ˣ →* (𝔭.adicCompletion K)ˣ).range) =
      p * Nat.card ((𝔭.adicCompletionIntegers K)ˣ ⧸
        (powMonoidHom p : (𝔭.adicCompletionIntegers K)ˣ →*
          (𝔭.adicCompletionIntegers K)ˣ).range) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have htorZ : ∀ h : Multiplicative ℤ, h ^ p = 1 → h = 1 := by
    intro h hh
    have h2 : Multiplicative.ofAdd ((p : ℤ) * Multiplicative.toAdd h) = 1 := by
      rw [← Commons.NumberTheory.NumberField.Completion.ofAdd_pow_eq (Multiplicative.toAdd h) p,
        ← ofAdd_toAdd h]
      exact hh
    have h3 : (p : ℤ) * Multiplicative.toAdd h = 0 := by
      have h2' := congrArg Multiplicative.toAdd h2
      rw [toAdd_ofAdd] at h2'
      rw [show Multiplicative.toAdd (1 : Multiplicative ℤ) = 0 from rfl] at h2'
      exact h2'
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h4 : Multiplicative.toAdd h = 0 := mul_left_cancel₀ hp0 (by rw [h3, mul_zero])
    apply Multiplicative.ext
    rw [show Multiplicative.toAdd (1 : Multiplicative ℤ) = 0 from rfl]
    exact h4
  have hker : (Commons.NumberTheory.NumberField.Completion.unitsValLog
        (𝔭.adicCompletion K)).ker = (𝔭.adicCompletionIntegers K).unitGroup := by
    simpa [Commons.NumberTheory.NumberField.Completion.adicUnitsVal] using
      Commons.NumberTheory.NumberField.Completion.adicUnitsVal_eq_unitGroup K 𝔭
  have h := Commons.NumberTheory.NumberField.Completion.natCard_quot_powMonoidHom_eq_mul
      (Commons.NumberTheory.NumberField.Completion.unitsValLog (𝔭.adicCompletion K))
      (Commons.NumberTheory.NumberField.Completion.unitsValLog_adicCompletion_surjective K 𝔭) p htorZ
  rw [Commons.NumberTheory.NumberField.Completion.natCard_multiplicative_int_quot_pow p] at h
  rw [hker] at h
  rw [natCard_unitGroup_quot_pow_eq 𝔭 p] at h
  exact h

/-- **The units of a `𝔭`-adic completion modulo `p`-th powers are finite.**

For a number field `K`, a finite prime `𝔭` of `K` and a prime `p`, the quotient of the unit group
`κˣ` of the completion `κ = 𝔭.adicCompletion K` by its subgroup of `p`-th powers is finite.

The proof is the one described in the docstring of the statement.  Fix `M ≥ 1` and the `p`-adic
exponential/logarithm of `κ` on the ball `v x ≤ exp (-M)`.  Writing `v p = exp (-e)`, the
logarithm identifies the level-`M` principal units with the additive group `𝔪^M`, and
multiplication by `p` maps `𝔪^M` onto `𝔪^(M+e)`; hence `pu 𝔭 (M+e) ≤ (𝒪_κˣ)^p`
(`principalUnits_deep_mem_pow`).  Since the level-`(M+e)` principal units have finite index in
`𝒪_κˣ`, the subgroup `(𝒪_κˣ)^p` does too, so `𝒪_κˣ ⧸ (𝒪_κˣ)^p` is finite.  Finally
`κˣ ⧸ (κˣ)^p` is `p` times `𝒪_κˣ ⧸ (𝒪_κˣ)^p`
(`natCard_units_adicCompletion_quot_pow_eq_mul`), hence finite as well. -/
theorem finite_units_quotient_adicCompletion (K : Type) [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (p : ℕ) [Fact p.Prime] :
    Finite ((𝔭.adicCompletion K)ˣ ⧸ Work.Kummer.nthPowerSubgroup p ((𝔭.adicCompletion K)ˣ)) := by
  have hp : p.Prime := Fact.out
  -- The exponential/logarithm of `κ` at some level `M ≥ 1`.
  obtain ⟨M, hM, D⟩ := NK.LocalInputs.PowerQuotient.exists_logData (K := K) 𝔭
  obtain ⟨D⟩ := D
  obtain ⟨e, he⟩ := exists_exp_neg_val_prime (K := K) 𝔭 p
  -- The deep principal units are `p`-th powers, so `(𝒪_κˣ)^p ⊇ pu 𝔭 (M + e)`.
  have hle : NK.LocalInputs.PowerQuotient.pu 𝔭 (M + e) ≤
      Work.Kummer.nthPowerSubgroup p ((𝔭.adicCompletionIntegers K)ˣ) := by
    intro u hu
    obtain ⟨y, hy⟩ := principalUnits_deep_mem_pow 𝔭 D p he hu
    exact Work.Kummer.mem_nthPowerSubgroup.mpr ⟨y, hy⟩
  -- The level-`(M+e)` principal units have finite index in `𝒪_κˣ`.
  obtain ⟨U, hU, hUfin⟩ :=
    Commons.NumberTheory.NumberField.Completion.finiteIndex_principalUnits_adicCompletionIntegers
      (K := K) 𝔭 (M + e)
  have hUpu : U = NK.LocalInputs.PowerQuotient.pu 𝔭 (M + e) := by
    ext u
    rw [hU u, NK.LocalInputs.PowerQuotient.mem_pu_iff]
    exact Iff.rfl
  haveI hpu_fin : (NK.LocalInputs.PowerQuotient.pu 𝔭 (M + e)).FiniteIndex := hUpu ▸ hUfin
  -- hence `(𝒪_κˣ)^p` has finite index, and `𝒪_κˣ ⧸ (𝒪_κˣ)^p` is finite.
  haveI hO_fin : (Work.Kummer.nthPowerSubgroup p ((𝔭.adicCompletionIntegers K)ˣ)).FiniteIndex :=
    Subgroup.finiteIndex_of_le hle
  have hFinO : Finite ((𝔭.adicCompletionIntegers K)ˣ ⧸
      Work.Kummer.nthPowerSubgroup p ((𝔭.adicCompletionIntegers K)ˣ)) :=
    Subgroup.finite_quotient_of_finiteIndex
  -- Finally `κˣ ⧸ (κˣ)^p` is `p` times `𝒪_κˣ ⧸ (𝒪_κˣ)^p`, hence finite.
  have hcard := natCard_units_adicCompletion_quot_pow_eq_mul (K := K) 𝔭 p hp
  rw [← nthPowerSubgroup_eq_range_powMonoidHom p ((𝔭.adicCompletion K)ˣ),
    ← nthPowerSubgroup_eq_range_powMonoidHom p ((𝔭.adicCompletionIntegers K)ˣ)] at hcard
  have hneO : Nat.card ((𝔭.adicCompletionIntegers K)ˣ ⧸
      Work.Kummer.nthPowerSubgroup p ((𝔭.adicCompletionIntegers K)ˣ)) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1⟩, hFinO⟩
  have hneK : Nat.card ((𝔭.adicCompletion K)ˣ ⧸
      Work.Kummer.nthPowerSubgroup p ((𝔭.adicCompletion K)ˣ)) ≠ 0 := by
    rw [hcard]
    exact mul_ne_zero hp.ne_zero hneO
  exact (Nat.card_ne_zero.mp hneK).2

end

end Work.SSGRoute.LocalFieldArith
