import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.CompletionLocalField
import Submission.Work.LocalFields.exists_pow_eq_of_one_sub_lt_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

open scoped Valued WithZero

namespace Work.LocalFields

/-- **Step 1**: a `ℤᐧ`-valued valuation on a non-archimedean local field is trivial on the
group of `1`-units (the elements of `v`-adic absolute value `< 1` from `1`).

Every `1`-unit is an `n`-th power for every `n` coprime to the residue characteristic `p`
(`Work.LocalFields.exists_pow_eq_of_one_sub_lt_one`), so its value `WithZero.exp a` has
`n ∣ a` for all such `n`; the numbers `p ^ N + 1` (`N ≥ 1`) are all coprime to `p` and
unbounded, forcing `a = 0`. -/
lemma valuation_eq_one_of_val_one_sub_lt_one {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [IsLocalField k]
    (μ : Valuation k (WithZero (Multiplicative ℤ))) {y : k}
    (hy : Valued.v (y - 1) < 1) : μ y = 1 := by
  haveI : Fintype 𝓀[k] := Fintype.ofFinite _
  -- the residue characteristic `p = ringChar 𝓀[k]` is a prime, hence `> 1`
  have hprime : Nat.Prime (ringChar 𝓀[k]) := by
    haveI : CharP 𝓀[k] (ringChar 𝓀[k]) := ringChar.charP _
    exact CharP.char_is_prime 𝓀[k] (ringChar 𝓀[k])
  have hp : 1 < ringChar 𝓀[k] := hprime.one_lt
  -- `y ≠ 0`, since `v y` is the nonzero value `1` at `y = 0`
  have hy0 : y ≠ 0 := by
    intro h0
    have h1 : Valued.v (y - 1) = 1 := by
      rw [h0, show (0 : k) - 1 = -1 by ring, Valuation.map_neg, map_one]
    rw [h1] at hy; exact lt_irrefl 1 hy
  have hμy0 : μ y ≠ 0 := (Valuation.ne_zero_iff μ).mpr hy0
  set a : ℤ := (μ y).log with ha
  -- For each `N ≥ 1`, `n = p ^ N + 1` is coprime to `p` and `n ∣ a`.
  have key : ∀ N : ℕ, 1 ≤ N → ((ringChar 𝓀[k] ^ N + 1 : ℕ) : ℤ) ∣ a := by
    intro N hN
    set n : ℕ := ringChar 𝓀[k] ^ N + 1 with hn
    have hcop : Nat.Coprime n (ringChar 𝓀[k]) := by
      have h1 : (ringChar 𝓀[k]).Coprime (1 + ringChar 𝓀[k] ^ (N - 1) * ringChar 𝓀[k]) :=
        (Nat.coprime_add_mul_right_right _ _ _).mpr (Nat.coprime_one_right _)
      have h2 : 1 + ringChar 𝓀[k] ^ (N - 1) * ringChar 𝓀[k] = n := by
        rw [hn, ← pow_succ, Nat.sub_add_cancel hN, add_comm]
      rw [h2] at h1
      exact h1.symm
    obtain ⟨z, hz⟩ := exists_pow_eq_of_one_sub_lt_one hcop hy
    have hzlog : a = (n : ℤ) * (μ z).log := by
      rw [ha, ← hz, Valuation.map_pow, WithZero.log_pow, nsmul_eq_mul]
    exact ⟨(μ z).log, hzlog⟩
  -- Taking `N = |a| + 1` gives `p ^ N + 1 > |a|` together with `p ^ N + 1 ∣ a`, so `a = 0`.
  have hazero : a = 0 := by
    by_contra ha0
    have hapos : 0 < a.natAbs := Int.natAbs_pos.mpr ha0
    have hN : a.natAbs < ringChar 𝓀[k] ^ (a.natAbs + 1) :=
      lt_trans (Nat.lt_succ_self _)
        (Nat.lt_pow_self (n := a.natAbs + 1) (a := ringChar 𝓀[k]) hp)
    have hN1 : 1 ≤ a.natAbs + 1 := Nat.le_add_left 1 _
    have hdvd := key (a.natAbs + 1) hN1
    have hdvd2 : (ringChar 𝓀[k] ^ (a.natAbs + 1) + 1 : ℕ) ∣ a.natAbs := by
      have h := (Int.natAbs_dvd_natAbs).mpr hdvd
      simpa only [Int.natAbs_natCast] using h
    have hlt : a.natAbs < (ringChar 𝓀[k] ^ (a.natAbs + 1) + 1 : ℕ) := by omega
    have hzero : a.natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvd2 hlt
    omega
  calc μ y = WithZero.exp (μ y).log := (WithZero.exp_log hμy0).symm
    _ = WithZero.exp a := by rw [ha]
    _ = WithZero.exp 0 := by rw [hazero]
    _ = 1 := WithZero.exp_zero

/-- Let `K` be a number field with completion `K_v` at a finite prime `v`.  Then any
`ℤᐧ = WithZero (Multiplicative ℤ)`-valued valuation `μ` on `K_v` takes the value `1` on every
element of `K_v` of `v`-adic absolute value `1` (i.e. on every unit of `𝒪[K_v]`).

Proof sketch (both steps use only the local structure of `K_v`):

*Step 1 (`1`-units).* If `Valued.v (y - 1) < 1` then `μ y = 1`.
By `Work.LocalFields.exists_pow_eq_of_one_sub_lt_one`, for every `n` coprime to
`p := ringChar 𝓀[K_v]` there is `z` with `z ^ n = y`; hence `μ y = (μ z) ^ n`.
Writing `μ y = WithZero.exp a` and `μ z = WithZero.exp b` (`WithZero.exp_log`), this gives
`a = b * n`, so `n ∣ a`.  As `n = p ^ N + 1` (take `N ≥ 1`) is coprime to `p` for every `N`, and
`a : ℤ` is fixed, choosing `N` with `|a| < p ^ N + 1` forces `a = 0`, i.e. `μ y = 1`.

*Step 2 (units).* Let `x` have `Valued.v x = 1`, so `x ∈ 𝒪[K_v]` and `x` is a unit of `𝒪[K_v]`.
The residue field `𝓀[K_v]` is finite of cardinality `q = Nat.card 𝓀[K_v] ≥ 2`; the residue class of
`x` is nonzero, so by `FiniteField.pow_card_sub_one_eq_one`
`x ^ (q - 1) - 1 ∈ 𝔪[K_v]`, i.e. `Valued.v (x ^ (q - 1) - 1) < 1`
(`Work.LocalFields.mem_maximalIdeal_iff_v_lt_one`).  By Step 1, `μ (x ^ (q - 1)) = 1`, i.e.
`(μ x) ^ (q - 1) = 1`; with `μ x = WithZero.exp a` this gives `a * (q - 1) = 0`, so `a = 0`. -/
theorem valuation_eq_one_of_val_eq_one {K : Type*} [Field K] [NumberField K]
    (v : Work.LocalFields.FinitePrime K)
    (μ : Valuation (Work.LocalFields.Completion K v) (WithZero (Multiplicative ℤ)))
    {x : Work.LocalFields.Completion K v} (hx : Valued.v x = 1) : μ x = 1 := by
  haveI : Fintype 𝓀[Work.LocalFields.Completion K v] := Fintype.ofFinite _
  set q : ℕ := Fintype.card 𝓀[Work.LocalFields.Completion K v] with hq
  -- `x` lies in the ring of integers `𝒪[K_v]` and is a unit there
  have hxle : Valued.v x ≤ 1 := le_of_eq hx
  set u : 𝒪[Work.LocalFields.Completion K v] :=
    ⟨x, (Valuation.mem_integer_iff (Valued.v) x).mpr hxle⟩ with hu_def
  have hu : (u : Work.LocalFields.Completion K v) = x := rfl
  have hu_unit : IsUnit u := by
    rw [(Valuation.integer.integers (Valued.v)).isUnit_iff_valuation_eq_one]
    exact hx
  -- the residue class of `x` in the (finite) residue field is nonzero, so its `(q - 1)`-st power
  -- is `1`; hence `x ^ (q - 1) - 1` lies in the maximal ideal
  have hr_ne : IsLocalRing.residue (𝒪[Work.LocalFields.Completion K v]) u ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit u).mpr hu_unit
  have hqone : 1 < q := by
    rw [hq, ← Nat.card_eq_fintype_card]; exact Finite.one_lt_card
  have hr_pow : (IsLocalRing.residue (𝒪[Work.LocalFields.Completion K v]) u) ^ (q - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ hr_ne
  have hmem : (u ^ (q - 1) - 1 : 𝒪[Work.LocalFields.Completion K v]) ∈
      𝓂[Work.LocalFields.Completion K v] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    rw [map_sub, map_pow, map_one, hr_pow, sub_self]
  have hlt : Valued.v (x ^ (q - 1) - 1) < 1 := by
    have h := (mem_maximalIdeal_iff_v_lt_one (k := Work.LocalFields.Completion K v)).mp hmem
    rwa [show ((u ^ (q - 1) - 1 : 𝒪[Work.LocalFields.Completion K v]) :
        Work.LocalFields.Completion K v) = x ^ (q - 1) - 1 by
      push_cast; rw [hu]] at h
  have hstep : μ (x ^ (q - 1)) = 1 := valuation_eq_one_of_val_one_sub_lt_one μ hlt
  -- deduce `(μ x) ^ (q - 1) = 1`, i.e. `(q - 1) • (μ x).log = 0`, so `(μ x).log = 0`
  have hx0 : x ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact zero_ne_one hx
  have hlog : (q - 1) • (μ x).log = 0 := by
    have h2 : μ x ^ (q - 1) = 1 := by
      rw [← Valuation.map_pow]; exact hstep
    have h3 := congrArg WithZero.log h2
    rwa [WithZero.log_pow, WithZero.log_one] at h3
  have hq1 : ((q - 1 : ℕ) : ℤ) ≠ 0 := by
    have : q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hqone
    exact_mod_cast this
  have hb0 : (μ x).log = 0 := by
    rw [nsmul_eq_mul] at hlog
    rcases mul_eq_zero.mp hlog with h | h
    · exact absurd h hq1
    · exact h
  rw [show μ x = WithZero.exp (μ x).log from
      (WithZero.exp_log ((Valuation.ne_zero_iff μ).mpr hx0)).symm,
    hb0, WithZero.exp_zero]

end Work.LocalFields
