/-
Workaround module: copy of `Submission/Work/ZeroFreeTables/lam0w/PrincipalAux.lean`.
The original currently does not compile in this workspace (four tactic steps need small repairs
in a recently changed Mathlib: `div_le_iff₀` produces `a ≤ c * b`, `mul_le_mul_of_nonneg_left`
instead of `mul_lt_mul_of_pos_left`, and one `ring` is redundant), and it is a dependency of the
`principalBound4` chain, so a `sorry`-free, compiling copy is kept here.  The declarations
`absorbArith` and `primeSumBound` are renamed with the `_fm` suffix; the mathematical content is
identical.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.lam0w.PrincipalDefs
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le

open DirichletCharacter Complex Filter
open scoped BigOperators Topology

noncomputable section

namespace Work.ZeroFreeTables.lam0w

/-! ## Arithmetic absorption -/

theorem absorbArith_fm {a e C D1 D2 D3 : ℝ} (ha : 0 < a) (he : 0 < e)
    (hC : 0 ≤ C) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3) :
    ∃ L₀ : ℝ, 3 ≤ L₀ ∧ a ≤ L₀ ∧ ∀ {L : ℝ}, L₀ ≤ L →
      (C + 2 * (D1 * (1 + (Real.log L) ^ 4)))
        + (2 * a) * (C + 4 * (D2 * (1 + (Real.log L) ^ 4)))
        + ((4 * a ^ 2) / 3) * (C + 16 * (D3 * (1 + (Real.log L) ^ 4)))
      ≤ e * L := by
  set A : ℝ := C + 2 * a * C + (4 * a ^ 2 / 3) * C with hA
  set B : ℝ := 2 * D1 + 8 * a * D2 + (64 * a ^ 2 / 3) * D3 with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hkey : ∀ L : ℝ,
      (C + 2 * (D1 * (1 + (Real.log L) ^ 4)))
        + (2 * a) * (C + 4 * (D2 * (1 + (Real.log L) ^ 4)))
        + ((4 * a ^ 2) / 3) * (C + 16 * (D3 * (1 + (Real.log L) ^ 4)))
      = A + B * (1 + (Real.log L) ^ 4) := by
    intro L; rw [hA, hB]; ring
  have htend : Tendsto (fun x : ℝ => Real.log x ^ 4 / x) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) 0 4 one_ne_zero
    simpa using h
  have hc0 : 0 < e / 2 / (max B 1) :=
    div_pos (div_pos he (by norm_num)) (lt_of_lt_of_le one_pos (le_max_right B 1))
  have hev : ∀ᶠ x : ℝ in atTop, Real.log x ^ 4 / x < e / 2 / (max B 1) := by
    have h := htend.eventually (isOpen_Iio.mem_nhds hc0)
    simpa [Set.mem_Iio] using h
  obtain ⟨L1, hL1⟩ := eventually_atTop.1 hev
  refine ⟨max (max 3 a) (max (4 * A / e) (max (4 * B / e) L1)), ?_, ?_, ?_⟩
  · exact le_trans (le_max_left 3 a) (le_max_left _ _)
  · exact le_trans (le_max_right 3 a) (le_max_left _ _)
  · intro L hL
    have h3 : (3 : ℝ) ≤ L :=
      le_trans (le_trans (le_max_left 3 a) (le_max_left _ _)) hL
    have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) h3
    have hAle : 4 * A / e ≤ L :=
      le_trans (le_trans (le_max_left (4 * A / e) (max (4 * B / e) L1))
        (le_max_right (max 3 a) (max (4 * A / e) (max (4 * B / e) L1)))) hL
    have hBle : 4 * B / e ≤ L :=
      le_trans (le_trans (le_trans (le_max_left (4 * B / e) L1)
        (le_max_right (4 * A / e) (max (4 * B / e) L1)))
        (le_max_right (max 3 a) (max (4 * A / e) (max (4 * B / e) L1)))) hL
    have hL1le : L1 ≤ L :=
      le_trans (le_trans (le_trans (le_max_right (4 * B / e) L1)
        (le_max_right (4 * A / e) (max (4 * B / e) L1)))
        (le_max_right (max 3 a) (max (4 * A / e) (max (4 * B / e) L1)))) hL
    have hAe : A ≤ e * L / 4 := by
      have : 4 * A ≤ L * e := (div_le_iff₀ he).mp hAle
      linarith
    have hBe : B ≤ e * L / 4 := by
      have : 4 * B ≤ L * e := (div_le_iff₀ he).mp hBle
      linarith
    have hlogL : Real.log L ^ 4 / L < e / 2 / (max B 1) := hL1 L hL1le
    have hlog4 : Real.log L ^ 4 < (e / 2 / (max B 1)) * L := by
      have := (div_lt_iff₀ hLpos).mp hlogL
      simpa [mul_comm] using this
    have hmaxpos : (0 : ℝ) < max B 1 := lt_of_lt_of_le one_pos (le_max_right B 1)
    have hratio : B / max B 1 ≤ 1 := (div_le_one hmaxpos).mpr (le_max_left B 1)
    have hBterm : B * Real.log L ^ 4 ≤ e * L / 2 := by
      have h1 : B * Real.log L ^ 4 ≤ B * ((e / 2 / (max B 1)) * L) :=
        mul_le_mul_of_nonneg_left hlog4.le hB0
      have h2 : B * ((e / 2 / (max B 1)) * L) ≤ e * L / 2 := by
        have heq : B * ((e / 2 / (max B 1)) * L) = (B / max B 1) * (e * L / 2) := by
          field_simp
          try ring
        rw [heq]
        exact mul_le_of_le_one_left (by positivity) hratio
      linarith [h1, h2]
    calc (C + 2 * (D1 * (1 + (Real.log L) ^ 4)))
          + (2 * a) * (C + 4 * (D2 * (1 + (Real.log L) ^ 4)))
          + ((4 * a ^ 2) / 3) * (C + 16 * (D3 * (1 + (Real.log L) ^ 4)))
        = A + B * (1 + (Real.log L) ^ 4) := hkey L
      _ = A + B + B * Real.log L ^ 4 := by ring
      _ ≤ e * L / 4 + e * L / 4 + e * L / 2 := by linarith [hAe, hBe, hBterm]
      _ = e * L := by ring

/-! ## The prime sums -/

private lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact Real.exp_one_lt_three

theorem primeSumBound_fm (D1 D2 D3 : ℝ) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hb1 : ∀ q : ℕ, 3 ≤ q → q.primeFactors.sum (fun p => Real.log (p : ℝ) / (p : ℝ))
        ≤ D1 * (Real.log (Real.log (q : ℝ))) ^ 2)
    (hb2 : ∀ q : ℕ, 3 ≤ q → q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        ≤ D2 * (Real.log (Real.log (q : ℝ))) ^ 3)
    (hb3 : ∀ q : ℕ, 3 ≤ q → q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
        ≤ D3 * (Real.log (Real.log (q : ℝ))) ^ 4)
    (q : ℕ) [NeZero q] {L : ℝ} (hLq : Real.log (q : ℝ) ≤ L) (hL3 : 3 ≤ L) :
    q.primeFactors.sum (fun p => Real.log (p : ℝ) / (p : ℝ))
        ≤ max D1 1 * (1 + (Real.log L) ^ 4)
      ∧ q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
        ≤ max D2 1 * (1 + (Real.log L) ^ 4)
      ∧ q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
        ≤ max D3 1 * (1 + (Real.log L) ^ 4) := by
  have ht0 : (0 : ℝ) ≤ (Real.log L) ^ 4 := by positivity
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hsmall : ∀ j : ℕ, q ≤ 2 →
      q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ j / (p : ℝ)) ≤ 1 := by
    intro j hq2
    have hp2 : ∀ p ∈ q.primeFactors, p = 2 := by
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      have hle : p ≤ q :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) (Nat.dvd_of_mem_primeFactors hp)
      have := hprime.two_le
      omega
    have hcard : q.primeFactors.card ≤ 1 :=
      Finset.card_le_one.mpr (fun a ha b hb => by rw [hp2 a ha, hp2 b hb])
    calc q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ j / (p : ℝ))
        ≤ q.primeFactors.sum (fun _ => (1 : ℝ)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [hp2 p hp]
          simp only [Nat.cast_ofNat]
          rw [div_le_one (by norm_num : (0:ℝ) < 2)]
          linarith [pow_le_one₀ hlog2 hlog2' (n := j)]
      _ = (q.primeFactors.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 1 := by exact_mod_cast hcard
  by_cases hq3 : 3 ≤ q
  · have hq3R : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have hlogq1 : 1 < Real.log (q : ℝ) :=
      lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hq3R)
    have ha_nn : 0 ≤ Real.log (Real.log (q : ℝ)) := Real.log_nonneg (le_of_lt hlogq1)
    have ha_le : Real.log (Real.log (q : ℝ)) ≤ Real.log L :=
      Real.log_le_log (by linarith) hLq
    have ht : (Real.log (Real.log (q : ℝ))) ^ 4 ≤ (Real.log L) ^ 4 :=
      pow_le_pow_left₀ ha_nn ha_le 4
    have h2 : (Real.log (Real.log (q : ℝ))) ^ 2 ≤ 1 + (Real.log L) ^ 4 := by
      by_cases h : Real.log (Real.log (q : ℝ)) ≤ 1
      · nlinarith [h, ha_nn]
      · have h24 : (Real.log (Real.log (q : ℝ))) ^ 2 ≤ (Real.log (Real.log (q : ℝ))) ^ 4 :=
          pow_le_pow_right₀ (le_of_lt (not_le.mp h)) (by norm_num)
        linarith
    have h3 : (Real.log (Real.log (q : ℝ))) ^ 3 ≤ 1 + (Real.log L) ^ 4 := by
      by_cases h : Real.log (Real.log (q : ℝ)) ≤ 1
      · nlinarith [h, ha_nn]
      · have h34 : (Real.log (Real.log (q : ℝ))) ^ 3 ≤ (Real.log (Real.log (q : ℝ))) ^ 4 :=
          pow_le_pow_right₀ (le_of_lt (not_le.mp h)) (by norm_num)
        linarith
    refine ⟨?_, ?_, ?_⟩
    · calc q.primeFactors.sum (fun p => Real.log (p : ℝ) / (p : ℝ))
          ≤ D1 * (Real.log (Real.log (q : ℝ))) ^ 2 := hb1 q hq3
        _ ≤ D1 * (1 + (Real.log L) ^ 4) := mul_le_mul_of_nonneg_left h2 hD1
        _ ≤ max D1 1 * (1 + (Real.log L) ^ 4) :=
            mul_le_mul_of_nonneg_right (le_max_left D1 1) (by positivity)
    · calc q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
          ≤ D2 * (Real.log (Real.log (q : ℝ))) ^ 3 := hb2 q hq3
        _ ≤ D2 * (1 + (Real.log L) ^ 4) := mul_le_mul_of_nonneg_left h3 hD2
        _ ≤ max D2 1 * (1 + (Real.log L) ^ 4) :=
            mul_le_mul_of_nonneg_right (le_max_left D2 1) (by positivity)
    · calc q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 3 / (p : ℝ))
          ≤ D3 * (Real.log (Real.log (q : ℝ))) ^ 4 := hb3 q hq3
        _ ≤ D3 * (1 + (Real.log L) ^ 4) := by
            apply mul_le_mul_of_nonneg_left _ hD3
            linarith [ht]
        _ ≤ max D3 1 * (1 + (Real.log L) ^ 4) :=
            mul_le_mul_of_nonneg_right (le_max_left D3 1) (by positivity)
  · have hq2 : q ≤ 2 := by omega
    have h1 : q.primeFactors.sum (fun p => Real.log (p : ℝ) / (p : ℝ)) ≤ 1 := by
      simpa [pow_one] using hsmall 1 hq2
    have h2 : q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) ≤ 1 := hsmall 2 hq2
    have h3 : q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) ≤ 1 := hsmall 3 hq2
    refine ⟨?_, ?_, ?_⟩
    · calc q.primeFactors.sum (fun p => Real.log (p : ℝ) / (p : ℝ)) ≤ 1 := h1
        _ ≤ max D1 1 * (1 + (Real.log L) ^ 4) := by
            have hge : (1:ℝ) ≤ max D1 1 := le_max_right D1 1
            nlinarith [hge, ht0]
    · calc q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 2 / (p : ℝ)) ≤ 1 := h2
        _ ≤ max D2 1 * (1 + (Real.log L) ^ 4) := by
            have hge : (1:ℝ) ≤ max D2 1 := le_max_right D2 1
            nlinarith [hge, ht0]
    · calc q.primeFactors.sum (fun p => (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) ≤ 1 := h3
        _ ≤ max D3 1 * (1 + (Real.log L) ^ 4) := by
            have hge : (1:ℝ) ≤ max D3 1 := le_max_right D3 1
            nlinarith [hge, ht0]

end Work.ZeroFreeTables.lam0w
