import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Submission.Commons.NumberTheory.ArithmeticFunction.vonMangoldt_eq_vaughan_sum

namespace Commons.NumberTheory.ArithmeticFunction

open Finset Nat
open scoped BigOperators

/-- If `b ∣ n` and `c ∣ n / b` then `c ∣ n` and `b ∣ n / c`. -/
private theorem dvd_div_of_dvd_of_dvd_div {b c n : ℕ} (hb : b ∣ n) (hc : c ∣ n / b) :
    c ∣ n ∧ b ∣ n / c := by
  obtain ⟨k, hk⟩ := hc
  have hn : n = c * (b * k) := by rw [← Nat.mul_div_cancel' hb, hk]; ring
  constructor
  · exact ⟨b * k, hn⟩
  · rcases eq_or_lt_of_le (Nat.zero_le c) with h | h
    · subst h
      simp only [zero_mul] at hn
      rw [hn]; exact dvd_zero b
    · rw [hn, Nat.mul_div_cancel_left _ h]; exact dvd_mul_right b k

/-- Exchange of the two `divisors` sums against the truncation thresholds `b ≤ T`, `T < c`. -/
private theorem sum_divisors_filter_mul_swap_aux (n T : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ b ∈ n.divisors.filter (fun b => b ≤ T),
        ∑ c ∈ (n / b).divisors.filter (fun c => T < c), F b c) =
      ∑ c ∈ n.divisors.filter (fun c => T < c),
        ∑ b ∈ (n / c).divisors.filter (fun b => b ≤ T), F b c := by
  have hL : (∑ b ∈ n.divisors.filter (fun b => b ≤ T),
        ∑ c ∈ (n / b).divisors.filter (fun c => T < c), F b c)
      = ∑ x ∈ (n.divisors.filter (fun b => b ≤ T)).sigma
            (fun b => (n / b).divisors.filter (fun c => T < c)), F x.1 x.2 :=
    Finset.sum_sigma' _ _ _
  have hR : (∑ c ∈ n.divisors.filter (fun c => T < c),
        ∑ b ∈ (n / c).divisors.filter (fun b => b ≤ T), F b c)
      = ∑ x ∈ (n.divisors.filter (fun c => T < c)).sigma
            (fun c => (n / c).divisors.filter (fun b => b ≤ T)), F x.2 x.1 :=
    Finset.sum_sigma' _ _ _
  rw [hL, hR]
  refine Finset.sum_bij (fun x _ => ⟨x.2, x.1⟩) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_sigma] at hx ⊢
    obtain ⟨hxb, hxc⟩ := hx
    rw [Finset.mem_filter] at hxb hxc
    obtain ⟨hxbdiv, hxbT⟩ := hxb
    obtain ⟨hxcdiv, hxTc⟩ := hxc
    have hbdvd : x.1 ∣ n := (Nat.mem_divisors.mp hxbdiv).1
    have hnne : n ≠ 0 := (Nat.mem_divisors.mp hxbdiv).2
    have hcdvd_div : x.2 ∣ n / x.1 := (Nat.mem_divisors.mp hxcdiv).1
    have hcpos : 0 < x.2 := Nat.pos_of_mem_divisors hxcdiv
    obtain ⟨hcdvd, hbdvd'⟩ := dvd_div_of_dvd_of_dvd_div hbdvd hcdvd_div
    have hncne : n / x.2 ≠ 0 :=
      ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hnne) hcdvd) hcpos)
    exact ⟨by rw [Finset.mem_filter]; exact ⟨Nat.mem_divisors.mpr ⟨hcdvd, hnne⟩, hxTc⟩,
           by rw [Finset.mem_filter]; exact ⟨Nat.mem_divisors.mpr ⟨hbdvd', hncne⟩, hxbT⟩⟩
  · intro x1 _ x2 _ heq
    obtain ⟨a1, b1⟩ := x1
    obtain ⟨a2, b2⟩ := x2
    simp only at heq
    rw [Sigma.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have h2' : a1 = a2 := eq_of_heq h2
    rw [h1, h2']
  · intro y hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hyc, hyb⟩ := hy
    rw [Finset.mem_filter] at hyc hyb
    obtain ⟨hycdiv, hyTc⟩ := hyc
    obtain ⟨hybdiv, hybT⟩ := hyb
    have hcdvd : y.1 ∣ n := (Nat.mem_divisors.mp hycdiv).1
    have hnne : n ≠ 0 := (Nat.mem_divisors.mp hycdiv).2
    have hbdvd_div : y.2 ∣ n / y.1 := (Nat.mem_divisors.mp hybdiv).1
    have hbpos : 0 < y.2 := Nat.pos_of_mem_divisors hybdiv
    obtain ⟨hbdvd, hcdvd'⟩ := dvd_div_of_dvd_of_dvd_div hcdvd hbdvd_div
    have hnbne : n / y.2 ≠ 0 :=
      ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hnne) hbdvd) hbpos)
    refine ⟨⟨y.2, y.1⟩, ?_, Sigma.eta y⟩
    rw [Finset.mem_sigma]
    exact ⟨by rw [Finset.mem_filter]; exact ⟨Nat.mem_divisors.mpr ⟨hbdvd, hnne⟩, hybT⟩,
           by rw [Finset.mem_filter]; exact ⟨Nat.mem_divisors.mpr ⟨hcdvd', hnbne⟩, hyTc⟩⟩
  · intro x _
    rfl

/-- `∑_{d | m} μ d = [m = 1]`. -/
private theorem sum_moebius_divisors_eq (m : ℕ) :
    (∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = if m = 1 then 1 else 0 := by
  have key : (∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) m := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ArithmeticFunction.intCoe_apply]
  rw [key, ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- If `k ≤ T` the truncated Möbius sum is the full one. -/
private theorem sum_moebius_filter_eq_of_le (k T : ℕ) (hk : k ≤ T) :
    (∑ d ∈ k.divisors.filter (fun d => d ≤ T), ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = if k = 1 then 1 else 0 := by
  have hf : k.divisors.filter (fun d => d ≤ T) = k.divisors := by
    apply Finset.filter_true_of_mem
    intro d hd
    rcases eq_or_ne k 0 with rfl | hk0
    · simp at hd
    · exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) (Nat.mem_divisors.mp hd).1) hk
  rw [hf, sum_moebius_divisors_eq]

/-- Collapsing the last sum: over the `m` with `T < m` and `n / m ≤ T` only `m = n`
survives, and it contributes `Λ n` exactly when `T < n`. -/
private theorem sum_filter_R_eq (n T : ℕ) (hT : 1 ≤ T) :
    (∑ m ∈ n.divisors.filter (fun m => T < m ∧ n / m ≤ T),
        ArithmeticFunction.vonMangoldt m *
          (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T), ((ArithmeticFunction.moebius d : ℤ) : ℝ)))
      = if n ≤ T then 0 else ArithmeticFunction.vonMangoldt n := by
  have hterm : ∀ m ∈ n.divisors.filter (fun m => T < m ∧ n / m ≤ T),
      ArithmeticFunction.vonMangoldt m *
        (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T), ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = if m = n then ArithmeticFunction.vonMangoldt n else 0 := by
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hmdiv, _hmT, hmnT⟩ := hm
    have hinner : (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = if n / m = 1 then 1 else 0 :=
      sum_moebius_filter_eq_of_le (n / m) T hmnT
    rw [hinner]
    have hmdvd : m ∣ n := (Nat.mem_divisors.mp hmdiv).1
    have hnpos : 0 < n := Nat.pos_of_ne_zero (Nat.mem_divisors.mp hmdiv).2
    have hiff : n / m = 1 ↔ m = n := by
      constructor
      · intro h
        have h1 : n = m * (n / m) := (Nat.mul_div_cancel' hmdvd).symm
        rw [h, mul_one] at h1; exact h1.symm
      · intro h; rw [h, Nat.div_self hnpos]
    have hite : (if n / m = 1 then (1:ℝ) else 0) = (if m = n then (1:ℝ) else 0) := by
      by_cases h : n / m = 1
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (fun hh => h (hiff.mpr hh))]
    rw [hite]
    by_cases h : m = n
    · rw [if_pos h, if_pos h, h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hterm,
    Finset.sum_ite_eq' (n.divisors.filter (fun m => T < m ∧ n / m ≤ T)) n
      (fun _ => ArithmeticFunction.vonMangoldt n)]
  have hmem : n ∈ n.divisors.filter (fun m => T < m ∧ n / m ≤ T) ↔ ¬ (n ≤ T) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hlt, _⟩; omega
    · intro hn
      have hpos : 0 < n := by omega
      exact ⟨⟨dvd_refl n, Nat.pos_iff_ne_zero.mp hpos⟩, by omega,
        by rw [Nat.div_self hpos]; exact hT⟩
  simp only [hmem]
  by_cases h : n ≤ T <;> simp [h]

theorem vonMangoldt_eq_lambda_decomp_pos (n T : ℕ) (hT : 1 ≤ T) :
    ArithmeticFunction.vonMangoldt n =
      (if n ≤ T then ArithmeticFunction.vonMangoldt n else 0)
      + (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)))
      - (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
            ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T),
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e)
      - (∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
            ArithmeticFunction.vonMangoldt m *
              (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
                ((ArithmeticFunction.moebius d : ℤ) : ℝ))) := by
  set S1 : ℝ := ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)) with hS1
  set S2 : ℝ := ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
      ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ T),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e with hS2
  set S3 : ℝ := ∑ m ∈ n.divisors.filter (fun m => T < m ∧ T < n / m),
      ArithmeticFunction.vonMangoldt m *
        (∑ d ∈ (n / m).divisors.filter (fun d => d ≤ T),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) with hS3
  have hS12 : S1 - S2 = ∑ c ∈ n.divisors.filter (fun c => T < c),
      ArithmeticFunction.vonMangoldt c *
        (∑ d ∈ (n / c).divisors.filter (fun d => d ≤ T),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
    have hA : S1 - S2 = ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
        ∑ e ∈ (n / d).divisors.filter (fun e => T < e),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e := by
      rw [hS1, hS2]
      have hS1' : (∑ d ∈ n.divisors.filter (fun d => d ≤ T),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ)))
          = ∑ d ∈ n.divisors.filter (fun d => d ≤ T),
              ∑ e ∈ (n / d).divisors,
                ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← ArithmeticFunction.vonMangoldt_sum (n := n / d), Finset.mul_sum]
      rw [hS1', ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases h : e ≤ T
      · rw [if_pos h, if_neg (not_lt.mpr h), sub_self]
      · rw [if_neg h, if_pos (not_le.mp h), sub_zero]
    rw [hA, sum_divisors_filter_mul_swap_aux n T (fun b c =>
      ((ArithmeticFunction.moebius b : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt c)]
    apply Finset.sum_congr rfl
    intro c hc
    rw [← Finset.sum_mul, mul_comm]
  have hC : S3 = ∑ c ∈ n.divisors.filter (fun c => T < c),
      (if T < n / c then ArithmeticFunction.vonMangoldt c *
        (∑ d ∈ (n / c).divisors.filter (fun d => d ≤ T),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) else 0) := by
    rw [hS3, ← Finset.filter_filter (p := fun m => T < m) (q := fun m => T < n / m),
      Finset.sum_filter]
  have hD : S1 - S2 - S3 = ∑ c ∈ n.divisors.filter (fun c => T < c ∧ n / c ≤ T),
      ArithmeticFunction.vonMangoldt c *
        (∑ d ∈ (n / c).divisors.filter (fun d => d ≤ T),
          ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
    rw [hS12, hC, ← Finset.sum_sub_distrib]
    have hstep : (∑ c ∈ n.divisors.filter (fun c => T < c),
        (ArithmeticFunction.vonMangoldt c *
            (∑ d ∈ (n / c).divisors.filter (fun d => d ≤ T),
              ((ArithmeticFunction.moebius d : ℤ) : ℝ))
          - (if T < n / c then ArithmeticFunction.vonMangoldt c *
              (∑ d ∈ (n / c).divisors.filter (fun d => d ≤ T),
                ((ArithmeticFunction.moebius d : ℤ) : ℝ)) else 0)))
        = ∑ c ∈ n.divisors.filter (fun c => T < c),
            (if n / c ≤ T then ArithmeticFunction.vonMangoldt c *
              (∑ d ∈ (n / c).divisors.filter (fun d => d ≤ T),
                ((ArithmeticFunction.moebius d : ℤ) : ℝ)) else 0) := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : T < n / c
      · rw [if_pos h, if_neg (not_le.mpr h), sub_self]
      · rw [if_neg h, if_pos (not_lt.mp h), sub_zero]
    rw [hstep, ← Finset.sum_filter,
      Finset.filter_filter (p := fun c => T < c) (q := fun c => n / c ≤ T)]
  have hkey : S1 - S2 - S3 = (if n ≤ T then 0 else ArithmeticFunction.vonMangoldt n) := by
    rw [hD, sum_filter_R_eq n T hT]
  have hfin : (if n ≤ T then ArithmeticFunction.vonMangoldt n else 0) + (S1 - S2 - S3)
      = ArithmeticFunction.vonMangoldt n := by
    rw [hkey]
    by_cases h : n ≤ T <;> simp [h]
  linarith [hfin]

end Commons.NumberTheory.ArithmeticFunction