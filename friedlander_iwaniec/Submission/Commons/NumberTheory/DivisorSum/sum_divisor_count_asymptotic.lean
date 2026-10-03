import Mathlib
import Submission.Commons.NumberTheory.Harmonic.abs_harmonic_sub_log_sub_euler_le_inv
import Submission.Commons.NumberTheory.DivisorSum.gcd_sum_square_bound
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le

namespace Commons.NumberTheory.DivisorSum

open Finset

/-- The number of `b ∈ {1,…,x}` with `a * b ≤ x` is `⌊x/a⌋` (for `1 ≤ a`). -/
lemma card_filter_mul_le (x a : ℕ) (ha : 1 ≤ a) :
    ((Finset.Icc 1 x).filter (fun b => a * b ≤ x)).card = x / a := by
  have ha0 : 0 < a := ha
  have hset : (Finset.Icc 1 x).filter (fun b => a * b ≤ x) = Finset.Icc 1 (x / a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hb1, _⟩, hb⟩
      exact ⟨hb1, (Nat.le_div_iff_mul_le ha0).mpr (by simpa [mul_comm] using hb)⟩
    · rintro ⟨hb1, hb⟩
      have h1 : b * a ≤ x := (Nat.le_div_iff_mul_le ha0).mp hb
      refine ⟨⟨hb1, ?_⟩, by simpa [mul_comm] using h1⟩
      calc b ≤ b * a := Nat.le_mul_of_pos_right b ha0
        _ ≤ x := h1
  rw [hset]
  simp [Nat.card_Icc]

/-- Sum of the divisor counting function equals the sum of `⌊x/a⌋`. -/
lemma sum_card_divisors_eq_sum_div (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, n.divisors.card) = ∑ a ∈ Finset.Icc 1 x, x / a := by
  have h1 : ∀ n ∈ Finset.Icc 1 x,
      n.divisors.card = ∑ a ∈ Finset.Icc 1 x, (if a ∣ n then 1 else 0 : ℕ) := by
    intro n hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1; omega
    have hdiv : n.divisors = (Finset.Icc 1 x).filter (fun a => a ∣ n) := by
      ext a
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨had, -⟩
        have ha0 : 0 < a := Nat.pos_of_mem_divisors (by
          rw [Nat.mem_divisors]; exact ⟨had, hn0⟩)
        have han : a ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) had
        exact ⟨⟨ha0, le_trans han (Finset.mem_Icc.mp hn).2⟩, had⟩
      · rintro ⟨⟨-, hle⟩, had⟩
        exact ⟨had, hn0⟩
    rw [hdiv, Finset.card_filter]
  calc ∑ n ∈ Finset.Icc 1 x, n.divisors.card
      = ∑ n ∈ Finset.Icc 1 x, ∑ a ∈ Finset.Icc 1 x, (if a ∣ n then 1 else 0 : ℕ) :=
        Finset.sum_congr rfl h1
    _ = ∑ a ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x, (if a ∣ n then 1 else 0 : ℕ) :=
        Finset.sum_comm
    _ = ∑ a ∈ Finset.Icc 1 x, ((Finset.Icc 1 x).filter (fun n => a ∣ n)).card := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.card_filter]
    _ = ∑ a ∈ Finset.Icc 1 x, x / a := by
        refine Finset.sum_congr rfl fun a ha => ?_
        exact card_filter_dvd_Icc x a (Finset.mem_Icc.mp ha).1

/-- The Dirichlet hyperbola identity in additive form. -/
lemma sum_Icc_div_add_sq_eq_two_mul (x : ℕ) :
    (∑ a ∈ Finset.Icc 1 x, x / a) + x.sqrt ^ 2
      = 2 * (∑ a ∈ Finset.Icc 1 x.sqrt, x / a) := by
  classical
  set N := x.sqrt with hN
  have hNsq : N ^ 2 ≤ x := by rw [hN]; exact Nat.sqrt_le' x
  have hNx : N ≤ x := by rw [hN]; exact Nat.sqrt_le_self x
  have hNlt : x < N.succ * N.succ := by rw [hN]; exact Nat.lt_succ_sqrt x
  set A : Finset (ℕ × ℕ) :=
    ((Finset.Icc 1 x) ×ˢ (Finset.Icc 1 x)).filter (fun p => p.1 * p.2 ≤ x) with hA
  set B : Finset (ℕ × ℕ) :=
    ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 x)).filter (fun p => p.1 * p.2 ≤ x) with hB
  set C : Finset (ℕ × ℕ) :=
    ((Finset.Icc 1 x) ×ˢ (Finset.Icc 1 N)).filter (fun p => p.1 * p.2 ≤ x) with hC
  have hAcard : A.card = ∑ a ∈ Finset.Icc 1 x, x / a := by
    rw [hA, Finset.card_filter]
    rw [Finset.sum_product' (Finset.Icc 1 x) (Finset.Icc 1 x)
      (fun a b : ℕ => if a * b ≤ x then 1 else 0)]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.card_filter]
    exact card_filter_mul_le x a (Finset.mem_Icc.mp ha).1
  have hBcard : B.card = ∑ a ∈ Finset.Icc 1 N, x / a := by
    rw [hB, Finset.card_filter]
    rw [Finset.sum_product' (Finset.Icc 1 N) (Finset.Icc 1 x)
      (fun a b : ℕ => if a * b ≤ x then 1 else 0)]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [← Finset.card_filter]
    exact card_filter_mul_le x a (Finset.mem_Icc.mp ha).1
  have hCB : B.card = C.card := by
    refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      obtain ⟨⟨ha, hb⟩, hab⟩ := by
        simpa only [hB, Finset.mem_filter, Finset.mem_product] using hp
      simp only [hC, Finset.mem_filter, Finset.mem_product, Prod.swap_prod_mk]
      exact ⟨⟨hb, ha⟩, by simpa [mul_comm] using hab⟩
    · rintro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ heq
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq ⊢
      exact ⟨heq.2, heq.1⟩
    · rintro ⟨a, b⟩ hp
      refine ⟨(b, a), ?_, rfl⟩
      obtain ⟨⟨ha, hb⟩, hab⟩ := by
        simpa only [hC, Finset.mem_filter, Finset.mem_product] using hp
      simp only [hB, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hb, ha⟩, by simpa [mul_comm] using hab⟩
  have hABC : A = B ∪ C := by
    ext p
    obtain ⟨a, b⟩ := p
    simp only [hA, hB, hC, Finset.mem_union, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨ha, hb⟩, hab⟩
      by_cases h : a ≤ N
      · exact Or.inl ⟨⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, h⟩, hb⟩, hab⟩
      · refine Or.inr ⟨⟨ha, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hb).1, ?_⟩⟩, hab⟩
        by_contra hbN
        have h1 : N.succ * N.succ ≤ a * b :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
    · rintro (⟨⟨ha, hb⟩, hab⟩ | ⟨⟨ha, hb⟩, hab⟩)
      · exact ⟨⟨Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1,
          le_trans (Finset.mem_Icc.mp ha).2 hNx⟩, hb⟩, hab⟩
      · exact ⟨⟨ha, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hb).1,
          le_trans (Finset.mem_Icc.mp hb).2 hNx⟩⟩, hab⟩
  have hBC : B ∩ C = (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) := by
    ext p
    obtain ⟨a, b⟩ := p
    simp only [hB, hC, Finset.mem_inter, Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨ha, -⟩, -⟩, ⟨⟨-, hb⟩, -⟩⟩
      exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩
      have hab : a * b ≤ x := by
        have h1 : a * b ≤ N * N :=
          Nat.mul_le_mul (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hb).2
        have h2 : N * N ≤ x := by simpa [pow_two] using hNsq
        exact le_trans h1 h2
      have hbIcc : b ∈ Finset.Icc 1 x :=
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hb).1, le_trans (Finset.mem_Icc.mp hb).2 hNx⟩
      have haIcc : a ∈ Finset.Icc 1 x :=
        Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha).1, le_trans (Finset.mem_Icc.mp ha).2 hNx⟩
      exact ⟨⟨⟨ha, hbIcc⟩, hab⟩, ⟨⟨haIcc, hb⟩, hab⟩⟩
  have hBCcard : (B ∩ C).card = N ^ 2 := by
    rw [hBC, Finset.card_product, Nat.card_Icc]
    simp [pow_two]
  have hcard : A.card + N ^ 2 = B.card + C.card := by
    have h := Finset.card_union_add_card_inter B C
    rw [← hABC] at h
    rw [hBCcard] at h
    exact h
  have h2 : B.card + C.card = 2 * B.card := by rw [← hCB]; ring
  rw [← hAcard, ← hBcard]
  exact hcard.trans h2

/-- The Dirichlet hyperbola identity: `∑_{a ≤ x} ⌊x/a⌋ = 2 ∑_{a ≤ √x} ⌊x/a⌋ - ⌊√x⌋²`. -/
lemma sum_Icc_div_eq_two_mul_sum_Icc_sqrt_div_sub_sq (x : ℕ) :
    (∑ a ∈ Finset.Icc 1 x, x / a)
      = 2 * (∑ a ∈ Finset.Icc 1 x.sqrt, x / a) - x.sqrt ^ 2 := by
  have h := sum_Icc_div_add_sq_eq_two_mul x
  omega

/-- Decomposition of `∑_{a ≤ N} ⌊x/a⌋` into a harmonic sum and a "fractional part" sum. -/
lemma sum_Icc_div_cast (x N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, ((x / a : ℕ) : ℝ))
      = (x : ℝ) * (harmonic N : ℝ)
        - ∑ a ∈ Finset.Icc 1 N, ((x % a : ℕ) : ℝ) / (a : ℝ) := by
  have hterm : ∀ a ∈ Finset.Icc 1 N,
      ((x / a : ℕ) : ℝ) = (x : ℝ)/(a : ℝ) - ((x % a : ℕ) : ℝ)/(a : ℝ) := by
    intro a ha
    have ha0 : (0 : ℝ) < (a : ℝ) := by
      have h1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      exact_mod_cast (by omega : 0 < a)
    have hdm : (a : ℝ) * ((x / a : ℕ) : ℝ) + ((x % a : ℕ) : ℝ) = (x : ℝ) := by
      exact_mod_cast Nat.div_add_mod x a
    field_simp
    linarith [hdm]
  calc (∑ a ∈ Finset.Icc 1 N, ((x / a : ℕ) : ℝ))
      = ∑ a ∈ Finset.Icc 1 N, ((x : ℝ)/(a : ℝ) - ((x % a : ℕ) : ℝ)/(a : ℝ)) :=
        Finset.sum_congr rfl hterm
    _ = (∑ a ∈ Finset.Icc 1 N, (x : ℝ)/(a : ℝ))
          - ∑ a ∈ Finset.Icc 1 N, ((x % a : ℕ) : ℝ)/(a : ℝ) :=
        Finset.sum_sub_distrib _ _
    _ = (x : ℝ) * (∑ a ∈ Finset.Icc 1 N, (1 : ℝ)/(a : ℝ))
          - ∑ a ∈ Finset.Icc 1 N, ((x % a : ℕ) : ℝ)/(a : ℝ) := by
        have hs : (∑ a ∈ Finset.Icc 1 N, (x : ℝ)/(a : ℝ))
            = (x : ℝ) * (∑ a ∈ Finset.Icc 1 N, (1 : ℝ)/(a : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
        rw [hs]
    _ = (x : ℝ) * (harmonic N : ℝ)
          - ∑ a ∈ Finset.Icc 1 N, ((x % a : ℕ) : ℝ)/(a : ℝ) := by
        rw [← harmonic_cast_eq_sum]

/-- The summatory divisor function `∑_{n ≤ x} d(n)` satisfies
`∑_{n ≤ x} d(n) = x log x + (2γ - 1) x + O(√x)`. -/
theorem sum_divisor_count_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      |(∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)))
        - ((x : ℝ) * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * (x : ℝ))|
        ≤ C * Real.sqrt x := by
  refine ⟨20, by norm_num, fun x hx => ?_⟩
  classical
  set N := x.sqrt with hN
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.le_sqrt.mpr (by simpa using hx)
  have hNx : N ≤ x := by rw [hN]; exact Nat.sqrt_le_self x
  have hNsq : N ^ 2 ≤ x := by rw [hN]; exact Nat.sqrt_le' x
  have hNlt : x < N.succ * N.succ := by rw [hN]; exact Nat.lt_succ_sqrt x
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hx)
  have hsqpos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have hNsqR : ((N : ℝ)) ^ 2 ≤ (x : ℝ) := by exact_mod_cast hNsq
  have hNle_sqrt : (N : ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact hNsqR
  have hNltR : (x : ℝ) < ((N : ℝ) + 1) ^ 2 := by
    have h2 : (x : ℝ) < ((N.succ : ℕ) : ℝ) * ((N.succ : ℕ) : ℝ) := by exact_mod_cast hNlt
    simpa [Nat.cast_succ, pow_two] using h2
  have h4N : ((N : ℝ) + 1) ^ 2 ≤ 4 * (N : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    nlinarith
  have hxlt4 : (x : ℝ) < 4 * (N : ℝ) ^ 2 := lt_of_lt_of_le hNltR h4N
  have hδ0 : 0 ≤ (x : ℝ) - (N : ℝ) ^ 2 := by linarith [hNsqR]
  have hδ2 : (x : ℝ) - (N : ℝ) ^ 2 ≤ 2 * (N : ℝ) := by
    have hcast : ((x - N ^ 2 : ℕ) : ℝ) = (x : ℝ) - (N : ℝ) ^ 2 := by
      rw [Nat.cast_sub hNsq, Nat.cast_pow]
    have hnat : x - N ^ 2 ≤ 2 * N := by
      have hsq : N.succ * N.succ = N ^ 2 + 2 * N + 1 := by
        rw [Nat.succ_eq_add_one]; ring
      have h := hNlt
      rw [hsq] at h
      omega
    rw [← hcast]
    exact_mod_cast hnat
  -- the "fractional part" sum `E`
  set E : ℝ := ∑ a ∈ Finset.Icc 1 N, ((x % a : ℕ) : ℝ) / (a : ℝ) with hEdef
  have hEnonneg : 0 ≤ E := by
    rw [hEdef]
    exact Finset.sum_nonneg fun a _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hEle : E ≤ (N : ℝ) := by
    rw [hEdef]
    calc ∑ a ∈ Finset.Icc 1 N, ((x % a : ℕ) : ℝ)/(a : ℝ)
        ≤ ∑ a ∈ Finset.Icc 1 N, (1 : ℝ) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
          have hapos : (0 : ℝ) < (a : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha1)
          rw [div_le_one hapos]
          exact_mod_cast (Nat.mod_lt x (lt_of_lt_of_le Nat.zero_lt_one ha1)).le
      _ = (N : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc]
          push_cast
          ring
  set S : ℝ := ∑ a ∈ Finset.Icc 1 N, ((x / a : ℕ) : ℝ) with hSdef
  set e : ℝ := (harmonic N : ℝ) - Real.log (N : ℝ) - Real.eulerMascheroniConstant with hedef
  have he_abs : |e| ≤ 1/(N : ℝ) := by
    rw [hedef]
    exact Commons.NumberTheory.Harmonic.abs_harmonic_sub_log_sub_euler_le_inv N hN1
  have hharm : (harmonic N : ℝ) = Real.log (N : ℝ) + Real.eulerMascheroniConstant + e := by
    rw [hedef]; ring
  have hSlin : S = (x : ℝ) * (harmonic N : ℝ) - E := by
    rw [hSdef, hEdef]
    exact sum_Icc_div_cast x N
  have hsq_eq : ((x.sqrt : ℕ) : ℝ) = (N : ℝ) := by rw [hN]
  have h3 : ((∑ a ∈ Finset.Icc 1 x, x / a : ℕ) : ℝ)
      = 2 * ((∑ a ∈ Finset.Icc 1 x.sqrt, x / a : ℕ) : ℝ) - (N : ℝ) ^ 2 := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (sum_Icc_div_add_sq_eq_two_mul x)
    push_cast at h ⊢
    rw [hsq_eq] at h
    linarith
  have h4 : ((∑ a ∈ Finset.Icc 1 x.sqrt, x / a : ℕ) : ℝ) = S := by
    rw [hSdef, ← hN, Nat.cast_sum]
  have hT : (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ))) = 2 * S - (N : ℝ) ^ 2 := by
    calc (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)))
        = ((∑ n ∈ Finset.Icc 1 x, n.divisors.card : ℕ) : ℝ) :=
          (Nat.cast_sum (Finset.Icc 1 x) (fun n => n.divisors.card)).symm
      _ = ((∑ a ∈ Finset.Icc 1 x, x / a : ℕ) : ℝ) := by rw [sum_card_divisors_eq_sum_div]
      _ = 2 * ((∑ a ∈ Finset.Icc 1 x.sqrt, x / a : ℕ) : ℝ) - (N : ℝ) ^ 2 := h3
      _ = 2 * S - (N : ℝ) ^ 2 := by rw [h4]
  -- estimates on the logarithmic and error terms
  have hLnonneg : 0 ≤ Real.log ((x : ℝ)/(N : ℝ) ^ 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hsqpos]
    linarith [hNsqR]
  have hLle : Real.log ((x : ℝ)/(N : ℝ) ^ 2) ≤ ((x : ℝ) - (N : ℝ) ^ 2)/(N : ℝ) ^ 2 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (x : ℝ)/(N : ℝ) ^ 2 by positivity)
    have h2 : (x : ℝ)/(N : ℝ) ^ 2 - 1 = ((x : ℝ) - (N : ℝ) ^ 2)/(N : ℝ) ^ 2 := by
      rw [sub_div, div_self (ne_of_gt hsqpos)]
    linarith
  have hxL : (x : ℝ) * Real.log ((x : ℝ)/(N : ℝ) ^ 2) ≤ 4 * ((x : ℝ) - (N : ℝ) ^ 2) := by
    have h1 : (x : ℝ) * Real.log ((x : ℝ)/(N : ℝ) ^ 2)
        ≤ (x : ℝ) * (((x : ℝ) - (N : ℝ) ^ 2)/(N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hLle hxpos.le
    have hxN2le4 : (x : ℝ)/(N : ℝ) ^ 2 ≤ 4 := by
      rw [div_le_iff₀ hsqpos]; linarith [hxlt4]
    have h2 : (x : ℝ) * (((x : ℝ) - (N : ℝ) ^ 2)/(N : ℝ) ^ 2)
        ≤ 4 * ((x : ℝ) - (N : ℝ) ^ 2) := by
      have heq : (x : ℝ) * (((x : ℝ) - (N : ℝ) ^ 2)/(N : ℝ) ^ 2)
          = ((x : ℝ)/(N : ℝ) ^ 2) * ((x : ℝ) - (N : ℝ) ^ 2) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hxN2le4 hδ0
    linarith
  have hxe_ub : (x : ℝ) * e ≤ 4 * (N : ℝ) := by
    have he2 : e ≤ 1/(N : ℝ) := (abs_le.mp he_abs).2
    have h1 : (x : ℝ) * e ≤ (x : ℝ) * (1/(N : ℝ)) := mul_le_mul_of_nonneg_left he2 hxpos.le
    have h2 : (x : ℝ) * (1/(N : ℝ)) = (x : ℝ)/(N : ℝ) := by ring
    have h3 : (x : ℝ)/(N : ℝ) ≤ 4 * (N : ℝ) := by
      rw [div_le_iff₀ hNpos]; linarith [hxlt4]
    linarith
  have hxe_lb : -4 * (N : ℝ) ≤ (x : ℝ) * e := by
    have he1 : -(1/(N : ℝ)) ≤ e := (abs_le.mp he_abs).1
    have h1 : (x : ℝ) * (-(1/(N : ℝ))) ≤ (x : ℝ) * e := mul_le_mul_of_nonneg_left he1 hxpos.le
    have h2 : (x : ℝ) * (-(1/(N : ℝ))) = -((x : ℝ)/(N : ℝ)) := by ring
    have h3 : -((x : ℝ)/(N : ℝ)) ≥ -4 * (N : ℝ) := by
      have h4 : (x : ℝ)/(N : ℝ) ≤ 4 * (N : ℝ) := by
        rw [div_le_iff₀ hNpos]; linarith [hxlt4]
      linarith
    linarith
  have hxLbound : (x : ℝ) * Real.log ((x : ℝ)/(N : ℝ) ^ 2) ≤ 8 * (N : ℝ) := by
    linarith [hxL, hδ2]
  have hTexp : (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)))
      - ((x : ℝ) * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * (x : ℝ))
      = (x : ℝ) * (2 * Real.log (N : ℝ) - Real.log (x : ℝ))
        + ((x : ℝ) - (N : ℝ) ^ 2) - 2 * E + 2 * (x : ℝ) * e := by
    rw [hT, hSlin, hharm]
    ring
  have hlogid : 2 * Real.log (N : ℝ) - Real.log (x : ℝ) = -Real.log ((x : ℝ)/(N : ℝ) ^ 2) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
    ring
  have hub : -((x : ℝ) * Real.log ((x : ℝ)/(N : ℝ) ^ 2)) + ((x : ℝ) - (N : ℝ) ^ 2)
      - 2 * E + 2 * (x : ℝ) * e ≤ 20 * Real.sqrt x := by
    nlinarith [hLnonneg, hδ0, hδ2, hEnonneg, hxe_ub, hNle_sqrt, hxpos.le]
  have hlb : -(20 * Real.sqrt x) ≤ -((x : ℝ) * Real.log ((x : ℝ)/(N : ℝ) ^ 2))
      + ((x : ℝ) - (N : ℝ) ^ 2) - 2 * E + 2 * (x : ℝ) * e := by
    nlinarith [hxLbound, hδ0, hEle, hxe_lb, hNle_sqrt]
  rw [hTexp, hlogid, mul_neg]
  exact abs_le.mpr ⟨hlb, hub⟩

end Commons.NumberTheory.DivisorSum
