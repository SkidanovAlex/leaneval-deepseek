import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.maximal_bilinear_char_large_sieve_sSup
import Submission.Commons.NumberTheory.ArithmeticFunction.vaughan_coefficient_bound

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- The Vaughan `λ₃` coefficient `a_t = Σ_{de = t, d,e ≤ T} μ(d) Λ(e)`. -/
noncomputable def lambda3Coef (T : ℕ) (t : ℕ) : ℂ :=
  ∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
    ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
      ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)

lemma lambda3Coef_eq (T t : ℕ) :
    lambda3Coef T t
      = ∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
          ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ) *
            ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) := by
  unfold lambda3Coef
  refine Finset.sum_congr rfl (fun kl _ => ?_)
  ring

lemma lambda3Coef_norm_le (T t : ℕ) : ‖lambda3Coef T t‖ ≤ max 0 (Real.log (t : ℝ)) := by
  rw [lambda3Coef_eq]
  exact Commons.NumberTheory.ArithmeticFunction.vaughan_coefficient_bound T T t

/-- `a_t = 0` when `t > T²`. -/
lemma lambda3Coef_eq_zero_of_lt (T t : ℕ) (ht : T * T < t) : lambda3Coef T t = 0 := by
  unfold lambda3Coef
  have hempty : (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro kl hkl hcon
    rw [Finset.mem_product] at hkl
    have h1 : kl.1 ≤ T := (Finset.mem_Icc.mp hkl.1).2
    have h2 : kl.2 ≤ T := (Finset.mem_Icc.mp hkl.2).2
    have : kl.1 * kl.2 ≤ T * T := Nat.mul_le_mul h1 h2
    omega
  rw [hempty, Finset.sum_empty]

/-- Norm bound on a dyadic block `(M, 2M]`. -/
lemma lambda3Coef_norm_le_of_mem (T M t : ℕ) (hM : 1 ≤ M)
    (ht : t ∈ Finset.Icc (M + 1) (2 * M)) :
    ‖lambda3Coef T t‖ ≤ Real.log (2 * (M : ℝ)) := by
  have ht1 : 1 ≤ t := by
    have := (Finset.mem_Icc.mp ht).1; omega
  have ht2 : t ≤ 2 * M := (Finset.mem_Icc.mp ht).2
  have hL := lambda3Coef_norm_le T t
  rw [max_eq_right (Real.log_nonneg (by exact_mod_cast ht1))] at hL
  have hpos : 0 < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hle : (t : ℝ) ≤ 2 * (M : ℝ) := by
    have : (t : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by exact_mod_cast ht2
    push_cast at this ⊢
    linarith
  exact hL.trans (Real.log_le_log hpos hle)

/-- Sum of squares of the coefficient over a dyadic block. -/
lemma sum_lambda3Coef_sq_le (T M : ℕ) (hM : 1 ≤ M) :
    (∑ t ∈ Finset.Icc (M + 1) (2 * M), ‖lambda3Coef T t‖ ^ 2)
      ≤ (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2 := by
  have hlog : 0 ≤ Real.log (2 * (M : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hcard : (Finset.Icc (M + 1) (2 * M)).card = M := by
    rw [Nat.card_Icc]; omega
  calc (∑ t ∈ Finset.Icc (M + 1) (2 * M), ‖lambda3Coef T t‖ ^ 2)
      ≤ ∑ _t ∈ Finset.Icc (M + 1) (2 * M), (Real.log (2 * (M : ℝ))) ^ 2 := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        have h1 := lambda3Coef_norm_le_of_mem T M t hM ht
        have h0 : 0 ≤ ‖lambda3Coef T t‖ := norm_nonneg _
        nlinarith [h1, h0, hlog]
    _ = (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2 := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]

/-- For `n ≥ 1`, `Nat.log 2 n ≤ Real.log n / Real.log 2`. -/
lemma nat_log_two_cast_le (n : ℕ) (hn : 1 ≤ n) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hpow : (2 : ℕ) ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hcast : ((2 : ℝ) ^ Nat.log 2 n) ≤ (n : ℝ) := by exact_mod_cast hpow
  have hlogeq : Real.log ((2 : ℝ) ^ Nat.log 2 n) = (Nat.log 2 n : ℝ) * Real.log 2 :=
    Real.log_pow 2 _
  have hpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by positivity) hcast
  rw [hlogeq] at hle
  rw [le_div_iff₀ hlog2]
  linarith

/-- `x ≤ M * (x / M + 1)` for `M ≥ 1`. -/
lemma le_mul_div_add (M x : ℕ) (hM : 1 ≤ M) : x ≤ M * (x / M + 1) := by
  have := Nat.div_add_mod x M
  have hmod : x % M < M := Nat.mod_lt _ (by omega)
  nlinarith [this, hmod]

/-! ### Elementary summation identities -/

lemma sum_Icc_union' {a b c : ℕ} (hab : a ≤ b + 1) (hbc : b ≤ c) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc a c, f n)
      = (∑ n ∈ Finset.Icc a b, f n) + (∑ n ∈ Finset.Icc (b + 1) c, f n) := by
  have hset : Finset.Icc a c = Finset.Icc a b ∪ Finset.Icc (b + 1) c := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : x ≤ b
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, le_trans h2 hbc⟩
      · exact ⟨le_trans hab h1, h2⟩
  rw [hset, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  simp only [Finset.mem_Icc] at hx1 hx2
  omega

lemma sum_Icc_dyadic_blocks (T K : ℕ) (f : ℕ → ℂ) :
    (∑ t ∈ Finset.Icc (T + 1) (T * 2 ^ K), f t)
      = ∑ j ∈ Finset.range K, ∑ t ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j)), f t := by
  induction K with
  | zero =>
      simp only [pow_zero, mul_one, Finset.range_zero, Finset.sum_empty]
      rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ T + 1 ≤ T), Finset.sum_empty]
  | succ K ih =>
      rw [Finset.sum_range_succ, ← ih]
      have heq : T * 2 ^ (K + 1) = 2 * (T * 2 ^ K) := by rw [Nat.pow_succ]; ring
      rw [heq]
      have hab : T + 1 ≤ T * 2 ^ K + 1 := by
        have h : 1 ≤ (2:ℕ) ^ K := Nat.one_le_pow K 2 (by norm_num)
        have := Nat.mul_le_mul_left T h
        omega
      have hbc : T * 2 ^ K ≤ 2 * (T * 2 ^ K) := by omega
      rw [← sum_Icc_union' hab hbc f]

/-- Truncated indicator sum. -/
lemma sum_Icc_ite_mul_eq (m y N : ℕ) (hm : 1 ≤ m) (hN : y / m ≤ N) (g : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 N, (if m * n ≤ y then (1 : ℂ) else 0) * g n)
      = ∑ n ∈ Finset.Icc 1 (y / m), g n := by
  have hset : (Finset.Icc 1 N).filter (fun n => m * n ≤ y) = Finset.Icc 1 (y / m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le hm).mpr (by simpa [mul_comm] using h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2 hN⟩, by
        have := (Nat.le_div_iff_mul_le hm).mp h2
        simpa [mul_comm] using this⟩
  calc (∑ n ∈ Finset.Icc 1 N, (if m * n ≤ y then (1 : ℂ) else 0) * g n)
      = ∑ n ∈ Finset.Icc 1 N, (if m * n ≤ y then g n else 0) := by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases h : m * n ≤ y <;> simp [h]
    _ = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => m * n ≤ y), g n := by
        rw [Finset.sum_filter]
    _ = ∑ n ∈ Finset.Icc 1 (y / m), g n := by rw [hset]

/-- **Bilinear representation of one dyadic block.** -/
lemma block_eq_bilinear (T M x y : ℕ) (hM : 1 ≤ M) (hy : y ≤ x)
    (q : ℕ) (χ : DirichletCharacter ℂ q) :
    (∑ t ∈ Finset.Icc (M + 1) (2 * M),
        lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)))
      = ∑ m ∈ Finset.Icc 1 (2 * M), ∑ n ∈ Finset.Icc 1 (x / M + 1),
          (if m * n ≤ y then (1 : ℂ) else 0)
            * (if m ∈ Finset.Icc (M + 1) (2 * M) then lambda3Coef T m else 0)
            * 1 * χ ((m * n : ℕ) : ZMod q) := by
  have hblock_sub : Finset.Icc (M + 1) (2 * M) ⊆ Finset.Icc 1 (2 * M) :=
    Finset.Icc_subset_Icc (by omega) le_rfl
  have hA : (∑ m ∈ Finset.Icc 1 (2 * M), ∑ n ∈ Finset.Icc 1 (x / M + 1),
          (if m * n ≤ y then (1 : ℂ) else 0)
            * (if m ∈ Finset.Icc (M + 1) (2 * M) then lambda3Coef T m else 0)
            * 1 * χ ((m * n : ℕ) : ZMod q))
      = ∑ m ∈ Finset.Icc (M + 1) (2 * M), ∑ n ∈ Finset.Icc 1 (x / M + 1),
          (if m * n ≤ y then (1 : ℂ) else 0)
            * (if m ∈ Finset.Icc (M + 1) (2 * M) then lambda3Coef T m else 0)
            * 1 * χ ((m * n : ℕ) : ZMod q) := by
    refine (Finset.sum_subset hblock_sub ?_).symm
    intro m _ hmnot
    rw [if_neg hmnot]
    simp
  rw [hA]
  have hstep1 : (∑ m ∈ Finset.Icc (M + 1) (2 * M), ∑ n ∈ Finset.Icc 1 (x / M + 1),
          (if m * n ≤ y then (1 : ℂ) else 0)
            * (if m ∈ Finset.Icc (M + 1) (2 * M) then lambda3Coef T m else 0)
            * 1 * χ ((m * n : ℕ) : ZMod q))
      = ∑ m ∈ Finset.Icc (M + 1) (2 * M), ∑ n ∈ Finset.Icc 1 (x / M + 1),
          (if m * n ≤ y then (1 : ℂ) else 0) * lambda3Coef T m * 1 * χ ((m * n : ℕ) : ZMod q) := by
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [if_pos hm]
  rw [hstep1]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hmlo : M + 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hmhi : m ≤ 2 * M := (Finset.mem_Icc.mp hm).2
  have hm1 : 1 ≤ m := by omega
  have hMle : M ≤ m := by omega
  have hNM : y / m ≤ x / M + 1 := by
    have h1 : y / m ≤ x / m := Nat.div_le_div_right hy
    have h2 : x / m ≤ x / M := Nat.div_le_div_left hMle (by omega)
    exact le_trans (le_trans h1 h2) (Nat.le_succ _)
  have hinner : (∑ n ∈ Finset.Icc 1 (x / M + 1),
        (if m * n ≤ y then (1 : ℂ) else 0) * 1 * χ ((m * n : ℕ) : ZMod q))
      = χ (m : ZMod q) * (∑ n ∈ Finset.Icc 1 (y / m), χ (n : ZMod q)) := by
    have h1 : (∑ n ∈ Finset.Icc 1 (x / M + 1),
          (if m * n ≤ y then (1 : ℂ) else 0) * 1 * χ ((m * n : ℕ) : ZMod q))
        = ∑ n ∈ Finset.Icc 1 (x / M + 1),
          (if m * n ≤ y then (1 : ℂ) else 0) * χ ((m * n : ℕ) : ZMod q) := by
      refine Finset.sum_congr rfl (fun n _ => by ring)
    rw [h1]
    have h2 : (∑ n ∈ Finset.Icc 1 (x / M + 1),
          (if m * n ≤ y then (1 : ℂ) else 0) * χ ((m * n : ℕ) : ZMod q))
        = ∑ n ∈ Finset.Icc 1 (x / M + 1),
          (if m * n ≤ y then (1 : ℂ) else 0) * (χ (m : ZMod q) * χ (n : ZMod q)) := by
      refine Finset.sum_congr rfl (fun n _ => by
        rw [Nat.cast_mul, map_mul])
    rw [h2]
    rw [show (∑ n ∈ Finset.Icc 1 (x / M + 1),
            (if m * n ≤ y then (1 : ℂ) else 0) * (χ (m : ZMod q) * χ (n : ZMod q)))
        = χ (m : ZMod q) * ∑ n ∈ Finset.Icc 1 (x / M + 1),
            (if m * n ≤ y then (1 : ℂ) else 0) * χ (n : ZMod q) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => by ring)]
    rw [sum_Icc_ite_mul_eq m y (x / M + 1) hm1 hNM (fun n => χ (n : ZMod q))]
  rw [show (∑ n ∈ Finset.Icc 1 (x / M + 1),
        (if m * n ≤ y then (1 : ℂ) else 0) * lambda3Coef T m * 1 * χ ((m * n : ℕ) : ZMod q))
      = lambda3Coef T m * (∑ n ∈ Finset.Icc 1 (x / M + 1),
          (if m * n ≤ y then (1 : ℂ) else 0) * 1 * χ ((m * n : ℕ) : ZMod q)) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => by ring)]
  rw [hinner]
  ring

/-! ### Auxiliary real / geometric lemmas -/

theorem sqrt_add_le_sqrt_add_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  have h2 : (0 : ℝ) ≤ Real.sqrt a + Real.sqrt b := by positivity
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq h2

theorem sqrt_two_pow (K : ℕ) : Real.sqrt ((2 : ℝ) ^ K) = (Real.sqrt 2) ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (2:ℝ)^K), ih, pow_succ]

theorem sum_range_sqrt_two_pow_mul_le (T K : ℕ) (hT : 1 ≤ T) :
    (∑ j ∈ Finset.range K, Real.sqrt ((T : ℝ) * (2 : ℝ) ^ j))
      ≤ 4 * Real.sqrt ((T : ℝ) * (2 : ℝ) ^ K) := by
  have hT0 : (0:ℝ) ≤ (T:ℝ) := by positivity
  have hsq : ∀ j, Real.sqrt ((T:ℝ) * (2:ℝ)^j) = Real.sqrt (T:ℝ) * (Real.sqrt 2)^j := by
    intro j
    rw [Real.sqrt_mul hT0, sqrt_two_pow]
  have hr : (5:ℝ)/4 ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5/4)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hgeo : ∀ K, (∑ j ∈ Finset.range K, (Real.sqrt 2)^j) ≤ 4 * (Real.sqrt 2)^K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have hpos : 0 ≤ (Real.sqrt 2)^K := by positivity
        nlinarith [ih, hr, hpos]
  rw [Finset.sum_congr rfl (fun j _ => hsq j), ← Finset.mul_sum]
  have hrhs : Real.sqrt ((T:ℝ) * (2:ℝ)^K) = Real.sqrt (T:ℝ) * (Real.sqrt 2)^K := by
    rw [Real.sqrt_mul hT0, sqrt_two_pow]
  rw [hrhs]
  nlinarith [hgeo K, Real.sqrt_nonneg (T:ℝ)]

/-- Rearrangement of a triple sum with a `q`-dependent character set. -/
lemma sum_swap_dep {ι : ℕ → Type*} (Q K : ℕ) (w : ℕ → ℝ) (S : (q : ℕ) → Finset (ι q))
    (X : (q : ℕ) → ι q → ℕ → ℝ) :
    (∑ q ∈ Finset.Icc 1 Q, w q * ∑ χ ∈ S q, ∑ j ∈ Finset.range K, X q χ j)
      = ∑ j ∈ Finset.range K, ∑ q ∈ Finset.Icc 1 Q, w q * ∑ χ ∈ S q, X q χ j := by
  have step1 : (∑ q ∈ Finset.Icc 1 Q, w q * ∑ χ ∈ S q, ∑ j ∈ Finset.range K, X q χ j)
      = ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ S q, ∑ j ∈ Finset.range K, w q * X q χ j := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [Finset.mul_sum]
  have step2 : (∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ S q, ∑ j ∈ Finset.range K, w q * X q χ j)
      = ∑ q ∈ Finset.Icc 1 Q, ∑ j ∈ Finset.range K, ∑ χ ∈ S q, w q * X q χ j := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_comm]
  have step3 : (∑ q ∈ Finset.Icc 1 Q, ∑ j ∈ Finset.range K, ∑ χ ∈ S q, w q * X q χ j)
      = ∑ j ∈ Finset.range K, ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ S q, w q * X q χ j := by
    rw [Finset.sum_comm]
  have step4 : (∑ j ∈ Finset.range K, ∑ q ∈ Finset.Icc 1 Q, ∑ χ ∈ S q, w q * X q χ j)
      = ∑ j ∈ Finset.range K, ∑ q ∈ Finset.Icc 1 Q, w q * ∑ χ ∈ S q, X q χ j := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.mul_sum]
  rw [step1, step2, step3, step4]

lemma sSup_image_Icc_mono (f : ℕ → ℝ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    sSup (f '' Set.Icc 1 a) ≤ sSup (f '' Set.Icc 1 b) := by
  refine csSup_le ⟨f 1, ⟨1, ⟨le_refl 1, ha⟩, rfl⟩⟩ ?_
  rintro v ⟨y, hy, rfl⟩
  exact le_csSup ((Set.finite_Icc 1 b).image f |>.bddAbove)
    (Set.mem_image_of_mem f ⟨hy.1, le_trans hy.2 hab⟩)

/-- The per-block real estimate. -/
lemma block_bound_le (c M N x Q L : ℝ) (hc : 0 ≤ c) (hM1 : 1 ≤ M) (hx1 : 1 ≤ x)
    (_hMx : M ≤ x) (hN : N ≤ 2 * (x / M)) (hN1 : 1 ≤ N) (hQ1 : 1 ≤ Q) (hL : 1 ≤ L)
    (hlogM : Real.log (2 * M) ≤ L) (hlogN : Real.log (2 * (2 * M) * N + 2) ≤ 2 * L) :
    c * Real.sqrt ((2 * M + Q ^ 2) * (M * (Real.log (2 * M)) ^ 2)) * Real.sqrt ((N + Q ^ 2) * N)
        * Real.log (2 * (2 * M) * N + 2)
      ≤ 4 * c * L ^ 2 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
          + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by
  have hM0 : 0 ≤ M := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hMne : (M:ℝ) ≠ 0 := by linarith
  have hlogMnn : 0 ≤ Real.log (2 * M) := Real.log_nonneg (by linarith)
  have hsqM : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0
  have hsqN : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0
  have hsMne : Real.sqrt M ≠ 0 := by
    intro h; rw [h, zero_mul] at hsqM; linarith
  have hsqrtmm : Real.sqrt (2 * M) = Real.sqrt 2 * Real.sqrt M :=
    Real.sqrt_mul (by norm_num) M
  have hf1 : Real.sqrt ((2 * M + Q ^ 2) * (M * (Real.log (2 * M)) ^ 2))
      ≤ (Real.sqrt 2 * M + Q * Real.sqrt M) * Real.log (2 * M) := by
    have h1 : Real.sqrt ((2 * M + Q ^ 2) * (M * (Real.log (2 * M)) ^ 2))
        = Real.sqrt (2 * M + Q ^ 2) * (Real.sqrt M * Real.log (2 * M)) := by
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * M + Q^2), Real.sqrt_mul hM0,
        Real.sqrt_sq hlogMnn]
    rw [h1]
    have h2 : Real.sqrt (2 * M + Q ^ 2) ≤ Real.sqrt 2 * Real.sqrt M + Q := by
      have h := sqrt_add_le_sqrt_add_sqrt (2 * M) (Q ^ 2) (by linarith) (by positivity)
      rw [Real.sqrt_sq hQ0, hsqrtmm] at h
      exact h
    have h3 : 0 ≤ Real.sqrt M * Real.log (2 * M) := mul_nonneg (Real.sqrt_nonneg _) hlogMnn
    calc Real.sqrt (2 * M + Q ^ 2) * (Real.sqrt M * Real.log (2 * M))
        ≤ (Real.sqrt 2 * Real.sqrt M + Q) * (Real.sqrt M * Real.log (2 * M)) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = (Real.sqrt 2 * M + Q * Real.sqrt M) * Real.log (2 * M) := by
          have hthis : (Real.sqrt 2 * Real.sqrt M + Q) * (Real.sqrt M * Real.log (2 * M))
              = Real.sqrt 2 * (Real.sqrt M * Real.sqrt M) * Real.log (2 * M)
                + Q * Real.sqrt M * Real.log (2 * M) := by ring
          rw [hthis, hsqM]
          ring
  have hf2 : Real.sqrt ((N + Q ^ 2) * N) ≤ N + Q * Real.sqrt N := by
    have h1 : Real.sqrt ((N + Q ^ 2) * N) = Real.sqrt (N + Q ^ 2) * Real.sqrt N :=
      Real.sqrt_mul (by positivity) N
    rw [h1]
    have h2 : Real.sqrt (N + Q ^ 2) ≤ Real.sqrt N + Q := by
      have h := sqrt_add_le_sqrt_add_sqrt N (Q ^ 2) hN0 (by positivity)
      rw [Real.sqrt_sq hQ0] at h
      exact h
    calc Real.sqrt (N + Q ^ 2) * Real.sqrt N ≤ (Real.sqrt N + Q) * Real.sqrt N :=
          mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg N)
      _ = N + Q * Real.sqrt N := by rw [add_mul, hsqN]
  have hNbound : N + Q * Real.sqrt N ≤ 2 * (x / M + Q * Real.sqrt (x / M)) := by
    have hsN : Real.sqrt N ≤ Real.sqrt (2 * (x / M)) := Real.sqrt_le_sqrt hN
    have hs2 : Real.sqrt (2 * (x / M)) ≤ 2 * Real.sqrt (x / M) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (x / M)]
      have h2 : Real.sqrt (2:ℝ) ≤ 2 := by
        have h := Real.sqrt_le_sqrt (by norm_num : (2:ℝ) ≤ 4)
        rwa [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h
      nlinarith [h2, Real.sqrt_nonneg (x / M)]
    have h3 : Real.sqrt N ≤ 2 * Real.sqrt (x / M) := le_trans hsN hs2
    have h4 : Q * Real.sqrt N ≤ Q * (2 * Real.sqrt (x / M)) := mul_le_mul_of_nonneg_left h3 hQ0
    linarith
  have hcomb : c * Real.sqrt ((2 * M + Q ^ 2) * (M * (Real.log (2 * M)) ^ 2))
        * Real.sqrt ((N + Q ^ 2) * N) * Real.log (2 * (2 * M) * N + 2)
      ≤ c * ((Real.sqrt 2 * M + Q * Real.sqrt M) * Real.log (2 * M))
          * (N + Q * Real.sqrt N) * (2 * L) := by
    have hA : (0:ℝ) ≤ (Real.sqrt 2 * M + Q * Real.sqrt M) * Real.log (2 * M) :=
      mul_nonneg (by positivity) hlogMnn
    have hC : (0:ℝ) ≤ Real.log (2 * (2 * M) * N + 2) :=
      Real.log_nonneg (by nlinarith [hM0, hN0])
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hf1 hc) hf2 (by positivity)
        (mul_nonneg hc hA)) hlogN hC (by positivity)
  have hAlg : (Real.sqrt 2 * M + Q * Real.sqrt M) * (x / M + Q * Real.sqrt (x / M))
      = Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M) + Q * x / Real.sqrt M
          + Q ^ 2 * Real.sqrt x := by
    have hxx : M * (x / M) = x := by field_simp
    have h1 : Real.sqrt M * Real.sqrt (x / M) = Real.sqrt x := by
      rw [← Real.sqrt_mul hM0 (x / M), hxx]
    have h2 : M * Real.sqrt (x / M) = Real.sqrt (x * M) := by
      calc M * Real.sqrt (x / M)
          = (Real.sqrt M * Real.sqrt M) * Real.sqrt (x / M) := by rw [hsqM]
        _ = Real.sqrt M * (Real.sqrt M * Real.sqrt (x / M)) := by ring
        _ = Real.sqrt M * Real.sqrt x := by rw [h1]
        _ = Real.sqrt (M * x) := (Real.sqrt_mul hM0 x).symm
        _ = Real.sqrt (x * M) := by rw [mul_comm]
    have h3 : Real.sqrt M * (x / M) = x / Real.sqrt M := by
      rw [eq_div_iff hsMne]
      rw [mul_assoc, mul_comm (x / M) (Real.sqrt M), ← mul_assoc, hsqM, hxx]
    calc (Real.sqrt 2 * M + Q * Real.sqrt M) * (x / M + Q * Real.sqrt (x / M))
        = Real.sqrt 2 * (M * (x / M)) + Real.sqrt 2 * Q * (M * Real.sqrt (x / M))
          + Q * (Real.sqrt M * (x / M)) + Q ^ 2 * (Real.sqrt M * Real.sqrt (x / M)) := by ring
      _ = Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M) + Q * (x / Real.sqrt M)
          + Q ^ 2 * Real.sqrt x := by rw [hxx, h2, h3, h1]
      _ = Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M) + Q * x / Real.sqrt M
          + Q ^ 2 * Real.sqrt x := by ring
  have hfinal : c * ((Real.sqrt 2 * M + Q * Real.sqrt M) * Real.log (2 * M))
        * (N + Q * Real.sqrt N) * (2 * L)
      ≤ 4 * c * L ^ 2 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
          + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by
    have hg1 : (0:ℝ) ≤ Real.sqrt 2 * M + Q * Real.sqrt M := by positivity
    have hstep : c * ((Real.sqrt 2 * M + Q * Real.sqrt M) * Real.log (2 * M))
          * (N + Q * Real.sqrt N) * (2 * L)
        ≤ c * ((Real.sqrt 2 * M + Q * Real.sqrt M) * L)
          * (2 * (x / M + Q * Real.sqrt (x / M))) * (2 * L) := by
      have e1 : c * ((Real.sqrt 2 * M + Q * Real.sqrt M) * Real.log (2 * M))
            ≤ c * ((Real.sqrt 2 * M + Q * Real.sqrt M) * L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogM hg1) hc
      exact mul_le_mul (mul_le_mul e1 hNbound (by positivity) (by positivity))
        (le_refl (2 * L)) (by positivity) (by positivity)
    calc c * ((Real.sqrt 2 * M + Q * Real.sqrt M) * Real.log (2 * M))
          * (N + Q * Real.sqrt N) * (2 * L)
        ≤ c * ((Real.sqrt 2 * M + Q * Real.sqrt M) * L)
          * (2 * (x / M + Q * Real.sqrt (x / M))) * (2 * L) := hstep
      _ = 4 * c * L ^ 2 * ((Real.sqrt 2 * M + Q * Real.sqrt M)
            * (x / M + Q * Real.sqrt (x / M))) := by ring
      _ = 4 * c * L ^ 2 * (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt (x * M)
            + Q * x / Real.sqrt M + Q ^ 2 * Real.sqrt x) := by rw [hAlg]
  linarith [hcomb, hfinal]

/-- Decomposition of the maximal `λ₃` sum into dyadic blocks, dominated by the sum of the
maximal bilinear forms of the blocks. -/
lemma sup_le_sum_block_sup (x T q : ℕ) (hx : 1 ≤ x) (hT : 1 ≤ T)
    (hTx : T ≤ x) (χ : DirichletCharacter ℂ q) :
    sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc (T + 1) (T ^ 2),
        lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖)
        '' Set.Icc 1 x)
      ≤ ∑ j ∈ Finset.range (Nat.log 2 (min (T ^ 2) x / T) + 1),
          sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
              ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
                (if m * n ≤ y then (1 : ℂ) else 0)
                  * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                      then lambda3Coef T m else 0)
                  * 1 * χ ((m * n : ℕ) : ZMod q)‖) '' Set.Icc 1 x) := by
  set K := Nat.log 2 (min (T ^ 2) x / T) + 1 with hK
  have hmT : T ≤ min (T ^ 2) x :=
    le_min (by rw [pow_two]; exact Nat.le_mul_of_pos_right T (by omega)) hTx
  have h2 : min (T ^ 2) x / T + 1 ≤ 2 ^ K := by
    rw [hK]
    exact Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _)
  have hTKmin : min (T ^ 2) x ≤ T * 2 ^ K := by
    have hd := Nat.div_add_mod (min (T ^ 2) x) T
    have hmod : min (T ^ 2) x % T < T := Nat.mod_lt _ (by omega)
    have hmul : T * (min (T ^ 2) x / T) + T ≤ T * 2 ^ K := by
      have h := Nat.mul_le_mul_left T h2
      rwa [Nat.mul_add, Nat.mul_one] at h
    omega
  have hzero : ∀ t y : ℕ, (T ^ 2 < t ∨ y < t) →
      lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)) = 0 := by
    intro t y h
    rcases h with h | h
    · have h' : T * T < t := by rw [pow_two] at h; exact h
      rw [lambda3Coef_eq_zero_of_lt T t h', zero_mul, zero_mul]
    · rw [Nat.div_eq_of_lt h, Finset.Icc_eq_empty_iff.mpr (by omega : ¬ (1:ℕ) ≤ 0),
        Finset.sum_empty, mul_zero]
  have hdrop : ∀ y A : ℕ, y ≤ x → min (T ^ 2) x ≤ A →
      (∑ t ∈ Finset.Icc (T + 1) (min (T ^ 2) x),
          lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)))
        = ∑ t ∈ Finset.Icc (T + 1) A,
          lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)) := by
    intro y A hyx hA
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hA) ?_
    intro t ht hnt
    simp only [Finset.mem_Icc] at ht hnt
    have htmin : min (T ^ 2) x < t := by omega
    rcases le_total (T ^ 2) x with hle | hle
    · rw [min_eq_left hle] at htmin
      exact hzero t y (Or.inl htmin)
    · rw [min_eq_right hle] at htmin
      exact hzero t y (Or.inr (by omega))
  have hpart : ∀ y : ℕ, y ≤ x →
      (∑ t ∈ Finset.Icc (T + 1) (T ^ 2),
          lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)))
        = ∑ j ∈ Finset.range K, ∑ t ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j)),
          lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)) := by
    intro y hyx
    rw [← hdrop y (T ^ 2) hyx (min_le_left _ _)]
    rw [(sum_Icc_dyadic_blocks T K
      (fun t => lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)))).symm,
      ← hdrop y (T * 2 ^ K) hyx hTKmin]
  have hGeq : ∀ j y, y ≤ x →
      (∑ t ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j)),
          lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)))
        = ∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)), ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
            (if m * n ≤ y then (1 : ℂ) else 0)
              * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                  then lambda3Coef T m else 0)
              * 1 * χ ((m * n : ℕ) : ZMod q) := by
    intro j y hyx
    exact block_eq_bilinear T (T * 2 ^ j) x y
      (by have h := Nat.one_le_pow j 2 (by norm_num); have := Nat.mul_le_mul hT h
          simpa using this) hyx q χ
  refine csSup_le ?_ ?_
  · exact ⟨‖∑ t ∈ Finset.Icc (T + 1) (T ^ 2),
        lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (1 / t), χ (r : ZMod q))‖,
        ⟨1, ⟨le_refl 1, hx⟩, rfl⟩⟩
  · rintro v ⟨y, hy, rfl⟩
    have hy1 : 1 ≤ y := hy.1
    have hyx : y ≤ x := hy.2
    calc ‖∑ t ∈ Finset.Icc (T + 1) (T ^ 2),
          lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖
        = ‖∑ j ∈ Finset.range K, ∑ t ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j)),
            lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖ := by
          rw [hpart y hyx]
      _ ≤ ∑ j ∈ Finset.range K, ‖∑ t ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j)),
            lambda3Coef T t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖ :=
          norm_sum_le _ _
      _ = ∑ j ∈ Finset.range K, ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
              ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
                (if m * n ≤ y then (1 : ℂ) else 0)
                  * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                      then lambda3Coef T m else 0)
                  * 1 * χ ((m * n : ℕ) : ZMod q)‖ := by
          refine Finset.sum_congr rfl (fun j _ => by rw [hGeq j y hyx])
      _ ≤ ∑ j ∈ Finset.range K, sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
              ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
                (if m * n ≤ y then (1 : ℂ) else 0)
                  * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                      then lambda3Coef T m else 0)
                  * 1 * χ ((m * n : ℕ) : ZMod q)‖) '' Set.Icc 1 x) := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          exact le_csSup (((Set.finite_Icc 1 x).image
            (fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
              ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
                (if m * n ≤ y then (1 : ℂ) else 0)
                  * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                      then lambda3Coef T m else 0)
                  * 1 * χ ((m * n : ℕ) : ZMod q)‖)).bddAbove)
            (Set.mem_image_of_mem _ ⟨hy1, hyx⟩)



/-- Per-block bound: the large-sieve input for one dyadic block, already reduced to the
real-variable estimate `block_bound_le`. -/
lemma per_block_bound
    (c : ℝ)
    (hc : ∀ (Q M N : ℕ) (hQ : 1 ≤ Q) (hM : 1 ≤ M) (hN : 1 ≤ N) (a b : ℕ → ℂ),
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
          (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
              (if m * n ≤ y then (1 : ℂ) else 0) * a m * b n * χ ((m * n : ℕ) : ZMod q)‖)
              '' Set.Icc 1 (M * N)))
      ≤ c * Real.sqrt (((M : ℝ) + (Q : ℝ) ^ 2) * ∑ m ∈ Finset.Icc 1 M, ‖a m‖ ^ 2)
        * Real.sqrt (((N : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2)
        * Real.log (2 * (M : ℝ) * (N : ℝ) + 2))
    (x Q T j : ℕ) (hcpos : 0 < c) (hx : 2 ≤ x) (hQ : 2 ≤ Q) (hT : 1 ≤ T)
    (hjx : T * 2 ^ j ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
      ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
        (Classical.decPred _) Finset.univ),
        sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
            ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
              (if m * n ≤ y then (1 : ℂ) else 0)
                * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                    then lambda3Coef T m else 0)
                * 1 * χ ((m * n : ℕ) : ZMod q)‖) '' Set.Icc 1 x))
      ≤ 4 * c * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 2 *
          (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt ((x : ℝ) * ((T * 2 ^ j : ℕ) : ℝ))
            + Q * x / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ) + Q ^ 2 * Real.sqrt x) := by
  set M : ℝ := ((T * 2 ^ j : ℕ) : ℝ) with hM
  set N : ℝ := ((x / (T * 2 ^ j) + 1 : ℕ) : ℝ) with hN
  set L : ℝ := Real.log ((x : ℝ) * (Q : ℝ) + 2) with hL
  have hMj1 : 1 ≤ T * 2 ^ j := by
    have := Nat.one_le_pow j 2 (by norm_num); nlinarith [hT, this]
  have hNj1 : 1 ≤ x / (T * 2 ^ j) + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hM1 : 1 ≤ M := by rw [hM]; exact_mod_cast hMj1
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) ≤ x := by positivity
  have hQ0 : (0:ℝ) ≤ Q := by positivity
  have hT0 : (0:ℝ) ≤ T := by positivity
  have hMx : M ≤ (x:ℝ) := by rw [hM]; exact_mod_cast hjx
  have hM0 : 0 ≤ M := by linarith
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast hNj1
  have hN0 : 0 ≤ N := by linarith
  have h2M : ((2 * (T * 2 ^ j) : ℕ) : ℝ) = 2 * M := by rw [hM]; push_cast; ring
  have hL1 : 1 ≤ L := by
    have h6 : (6:ℝ) ≤ (x:ℝ)*(Q:ℝ)+2 := by
      have h1 : (2:ℝ) ≤ x := by exact_mod_cast hx
      have h2 : (2:ℝ) ≤ Q := by exact_mod_cast hQ
      nlinarith
    have hlog6 : (1:ℝ) ≤ Real.log 6 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    rw [hL]
    exact le_trans hlog6 (Real.log_le_log (by norm_num) h6)
  have hNle : N ≤ 2 * ((x:ℝ)/M) := by
    have hcastN : N = ((x / (T * 2 ^ j) : ℕ) : ℝ) + 1 := by rw [hN]; push_cast; ring
    rw [hcastN, hM]
    have h1 : ((x / (T * 2 ^ j) : ℕ) : ℝ) ≤ (x:ℝ)/((T * 2 ^ j : ℕ):ℝ) := Nat.cast_div_le
    have h2 : (1:ℝ) ≤ (x:ℝ)/((T * 2 ^ j : ℕ):ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hMj1)]
      simpa using (show (((T * 2 ^ j : ℕ)) : ℝ) ≤ (x:ℝ) from by exact_mod_cast hjx)
    linarith
  have hlogM : Real.log (2 * M) ≤ L := by
    rw [hL]
    apply Real.log_le_log (by positivity)
    have h2 : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
    nlinarith [hMx, hx0, hQ0]
  have hlogN : Real.log (2 * (2 * M) * N + 2) ≤ 2 * L := by
    have hMN : M * N ≤ 2 * x := by
      have hMM : M * (x / M) = x := by field_simp
      have h1 := mul_le_mul_of_nonneg_left hNle hM0
      have he : M * (2 * (x / M)) = 2 * x := by
        rw [show M * (2 * (x / M)) = 2 * (M * (x / M)) from by ring, hMM]
      rw [he] at h1
      exact h1
    have h1 : 2 * (2 * M) * N + 2 ≤ 4 * ((x:ℝ)*(Q:ℝ)+2) := by
      have h2 : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
      nlinarith [hMN, hx0, hQ0]
    have h2 : Real.log (2 * (2 * M) * N + 2) ≤ Real.log (4 * ((x:ℝ)*(Q:ℝ)+2)) :=
      Real.log_le_log (by positivity) h1
    have h3 : Real.log (4 * ((x:ℝ)*(Q:ℝ)+2)) = Real.log 4 + L := by
      rw [hL, Real.log_mul (by norm_num) (by positivity)]
    have h4 : Real.log 4 ≤ L := by
      rw [hL]
      apply Real.log_le_log (by norm_num)
      have h1 : (2:ℝ) ≤ x := by exact_mod_cast hx
      have h2 : (2:ℝ) ≤ Q := by exact_mod_cast hQ
      nlinarith
    linarith
  -- sup over Icc 1 x ≤ sup over Icc 1 ((2Mj) * Nj)
  have hxle : x ≤ 2 * (T * 2 ^ j) * (x / (T * 2 ^ j) + 1) := by
    have h := le_mul_div_add (T * 2 ^ j) x hMj1
    calc x ≤ (T * 2 ^ j) * (x / (T * 2 ^ j) + 1) := h
      _ ≤ 2 * (T * 2 ^ j) * (x / (T * 2 ^ j) + 1) :=
          Nat.mul_le_mul_right _ (by omega)
  have hstep : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
          (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
              ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
                (if m * n ≤ y then (1 : ℂ) else 0)
                  * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                      then lambda3Coef T m else 0)
                  * 1 * χ ((m * n : ℕ) : ZMod q)‖) '' Set.Icc 1 x))
      ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
          (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
              ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
                (if m * n ≤ y then (1 : ℂ) else 0)
                  * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                      then lambda3Coef T m else 0)
                  * 1 * χ ((m * n : ℕ) : ZMod q)‖)
              '' Set.Icc 1 (2 * (T * 2 ^ j) * (x / (T * 2 ^ j) + 1))) := by
    refine Finset.sum_le_sum (fun q _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by positivity) (by positivity))
    refine Finset.sum_le_sum (fun χ _ => ?_)
    exact sSup_image_Icc_mono _ hx1 hxle
  refine le_trans hstep ?_
  have hcJ := hc Q (2 * (T * 2 ^ j)) (x / (T * 2 ^ j) + 1) (by omega) (by omega) hNj1
    (fun m => if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
      then lambda3Coef T m else 0) (fun _ => 1)
  refine le_trans hcJ ?_
  have hs : (∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
        ‖(if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
            then lambda3Coef T m else 0)‖ ^ 2) ≤ M * (Real.log (2 * M)) ^ 2 := by
    have hsub : Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j)) ⊆ Finset.Icc 1 (2 * (T * 2 ^ j)) :=
      Finset.Icc_subset_Icc (by omega) le_rfl
    have h1 : (∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
          ‖(if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
              then lambda3Coef T m else 0)‖ ^ 2)
        = ∑ m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j)), ‖lambda3Coef T m‖ ^ 2 := by
      rw [← Finset.sum_subset hsub (fun m _ hmnot => by rw [if_neg hmnot]; simp)]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [if_pos hm]
    rw [h1, hM]
    exact sum_lambda3Coef_sq_le T (T * 2 ^ j) hMj1
  have hb : (∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1), ‖(fun _ : ℕ => (1:ℂ)) n‖ ^ 2) = N := by
    rw [hN]
    have h1 : (∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1), ‖(fun _ : ℕ => (1:ℂ)) n‖ ^ 2)
        = ((x / (T * 2 ^ j) + 1 : ℕ) : ℝ) := by
      rw [show (∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1), ‖(fun _ : ℕ => (1:ℂ)) n‖ ^ 2)
            = ∑ _n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1), (1:ℝ) from
          Finset.sum_congr rfl (fun n _ => by simp)]
      rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
    exact h1
  rw [h2M, hb]
  have hstep2 : c * Real.sqrt ((2 * M + (Q:ℝ) ^ 2) * (∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
          ‖(if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
              then lambda3Coef T m else 0)‖ ^ 2))
        * Real.sqrt ((N + (Q:ℝ) ^ 2) * N) * Real.log (2 * (2 * M) * N + 2)
      ≤ c * Real.sqrt ((2 * M + (Q:ℝ) ^ 2) * (M * (Real.log (2 * M)) ^ 2))
        * Real.sqrt ((N + (Q:ℝ) ^ 2) * N) * Real.log (2 * (2 * M) * N + 2) := by
    have h := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 2 * M + (Q:ℝ)^2))
    have hlog0 : 0 ≤ Real.log (2 * (2 * M) * N + 2) := Real.log_nonneg (by nlinarith [hM0, hN0])
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (le_of_lt hcpos)) (Real.sqrt_nonneg _))
      hlog0
  refine le_trans hstep2 ?_
  exact block_bound_le c M N (x:ℝ) (Q:ℝ) L (le_of_lt hcpos) hM1 (by exact_mod_cast hx1) hMx hNle hN1 (by exact_mod_cast (by omega : 1 ≤ Q)) hL1 hlogM hlogN


/-- The main estimate. -/
theorem vaughan_type2_lambda3_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q T : ℕ, 2 ≤ x → 2 ≤ Q → 1 ≤ T → T ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc (T + 1) (T ^ 2),
              (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
                ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
                  ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
              * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
              + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 5 := by
  obtain ⟨c, hcpos, hc⟩ := maximal_bilinear_char_large_sieve_sSup
  refine ⟨100 * c, by positivity, fun x Q T hx hQ hT hTx => ?_⟩
  set K := Nat.log 2 (min (T ^ 2) x / T) + 1 with hK
  set L := Real.log ((x : ℝ) * (Q : ℝ) + 2) with hL
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) ≤ x := by positivity
  have hQ0 : (0:ℝ) ≤ Q := by positivity
  have hT0 : (0:ℝ) ≤ T := by positivity
  have hL1 : 1 ≤ L := by
    have h6 : (6:ℝ) ≤ (x:ℝ)*(Q:ℝ)+2 := by
      have : (2:ℝ) ≤ x := by exact_mod_cast hx
      have : (2:ℝ) ≤ Q := by exact_mod_cast hQ
      nlinarith
    have hlog6 : (1:ℝ) ≤ Real.log 6 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    exact le_trans hlog6 (Real.log_le_log (by norm_num) h6)
  -- basic dyadic index facts
  have hmT : T ≤ min (T ^ 2) x :=
    le_min (by rw [pow_two]; exact Nat.le_mul_of_pos_right T (by omega)) hTx
  have h2K : min (T ^ 2) x / T + 1 ≤ 2 ^ K := by
    rw [hK]
    exact Nat.succ_le_of_lt (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _)
  have hTKmin : min (T ^ 2) x ≤ T * 2 ^ K := by
    have hd := Nat.div_add_mod (min (T ^ 2) x) T
    have hmod : min (T ^ 2) x % T < T := Nat.mod_lt _ (by omega)
    have hmul : T * (min (T ^ 2) x / T) + T ≤ T * 2 ^ K := by
      have h := Nat.mul_le_mul_left T h2K
      rwa [Nat.mul_add, Nat.mul_one] at h
    omega
  have hMjx : ∀ j, j < K → T * 2 ^ j ≤ x := by
    intro j hj
    have hlogK : Nat.log 2 (min (T ^ 2) x / T) = K - 1 := by omega
    have hjle : j ≤ K - 1 := by omega
    have hMjle : T * 2 ^ j ≤ T * 2 ^ (K - 1) :=
      Nat.mul_le_mul_left T (Nat.pow_le_pow_right (by norm_num) hjle)
    have hne : min (T ^ 2) x / T ≠ 0 :=
      Nat.ne_of_gt (Nat.div_pos hmT (by omega))
    have hpow : 2 ^ (K - 1) ≤ min (T ^ 2) x / T := by
      have := Nat.pow_log_le_self 2 hne
      rwa [hlogK] at this
    have hTdiv : T * (min (T ^ 2) x / T) ≤ min (T ^ 2) x := by
      rw [mul_comm]; exact Nat.div_mul_le_self _ _
    have : T * 2 ^ j ≤ min (T ^ 2) x := by
      calc T * 2 ^ j ≤ T * 2 ^ (K - 1) := hMjle
        _ ≤ T * (min (T ^ 2) x / T) := Nat.mul_le_mul_left T hpow
        _ ≤ min (T ^ 2) x := hTdiv
    exact le_trans this (min_le_right _ _)
  -- Step A + B: reduce to the per-block real bounds
  have hAB : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc (T + 1) (T ^ 2),
              (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
                ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
                  ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
              * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) '' Set.Icc 1 x))
      ≤ 100 * c * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹
            + Q ^ 2 * Real.sqrt x) * L ^ 5 := by
    calc (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc (T + 1) (T ^ 2),
              (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
                ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
                  ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
              * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) '' Set.Icc 1 x))
        ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
              ∑ j ∈ Finset.range K,
                sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
                    ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
                      (if m * n ≤ y then (1 : ℂ) else 0)
                        * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                            then lambda3Coef T m else 0)
                        * 1 * χ ((m * n : ℕ) : ZMod q)‖) '' Set.Icc 1 x) := by
          refine Finset.sum_le_sum (fun q _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by positivity) (by positivity))
          refine Finset.sum_le_sum (fun χ _ => ?_)
          exact sup_le_sum_block_sup x T q hx1 hT hTx χ
      _ = ∑ j ∈ Finset.range K, ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
              sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
                  ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
                    (if m * n ≤ y then (1 : ℂ) else 0)
                      * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                          then lambda3Coef T m else 0)
                      * 1 * χ ((m * n : ℕ) : ZMod q)‖) '' Set.Icc 1 x) := by
          exact sum_swap_dep Q K
            (fun q => ((q : ℝ) / (q.totient : ℝ)))
            (fun q => (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ))
            (fun q χ j => sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 (2 * (T * 2 ^ j)),
                  ∑ n ∈ Finset.Icc 1 (x / (T * 2 ^ j) + 1),
                    (if m * n ≤ y then (1 : ℂ) else 0)
                      * (if m ∈ Finset.Icc (T * 2 ^ j + 1) (2 * (T * 2 ^ j))
                          then lambda3Coef T m else 0)
                      * 1 * χ ((m * n : ℕ) : ZMod q)‖) '' Set.Icc 1 x))
      _ ≤ ∑ j ∈ Finset.range K, 4 * c * L ^ 2 *
          (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ))
            + Q * x / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ) + Q ^ 2 * Real.sqrt x) := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have hjx : T * 2 ^ j ≤ x := hMjx j (Finset.mem_range.mp hj)
          simpa [hL] using per_block_bound c hc x Q T j hcpos hx hQ hT hjx

      -- Step C: analytic summation
      _ ≤ 100 * c * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹
            + Q ^ 2 * Real.sqrt x) * L ^ 5 := by
          have hKle : (K:ℝ) ≤ 3 * L := by
            have hmin : min (T ^ 2) x / T ≤ T := by
              have h1 : min (T ^ 2) x ≤ T * T := by
                calc min (T ^ 2) x ≤ T ^ 2 := min_le_left _ _
                  _ = T * T := by ring
              calc min (T ^ 2) x / T ≤ T * T / T := Nat.div_le_div_right h1
                _ = T := Nat.mul_div_cancel_left T (by omega)
            have hlogT : Real.log (T:ℝ) ≤ L := by
              rw [hL]
              apply Real.log_le_log (by positivity)
              have h1 : (T:ℝ) ≤ (x:ℝ) := by exact_mod_cast hTx
              have h2 : (2:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ
              nlinarith [hx0, hQ0]
            have hNatlog : (Nat.log 2 T : ℝ) ≤ 2 * L := by
              have h := nat_log_two_cast_le T hT
              have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
              have hlogT0 : 0 ≤ Real.log (T:ℝ) := Real.log_nonneg (by exact_mod_cast hT)
              have hdiv : Real.log (T:ℝ) / Real.log 2 ≤ Real.log (T:ℝ) / (1/2) :=
                div_le_div_of_nonneg_left hlogT0 (by norm_num) hlog2
              calc (Nat.log 2 T : ℝ) ≤ Real.log (T:ℝ) / Real.log 2 := h
                _ ≤ Real.log (T:ℝ) / (1/2) := hdiv
                _ = 2 * Real.log (T:ℝ) := by ring
                _ ≤ 2 * L := by linarith
            have hmono : Nat.log 2 (min (T ^ 2) x / T) ≤ Nat.log 2 T := Nat.log_mono_right hmin
            have hmono' : (Nat.log 2 (min (T ^ 2) x / T) : ℝ) ≤ (Nat.log 2 T : ℝ) := by
              exact_mod_cast hmono
            rw [hK]
            push_cast
            have := le_trans hmono' hNatlog
            linarith [hL1, this]
          have hK1 : (1:ℝ) ≤ K := by
            rw [hK]; push_cast; linarith [Nat.zero_le (Nat.log 2 (min (T ^ 2) x / T))]
          have hsum1 : (∑ j ∈ Finset.range K, Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ)))
              ≤ Real.sqrt x * (4 * Real.sqrt 2 * T) := by
            have hcast : ∀ j, Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ))
                = Real.sqrt x * Real.sqrt ((T * 2 ^ j : ℕ) : ℝ) := fun j =>
              Real.sqrt_mul (by positivity) _
            rw [Finset.sum_congr rfl (fun j _ => hcast j), ← Finset.mul_sum]
            apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg x)
            have hcast2 : ∀ j, Real.sqrt ((T * 2 ^ j : ℕ) : ℝ)
                = Real.sqrt ((T:ℝ) * (2:ℝ)^j) := by
              intro j; congr 1; push_cast; ring
            rw [Finset.sum_congr rfl (fun j _ => hcast2 j)]
            have h := sum_range_sqrt_two_pow_mul_le T K hT
            have hle2 : T * 2 ^ K ≤ 2 * min (T ^ 2) x := by
              have hne : min (T ^ 2) x / T ≠ 0 := Nat.ne_of_gt (Nat.div_pos hmT (by omega))
              have hple : 2 ^ Nat.log 2 (min (T ^ 2) x / T) ≤ min (T ^ 2) x / T :=
                Nat.pow_log_le_self 2 hne
              have h2K : 2 ^ K = 2 ^ Nat.log 2 (min (T ^ 2) x / T) * 2 := by
                rw [hK, Nat.pow_succ]
              have hTdivle : T * (min (T ^ 2) x / T) ≤ min (T ^ 2) x := by
                rw [mul_comm]; exact Nat.div_mul_le_self _ _
              rw [h2K]
              calc T * (2 ^ Nat.log 2 (min (T ^ 2) x / T) * 2)
                  = 2 * (T * 2 ^ Nat.log 2 (min (T ^ 2) x / T)) := by ring
                _ ≤ 2 * (T * (min (T ^ 2) x / T)) :=
                    Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left T hple)
                _ ≤ 2 * min (T ^ 2) x := Nat.mul_le_mul_left 2 hTdivle
            have hTK : (T:ℝ) * (2:ℝ)^K ≤ 2 * (T:ℝ)^2 := by
              have h1 : T * 2 ^ K ≤ 2 * (T ^ 2) :=
                le_trans hle2 (Nat.mul_le_mul_left 2 (min_le_left _ _))
              have hh : ((T * 2 ^ K : ℕ) : ℝ) ≤ 2 * ((T ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
              have e1 : ((T * 2 ^ K : ℕ) : ℝ) = (T:ℝ) * (2:ℝ)^K := by push_cast; ring
              have e2 : ((T ^ 2 : ℕ) : ℝ) = (T:ℝ)^2 := by push_cast; ring
              rw [e1, e2] at hh
              exact hh
            calc (∑ j ∈ Finset.range K, Real.sqrt ((T:ℝ) * (2:ℝ)^j))
                ≤ 4 * Real.sqrt ((T:ℝ) * (2:ℝ)^K) := h
              _ ≤ 4 * Real.sqrt (2 * (T:ℝ)^2) :=
                  mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTK) (by norm_num)
              _ = 4 * Real.sqrt 2 * T := by
                  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq (by positivity)]
                  ring
          have hsum2 : (∑ j ∈ Finset.range K, (Real.sqrt ((T * 2 ^ j : ℕ) : ℝ))⁻¹)
              ≤ (K:ℝ) * (Real.sqrt T)⁻¹ := by
            have hle : ∀ j, (Real.sqrt ((T * 2 ^ j : ℕ) : ℝ))⁻¹ ≤ (Real.sqrt T)⁻¹ := by
              intro j
              have hcast : Real.sqrt ((T * 2 ^ j : ℕ) : ℝ) = Real.sqrt ((T:ℝ) * (2:ℝ)^j) := by
                congr 1; push_cast; ring
              have h1 : Real.sqrt (T:ℝ) ≤ Real.sqrt ((T:ℝ) * (2:ℝ)^j) := by
                apply Real.sqrt_le_sqrt
                have : (1:ℝ) ≤ (2:ℝ)^j := by exact_mod_cast Nat.one_le_pow j 2 (by norm_num)
                nlinarith
              have h2 : 0 < Real.sqrt (T:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hT)
              rw [hcast]
              simpa [one_div] using one_div_le_one_div_of_le h2 h1
            calc (∑ j ∈ Finset.range K, (Real.sqrt ((T * 2 ^ j : ℕ) : ℝ))⁻¹)
                ≤ ∑ _j ∈ Finset.range K, (Real.sqrt T)⁻¹ := Finset.sum_le_sum (fun j _ => hle j)
              _ = (K:ℝ) * (Real.sqrt T)⁻¹ := by
                  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hterm : (∑ j ∈ Finset.range K,
                (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ))
                  + Q * x / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ) + Q ^ 2 * Real.sqrt x))
              ≤ (K:ℝ) * (Real.sqrt 2 * x) + (K:ℝ) * (8 * Q * Real.sqrt x * T)
                + (K:ℝ) * (Q * x * (Real.sqrt T)⁻¹) + (K:ℝ) * (Q ^ 2 * Real.sqrt x) := by
            have e1 : (∑ j ∈ Finset.range K, Real.sqrt 2 * x) = (K:ℝ) * (Real.sqrt 2 * x) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have e4 : (∑ j ∈ Finset.range K, Q ^ 2 * Real.sqrt x)
                = (K:ℝ) * (Q ^ 2 * Real.sqrt x) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have e2 : (∑ j ∈ Finset.range K,
                  Real.sqrt 2 * Q * Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ)))
                ≤ (K:ℝ) * (8 * Q * Real.sqrt x * T) := by
              have h2 : (∑ j ∈ Finset.range K, Real.sqrt 2 * Q * Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ)))
                  = Real.sqrt 2 * Q * ∑ j ∈ Finset.range K, Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ)) := by
                rw [Finset.mul_sum]
              rw [h2]
              have h3 : Real.sqrt 2 * Q * (Real.sqrt x * (4 * Real.sqrt 2 * T))
                  = 8 * Q * Real.sqrt x * T := by
                have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
                calc Real.sqrt 2 * Q * (Real.sqrt x * (4 * Real.sqrt 2 * T))
                    = 4 * (Real.sqrt 2 * Real.sqrt 2) * Q * Real.sqrt x * T := by ring
                  _ = 8 * Q * Real.sqrt x * T := by rw [hs]; ring
              calc Real.sqrt 2 * Q * (∑ j ∈ Finset.range K, Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ)))
                  ≤ Real.sqrt 2 * Q * (Real.sqrt x * (4 * Real.sqrt 2 * T)) :=
                    mul_le_mul_of_nonneg_left hsum1 (by positivity)
                _ = 8 * Q * Real.sqrt x * T := h3
                _ ≤ (K:ℝ) * (8 * Q * Real.sqrt x * T) := by
                    have hnn : (0:ℝ) ≤ 8 * Q * Real.sqrt x * T := by positivity
                    nlinarith [mul_le_mul_of_nonneg_left hK1 hnn]
            have e3 : (∑ j ∈ Finset.range K, Q * x / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ))
                ≤ (K:ℝ) * (Q * x * (Real.sqrt T)⁻¹) := by
              have h2 : (∑ j ∈ Finset.range K, Q * x / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ))
                  = Q * x * ∑ j ∈ Finset.range K, (Real.sqrt ((T * 2 ^ j : ℕ) : ℝ))⁻¹ := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl (fun j _ => ?_)
                rw [div_eq_mul_inv]
              rw [h2]
              calc Q * x * (∑ j ∈ Finset.range K, (Real.sqrt ((T * 2 ^ j : ℕ) : ℝ))⁻¹)
                  ≤ Q * x * ((K:ℝ) * (Real.sqrt T)⁻¹) :=
                    mul_le_mul_of_nonneg_left hsum2 (by positivity)
                _ = (K:ℝ) * (Q * x * (Real.sqrt T)⁻¹) := by ring
            have haux : (∑ j ∈ Finset.range K,
                  (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ))
                    + Q * x / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ) + Q ^ 2 * Real.sqrt x))
                = (∑ j ∈ Finset.range K, Real.sqrt 2 * x)
                  + (∑ j ∈ Finset.range K, Real.sqrt 2 * Q * Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ)))
                  + (∑ j ∈ Finset.range K, Q * x / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ))
                  + (∑ j ∈ Finset.range K, Q ^ 2 * Real.sqrt x) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
            rw [haux, e1, e4]
            linarith [e2, e3]
          have hX : (0:ℝ) ≤ x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹ + Q ^ 2 * Real.sqrt x := by
            have h1 : (0:ℝ) ≤ Q * Real.sqrt x * T := by positivity
            have h2 : (0:ℝ) ≤ Q * x * (Real.sqrt T)⁻¹ := by positivity
            have h3 : (0:ℝ) ≤ Q ^ 2 * Real.sqrt x := by positivity
            linarith [hx0]
          have hcoef : Real.sqrt 2 * x + 8 * Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹
                + Q ^ 2 * Real.sqrt x
              ≤ 8 * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹ + Q ^ 2 * Real.sqrt x) := by
            have h1 : Real.sqrt 2 * x ≤ 8 * x := by
              have h2 : Real.sqrt 2 ≤ 8 := by
                have h := Real.sqrt_le_sqrt (by norm_num : (2:ℝ) ≤ 64)
                rwa [show Real.sqrt 64 = 8 from by
                  rw [show (64:ℝ) = 8^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
              nlinarith [h2, hx0]
            have h3 : (0:ℝ) ≤ Q * x * (Real.sqrt T)⁻¹ := by positivity
            have h4 : (0:ℝ) ≤ Q ^ 2 * Real.sqrt x := by positivity
            have h5 : (0:ℝ) ≤ Q * Real.sqrt x * T := by positivity
            have h2 : 8 * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹ + Q ^ 2 * Real.sqrt x)
                = 8 * x + 8 * Q * Real.sqrt x * T + 8 * Q * x * (Real.sqrt T)⁻¹
                  + 8 * Q ^ 2 * Real.sqrt x := by ring
            rw [h2]
            linarith [h1, h3, h4, h5]
          have hSnn : (0:ℝ) ≤ Real.sqrt 2 * x + 8 * Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹
              + Q ^ 2 * Real.sqrt x := by
            have h1 : (0:ℝ) ≤ Real.sqrt 2 * x := by positivity
            have h2 : (0:ℝ) ≤ 8 * Q * Real.sqrt x * T := by positivity
            have h3 : (0:ℝ) ≤ Q * x * (Real.sqrt T)⁻¹ := by positivity
            have h4 : (0:ℝ) ≤ Q ^ 2 * Real.sqrt x := by positivity
            linarith
          calc (∑ j ∈ Finset.range K, 4 * c * L ^ 2 *
                (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ))
                  + Q * x / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ) + Q ^ 2 * Real.sqrt x))
              = 4 * c * L ^ 2 * (∑ j ∈ Finset.range K,
                (Real.sqrt 2 * x + Real.sqrt 2 * Q * Real.sqrt ((x:ℝ) * ((T * 2 ^ j : ℕ) : ℝ))
                  + Q * x / Real.sqrt ((T * 2 ^ j : ℕ) : ℝ) + Q ^ 2 * Real.sqrt x)) := by
                rw [Finset.mul_sum]
            _ ≤ 4 * c * L ^ 2 * ((K:ℝ) * (Real.sqrt 2 * x) + (K:ℝ) * (8 * Q * Real.sqrt x * T)
                  + (K:ℝ) * (Q * x * (Real.sqrt T)⁻¹) + (K:ℝ) * (Q ^ 2 * Real.sqrt x)) :=
                mul_le_mul_of_nonneg_left hterm (by positivity)
            _ = 4 * c * L ^ 2 * K * (Real.sqrt 2 * x + 8 * Q * Real.sqrt x * T
                  + Q * x * (Real.sqrt T)⁻¹ + Q ^ 2 * Real.sqrt x) := by ring
            _ ≤ 4 * c * L ^ 2 * (3 * L) * (8 * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹
                  + Q ^ 2 * Real.sqrt x)) := by
                have h1 : 4 * c * L ^ 2 * K ≤ 4 * c * L ^ 2 * (3 * L) :=
                  mul_le_mul_of_nonneg_left hKle (by positivity)
                exact mul_le_mul h1 hcoef (by positivity) (by positivity)
            _ = 96 * c * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹
                  + Q ^ 2 * Real.sqrt x) * (L ^ 2 * L) := by ring
            _ ≤ 100 * c * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹
                  + Q ^ 2 * Real.sqrt x) * L ^ 5 := by
                have h3 : L ^ 2 * L ≤ L ^ 5 := by
                  rw [show L ^ 2 * L = L ^ 3 by ring]
                  exact pow_le_pow_right₀ (by linarith) (by norm_num)
                have h3nn : 0 ≤ L ^ 2 * L := by positivity
                have hg : 96 * c * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹ + Q ^ 2 * Real.sqrt x) * (L ^ 2 * L)
                    ≤ 100 * c * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹ + Q ^ 2 * Real.sqrt x) * (L ^ 2 * L) := by
                  apply mul_le_mul_of_nonneg_right _ h3nn
                  nlinarith [hcpos, hX]
                have hh : 100 * c * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹ + Q ^ 2 * Real.sqrt x) * (L ^ 2 * L)
                    ≤ 100 * c * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹ + Q ^ 2 * Real.sqrt x) * L ^ 5 :=
                  mul_le_mul_of_nonneg_left h3 (by positivity)
                linarith [hg, hh]
  refine le_trans hAB ?_
  have hconv : 100 * c * (x + Q * Real.sqrt x * T + Q * x * (Real.sqrt T)⁻¹ + Q ^ 2 * Real.sqrt x) * L ^ 5
      = 100 * c * ((x : ℝ) + (Q : ℝ) * (x : ℝ) ^ (1 / 2 : ℝ) * (T : ℝ)
              + (Q : ℝ) * (x : ℝ) * ((T : ℝ) ^ (1 / 2 : ℝ))⁻¹
              + (Q : ℝ) ^ 2 * (x : ℝ) ^ (1 / 2 : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 5 := by
    rw [hL, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  rw [← hconv]


end Commons.NumberTheory.BombieriVinogradov
