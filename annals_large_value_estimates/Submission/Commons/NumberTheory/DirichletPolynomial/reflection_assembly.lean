import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.kerr_coefficient_majorant
import Submission.Commons.NumberTheory.DirichletPolynomial.dirichlet_poly_increase_length

namespace Commons.NumberTheory.DirichletPolynomial

open Finset
set_option autoImplicit false

set_option maxHeartbeats 1600000

noncomputable section

/-- The atomic term `n^{iτ}/√n` of a Dirichlet polynomial. -/
def raTerm (n : ℕ) (τ : ℝ) : ℂ :=
  (n : ℂ) ^ (Complex.I * (τ : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)

/-- The coefficient-free Dirichlet block sum `∑_{A ≤ n ≤ B} n^{iτ}/√n`. -/
def raBlock (A B : ℕ) (τ : ℝ) : ℂ := ∑ n ∈ Finset.Icc A B, raTerm n τ

/-- The number of pairs `(i,j)` with `|t i - t j| ≤ W`, as a real number. -/
def raPC (W : ℝ) (R : ℕ) (t : Fin R → ℝ) : ℝ :=
  ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ W then (1 : ℝ) else 0)

/-- The coefficient-free Dirichlet difference sum over the block `[A,B]` with window `W`. -/
def raDS (A B : ℕ) (W : ℝ) (R : ℕ) (t : Fin R → ℝ) : ℝ :=
  ∑ i : Fin R, ∑ j : Fin R,
    (if |t i - t j| ≤ W then ‖raBlock A B (t i - t j)‖ ^ 2 else 0)

/-- The annulus `W ≤ |τ| ≤ 2W` difference sum at scale `N`. -/
def raAnn (N : ℕ) (W : ℝ) (R : ℕ) (t : Fin R → ℝ) : ℝ :=
  ∑ i : Fin R, ∑ j : Fin R,
    (if W ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * W then ‖raBlock N (2 * N) (t i - t j)‖ ^ 2
      else 0)

lemma raPC_nonneg (W : ℝ) (R : ℕ) (t : Fin R → ℝ) : 0 ≤ raPC W R t :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

lemma raDS_nonneg (A B : ℕ) (W : ℝ) (R : ℕ) (t : Fin R → ℝ) : 0 ≤ raDS A B W R t :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

lemma raAnn_nonneg (N : ℕ) (W : ℝ) (R : ℕ) (t : Fin R → ℝ) : 0 ≤ raAnn N W R t :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

lemma raPC_window_le {W₁ W₂ : ℝ} (h : W₁ ≤ W₂) (R : ℕ) (t : Fin R → ℝ) :
    raPC W₁ R t ≤ raPC W₂ R t := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hc : |t i - t j| ≤ W₁
  · rw [if_pos hc, if_pos (le_trans hc h)]
  · rw [if_neg hc]; split_ifs <;> norm_num

lemma raDS_window_le {W₁ W₂ : ℝ} (h : W₁ ≤ W₂) (A B : ℕ) (R : ℕ) (t : Fin R → ℝ) :
    raDS A B W₁ R t ≤ raDS A B W₂ R t := by
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hc : |t i - t j| ≤ W₁
  · rw [if_pos hc, if_pos (le_trans hc h)]
  · rw [if_neg hc]; split_ifs <;> positivity

private lemma raTerm_normSq (n : ℕ) (τ : ℝ) (hn : 1 ≤ n) : ‖raTerm n τ‖ ^ 2 = (n : ℝ)⁻¹ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : ‖(n : ℂ) ^ (Complex.I * (τ : ℂ))‖ = 1 := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    have : (Complex.I * (τ : ℂ)).re = 0 := by simp
    rw [this, Real.rpow_zero]
  have h2 : ‖((Real.sqrt (n : ℝ) : ℝ) : ℂ)‖ = Real.sqrt (n : ℝ) :=
    Complex.norm_of_nonneg (Real.sqrt_nonneg _)
  rw [raTerm, norm_div, h1, h2]
  rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hnpos), one_div]

private lemma raTerm_norm_le_one (n : ℕ) (τ : ℝ) (hn : 1 ≤ n) : ‖raTerm n τ‖ ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := raTerm_normSq n τ hn
  have hinv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hn1
  have hnn : 0 ≤ ‖raTerm n τ‖ := norm_nonneg _
  nlinarith [h, hinv, hnn]

private lemma four_sq_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

private lemma ceil_le_two_ceil_half (x : ℝ) : Nat.ceil x ≤ 2 * Nat.ceil (x / 2) := by
  rw [Nat.ceil_le]
  have h := Nat.le_ceil (x / 2)
  push_cast
  linarith

private lemma four_ceil_half_le (x : ℝ) (hx : 0 ≤ x) : 4 * Nat.ceil (x / 2) ≤ 2 * Nat.ceil x + 4 := by
  have h1 : (Nat.ceil (x / 2) : ℝ) < x / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have h2 : x ≤ (Nat.ceil x : ℝ) := by
    have := Nat.le_ceil x; linarith
  have h3 : (4 * Nat.ceil (x / 2) : ℝ) < ((2 * Nat.ceil x + 4 : ℕ) : ℝ) := by
    push_cast
    linarith
  have h4 : (4 * Nat.ceil (x / 2) : ℝ) ≤ ((2 * Nat.ceil x + 4 : ℕ) : ℝ) := le_of_lt h3
  exact_mod_cast h4

private lemma raBlock_split (a b : ℕ) (τ : ℝ) (ha : 1 ≤ a) (ha2 : 2 * a ≤ b)
    (h1 : 4 * a ≤ b + 4) (h2 : b ≤ 4 * a) :
    ‖raBlock a b τ‖ ^ 2
      ≤ 4 * ‖raBlock a (2 * a) τ‖ ^ 2 + 8 * ‖raBlock (2 * a) (4 * a) τ‖ ^ 2 + 72 := by
  set B1 := ∑ n ∈ Finset.Icc (2 * a + 1) b, raTerm n τ with hB1
  set D := ∑ n ∈ Finset.Icc (b + 1) (4 * a), raTerm n τ with hD
  have hI1 : Finset.Icc a b = Finset.Icc a (2 * a) ∪ Finset.Icc (2 * a + 1) b := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj1 : Disjoint (Finset.Icc a (2 * a)) (Finset.Icc (2 * a + 1) b) := by
    rw [Finset.disjoint_left]
    intro n hn1
    simp only [Finset.mem_Icc] at hn1
    intro hn2
    simp only [Finset.mem_Icc] at hn2
    omega
  have hI2 : Finset.Icc (2 * a) (4 * a)
      = {2 * a} ∪ Finset.Icc (2 * a + 1) b ∪ Finset.Icc (b + 1) (4 * a) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
  have hdisj2 : Disjoint ({2 * a} : Finset ℕ) (Finset.Icc (2 * a + 1) b) := by
    rw [Finset.disjoint_left]
    intro n hn1
    simp only [Finset.mem_singleton] at hn1
    intro hn2
    simp only [Finset.mem_Icc] at hn2
    omega
  have hdu : Disjoint ({2 * a} ∪ Finset.Icc (2 * a + 1) b : Finset ℕ)
      (Finset.Icc (b + 1) (4 * a)) := by
    rw [Finset.disjoint_left]
    intro n hn1
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc] at hn1
    intro hn2
    simp only [Finset.mem_Icc] at hn2
    omega
  have e1 : raBlock a b τ = raBlock a (2 * a) τ + B1 := by
    unfold raBlock
    rw [hI1, Finset.sum_union hdisj1, ← hB1]
  have e2 : raBlock (2 * a) (4 * a) τ = raTerm (2 * a) τ + B1 + D := by
    unfold raBlock
    rw [hI2, Finset.sum_union hdu, Finset.sum_union hdisj2, Finset.sum_singleton, ← hB1, ← hD]
  have hS : raBlock a b τ
      = raBlock a (2 * a) τ + raBlock (2 * a) (4 * a) τ - raTerm (2 * a) τ - D := by
    rw [e1, e2]; ring
  have hnorm : ‖raBlock a b τ‖
      ≤ ‖raBlock a (2 * a) τ‖ + ‖raBlock (2 * a) (4 * a) τ‖ + ‖raTerm (2 * a) τ‖ + ‖D‖ := by
    rw [hS]
    have h1' := norm_sub_le (raBlock a (2 * a) τ + raBlock (2 * a) (4 * a) τ - raTerm (2 * a) τ) D
    have h2' := norm_sub_le (raBlock a (2 * a) τ + raBlock (2 * a) (4 * a) τ) (raTerm (2 * a) τ)
    have h3' := norm_add_le (raBlock a (2 * a) τ) (raBlock (2 * a) (4 * a) τ)
    linarith
  have hsq : ‖raBlock a b τ‖ ^ 2
      ≤ (‖raBlock a (2 * a) τ‖ + ‖raBlock (2 * a) (4 * a) τ‖ + ‖raTerm (2 * a) τ‖ + ‖D‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hz : ‖raTerm (2 * a) τ‖ ≤ 1 := by
    apply raTerm_norm_le_one
    omega
  have hD' : ‖D‖ ≤ 4 := by
    have hcard : (Finset.Icc (b + 1) (4 * a)).card = 4 * a - b := by
      rw [Nat.card_Icc]; omega
    calc ‖D‖ ≤ ∑ n ∈ Finset.Icc (b + 1) (4 * a), ‖raTerm n τ‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc (b + 1) (4 * a), (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro n hn
            apply raTerm_norm_le_one
            simp only [Finset.mem_Icc] at hn
            omega
      _ = ((Finset.Icc (b + 1) (4 * a)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ((4 * a - b : ℕ) : ℝ) := by rw [hcard]
      _ ≤ 4 := by
            have h : 4 * a - b ≤ 4 := by omega
            exact_mod_cast h
  have hz2 : ‖raTerm (2 * a) τ‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (raTerm (2 * a) τ), hz]
  have hD2 : ‖D‖ ^ 2 ≤ 16 := by
    nlinarith [norm_nonneg D, hD']
  have h4 := four_sq_le ‖raBlock a (2 * a) τ‖ ‖raBlock (2 * a) (4 * a) τ‖
    ‖raTerm (2 * a) τ‖ ‖D‖
  nlinarith [hsq, h4, hz2, hD2, sq_nonneg ‖raBlock a (2 * a) τ‖,
    sq_nonneg ‖raBlock (2 * a) (4 * a) τ‖]

private lemma sum_sum_combine {R : ℕ} (X Y Z : Fin R → Fin R → ℝ) :
    (∑ i, ∑ j, (4 * X i j + 8 * Y i j + 72 * Z i j))
      = 4 * (∑ i, ∑ j, X i j) + 8 * (∑ i, ∑ j, Y i j) + 72 * (∑ i, ∑ j, Z i j) := by
  simp only [Finset.sum_add_distrib, Finset.mul_sum]

private lemma raDS_block_split (a b : ℕ) (W : ℝ) (R : ℕ) (t : Fin R → ℝ)
    (ha : 1 ≤ a) (ha2 : 2 * a ≤ b) (h1 : 4 * a ≤ b + 4) (h2 : b ≤ 4 * a) :
    raDS a b W R t ≤ 4 * raDS a (2 * a) W R t + 8 * raDS (2 * a) (4 * a) W R t
      + 72 * raPC W R t := by
  unfold raDS raPC
  have hterm : ∀ i j : Fin R,
      (if |t i - t j| ≤ W then ‖raBlock a b (t i - t j)‖ ^ 2 else 0)
      ≤ 4 * (if |t i - t j| ≤ W then ‖raBlock a (2 * a) (t i - t j)‖ ^ 2 else 0)
        + 8 * (if |t i - t j| ≤ W then ‖raBlock (2 * a) (4 * a) (t i - t j)‖ ^ 2 else 0)
        + 72 * (if |t i - t j| ≤ W then (1 : ℝ) else 0) := by
    intro i j
    by_cases hc : |t i - t j| ≤ W
    · rw [if_pos hc, if_pos hc, if_pos hc, if_pos hc]
      simpa using raBlock_split a b (t i - t j) ha ha2 h1 h2
    · rw [if_neg hc, if_neg hc, if_neg hc, if_neg hc]; norm_num
  calc (∑ i, ∑ j, (if |t i - t j| ≤ W then ‖raBlock a b (t i - t j)‖ ^ 2 else 0))
      ≤ ∑ i, ∑ j, (4 * (if |t i - t j| ≤ W then ‖raBlock a (2 * a) (t i - t j)‖ ^ 2 else 0)
          + 8 * (if |t i - t j| ≤ W then ‖raBlock (2 * a) (4 * a) (t i - t j)‖ ^ 2 else 0)
          + 72 * (if |t i - t j| ≤ W then (1 : ℝ) else 0)) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact hterm i j
    _ = 4 * (∑ i, ∑ j, (if |t i - t j| ≤ W then ‖raBlock a (2 * a) (t i - t j)‖ ^ 2 else 0))
        + 8 * (∑ i, ∑ j, (if |t i - t j| ≤ W then ‖raBlock (2 * a) (4 * a) (t i - t j)‖ ^ 2 else 0))
        + 72 * (∑ i, ∑ j, (if |t i - t j| ≤ W then (1 : ℝ) else 0)) := by
        exact sum_sum_combine _ _ _

private lemma sum_sum_sum_swap {R : ℕ} (f : Fin R → Fin R → ℕ → ℝ) (s : Finset ℕ) :
    (∑ i, ∑ j, ∑ k ∈ s, f i j k) = ∑ k ∈ s, ∑ i, ∑ j, f i j k := by
  have h1 : ∀ i : Fin R, (∑ j, ∑ k ∈ s, f i j k) = ∑ k ∈ s, ∑ j, f i j k :=
    fun i => Finset.sum_comm
  simp only [h1]
  exact Finset.sum_comm

private lemma sum_sum_add_sum_swap {R : ℕ} (A : Fin R → Fin R → ℝ)
    (f : Fin R → Fin R → ℕ → ℝ) (s : Finset ℕ) :
    (∑ i, ∑ j, (A i j + ∑ k ∈ s, f i j k))
      = (∑ i, ∑ j, A i j) + ∑ k ∈ s, ∑ i, ∑ j, f i j k := by
  simp only [Finset.sum_add_distrib]
  rw [sum_sum_sum_swap]

private lemma dyadic_cover_window {b b₀ x : ℝ} (hb₀ : 0 < b₀) (hb₀b : b₀ ≤ b) (hx0 : 0 ≤ x)
    (hxb : x ≤ b) :
    x ≤ b₀ ∨ ∃ k : ℕ, 1 ≤ k ∧ b / (2 : ℝ) ^ k ≤ x ∧ x ≤ b / (2 : ℝ) ^ (k - 1) := by
  by_cases h : x ≤ b₀
  · exact Or.inl h
  · push_neg at h
    have hbpos : 0 < b := lt_of_lt_of_le hb₀ hb₀b
    have hxpos : 0 < x := lt_trans hb₀ h
    have hex : ∃ k : ℕ, b / (2 : ℝ) ^ k ≤ x := by
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / x) (by norm_num : (1 : ℝ) < 2)
      refine ⟨n, ?_⟩
      have hn' : b / x < (2 : ℝ) ^ n := hn
      rw [div_lt_iff₀ hxpos] at hn'
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
      linarith
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · have hK : b / (2 : ℝ) ^ 0 ≤ x := by
        have hfs := Nat.find_spec hex
        rw [h0] at hfs
        exact hfs
      have hbeq : x = b := by
        simp only [pow_zero, div_one] at hK
        exact le_antisymm hxb hK
      refine Or.inr ⟨1, le_refl 1, ?_, ?_⟩
      · rw [hbeq, pow_one]
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith
      · rw [hbeq]
        norm_num
    · refine Or.inr ⟨Nat.find hex, hpos, Nat.find_spec hex, ?_⟩
      have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
      push_neg at hmin
      exact le_of_lt hmin
theorem reflection_assembly
    (hmv : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → (N : ℝ) ≤ Δ →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * Δ ^ ε *
      ((N : ℝ) * (R : ℝ) + (Δ / (N : ℝ)) * (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then (1 : ℝ) else 0))))
    (hmain : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → (N : ℝ) ≤ Δ →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if Δ ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * Δ ^ ε *
      ((∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ 2 * Δ then
          ‖∑ n ∈ Finset.Icc (Nat.ceil (Δ / (2 * (N : ℝ)))) (2 * Nat.ceil (Δ / (N : ℝ))),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0))
      + (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ 2 * Δ then (1 : ℝ) else 0)))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 1 ≤ Δ → (N : ℝ) ≤ Δ → ∀ (B : ℝ), 1 ≤ B →
    ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ B) → ∀ (R : ℕ) (t : Fin R → ℝ),
    (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * B ^ 2 * Δ ^ ε *
      ((∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0))
      + (∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then (1 : ℝ) else 0))
      + (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1)) := by
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨Cmv, hCmvp, hmvε⟩ := hmv (ε / 4) hε4
  obtain ⟨Cmn, hCmnp, hmainε⟩ := hmain (ε / 4) hε4
  obtain ⟨Cinc, hCincp, hincε⟩ := dirichlet_poly_increase_length (ε / 4) hε4
  obtain ⟨Cmaj, hCmajp, hmaj⟩ := kerr_coefficient_majorant
  clear hmv hmain
  set p5 : ℝ := (5 : ℝ) ^ (ε / 4) with hp5
  set Clog : ℝ := 1 / ((ε / 4) * Real.log 2) + 1 with hClog
  set KQ : ℝ := 3 * Cmv + Clog * Cmn * (12 * Cinc * p5 + 73) + 1 with hKQ
  have hp5pos : 0 < p5 := by rw [hp5]; positivity
  have hClogpos : 0 < Clog := by rw [hClog]; positivity
  have hKQpos : 0 < KQ := by rw [hKQ]; positivity
  refine ⟨Cmaj * KQ + 1, by positivity, ?_⟩
  intro N hN Δ hΔ1 hNΔ B hB c hc R t hsep
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hΔpos : (0 : ℝ) < Δ := by linarith
  have hmaj' : (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0)) ≤ Cmaj * B ^ 2 * raDS N (2 * N) Δ R t := by
    have h := hmaj N hN Δ hΔpos B hB c hc R t hsep
    simpa only [raDS, raBlock, raTerm] using h
  have hΔeps4 : Δ ^ (ε / 4) ≤ Δ ^ ε := Real.rpow_le_rpow_of_exponent_le hΔ1 (by linarith)
  have hΔeps4nn : 0 ≤ Δ ^ (ε / 4) := Real.rpow_nonneg (le_of_lt hΔpos) _
  have hΔepsnn : 0 ≤ Δ ^ ε := Real.rpow_nonneg (le_of_lt hΔpos) _
  have hΔpm : ∀ a b : ℝ, Δ ^ a * Δ ^ b = Δ ^ (a + b) := fun a b => (Real.rpow_add hΔpos a b).symm
  have hQ : raDS N (2 * N) Δ R t ≤ KQ * Δ ^ ε *
      (raDS (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)) Δ R t
        + raPC Δ R t + (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1)) := by
    set SD : ℝ := raDS (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)) Δ R t with hSD
    set BT : ℝ := (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1) with hBT
    have hSDnn : 0 ≤ SD := by rw [hSD]; exact raDS_nonneg _ _ _ _ _
    have hBTnn : 0 ≤ BT := by rw [hBT]; positivity
    have hPCnn : 0 ≤ raPC Δ R t := raPC_nonneg Δ R t
    have hNR : (N : ℝ) * (R : ℝ) ≤ BT := by
      rw [hBT]
      have h1 : (N : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
        have h2 := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (1 : ℝ) ≤ 1 + ε)
        simpa using h2
      calc (N : ℝ) * (R : ℝ) ≤ (N : ℝ) ^ (1 + ε) * (R : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rcases le_or_gt Δ (2 * (N : ℝ)) with hcaseA | hcaseB
    · -- Case A
      have h1 : raDS N (2 * N) Δ R t ≤ Cmv * Δ ^ (ε / 4) *
          ((N : ℝ) * (R : ℝ) + (Δ / (N : ℝ)) * raPC Δ R t) := by
        have h := hmvε N hN Δ hΔ1 hNΔ R t hsep
        simpa only [raDS, raPC, raBlock, raTerm] using h
      have hDN : Δ / (N : ℝ) ≤ 2 := by rw [div_le_iff₀ hNpos]; linarith
      have h2 : raDS N (2 * N) Δ R t ≤
          Cmv * Δ ^ (ε / 4) * ((N : ℝ) * (R : ℝ) + 2 * raPC Δ R t) := by
        refine le_trans h1 ?_
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (le_of_lt hCmvp) hΔeps4nn)
        nlinarith [hDN, hPCnn]
      have hbr : (N : ℝ) * (R : ℝ) + 2 * raPC Δ R t ≤ 3 * (SD + raPC Δ R t + BT) := by
        nlinarith [hNR, hSDnn, hPCnn, hBTnn]
      have h3 : 3 * Cmv ≤ KQ := by
        rw [hKQ]
        have hpos : 0 ≤ Clog * Cmn * (12 * Cinc * p5 + 73) := by positivity
        linarith
      have hcomb_nn : 0 ≤ SD + raPC Δ R t + BT := by linarith
      calc raDS N (2 * N) Δ R t
            ≤ Cmv * Δ ^ (ε / 4) * ((N : ℝ) * (R : ℝ) + 2 * raPC Δ R t) := h2
        _ ≤ Cmv * Δ ^ (ε / 4) * (3 * (SD + raPC Δ R t + BT)) :=
              mul_le_mul_of_nonneg_left hbr (mul_nonneg (le_of_lt hCmvp) hΔeps4nn)
        _ = 3 * Cmv * Δ ^ (ε / 4) * (SD + raPC Δ R t + BT) := by ring
        _ ≤ KQ * Δ ^ ε * (SD + raPC Δ R t + BT) := by
              have h4 : 3 * Cmv * Δ ^ (ε / 4) ≤ KQ * Δ ^ ε := by
                have h5 : 3 * Cmv * Δ ^ (ε / 4) ≤ KQ * Δ ^ (ε / 4) :=
                  mul_le_mul_of_nonneg_right h3 hΔeps4nn
                have h6 : KQ * Δ ^ (ε / 4) ≤ KQ * Δ ^ ε :=
                  mul_le_mul_of_nonneg_left hΔeps4 (le_of_lt hKQpos)
                linarith
              exact mul_le_mul_of_nonneg_right h4 hcomb_nn
    · -- Case B
      have h2Nlt : 2 * (N : ℝ) < Δ := hcaseB
      set W : ℕ → ℝ := fun k => Δ / (2 : ℝ) ^ k with hW
      have hW0 : W 0 = Δ := by show Δ / (2 : ℝ) ^ 0 = Δ; norm_num
      have hWpos : ∀ k, 0 < W k := by intro k; show 0 < Δ / (2 : ℝ) ^ k; positivity
      have hWmono : ∀ k l : ℕ, k ≤ l → W l ≤ W k := by
        intro k l hkl
        show Δ / (2 : ℝ) ^ l ≤ Δ / (2 : ℝ) ^ k
        apply div_le_div_of_nonneg_left (le_of_lt hΔpos) (by positivity)
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hkl
      have hWstep : ∀ k : ℕ, 1 ≤ k → W (k - 1) = 2 * W k := by
        intro k hk
        show Δ / (2 : ℝ) ^ (k - 1) = 2 * (Δ / (2 : ℝ) ^ k)
        have hpow : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
          rw [mul_comm]
          conv_lhs => rw [← Nat.sub_add_cancel hk]
          rw [pow_succ]
        conv_rhs => rw [hpow]
        field_simp
      have hex : ∃ k : ℕ, W k ≤ 2 * (N : ℝ) := by
        have hN2 : (0 : ℝ) < 2 * (N : ℝ) := by positivity
        obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (Δ / (2 * (N : ℝ)))
          (by norm_num : (1 : ℝ) < 2)
        refine ⟨n, ?_⟩
        show Δ / (2 : ℝ) ^ n ≤ 2 * (N : ℝ)
        have hn' : Δ / (2 * (N : ℝ)) < (2 : ℝ) ^ n := hn
        rw [div_lt_iff₀ hN2] at hn'
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
        linarith
      set J : ℕ := Nat.find hex with hJ
      have hJs : W J ≤ 2 * (N : ℝ) := by rw [hJ]; exact Nat.find_spec hex
      have hJmin : ∀ m, m < J → 2 * (N : ℝ) < W m := by
        intro m hm
        rw [hJ] at hm
        have h := Nat.find_min hex hm
        simp only [not_le] at h
        exact h
      have hJpos : 1 ≤ J := by
        rcases Nat.eq_zero_or_pos J with h0 | h1
        · exfalso
          rw [h0, hW0] at hJs
          linarith
        · exact h1
      have hWJ : (N : ℝ) < W J := by
        have h1 : 2 * (N : ℝ) < W (J - 1) := hJmin (J - 1) (by omega)
        rw [hWstep J hJpos] at h1
        linarith
      have hWkgt : ∀ k, k ≤ J → (N : ℝ) < W k := by
        intro k hk
        have h := hWmono k J hk
        linarith
      have hcover : ∀ i j : Fin R, |t i - t j| ≤ Δ →
          (|t i - t j| ≤ 2 * (N : ℝ)) ∨
            ∃ k ∈ Finset.Icc 1 J, W k ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * W k := by
        intro i j hij
        by_cases hle : |t i - t j| ≤ 2 * (N : ℝ)
        · exact Or.inl hle
        · simp only [not_le] at hle
          rcases dyadic_cover_window (b := Δ) (b₀ := 2 * (N : ℝ)) (x := |t i - t j|)
              (by positivity) (le_of_lt h2Nlt) (abs_nonneg _) hij with h' | ⟨k, hk1, hkW, hkW'⟩
          · exact absurd h' (not_le.mpr hle)
          · refine Or.inr ⟨k, ?_, hkW, ?_⟩
            · rw [Finset.mem_Icc]
              refine ⟨hk1, ?_⟩
              by_contra hcon
              simp only [not_le] at hcon
              have hJlek : J ≤ k - 1 := by omega
              have hWle : W (k - 1) ≤ W J := hWmono J (k - 1) hJlek
              linarith [hJs, hWle, hle, hkW']
            · rw [← hWstep k hk1]; exact hkW'
      have hpair : ∀ i j : Fin R,
          (if |t i - t j| ≤ Δ then ‖raBlock N (2 * N) (t i - t j)‖ ^ 2 else 0) ≤
          (if |t i - t j| ≤ 2 * (N : ℝ) then ‖raBlock N (2 * N) (t i - t j)‖ ^ 2 else 0)
            + ∑ k ∈ Finset.Icc 1 J,
                (if W k ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * W k then
                  ‖raBlock N (2 * N) (t i - t j)‖ ^ 2 else 0) := by
        intro i j
        by_cases hc : |t i - t j| ≤ Δ
        · rw [if_pos hc]
          rcases hcover i j hc with hle | ⟨k, hk, h1', h2'⟩
          · rw [if_pos hle]
            have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.Icc 1 J,
                (if W k ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * W k then
                  ‖raBlock N (2 * N) (t i - t j)‖ ^ 2 else 0) := by positivity
            linarith
          · have hs := Finset.single_le_sum (f := fun k =>
                (if W k ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * W k then
                  ‖raBlock N (2 * N) (t i - t j)‖ ^ 2 else 0))
                (fun k _ => by positivity) hk
            rw [if_pos ⟨h1', h2'⟩] at hs
            have hnn : (0 : ℝ) ≤ (if |t i - t j| ≤ 2 * (N : ℝ) then
                ‖raBlock N (2 * N) (t i - t j)‖ ^ 2 else 0) := by positivity
            linarith
        · rw [if_neg hc]; positivity
      have hQcover : raDS N (2 * N) Δ R t
          ≤ raDS N (2 * N) (2 * (N : ℝ)) R t + ∑ k ∈ Finset.Icc 1 J, raAnn N (W k) R t := by
        calc raDS N (2 * N) Δ R t
            = ∑ i, ∑ j, (if |t i - t j| ≤ Δ then
                ‖raBlock N (2 * N) (t i - t j)‖ ^ 2 else 0) := rfl
          _ ≤ ∑ i, ∑ j, ((if |t i - t j| ≤ 2 * (N : ℝ) then
                ‖raBlock N (2 * N) (t i - t j)‖ ^ 2 else 0)
              + ∑ k ∈ Finset.Icc 1 J, (if W k ≤ |t i - t j| ∧ |t i - t j| ≤ 2 * W k then
                  ‖raBlock N (2 * N) (t i - t j)‖ ^ 2 else 0)) := by
                apply Finset.sum_le_sum; intro i _
                apply Finset.sum_le_sum; intro j _
                exact hpair i j
          _ = raDS N (2 * N) (2 * (N : ℝ)) R t + ∑ k ∈ Finset.Icc 1 J, raAnn N (W k) R t := by
                rw [sum_sum_add_sum_swap]
                rfl
      have hQ0 : raDS N (2 * N) (2 * (N : ℝ)) R t ≤
          Cmv * Δ ^ (ε / 4) * ((N : ℝ) * (R : ℝ) + 2 * raPC Δ R t) := by
        have h1 : raDS N (2 * N) (2 * (N : ℝ)) R t ≤ Cmv * (2 * (N : ℝ)) ^ (ε / 4) *
            ((N : ℝ) * (R : ℝ) + ((2 * (N : ℝ)) / (N : ℝ)) * raPC (2 * (N : ℝ)) R t) := by
          have h := hmvε N hN (2 * (N : ℝ)) (by linarith) (by linarith [h2Nlt]) R t hsep
          simpa only [raDS, raPC, raBlock, raTerm] using h
        have h2Neps : (2 * (N : ℝ)) ^ (ε / 4) ≤ Δ ^ (ε / 4) :=
          Real.rpow_le_rpow (by positivity) (le_of_lt h2Nlt) (by linarith)
        have hdiv : (2 * (N : ℝ)) / (N : ℝ) = 2 := by field_simp
        have hpc : raPC (2 * (N : ℝ)) R t ≤ raPC Δ R t := raPC_window_le (le_of_lt h2Nlt) R t
        have hpc2nn : 0 ≤ raPC (2 * (N : ℝ)) R t := raPC_nonneg _ _ _
        rw [hdiv] at h1
        refine le_trans h1 ?_
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h2Neps (le_of_lt hCmvp)
        · nlinarith [hpc, hpc2nn]
        · have h1 : 0 ≤ (N : ℝ) * (R : ℝ) := by positivity
          linarith [h1, hpc2nn]
        · positivity
      set X : ℝ := 12 * Cinc * p5 * SD + 73 * raPC Δ R t with hX
      have hXnn : 0 ≤ X := by
        rw [hX]
        have h1 : 0 ≤ 12 * Cinc * p5 * SD := by
          apply mul_nonneg
          · exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hCincp)) (le_of_lt hp5pos)
          · exact hSDnn
        have h2 : 0 ≤ 73 * raPC Δ R t := mul_nonneg (by norm_num) hPCnn
        linarith
      have hperk : ∀ k ∈ Finset.Icc 1 J, raAnn N (W k) R t ≤ Cmn * Δ ^ (ε / 2) * X := by
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkJ : k ≤ J := (Finset.mem_Icc.mp hk).2
        have hWknn : 0 ≤ W k := le_of_lt (hWpos k)
        have hWkg := hWkgt k hkJ
        have hWk1 : 1 ≤ W k := by linarith
        have hWkN : (N : ℝ) ≤ W k := le_of_lt hWkg
        have hWkΔ : W k ≤ Δ := by
          have h := hWmono 0 k (Nat.zero_le k)
          rwa [hW0] at h
        have hWkeps : (W k) ^ (ε / 4) ≤ Δ ^ (ε / 4) := Real.rpow_le_rpow hWknn hWkΔ (by linarith)
        have hm := hmainε N hN (W k) hWk1 hWkN R t hsep
        have hm' : raAnn N (W k) R t ≤ Cmn * (W k) ^ (ε / 4) *
            (raDS (Nat.ceil (W k / (2 * (N : ℝ)))) (2 * Nat.ceil (W k / (N : ℝ))) (2 * W k) R t
              + raPC (2 * W k) R t) := by
          simpa only [raAnn, raDS, raPC, raBlock, raTerm] using hm
        have h2WkΔ : 2 * W k ≤ Δ := by
          rw [← hWstep k hk1]
          have h := hWmono 0 (k - 1) (Nat.zero_le _)
          rwa [hW0] at h
        have hpc2 : raPC (2 * W k) R t ≤ raPC Δ R t := raPC_window_le h2WkΔ R t
        have hpc2nn : 0 ≤ raPC (2 * W k) R t := raPC_nonneg _ _ _
        set a : ℕ := Nat.ceil (W k / (2 * (N : ℝ))) with ha
        set b : ℕ := 2 * Nat.ceil (W k / (N : ℝ)) with hb
        have ha1 : 1 ≤ a := by
          rw [ha]
          exact Nat.ceil_pos.mpr (by positivity)
        have hb4 : 2 * a ≤ b := by
          rw [ha, hb]
          have hle : W k / (2 * (N : ℝ)) ≤ W k / (N : ℝ) := by
            apply div_le_div_of_nonneg_left hWknn (by positivity)
            linarith [hN1]
          have h := Nat.ceil_le.mpr (le_trans hle (Nat.le_ceil _))
          omega
        have hb2 : b ≤ 4 * a := by
          rw [ha, hb]
          have hx : W k / (2 * (N : ℝ)) = (W k / (N : ℝ)) / 2 := by ring
          have h := ceil_le_two_ceil_half (W k / (N : ℝ))
          rw [← hx] at h
          omega
        have hb3 : 4 * a ≤ b + 4 := by
          rw [ha, hb]
          have hx : W k / (2 * (N : ℝ)) = (W k / (N : ℝ)) / 2 := by ring
          have h := four_ceil_half_le (W k / (N : ℝ)) (by positivity)
          rw [← hx] at h
          omega
        have haM : 4 * a ≤ Nat.ceil (4 * Δ / N) := by
          rw [ha]
          have h1 : (4 * Nat.ceil (W k / (2 * (N : ℝ))) : ℝ) < 2 * (W k / (N : ℝ)) + 4 := by
            have hc : (Nat.ceil (W k / (2 * (N : ℝ))) : ℝ) < W k / (2 * (N : ℝ)) + 1 :=
              Nat.ceil_lt_add_one (by positivity)
            calc (4 * Nat.ceil (W k / (2 * (N : ℝ))) : ℝ)
                = 4 * (Nat.ceil (W k / (2 * (N : ℝ))) : ℝ) := by push_cast; ring
              _ < 4 * (W k / (2 * (N : ℝ)) + 1) := by
                    exact mul_lt_mul_of_pos_left hc (by norm_num)
              _ = 2 * (W k / (N : ℝ)) + 4 := by field_simp; ring
          have h2 : W k / (N : ℝ) ≤ Δ / (N : ℝ) := div_le_div_of_nonneg_right hWkΔ (by positivity)
          have h3 : 2 * (Δ / (N : ℝ)) + 4 ≤ 4 * (Δ / (N : ℝ)) := by
            have h4 : 4 ≤ 2 * (Δ / (N : ℝ)) := by
              rw [show (2 : ℝ) * (Δ / (N : ℝ)) = 2 * Δ / (N : ℝ) by ring]
              rw [le_div_iff₀ hNpos]
              nlinarith [h2Nlt, hΔpos]
            linarith
          have h4 : 4 * (Δ / (N : ℝ)) ≤ (Nat.ceil (4 * Δ / N) : ℝ) := by
            rw [show (4 : ℝ) * (Δ / (N : ℝ)) = 4 * Δ / (N : ℝ) by ring]
            exact Nat.le_ceil _
          have h5 : (4 * Nat.ceil (W k / (2 * (N : ℝ))) : ℝ) < (Nat.ceil (4 * Δ / N) : ℝ) := by
            linarith
          exact_mod_cast (le_of_lt h5)
        have hinc1 : raDS a (2 * a) Δ R t ≤ Cinc * (Nat.ceil (4 * Δ / N) : ℝ) ^ (ε / 4) * SD := by
          rw [hSD]
          have h := hincε a (Nat.ceil (4 * Δ / N)) ha1 (by omega) Δ hΔ1 1 le_rfl
            (fun _ => (1 : ℂ)) (fun n => by simp) R t hsep
          simpa only [raDS, raBlock, raTerm, one_mul, mul_one, one_pow] using h
        have hinc2 : raDS (2 * a) (4 * a) Δ R t ≤ Cinc * (Nat.ceil (4 * Δ / N) : ℝ) ^ (ε / 4) * SD := by
          have h4aM : 2 * (2 * a) ≤ Nat.ceil (4 * Δ / N) := by omega
          have h2a : 2 * (2 * a) = 4 * a := by ring
          rw [hSD]
          have h := hincε (2 * a) (Nat.ceil (4 * Δ / N)) (by omega) h4aM Δ hΔ1 1 le_rfl
            (fun _ => (1 : ℂ)) (fun n => by simp) R t hsep
          simpa only [raDS, raBlock, raTerm, one_mul, mul_one, one_pow, h2a] using h
        have hblk : raDS a b (2 * W k) R t ≤ 12 * Cinc * (p5 * Δ ^ (ε / 4)) * SD + 72 * raPC Δ R t := by
          have s1 : raDS a b (2 * W k) R t ≤ raDS a b Δ R t := raDS_window_le h2WkΔ a b R t
          have s2 : raDS a b Δ R t ≤ 4 * raDS a (2 * a) Δ R t + 8 * raDS (2 * a) (4 * a) Δ R t
              + 72 * raPC Δ R t := raDS_block_split a b Δ R t ha1 hb4 hb3 hb2
          have s3 : 4 * raDS a (2 * a) Δ R t ≤
              4 * (Cinc * (Nat.ceil (4 * Δ / N) : ℝ) ^ (ε / 4) * SD) :=
            mul_le_mul_of_nonneg_left hinc1 (by norm_num)
          have s4 : 8 * raDS (2 * a) (4 * a) Δ R t ≤
              8 * (Cinc * (Nat.ceil (4 * Δ / N) : ℝ) ^ (ε / 4) * SD) :=
            mul_le_mul_of_nonneg_left hinc2 (by norm_num)
          have hMeps : (Nat.ceil (4 * Δ / N) : ℝ) ^ (ε / 4) ≤ p5 * Δ ^ (ε / 4) := by
            have hMle : (Nat.ceil (4 * Δ / N) : ℝ) ≤ 5 * Δ := by
              have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 * Δ / (N : ℝ) by positivity)
              have h4 : 4 * Δ / (N : ℝ) ≤ 4 * Δ := by
                rw [div_le_iff₀ hNpos]; nlinarith [hN1, hΔpos]
              linarith
            calc (Nat.ceil (4 * Δ / N) : ℝ) ^ (ε / 4) ≤ (5 * Δ) ^ (ε / 4) :=
                  Real.rpow_le_rpow (by positivity) hMle (by linarith)
              _ = p5 * Δ ^ (ε / 4) := by rw [hp5, Real.mul_rpow (by norm_num) (le_of_lt hΔpos)]
          have hfin : 12 * Cinc * (Nat.ceil (4 * Δ / N) : ℝ) ^ (ε / 4) * SD
              ≤ 12 * Cinc * (p5 * Δ ^ (ε / 4)) * SD := by
            have hc1 : 0 ≤ Cinc := le_of_lt hCincp
            have h := mul_le_mul_of_nonneg_right hMeps hSDnn
            nlinarith [h, hCincp, hSDnn]
          have hmmm : 4 * (Cinc * (Nat.ceil (4 * Δ / N) : ℝ) ^ (ε / 4) * SD)
              + 8 * (Cinc * (Nat.ceil (4 * Δ / N) : ℝ) ^ (ε / 4) * SD)
              = 12 * Cinc * (Nat.ceil (4 * Δ / N) : ℝ) ^ (ε / 4) * SD := by ring
          linarith [s1, s2, s3, s4, hfin, hPCnn]
        rw [hX]
        have hY : 0 ≤ 12 * Cinc * (p5 * Δ ^ (ε / 4)) * SD + 73 * raPC Δ R t := by
          have h1 : 0 ≤ 12 * Cinc * (p5 * Δ ^ (ε / 4)) * SD := by
            apply mul_nonneg
            · exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hCincp))
                (mul_nonneg (le_of_lt hp5pos) (Real.rpow_nonneg (le_of_lt hΔpos) _))
            · exact hSDnn
          have h2 : 0 ≤ 73 * raPC Δ R t := mul_nonneg (by norm_num) hPCnn
          linarith
        have hlast : Cmn * Δ ^ (ε / 4) * (12 * Cinc * (p5 * Δ ^ (ε / 4)) * SD + 73 * raPC Δ R t)
            ≤ Cmn * Δ ^ (ε / 2) * (12 * Cinc * p5 * SD + 73 * raPC Δ R t) := by
          have hpp : Δ ^ (ε / 4) * Δ ^ (ε / 4) = Δ ^ (ε / 2) := by
            rw [hΔpm, show ε / 4 + ε / 4 = ε / 2 by ring]
          have h42 : Δ ^ (ε / 4) ≤ Δ ^ (ε / 2) :=
            Real.rpow_le_rpow_of_exponent_le hΔ1 (by linarith)
          have hL : Cmn * Δ ^ (ε / 4) * (12 * Cinc * (p5 * Δ ^ (ε / 4)) * SD + 73 * raPC Δ R t)
              = Cmn * (12 * Cinc * p5 * (Δ ^ (ε / 4) * Δ ^ (ε / 4)) * SD
                  + 73 * Δ ^ (ε / 4) * raPC Δ R t) := by ring
          have hR : Cmn * Δ ^ (ε / 2) * (12 * Cinc * p5 * SD + 73 * raPC Δ R t)
              = Cmn * (12 * Cinc * p5 * Δ ^ (ε / 2) * SD
                  + 73 * Δ ^ (ε / 2) * raPC Δ R t) := by ring
          rw [hL, hR]
          have hb1 : 12 * Cinc * p5 * (Δ ^ (ε / 4) * Δ ^ (ε / 4)) * SD
              ≤ 12 * Cinc * p5 * Δ ^ (ε / 2) * SD := by rw [hpp]
          have hb2 : 73 * Δ ^ (ε / 4) * raPC Δ R t ≤ 73 * Δ ^ (ε / 2) * raPC Δ R t := by
            have h3 := mul_le_mul_of_nonneg_right h42 hPCnn
            linarith [h3]
          exact mul_le_mul_of_nonneg_left (by linarith [hb1, hb2]) (le_of_lt hCmnp)
        calc raAnn N (W k) R t
            ≤ Cmn * (W k) ^ (ε / 4) * (raDS a b (2 * W k) R t + raPC (2 * W k) R t) := hm'
          _ ≤ Cmn * (W k) ^ (ε / 4) * (12 * Cinc * (p5 * Δ ^ (ε / 4)) * SD + 73 * raPC Δ R t) := by
                apply mul_le_mul_of_nonneg_left _ (mul_nonneg (le_of_lt hCmnp) (Real.rpow_nonneg hWknn _))
                linarith [hblk, hpc2]
          _ ≤ Cmn * Δ ^ (ε / 4) * (12 * Cinc * (p5 * Δ ^ (ε / 4)) * SD + 73 * raPC Δ R t) := by
                apply mul_le_mul_of_nonneg_right _ hY
                exact mul_le_mul_of_nonneg_left hWkeps (le_of_lt hCmnp)
          _ ≤ Cmn * Δ ^ (ε / 2) * (12 * Cinc * p5 * SD + 73 * raPC Δ R t) := hlast
      have hJle : (J : ℝ) ≤ Clog * Δ ^ (ε / 4) := by
        have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hlog : Real.log Δ ≤ Δ ^ (ε / 4) / (ε / 4) := Real.log_le_rpow_div (le_of_lt hΔpos) hε4
        have h2J : (2 : ℝ) ^ J < Δ / (N : ℝ) := by
          have h := hWJ
          have h' : (N : ℝ) < Δ / (2 : ℝ) ^ J := h
          rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ J)] at h'
          rw [lt_div_iff₀ hNpos]
          nlinarith [h']
        have hΔNle : Δ / (N : ℝ) ≤ Δ := by rw [div_le_iff₀ hNpos]; nlinarith [hN1]
        have hlt : (2 : ℝ) ^ J < Δ := lt_of_lt_of_le h2J hΔNle
        have hlg := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ J) hlt
        rw [Real.log_pow] at hlg
        have hJlt : (J : ℝ) < Real.log Δ / Real.log 2 := by
          rw [lt_div_iff₀ hl2]; linarith
        have hstep : Real.log Δ / Real.log 2 ≤ (1 / ((ε / 4) * Real.log 2)) * Δ ^ (ε / 4) := by
          have h1 : Real.log Δ / Real.log 2 = (1 / Real.log 2) * Real.log Δ := by ring
          have h2 : (1 / ((ε / 4) * Real.log 2)) * Δ ^ (ε / 4)
              = (1 / Real.log 2) * (Δ ^ (ε / 4) / (ε / 4)) := by
            field_simp
          rw [h1, h2]
          exact mul_le_mul_of_nonneg_left hlog (by positivity)
        have hle1 : (1 / ((ε / 4) * Real.log 2)) * Δ ^ (ε / 4) ≤ Clog * Δ ^ (ε / 4) := by
          apply mul_le_mul_of_nonneg_right _ hΔeps4nn
          rw [hClog]; linarith
        linarith
      have hsum : ∑ k ∈ Finset.Icc 1 J, raAnn N (W k) R t ≤ Clog * Cmn * Δ ^ ε * X := by
        have hcard : (Finset.Icc 1 J).card = J := by rw [Nat.card_Icc]; omega
        have h34 : Δ ^ (3 * (ε / 4)) ≤ Δ ^ ε :=
          Real.rpow_le_rpow_of_exponent_le hΔ1 (by linarith)
        have hpm : Δ ^ (ε / 4) * Δ ^ (ε / 2) = Δ ^ (3 * (ε / 4)) := by
          rw [hΔpm, show ε / 4 + ε / 2 = 3 * (ε / 4) by ring]
        have hCnn : 0 ≤ Clog * Cmn := by positivity
        rw [hX]
        calc ∑ k ∈ Finset.Icc 1 J, raAnn N (W k) R t
            ≤ ∑ k ∈ Finset.Icc 1 J, (Cmn * Δ ^ (ε / 2) * (12 * Cinc * p5 * SD + 73 * raPC Δ R t)) :=
                Finset.sum_le_sum hperk
          _ = (J : ℝ) * (Cmn * Δ ^ (ε / 2) * (12 * Cinc * p5 * SD + 73 * raPC Δ R t)) := by
                rw [Finset.sum_const, nsmul_eq_mul, hcard]
          _ ≤ (Clog * Δ ^ (ε / 4)) *
                (Cmn * Δ ^ (ε / 2) * (12 * Cinc * p5 * SD + 73 * raPC Δ R t)) :=
                mul_le_mul_of_nonneg_right hJle (by positivity)
          _ = Clog * Cmn * (Δ ^ (ε / 4) * Δ ^ (ε / 2))
                * (12 * Cinc * p5 * SD + 73 * raPC Δ R t) := by ring
          _ = Clog * Cmn * Δ ^ (3 * (ε / 4)) * (12 * Cinc * p5 * SD + 73 * raPC Δ R t) := by
                rw [hpm]
          _ ≤ Clog * Cmn * Δ ^ ε * (12 * Cinc * p5 * SD + 73 * raPC Δ R t) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                exact mul_le_mul_of_nonneg_left h34 hCnn
      have hcomb : raDS N (2 * N) Δ R t ≤ KQ * Δ ^ ε * (SD + raPC Δ R t + BT) := by
        have hY1 : 0 ≤ (N : ℝ) * (R : ℝ) + 2 * raPC Δ R t := by
          have h1 : 0 ≤ (N : ℝ) * (R : ℝ) := by positivity
          have h2 : 0 ≤ 2 * raPC Δ R t := by linarith [hPCnn]
          linarith
        have hstep1 : Cmv * Δ ^ (ε / 4) * ((N : ℝ) * (R : ℝ) + 2 * raPC Δ R t)
            ≤ Cmv * Δ ^ ε * ((N : ℝ) * (R : ℝ) + 2 * raPC Δ R t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔeps4 (le_of_lt hCmvp)) hY1
        have hbr : Cmv * ((N : ℝ) * (R : ℝ) + 2 * raPC Δ R t) + Clog * Cmn * X
            ≤ KQ * (SD + raPC Δ R t + BT) := by
          rw [hX, hKQ]
          have hYb : 0 ≤ SD + raPC Δ R t + BT := by linarith
          have hA : Cmv * ((N : ℝ) * (R : ℝ) + 2 * raPC Δ R t)
              ≤ Cmv * (3 * (SD + raPC Δ R t + BT)) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hCmvp)
            nlinarith [hNR, hSDnn, hPCnn, hBTnn]
          have hB : Clog * Cmn * (12 * Cinc * p5 * SD + 73 * raPC Δ R t)
              ≤ Clog * Cmn * (12 * Cinc * p5 + 73) * (SD + raPC Δ R t + BT) := by
            have hcc : 0 ≤ Clog * Cmn := by positivity
            have h1 : 12 * Cinc * p5 * SD + 73 * raPC Δ R t
                ≤ (12 * Cinc * p5 + 73) * (SD + raPC Δ R t + BT) := by
              have hA1 : 0 ≤ 12 * Cinc * p5 * raPC Δ R t :=
                mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hCincp))
                  (le_of_lt hp5pos)) hPCnn
              have hA2 : 0 ≤ 12 * Cinc * p5 * BT :=
                mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hCincp))
                  (le_of_lt hp5pos)) hBTnn
              have hA3 : 0 ≤ 73 * SD := mul_nonneg (by norm_num) hSDnn
              have hA4 : 0 ≤ 73 * BT := mul_nonneg (by norm_num) hBTnn
              nlinarith [hA1, hA2, hA3, hA4]
            calc Clog * Cmn * (12 * Cinc * p5 * SD + 73 * raPC Δ R t)
                ≤ Clog * Cmn * ((12 * Cinc * p5 + 73) * (SD + raPC Δ R t + BT)) :=
                    mul_le_mul_of_nonneg_left h1 hcc
              _ = Clog * Cmn * (12 * Cinc * p5 + 73) * (SD + raPC Δ R t + BT) := by ring
          have hC : Cmv * (3 * (SD + raPC Δ R t + BT))
              + Clog * Cmn * (12 * Cinc * p5 + 73) * (SD + raPC Δ R t + BT)
              ≤ KQ * (SD + raPC Δ R t + BT) := by
            have hsum : Cmv * (3 * (SD + raPC Δ R t + BT))
                + Clog * Cmn * (12 * Cinc * p5 + 73) * (SD + raPC Δ R t + BT)
                = (3 * Cmv + Clog * Cmn * (12 * Cinc * p5 + 73)) * (SD + raPC Δ R t + BT) := by ring
            rw [hsum, hKQ]
            exact mul_le_mul_of_nonneg_right (by linarith) hYb
          linarith [hA, hB, hC]
        calc raDS N (2 * N) Δ R t
            ≤ raDS N (2 * N) (2 * (N : ℝ)) R t + ∑ k ∈ Finset.Icc 1 J, raAnn N (W k) R t := hQcover
          _ ≤ Cmv * Δ ^ (ε / 4) * ((N : ℝ) * (R : ℝ) + 2 * raPC Δ R t)
              + Clog * Cmn * Δ ^ ε * X := add_le_add hQ0 hsum
          _ ≤ Cmv * Δ ^ ε * ((N : ℝ) * (R : ℝ) + 2 * raPC Δ R t)
              + Clog * Cmn * Δ ^ ε * X := by linarith [hstep1]
          _ = Δ ^ ε * (Cmv * ((N : ℝ) * (R : ℝ) + 2 * raPC Δ R t) + Clog * Cmn * X) := by ring
          _ ≤ Δ ^ ε * (KQ * (SD + raPC Δ R t + BT)) := mul_le_mul_of_nonneg_left hbr hΔepsnn
          _ = KQ * Δ ^ ε * (SD + raPC Δ R t + BT) := by ring
      rw [hSD, hBT] at hcomb
      exact hcomb
  calc (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0)) ≤ Cmaj * B ^ 2 * raDS N (2 * N) Δ R t := hmaj'
    _ ≤ Cmaj * B ^ 2 * (KQ * Δ ^ ε *
          (raDS (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)) Δ R t
            + raPC Δ R t + (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hQ (by positivity)
    _ ≤ (Cmaj * KQ + 1) * B ^ 2 * Δ ^ ε *
          (raDS (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)) Δ R t
            + raPC Δ R t + (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1)) := by
        have hYt : 0 ≤ raDS (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)) Δ R t
            + raPC Δ R t + (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1) := by
          have h1 : 0 ≤ raDS (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)) Δ R t :=
            raDS_nonneg _ _ _ _ _
          have h2 : 0 ≤ raPC Δ R t := raPC_nonneg _ _ _
          have h3 : 0 ≤ (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1) := by positivity
          linarith
        have hprod : 0 ≤ B ^ 2 * Δ ^ ε *
            (raDS (Nat.ceil (4 * Δ / N)) (2 * Nat.ceil (4 * Δ / N)) Δ R t
              + raPC Δ R t + (N : ℝ) ^ (1 + ε) * ((R : ℝ) + 1)) :=
          mul_nonneg (mul_nonneg (sq_nonneg B) hΔepsnn) hYt
        nlinarith [hprod, hCmajp, hKQpos]

end

end Commons.NumberTheory.DirichletPolynomial
