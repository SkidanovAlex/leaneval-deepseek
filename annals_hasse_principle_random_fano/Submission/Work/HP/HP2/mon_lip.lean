import Mathlib

namespace Work.HP.HP2

open Finset

/-- The absolute value of a product of monomials is bounded by `R ^ (sum of exponents)`
whenever every variable is bounded by `R` in absolute value. -/
lemma abs_prod_pow_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (μ : ι → ℕ) (R : ℝ)
    (hx : ∀ i ∈ s, |x i| ≤ R) :
    |∏ i ∈ s, x i ^ (μ i)| ≤ R ^ (∑ i ∈ s, μ i) := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ s, |x i ^ (μ i)| ≤ ∏ i ∈ s, R ^ (μ i) := by
        apply Finset.prod_le_prod₀
        · intro i _; exact abs_nonneg _
        · intro i hi
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hx i hi) _
    _ = R ^ (∑ i ∈ s, μ i) := Finset.prod_pow_eq_pow_sum s μ R

/-- One-variable Lipschitz bound for `t ↦ t ^ m` on a box of radius `R ≥ 1`. -/
lemma abs_pow_sub_pow_le_pow {x y R : ℝ} {m : ℕ} (hR : 1 ≤ R)
    (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |x ^ m - y ^ m| ≤ (m : ℝ) * R ^ m * |x - y| := by
  have hmax : max |x| |y| ≤ R := max_le hx hy
  have hmax0 : 0 ≤ max |x| |y| := le_trans (abs_nonneg x) (le_max_left _ _)
  have h1 : max |x| |y| ^ (m - 1) ≤ R ^ m :=
    le_trans (pow_le_pow_left₀ hmax0 hmax _) (pow_le_pow_right₀ hR (Nat.sub_le m 1))
  calc |x ^ m - y ^ m| ≤ |x - y| * (m : ℝ) * max |x| |y| ^ (m - 1) := abs_pow_sub_pow_le x y m
    _ ≤ |x - y| * (m : ℝ) * R ^ m := by gcongr
    _ = (m : ℝ) * R ^ m * |x - y| := by ring

/-- Monomials of degree `D` are Lipschitz on the box of radius `R ≥ 1`:
`|∏ᵢ xᵢ^{μᵢ} − ∏ᵢ yᵢ^{μᵢ}| ≤ D * R^D * Σᵢ |xᵢ − yᵢ|`.

Route.  Induction on the finset of variables (the same statement is in
`Submission/Work/HP/HP2/monomial_lipschitz.lean`).  For `|xᵢ|, |yᵢ| ≤ R` and `k ∉ s`,
`|x_k^{μ_k} A − y_k^{μ_k} B| ≤ |x_k|^{μ_k}|A − B| + |x_k^{μ_k} − y_k^{μ_k}||B|`, where
`A = ∏_{i∈s} xᵢ^{μᵢ}`, `B = ∏_{i∈s} yᵢ^{μᵢ}`; the induction hypothesis bounds `|A − B|`, the
one-variable bound `|x_k^{μ_k} − y_k^{μ_k}| ≤ μ_k R^{μ_k − 1}|x_k − y_k| ≤ μ_k R^{μ_k}|x_k − y_k|`
(using `R ≥ 1`) handles the second term, and `|A|, |B| ≤ R^{Σ_{i∈s} μ_i}`, `|x_k| ≤ R`. -/
theorem mon_lip {ι : Type*} [DecidableEq ι] (s : Finset ι) (x y : ι → ℝ) (μ : ι → ℕ)
    (R : ℝ) (hR : 1 ≤ R) (hx : ∀ i ∈ s, |x i| ≤ R) (hy : ∀ i ∈ s, |y i| ≤ R) :
    |∏ i ∈ s, x i ^ (μ i) - ∏ i ∈ s, y i ^ (μ i)| ≤
      (∑ i ∈ s, μ i : ℝ) * R ^ (∑ i ∈ s, μ i) * (∑ i ∈ s, |x i - y i|) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert k s' hk ih =>
    simp only [Finset.prod_insert hk, Finset.sum_insert hk]
    set A : ℝ := ∏ i ∈ s', x i ^ (μ i) with hA
    set B : ℝ := ∏ i ∈ s', y i ^ (μ i) with hB
    have hx' : ∀ i ∈ s', |x i| ≤ R := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hy' : ∀ i ∈ s', |y i| ≤ R := fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hxk : |x k| ≤ R := hx k (Finset.mem_insert_self k s')
    have hyk : |y k| ≤ R := hy k (Finset.mem_insert_self k s')
    have hR0 : 0 ≤ R := le_trans zero_le_one hR
    have hIH : |A - B| ≤ (∑ i ∈ s', (μ i : ℝ)) * R ^ (∑ i ∈ s', μ i) * (∑ i ∈ s', |x i - y i|) :=
      ih hx' hy'
    have ha : |x k ^ μ k| ≤ R ^ μ k := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hxk _
    have hB2 : |B| ≤ R ^ (∑ i ∈ s', μ i) := abs_prod_pow_le s' y μ R hy'
    have hab : |x k ^ μ k - y k ^ μ k| ≤ (μ k : ℝ) * R ^ (μ k) * |x k - y k| :=
      abs_pow_sub_pow_le_pow hR hxk hyk
    have hDk0 : 0 ≤ |x k - y k| := abs_nonneg _
    have hT0 : 0 ≤ (∑ i ∈ s', |x i - y i|) := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hC0 : 0 ≤ (∑ i ∈ s', (μ i : ℝ)) := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
    have hsplit : |x k ^ μ k * A - y k ^ μ k * B|
        ≤ |x k ^ μ k| * |A - B| + |x k ^ μ k - y k ^ μ k| * |B| := by
      have h : x k ^ μ k * A - y k ^ μ k * B
          = x k ^ μ k * (A - B) + (x k ^ μ k - y k ^ μ k) * B := by ring
      rw [h]
      calc |x k ^ μ k * (A - B) + (x k ^ μ k - y k ^ μ k) * B|
          ≤ |x k ^ μ k * (A - B)| + |(x k ^ μ k - y k ^ μ k) * B| := abs_add_le _ _
        _ = |x k ^ μ k| * |A - B| + |x k ^ μ k - y k ^ μ k| * |B| := by rw [abs_mul, abs_mul]
    have h1 : |x k ^ μ k| * |A - B|
        ≤ R ^ μ k * ((∑ i ∈ s', (μ i : ℝ)) * R ^ (∑ i ∈ s', μ i) * (∑ i ∈ s', |x i - y i|)) :=
      mul_le_mul ha hIH (abs_nonneg _) (pow_nonneg hR0 _)
    have h2 : |x k ^ μ k - y k ^ μ k| * |B|
        ≤ ((μ k : ℝ) * R ^ (μ k) * |x k - y k|) * R ^ (∑ i ∈ s', μ i) :=
      mul_le_mul hab hB2 (abs_nonneg _)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hR0 _)) hDk0)
    have hsum : |x k ^ μ k * A - y k ^ μ k * B|
        ≤ R ^ μ k * ((∑ i ∈ s', (μ i : ℝ)) * R ^ (∑ i ∈ s', μ i) * (∑ i ∈ s', |x i - y i|))
          + ((μ k : ℝ) * R ^ (μ k) * |x k - y k|) * R ^ (∑ i ∈ s', μ i) :=
      le_trans hsplit (add_le_add h1 h2)
    have hkey : (∑ i ∈ s', (μ i : ℝ)) * (∑ i ∈ s', |x i - y i|) + (μ k : ℝ) * |x k - y k|
        ≤ ((μ k : ℝ) + ∑ i ∈ s', (μ i : ℝ)) * (|x k - y k| + ∑ i ∈ s', |x i - y i|) := by
      have hmk0 : (0:ℝ) ≤ (μ k : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg hmk0 hT0, mul_nonneg hC0 hDk0]
    calc |x k ^ μ k * A - y k ^ μ k * B|
        ≤ R ^ μ k * ((∑ i ∈ s', (μ i : ℝ)) * R ^ (∑ i ∈ s', μ i) * (∑ i ∈ s', |x i - y i|))
          + ((μ k : ℝ) * R ^ (μ k) * |x k - y k|) * R ^ (∑ i ∈ s', μ i) := hsum
      _ = R ^ (μ k + ∑ i ∈ s', μ i)
            * ((∑ i ∈ s', (μ i : ℝ)) * (∑ i ∈ s', |x i - y i|) + (μ k : ℝ) * |x k - y k|) := by
            rw [pow_add]; ring
      _ ≤ R ^ (μ k + ∑ i ∈ s', μ i)
            * (((μ k : ℝ) + ∑ i ∈ s', (μ i : ℝ)) * (|x k - y k| + ∑ i ∈ s', |x i - y i|)) := by
            apply mul_le_mul_of_nonneg_left hkey (pow_nonneg hR0 _)
      _ = ((μ k : ℝ) + ∑ i ∈ s', (μ i : ℝ)) * R ^ (μ k + ∑ i ∈ s', μ i)
            * (|x k - y k| + ∑ i ∈ s', |x i - y i|) := by ring

end Work.HP.HP2
