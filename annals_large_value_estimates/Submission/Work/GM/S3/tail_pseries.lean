import Mathlib

namespace Work.GM.S3

/-!
# The tail of the `j`-th power series over `ℤ`

Supporting estimates for the tail of `∑_{|m| > K} D/|m|^j` (`j ≥ 2`, `K ≥ 1`, `D ≥ 0`): the
family is summable and its total mass is at most `4·D·K/K^j`.

The route is the one sketched in the statement: for integers `m` with `|m| > K` one has
`|m| ≥ ⌊K⌋+1`, so `1/|m|^j = 1/(|m|^{j-2}·|m|²) ≤ 1/((⌊K⌋+1)^{j-2}·|m|²)`, and the resulting
quadratic tail is bounded by the telescoping estimate `sum_Ioo_inv_sq_le`
(`∑_{⌊K⌋<i<n} 1/i² ≤ 2/(⌊K⌋+1) ≤ 2/K`).  Summing over `ℕ` with `Real.tsum_le_of_sum_range_le`
and passing to `ℤ` with `Summable.of_nat_of_neg_add_one` / `tsum_of_nat_of_neg_add_one` gives the
claim (the two halves `m ≥ 0` and `m < 0` each contribute at most `2DK/K^j`).
-/

/-- Comparison of `D/x^j` with `D·K^{2-j}/x²` for `x ≥ K ≥ 1`, `j ≥ 2`. -/
private lemma div_pow_le_mul_inv_sq (j : ℕ) (hj : 2 ≤ j) {D K x : ℝ} (hD : 0 ≤ D) (hK : 0 < K)
    (hKx : K ≤ x) : D / x ^ j ≤ D * (K ^ (j - 2))⁻¹ * (x ^ 2)⁻¹ := by
  have hx : 0 < x := lt_of_lt_of_le hK hKx
  have hpow : x ^ j = x ^ (j - 2) * x ^ 2 := by rw [← pow_add]; congr 1; omega
  have h1 : (x ^ j)⁻¹ ≤ (K ^ (j - 2))⁻¹ * (x ^ 2)⁻¹ := by
    rw [hpow, mul_inv]
    exact mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ (pow_pos hx _) (pow_pos hK _)).mpr (pow_le_pow_left₀ hK.le hKx _))
      (by positivity)
  calc D / x ^ j = D * (x ^ j)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ D * ((K ^ (j - 2))⁻¹ * (x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 hD
    _ = D * (K ^ (j - 2))⁻¹ * (x ^ 2)⁻¹ := by ring

/-- `D·K^{2-j}·(2/K) = 2DK/K^j`. -/
private lemma mul_inv_pow_arith (j : ℕ) (hj : 2 ≤ j) {D K : ℝ} (hK : 1 ≤ K) :
    D * (K ^ (j - 2))⁻¹ * (2 / K) = 2 * D * K / K ^ j := by
  have hK0 : K ≠ 0 := by positivity
  have hpow : K ^ j = K ^ (j - 2) * K ^ 2 := by rw [← pow_add]; congr 1; omega
  rw [hpow]
  field_simp

/-- The finite bound `∑_{i<n} D/i^j ≤ 2DK/K^j` (over the integers `i > K`). -/
private lemma sum_range_div_pow_le (j : ℕ) (hj : 2 ≤ j) (D K : ℝ) (hD : 0 ≤ D) (hK : 1 ≤ K)
    (n : ℕ) :
    ∑ i ∈ Finset.range n, (if K < (i : ℝ) then D / (i : ℝ) ^ j else 0) ≤ 2 * D * K / K ^ j := by
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK
  have hstep : ∑ i ∈ Finset.range n, (if K < (i : ℝ) then D / (i : ℝ) ^ j else 0)
      = ∑ i ∈ (Finset.range n).filter (fun i : ℕ => K < (i : ℝ)), D / (i : ℝ) ^ j :=
    (Finset.sum_filter (s := Finset.range n) (fun i : ℕ => K < (i : ℝ))
      (fun i => D / (i : ℝ) ^ j)).symm
  rw [hstep]
  have hsub : (Finset.range n).filter (fun i : ℕ => K < (i : ℝ)) ⊆ Finset.Ioo ⌊K⌋₊ n := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hir, hiK⟩ := hi
    rw [Finset.mem_range] at hir
    rw [Finset.mem_Ioo]
    refine ⟨?_, hir⟩
    have h1 : ((⌊K⌋₊ : ℕ) : ℝ) < (i : ℝ) :=
      lt_of_le_of_lt (by exact_mod_cast Nat.floor_le hKpos.le : ((⌊K⌋₊ : ℕ) : ℝ) ≤ K) hiK
    exact_mod_cast h1
  have hmid : (∑ i ∈ Finset.Ioo ⌊K⌋₊ n, D / (i : ℝ) ^ j)
      ≤ ∑ i ∈ Finset.Ioo ⌊K⌋₊ n, D * (K ^ (j - 2))⁻¹ * ((i : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_Ioo] at hi
    have hiK : K ≤ (i : ℝ) := by
      have h3 : ((⌊K⌋₊ : ℕ) : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi.1
      have h4 : K < ((⌊K⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one K
      linarith
    exact div_pow_le_mul_inv_sq j hj hD hKpos hiK
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)) ?_
  refine le_trans hmid ?_
  rw [← Finset.mul_sum]
  have hsum : (∑ i ∈ Finset.Ioo ⌊K⌋₊ n, ((i : ℝ) ^ 2)⁻¹) ≤ 2 / ((⌊K⌋₊ : ℝ) + 1) :=
    sum_Ioo_inv_sq_le ⌊K⌋₊ n
  have hKle : K ≤ ((⌊K⌋₊ : ℝ) + 1) := le_of_lt (Nat.lt_floor_add_one K)
  have hfac : 0 ≤ D * (K ^ (j - 2))⁻¹ :=
    mul_nonneg hD (inv_nonneg.mpr (pow_nonneg hKpos.le _))
  have h2 : 2 / ((⌊K⌋₊ : ℝ) + 1) ≤ 2 / K :=
    div_le_div_of_nonneg_left (by norm_num) hKpos hKle
  calc D * (K ^ (j - 2))⁻¹ * (∑ i ∈ Finset.Ioo ⌊K⌋₊ n, ((i : ℝ) ^ 2)⁻¹)
      ≤ D * (K ^ (j - 2))⁻¹ * (2 / ((⌊K⌋₊ : ℝ) + 1)) := mul_le_mul_of_nonneg_left hsum hfac
    _ ≤ D * (K ^ (j - 2))⁻¹ * (2 / K) := mul_le_mul_of_nonneg_left h2 hfac
    _ = 2 * D * K / K ^ j := mul_inv_pow_arith j hj hK

/-- The tail of the `j`-th power series over `ℤ`, for `j ≥ 2`: if `K ≥ 1` and `D ≥ 0` then
`∑_{|m| > K} D/|m|^j ≤ 4·D·K/K^j` and the family is summable.  Intended route: compare
`1/|m|^j ≤ K^{2-j}/m²` for `|m| > K` with the telescoping bound `∑_{m>K} 1/m² ≤ 1/K` (careful:
apply `sum_Ioo_inv_sq_le` at the integer `⌊K⌋` and then use `1/⌊K⌋ ≤ 2/K`, since
`∑_{m>K} 1/m² ≤ 1/K` is false for non-integer `K`) and `Real.tsum_le_of_sum_range_le`; pass from
`ℕ` to `ℤ` with `Summable.of_nat_of_neg_add_one` / `tsum_of_nat_of_neg_add_one`. -/
theorem tail_pseries (j : ℕ) (hj : 2 ≤ j) (D K : ℝ) (hD : 0 ≤ D) (hK : 1 ≤ K) :
    Summable (fun m : ℤ => if K < |(m : ℝ)| then D / |(m : ℝ)| ^ j else 0) ∧
      tsum (fun m : ℤ => if K < |(m : ℝ)| then D / |(m : ℝ)| ^ j else 0) ≤ 4 * D * K / K ^ j := by
  set f : ℤ → ℝ := fun m => if K < |(m : ℝ)| then D / |(m : ℝ)| ^ j else 0 with hf
  set g : ℕ → ℝ := fun n => if K < (n : ℝ) then D / (n : ℝ) ^ j else 0 with hg
  have hg0 : g 0 = 0 := by
    rw [hg]
    simp only [Nat.cast_zero]
    rw [if_neg (not_lt.mpr (by linarith : (0 : ℝ) ≤ K))]
  have hg_nonneg : ∀ n, 0 ≤ g n := by
    intro n
    rw [hg]
    simp only
    split_ifs with h
    · exact div_nonneg hD (pow_nonneg (Nat.cast_nonneg n) j)
    · exact le_refl 0
  have hg_bound : ∀ n, ∑ i ∈ Finset.range n, g i ≤ 2 * D * K / K ^ j := by
    intro n
    rw [hg]
    exact sum_range_div_pow_le j hj D K hD hK n
  have heven : ∀ m : ℤ, f (-m) = f m := by
    intro m
    rw [hf]
    simp only [Int.cast_neg, abs_neg]
  have hpos_eq : ∀ k : ℕ, f (k : ℤ) = g k := by
    intro k
    rw [hf, hg]
    simp only [Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg k)]
  have hneg_eq : ∀ n : ℕ, f (-((n : ℤ) + 1)) = g (n + 1) := by
    intro n
    have h1 : -((n : ℤ) + 1) = -(((n + 1 : ℕ)) : ℤ) := by push_cast; ring
    rw [h1, heven]
    exact hpos_eq (n + 1)
  have hA : Summable (fun n : ℕ => f (n : ℤ)) := by
    rw [funext hpos_eq]
    exact summable_of_sum_range_le hg_nonneg hg_bound
  have hB : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := by
    rw [funext hneg_eq]
    exact (summable_nat_add_iff 1).mpr (summable_of_sum_range_le hg_nonneg hg_bound)
  have hAg : (∑' n : ℕ, f (n : ℤ)) ≤ 2 * D * K / K ^ j := by
    rw [funext hpos_eq]
    exact Real.tsum_le_of_sum_range_le hg_nonneg hg_bound
  have hBg : (∑' n : ℕ, f (-((n : ℤ) + 1))) ≤ 2 * D * K / K ^ j := by
    rw [funext hneg_eq]
    refine Real.tsum_le_of_sum_range_le (fun n => hg_nonneg (n + 1)) (fun n => ?_)
    have h := hg_bound (n + 1)
    have hs := Finset.sum_range_succ' g n
    linarith
  refine ⟨Summable.of_nat_of_neg_add_one hA hB, ?_⟩
  have htsum : ∑' m : ℤ, f m = (∑' n : ℕ, f (n : ℤ)) + (∑' n : ℕ, f (-((n : ℤ) + 1))) :=
    tsum_of_nat_of_neg_add_one hA hB
  calc ∑' m : ℤ, f m = (∑' n : ℕ, f (n : ℤ)) + (∑' n : ℕ, f (-((n : ℤ) + 1))) := htsum
    _ ≤ 2 * D * K / K ^ j + 2 * D * K / K ^ j := add_le_add hAg hBg
    _ = 4 * D * K / K ^ j := by ring

end Work.GM.S3
