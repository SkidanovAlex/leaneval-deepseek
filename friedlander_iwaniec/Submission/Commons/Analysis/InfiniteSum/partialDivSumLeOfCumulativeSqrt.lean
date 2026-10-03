import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt

open scoped BigOperators
open Finset

namespace Commons.Analysis.InfiniteSum

private lemma inv_sub_inv_succ (i : ℕ) (hi : 1 ≤ i) :
    ((i : ℝ) ⁻¹ - ((i : ℝ) + 1)⁻¹) = ((i : ℝ) * ((i : ℝ) + 1))⁻¹ := by
  have hiR : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
  have h1 : (i : ℝ) ≠ 0 := ne_of_gt hiR
  have h2 : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

/-- `√n / (n(n+1)) ≤ 2(1/√n − 1/√(n+1))` for `n ≥ 1`. -/
private lemma sqrt_div_mul_add_one_le_two_inv_sub (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      2 * ((Real.sqrt (n : ℝ))⁻¹ - (Real.sqrt ((n : ℝ) + 1))⁻¹) := by
  set s : ℝ := Real.sqrt (n : ℝ) with hs_def
  set t : ℝ := Real.sqrt ((n : ℝ) + 1) with ht_def
  have hsq : s ^ 2 = (n : ℝ) := by
    rw [hs_def]
    exact Real.sq_sqrt (by positivity)
  have htq : t ^ 2 = (n : ℝ) + 1 := by
    rw [ht_def]
    exact Real.sq_sqrt (by positivity)
  have hspos : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.mpr (by positivity)
  have htpos : 0 < t := by rw [ht_def]; exact Real.sqrt_pos.mpr (by positivity)
  have hst : s ≤ t := by
    rw [hs_def, ht_def]
    exact Real.sqrt_le_sqrt (by norm_num : (n : ℝ) ≤ (n : ℝ) + 1)
  have hs_ne : s ≠ 0 := ne_of_gt hspos
  have ht_ne : t ≠ 0 := ne_of_gt htpos
  have hts_ne : t + s ≠ 0 := by positivity
  have h_ts : t - s = (t + s)⁻¹ := by
    have hprod : (t - s) * (t + s) = 1 := by nlinarith [hsq, htq]
    field_simp [hts_ne]
    exact hprod
  rw [← htq, ← hsq]
  have hL : s / (s ^ 2 * t ^ 2) = (s * t ^ 2)⁻¹ := by
    field_simp [hs_ne, ht_ne]
  rw [hL]
  have hRHS : 2 * (s⁻¹ - t⁻¹) = 2 / (s * t * (t + s)) := by
    have hsub : s⁻¹ - t⁻¹ = (t - s) / (s * t) := by
      field_simp [hs_ne, ht_ne]
    rw [hsub]
    rw [h_ts]
    field_simp [hs_ne, ht_ne, hts_ne]
  rw [hRHS]
  rw [le_div_iff₀]
  · field_simp [hs_ne, ht_ne, hts_ne]
    nlinarith [hst]
  · positivity

/-- Abel summation identity (partial summation), `G` are prefix sums from 0. -/
private lemma abel_id {a : ℕ → ℝ} {N U : ℕ} (hN : 1 ≤ N) (hNU : N ≤ U) :
    (∑ i ∈ Finset.Ico N (U + 1), a i / (i : ℝ)) =
      (∑ i ∈ Finset.range (U + 1), a i) / (U : ℝ) -
        (∑ i ∈ Finset.range N, a i) / (N : ℝ) +
        (∑ i ∈ Finset.Ico N U, (∑ j ∈ Finset.range (i + 1), a j) / ((i : ℝ) * ((i : ℝ) + 1))) := by
  let f : ℕ → ℝ := fun n => (n : ℝ)⁻¹
  let G : ℕ → ℝ := fun m => ∑ i ∈ Finset.range m, a i
  have hbp := Finset.sum_Ico_by_parts (R := ℝ) (M := ℝ) (f := f) (g := a) (m := N) (n := U + 1)
    (hmn := by omega)
  have hterm : ∀ i ∈ Finset.Ico N (U + 1), f i • a i = a i / (i : ℝ) := by
    intro i hi
    dsimp [f]
    rw [div_eq_mul_inv]
    ring
  have hL : (∑ i ∈ Finset.Ico N (U + 1), f i • a i) =
      ∑ i ∈ Finset.Ico N (U + 1), a i / (i : ℝ) := by
    exact Finset.sum_congr rfl hterm
  have hmain : (∑ i ∈ Finset.Ico N (U + 1), a i / (i : ℝ)) =
      f (U + 1 - 1) • G (U + 1) - f N • G N -
        (∑ i ∈ Finset.Ico N (U + 1 - 1), (f (i + 1) - f i) • G (i + 1)) := by
    rwa [← hL]
  have hU1 : U + 1 - 1 = U := by omega
  have hG : ∀ m : ℕ, G m = ∑ i ∈ Finset.range m, a i := by intro m; rfl
  calc
    (∑ i ∈ Finset.Ico N (U + 1), a i / (i : ℝ))
        = f U • G (U + 1) - f N • G N -
            (∑ i ∈ Finset.Ico N U, (f (i + 1) - f i) • G (i + 1)) := by
          rw [hU1] at hmain
          exact hmain
    _ = G (U + 1) / (U : ℝ) - G N / (N : ℝ) +
          (∑ i ∈ Finset.Ico N U, G (i + 1) / ((i : ℝ) * ((i : ℝ) + 1))) := by
          rw [show f U • G (U + 1) = G (U + 1) / (U : ℝ) by
            dsimp [f]
            rw [div_eq_mul_inv]
            rw [mul_comm]]
          rw [show f N • G N = G N / (N : ℝ) by
            dsimp [f]
            rw [div_eq_mul_inv]
            rw [mul_comm]]
          have hmiddle :
            -(∑ i ∈ Finset.Ico N U, (f (i + 1) - f i) • G (i + 1)) =
              ∑ i ∈ Finset.Ico N U, G (i + 1) / ((i : ℝ) * ((i : ℝ) + 1)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            have hiN : N ≤ i := by
              simp at hi
              exact hi.1
            have hi1 : 1 ≤ i := le_trans hN hiN
            dsimp [f]
            have hneg : ((↑(i + 1))⁻¹ - (↑i)⁻¹) = -(((i : ℝ) * ((i : ℝ) + 1))⁻¹) := by
              have h := inv_sub_inv_succ i hi1
              rw [show ((↑(i + 1) : ℝ)⁻¹) = ((↑i : ℝ) + 1)⁻¹ by norm_num]
              linarith
            rw [hneg]
            rw [show -(-((↑i * (↑i + 1))⁻¹) * G (i + 1)) = (↑i * (↑i + 1))⁻¹ * G (i + 1) by ring]
            rw [div_eq_mul_inv]
            rw [mul_comm]
          rw [show G (U + 1) / (U : ℝ) - G N / (N : ℝ) -
                  (∑ i ∈ Finset.Ico N U, (f (i + 1) - f i) • G (i + 1))
              = G (U + 1) / (U : ℝ) - G N / (N : ℝ) +
                  -(∑ i ∈ Finset.Ico N U, (f (i + 1) - f i) • G (i + 1)) by ring]
          rw [hmiddle]
    _ = (∑ i ∈ Finset.range (U + 1), a i) / (U : ℝ) -
          (∑ i ∈ Finset.range N, a i) / (N : ℝ) +
          (∑ i ∈ Finset.Ico N U, (∑ j ∈ Finset.range (i + 1), a j) / ((i : ℝ) * ((i : ℝ) + 1))) := by
          rfl

/-- Telescoping: `∑_{i=N}^{U-1} (1/√i − 1/√(i+1)) = 1/√N − 1/√U`. -/
private lemma sum_Ico_inv_sqrt_sub {N U : ℕ} (hNU : N ≤ U) :
    (∑ i ∈ Finset.Ico N U, ((Real.sqrt (i : ℝ))⁻¹ - (Real.sqrt ((i : ℝ) + 1))⁻¹)) =
      (Real.sqrt (N : ℝ))⁻¹ - (Real.sqrt (U : ℝ))⁻¹ := by
  rw [Finset.sum_Ico_eq_sum_range]
  let f : ℕ → ℝ := fun k : ℕ => (Real.sqrt (((N + k : ℕ) : ℝ)))⁻¹
  have hstep : (∑ k ∈ Finset.range (U - N), (f k - f (k + 1))) =
      f 0 - f (U - N) := by
    exact Finset.sum_range_sub' (f := f) (U - N)
  calc
    (∑ k ∈ Finset.range (U - N),
        ((Real.sqrt (((N + k : ℕ) : ℝ)))⁻¹ - (Real.sqrt (((N + k : ℕ) : ℝ) + 1))⁻¹))
        = ∑ k ∈ Finset.range (U - N), (f k - f (k + 1)) := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp [f]
          congr 1
          congr 1
          congr 1
          norm_num
          ring
    _ = f 0 - f (U - N) := hstep
    _ = (Real.sqrt (N : ℝ))⁻¹ - (Real.sqrt (U : ℝ))⁻¹ := by
          dsimp [f]
          congr 1
          congr 1
          have hsub : N + (U - N) = U := by omega
          rw [hsub]

/-- Finite Abel-summation tail bound:
`∑_{i=N}^{U} a i / i ≤ 3B/√N` under the cumulative hypothesis. -/
private lemma partial_sum_tail_le {a : ℕ → ℝ} (ha_nonneg : ∀ n : ℕ, 0 ≤ a n)
    {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ m : ℕ, (∑ k ∈ Finset.Icc 0 m, a k) ≤ B * Real.sqrt (m : ℝ))
    {N U : ℕ} (hN : 2 ≤ N) (hNU : N ≤ U) :
    (∑ i ∈ Finset.Ico N (U + 1), a i / (i : ℝ)) ≤ 3 * B / Real.sqrt (N : ℝ) := by
  have hN1 : 1 ≤ N := by omega
  have hUpos : (0 : ℝ) < (U : ℝ) := by exact_mod_cast (by omega : 0 < U)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hsqrtNpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hG_nonneg : ∀ m : ℕ, 0 ≤ (∑ i ∈ Finset.range m, a i) := by
    intro m
    exact Finset.sum_nonneg (fun i hi => ha_nonneg i)
  have hA' : ∀ m : ℕ, (∑ i ∈ Finset.range (m + 1), a i) ≤ B * Real.sqrt (m : ℝ) := by
    intro m
    have hset : Finset.range (m + 1) = Finset.Icc 0 m := by
      ext x
      simp only [Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    exact hA m
  have habel := abel_id (a := a) (N := N) (U := U) hN1 hNU
  have h1 : (∑ i ∈ Finset.Ico N (U + 1), a i / (i : ℝ)) ≤
      (∑ i ∈ Finset.range (U + 1), a i) / (U : ℝ) +
        (∑ i ∈ Finset.Ico N U, (∑ j ∈ Finset.range (i + 1), a j) / ((i : ℝ) * ((i : ℝ) + 1))) := by
    rw [habel]
    have hneg : 0 ≤ (∑ i ∈ Finset.range N, a i) / (N : ℝ) := by
      exact div_nonneg (hG_nonneg N) hNpos.le
    nlinarith
  have h2 : (∑ i ∈ Finset.range (U + 1), a i) / (U : ℝ) ≤ B / Real.sqrt (N : ℝ) := by
    have hsqrtUpos : 0 < Real.sqrt (U : ℝ) := Real.sqrt_pos.mpr hUpos
    have hsqrtU_ne : Real.sqrt (U : ℝ) ≠ 0 := ne_of_gt hsqrtUpos
    have hU_eq : (U : ℝ) = Real.sqrt (U : ℝ) * Real.sqrt (U : ℝ) :=
      (Real.mul_self_sqrt hUpos.le).symm
    calc
      (∑ i ∈ Finset.range (U + 1), a i) / (U : ℝ)
          ≤ (B * Real.sqrt (U : ℝ)) / (U : ℝ) := by
            exact div_le_div_of_nonneg_right (hA' U) hUpos.le
      _ = B / Real.sqrt (U : ℝ) := by
            field_simp [hsqrtU_ne]
            rw [pow_two, ← hU_eq]
      _ ≤ B / Real.sqrt (N : ℝ) := by
            have hsqrtN_le_sqrtU : Real.sqrt (N : ℝ) ≤ Real.sqrt (U : ℝ) :=
              Real.sqrt_le_sqrt (by exact_mod_cast hNU)
            have hrec : (Real.sqrt (U : ℝ))⁻¹ ≤ (Real.sqrt (N : ℝ))⁻¹ := by
              simpa [div_eq_mul_inv]
                using (one_div_le_one_div_of_le hsqrtNpos hsqrtN_le_sqrtU)
            simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_left hrec hB)
  have h3 : (∑ i ∈ Finset.Ico N U,
        (∑ j ∈ Finset.range (i + 1), a j) / ((i : ℝ) * ((i : ℝ) + 1))) ≤
      2 * B / Real.sqrt (N : ℝ) := by
    have htel := sum_Ico_inv_sqrt_sub (N := N) (U := U) hNU
    calc
      (∑ i ∈ Finset.Ico N U,
          (∑ j ∈ Finset.range (i + 1), a j) / ((i : ℝ) * ((i : ℝ) + 1)))
          ≤ (∑ i ∈ Finset.Ico N U, (B * Real.sqrt (i : ℝ)) / ((i : ℝ) * ((i : ℝ) + 1))) := by
            apply Finset.sum_le_sum
            intro i hi
            have hiN : N ≤ i := by
              simp at hi
              exact hi.1
            have hden : 0 ≤ (i : ℝ) * ((i : ℝ) + 1) := by positivity
            exact div_le_div_of_nonneg_right (hA' i) hden
      _ ≤ (∑ i ∈ Finset.Ico N U, 2 * B * ((Real.sqrt (i : ℝ))⁻¹ - (Real.sqrt ((i : ℝ) + 1))⁻¹)) := by
            apply Finset.sum_le_sum
            intro i hi
            have hiN : N ≤ i := by
              simp at hi
              exact hi.1
            have hi1 : 1 ≤ i := le_trans hN1 hiN
            have hpt := sqrt_div_mul_add_one_le_two_inv_sub i hi1
            calc
              (B * Real.sqrt (i : ℝ)) / ((i : ℝ) * ((i : ℝ) + 1))
                  = B * (Real.sqrt (i : ℝ) / ((i : ℝ) * ((i : ℝ) + 1))) := by ring
              _ ≤ B * (2 * ((Real.sqrt (i : ℝ))⁻¹ - (Real.sqrt ((i : ℝ) + 1))⁻¹)) := by
                  exact mul_le_mul_of_nonneg_left hpt hB
              _ = 2 * B * ((Real.sqrt (i : ℝ))⁻¹ - (Real.sqrt ((i : ℝ) + 1))⁻¹) := by ring
      _ = 2 * B * (∑ i ∈ Finset.Ico N U, ((Real.sqrt (i : ℝ))⁻¹ - (Real.sqrt ((i : ℝ) + 1))⁻¹)) := by
            rw [← Finset.mul_sum]
      _ = 2 * B * ((Real.sqrt (N : ℝ))⁻¹ - (Real.sqrt (U : ℝ))⁻¹) := by
            rw [htel]
      _ ≤ 2 * B / Real.sqrt (N : ℝ) := by
            have hB2 : 0 ≤ 2 * B := by positivity
            have hUinv : 0 ≤ (Real.sqrt (U : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg U)
            have hmain : (Real.sqrt (N : ℝ))⁻¹ - (Real.sqrt (U : ℝ))⁻¹ ≤ (Real.sqrt (N : ℝ))⁻¹ := by
              linarith
            have hbound : 2 * B * ((Real.sqrt (N : ℝ))⁻¹ - (Real.sqrt (U : ℝ))⁻¹) ≤
                2 * B * (Real.sqrt (N : ℝ))⁻¹ :=
              mul_le_mul_of_nonneg_left hmain hB2
            simpa [div_eq_mul_inv] using hbound
  calc
    (∑ i ∈ Finset.Ico N (U + 1), a i / (i : ℝ))
        ≤ (∑ i ∈ Finset.range (U + 1), a i) / (U : ℝ) +
            (∑ i ∈ Finset.Ico N U, (∑ j ∈ Finset.range (i + 1), a j) / ((i : ℝ) * ((i : ℝ) + 1))) := h1
    _ ≤ B / Real.sqrt (N : ℝ) + 2 * B / Real.sqrt (N : ℝ) := add_le_add h2 h3
    _ = 3 * B / Real.sqrt (N : ℝ) := by
          field_simp [ne_of_gt hsqrtNpos]
          ring

/-- `Finset.Icc N M` and `Finset.Ico N (M + 1)` are the same set. -/
private lemma Icc_eq_Ico_succ_right (N M : ℕ) : Finset.Icc N M = Finset.Ico N (M + 1) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  omega

/-- If the cumulative sums `∑_{k ≤ m} a k` are `O(√m)` and the terms `a n` are
nonnegative, then the finite partial sum `∑_{k = N}^{M} a k / k` (of the
`1/k`-weighted series) is `O(1/√N)`, uniformly in `M ≥ N`. -/
theorem partialDivSumLeOfCumulativeSqrt {a : ℕ → ℝ} (ha_nonneg : ∀ n : ℕ, 0 ≤ a n)
    {B : ℝ} (hB : 0 ≤ B)
    (hA : ∀ m : ℕ, (∑ k ∈ Finset.Icc 0 m, a k) ≤ B * Real.sqrt (m : ℝ)) :
    ∀ ⦃N M : ℕ⦄, 2 ≤ N → N ≤ M →
      (∑ k ∈ Finset.Icc N M, a k / (k : ℝ)) ≤ 3 * B / Real.sqrt (N : ℝ) := by
  intro N M hN hNM
  rw [Icc_eq_Ico_succ_right]
  simpa using partial_sum_tail_le (a := a) ha_nonneg hB hA (N := N) (U := M) hN hNM

end Commons.Analysis.InfiniteSum