import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_aux.caseT_defs
import Submission.Work.LinnikBurgess.a2_dist_le_two_Icc
import Submission.Work.LinnikBurgess.sum_sqrtGcd_Icc_le
import Submission.Work.LinnikBurgess.sum_filter_dvd_Icc

/-!
# Case T: the `Bsum` (single-weight) estimate

For the Case-T estimate of the frame count one needs the elementary bound

`Bsum H m e x0 = ∑_{x ∈ [1,H]} [x ≠ x0][e ∣ |x - x0|] √(gcd m |x - x0|) ≤ 2 (H/e) τ(m)`,

with `gcd(m,e) = 1`.  The point is that the `y ↦ |x - x0|` map is at most two-to-one
(`a2_dist_le_two_Icc`), and that after writing a contributing `x` as `x0 ± e s`, coprimality
turns `√(gcd m |x0 - x|) = √(gcd m (e s))` into `√(gcd m s)`, so the remaining sum is over
`s ∈ [1, H/e]`, giving the factor `H/e` and the divisor-counting bound
`∑_{s ≤ N} √(gcd m s) ≤ N τ(m)` (`sum_sqrtGcd_Icc_le`).
-/

namespace Work.LinnikBurgess

open scoped BigOperators

theorem caseT_Bsum_le {H m e : ℕ} (hm : 0 < m) (he : 0 < e) (hme : Nat.Coprime m e)
    {x0 : ℕ} (hx0 : x0 ∈ Finset.Icc 1 H) :
    Work.LinnikBurgess.frame_count_prov_aux.Bsum H m e x0
      ≤ 2 * ((H : ℝ) / (e : ℝ)) * ((m.divisors.card : ℕ) : ℝ) := by
  obtain ⟨hx1, hxH⟩ := Finset.mem_Icc.mp hx0
  -- the summand, as a function of the distance
  set F : ℕ → ℝ := fun c => if e ∣ c then Real.sqrt ((Nat.gcd m c : ℕ) : ℝ) else 0 with hF
  have hFnn : ∀ n, 0 ≤ F n := by
    intro n
    change 0 ≤ (if e ∣ n then Real.sqrt ((Nat.gcd m n : ℕ) : ℝ) else 0)
    split_ifs with h
    · exact Real.sqrt_nonneg _
    · exact le_refl 0
  -- `Bsum` is the sum of `F` over the distances `|x0 - x|`
  have hB : Work.LinnikBurgess.frame_count_prov_aux.Bsum H m e x0
      = ∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x0), F (del x0 y) := by
    rw [Work.LinnikBurgess.frame_count_prov_aux.Bsum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    change (if y ≠ x0 ∧ e ∣ del x0 y then wg m x0 y else 0)
      = (if y ≠ x0 then
          (if e ∣ del x0 y then Real.sqrt ((Nat.gcd m (del x0 y) : ℕ) : ℝ) else 0) else 0)
    by_cases hy : y ≠ x0 <;> by_cases hed : e ∣ del x0 y <;> simp [hy, hed, wg]
  -- the distance sum runs over the multiples of `e` in `[1, H-1]`
  have hFsum : ∑ c ∈ Finset.Icc 1 (H - 1), F c
      = ∑ s ∈ Finset.Icc 1 ((H - 1) / e), Real.sqrt ((Nat.gcd m s : ℕ) : ℝ) := by
    change (∑ c ∈ Finset.Icc 1 (H - 1),
      (if e ∣ c then Real.sqrt ((Nat.gcd m c : ℕ) : ℝ) else 0)) = _
    rw [← Finset.sum_filter]
    rw [sum_filter_dvd_Icc e (H - 1) he (fun c => Real.sqrt ((Nat.gcd m c : ℕ) : ℝ))]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Nat.Coprime.gcd_mul_left_cancel_right s hme.symm]
  have hτ : (0 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := by positivity
  have hdiv : (((H - 1) / e : ℕ) : ℝ) ≤ (H : ℝ) / (e : ℝ) :=
    le_trans (Nat.cast_le.mpr (Nat.div_le_div_right (Nat.sub_le H 1))) Nat.cast_div_le
  have hN := sum_sqrtGcd_Icc_le m ((H - 1) / e) hm
  calc Work.LinnikBurgess.frame_count_prov_aux.Bsum H m e x0
      = ∑ y ∈ (Finset.Icc 1 H).filter (fun y => y ≠ x0), F (del x0 y) := hB
    _ ≤ 2 * ∑ c ∈ Finset.Icc 1 (H - 1), F c := a2_dist_le_two_Icc hx1 hxH hFnn
    _ = 2 * ∑ s ∈ Finset.Icc 1 ((H - 1) / e), Real.sqrt ((Nat.gcd m s : ℕ) : ℝ) := by
        rw [hFsum]
    _ ≤ 2 * ((((H - 1) / e : ℕ) : ℝ) * ((m.divisors.card : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hN (by norm_num)
    _ ≤ 2 * ((H : ℝ) / (e : ℝ)) * ((m.divisors.card : ℕ) : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hdiv hτ
        linarith

end Work.LinnikBurgess
