import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.KronP.defs

/-!
# KronP: bounds on `pack` and `digitOffset`

Elementary estimates used by the Kronecker word.
-/

set_option autoImplicit false

namespace Work.KronP

open HvdH

/-! ## A geometric bound for the range sums -/

theorem sum_range_pow_le (b n : ℕ) (hb : 1 ≤ b) :
    ((List.range n).map (fun j => 2 ^ (b * j))).sum ≤ 2 ^ (b * (n - 1) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : ((List.range (n + 1)).map (fun j => 2 ^ (b * j))).sum
        = ((List.range n).map (fun j => 2 ^ (b * j))).sum + 2 ^ (b * n) := by
      rw [List.range_succ, List.map_append]
      simp
    rw [hstep, Nat.succ_sub_one]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have he : b * n = b * (n - 1) + b := by
        have h1 : n = (n - 1) + 1 := by omega
        conv_lhs => rw [h1, Nat.mul_add, Nat.mul_one]
      have hpred : b * (n - 1) + 1 ≤ b * n := by omega
      have h2 : 2 ^ (b * (n - 1) + 1) ≤ 2 ^ (b * n) := Nat.pow_le_pow_right (by norm_num) hpred
      have h3 : 2 ^ (b * n) + 2 ^ (b * n) = 2 ^ (b * n + 1) := by ring
      linarith [ih, h2, h3]

/-! ## Bounds on `pack` -/

theorem natAbs_sum_le_map (l : List ℤ) :
    l.sum.natAbs ≤ (l.map Int.natAbs).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h : (a + l.sum).natAbs ≤ a.natAbs + l.sum.natAbs := Int.natAbs_add_le a l.sum
    simpa using le_trans h (Nat.add_le_add_left ih _)

theorem natAbs_mul_pow (z : ℤ) (k : ℕ) : (z * (2 : ℤ) ^ k).natAbs = z.natAbs * 2 ^ k := by
  rw [Int.natAbs_mul]
  simp

theorem getD_mem_of_lt {l : List ℤ} {j : ℕ} (hj : j < l.length) : l.getD j 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

/-- `|pack l b| ≤ M · 2^{b(|l|-1)+1}` when all entries of `l` have absolute value `≤ M`. -/
theorem pack_natAbs_le (l : List ℤ) (b M : ℕ) (hb : 1 ≤ b) (h : ∀ x ∈ l, x.natAbs ≤ M) :
    (pack l b).natAbs ≤ M * 2 ^ (b * (l.length - 1) + 1) := by
  have h1 : ((List.range l.length).map
      (fun j => (l.getD j 0 * (2 : ℤ) ^ (b * j)).natAbs)).sum
      ≤ ((List.range l.length).map (fun j => M * 2 ^ (b * j))).sum := by
    apply List.sum_le_sum
    intro j hj
    rw [List.mem_range] at hj
    rw [natAbs_mul_pow]
    exact Nat.mul_le_mul_right _ (h _ (getD_mem_of_lt hj))
  have h2 : (pack l b).natAbs
      ≤ ((List.range l.length).map
          (fun j => (l.getD j 0 * (2 : ℤ) ^ (b * j)).natAbs)).sum := by
    rw [pack]
    have h3 := natAbs_sum_le_map
      ((List.range l.length).map (fun j => l.getD j 0 * (2 : ℤ) ^ (b * j)))
    rw [List.map_map] at h3
    simpa [Function.comp_def] using h3
  refine le_trans h2 (le_trans h1 ?_)
  rw [List.sum_map_mul_left]
  exact Nat.mul_le_mul_left M (sum_range_pow_le b l.length hb)

/-! ## Bounds on `digitOffset` -/

theorem digitOffset_nonneg (p N : ℕ) : 0 ≤ digitOffset p N := by
  unfold digitOffset
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨m, _, rfl⟩ := hx
  positivity

/-- Crude bound: `|C| ≤ N · 2^{3pN}`. -/
theorem digitOffset_natAbs_le (p N : ℕ) (hp : 1 ≤ p) :
    (digitOffset p N).natAbs ≤ N * 2 ^ (3 * p * N) := by
  have h1 : ∀ m ∈ List.range N,
      ((2 : ℤ) ^ (3 * p - 1) * (2 : ℤ) ^ (3 * p * m)).natAbs ≤ 2 ^ (3 * p * N) := by
    intro m hm
    rw [List.mem_range] at hm
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
    norm_num
    rw [← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    have hm1 : m + 1 ≤ N := hm
    have h3 : 3 * p * (m + 1) ≤ 3 * p * N := Nat.mul_le_mul_left _ hm1
    have hr : 3 * p * (m + 1) = 3 * p * m + 3 * p := by ring
    omega
  have h2 : (digitOffset p N).natAbs
      ≤ ((List.range N).map (fun _ => 2 ^ (3 * p * N))).sum := by
    unfold digitOffset
    have h3 := natAbs_sum_le_map
      ((List.range N).map (fun m => (2 : ℤ) ^ (3 * p - 1) * (2 : ℤ) ^ (3 * p * m)))
    rw [List.map_map] at h3
    simp only [Function.comp_def] at h3
    refine le_trans h3 ?_
    apply List.sum_le_sum
    intro m hm
    exact h1 m hm
  refine le_trans h2 ?_
  rw [Work.ConvR.sum_map_const]
  simp

/-! ## The offset `C = Σ_{m<N} 2^{3p-1}·2^{3p·m}` -/

end Work.KronP
