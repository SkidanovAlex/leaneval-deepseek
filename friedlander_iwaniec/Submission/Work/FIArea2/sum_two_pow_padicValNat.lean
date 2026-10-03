import Mathlib

namespace Work.FIArea2

/-- Sum over the nonzero even integers `i < M` of `2 ^ (padicValNat 2 i + 1)`. -/
def SumA (M : ℕ) : ℕ :=
  ∑ i ∈ (Finset.range M).filter (fun i => i ≠ 0 ∧ 2 ∣ i), 2 ^ (padicValNat 2 i + 1)

/-- Sum over the nonzero integers `i < M` of `2 ^ (padicValNat 2 i)`. -/
def SumB (M : ℕ) : ℕ :=
  ∑ i ∈ (Finset.range M).filter (fun i => i ≠ 0), 2 ^ padicValNat 2 i

lemma padicValNat_two_mul (j : ℕ) (hj : j ≠ 0) :
    padicValNat 2 (2 * j) = padicValNat 2 j + 1 := by
  rw [padicValNat.mul (p := 2) (by norm_num) hj, padicValNat_self, Nat.add_comm]

lemma padicValNat_two_mul_add_one (j : ℕ) : padicValNat 2 (2 * j + 1) = 0 := by
  rw [padicValNat.eq_zero_of_not_dvd]
  intro h; obtain ⟨c, hc⟩ := h; omega

lemma pow_padicValNat_two_mul (j : ℕ) (hj : j ≠ 0) :
    2 ^ padicValNat 2 (2 * j) = 2 * 2 ^ padicValNat 2 j := by
  rw [padicValNat_two_mul j hj, pow_succ']

lemma pow_padicValNat_two_mul_succ (j : ℕ) (hj : j ≠ 0) :
    2 ^ (padicValNat 2 (2 * j) + 1) = 4 * 2 ^ padicValNat 2 j := by
  rw [pow_succ', pow_padicValNat_two_mul j hj]
  ring

/-- The nonzero integers `i < 2M` split into the even ones `2j` (with `0 < j < M`)
and the odd ones `2j+1` (with `j < M`). -/
lemma range_two_mul_filter_ne (M : ℕ) :
    (Finset.range (2 * M)).filter (fun i => i ≠ 0)
      = ((Finset.range M).filter (fun j => j ≠ 0)).image (fun j => 2 * j)
        ∪ (Finset.range M).image (fun j => 2 * j + 1) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hi, hne⟩
    rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨k, ⟨by omega, by omega⟩, by omega⟩
    · exact Or.inr ⟨k, by omega, by omega⟩
  · rintro (⟨k, ⟨hk, hkne⟩, heq⟩ | ⟨k, hk, heq⟩) <;> omega

lemma disjoint_even_odd (M : ℕ) :
    Disjoint (((Finset.range M).filter (fun j => j ≠ 0)).image (fun j => 2 * j))
             ((Finset.range M).image (fun j => 2 * j + 1)) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_image] at hx hy
  obtain ⟨j, -, hj⟩ := hx
  obtain ⟨k, -, hk⟩ := hy
  omega

/-- `SumA` at `2M` equals `4` times `SumB` at `M`: the map `j ↦ 2j` is a bijection
from the nonzero `j < M` onto the nonzero even `i < 2M`, and `padicValNat 2 (2j) = padicValNat 2 j + 1`. -/
lemma A_even (M : ℕ) : SumA (2 * M) = 4 * SumB M := by
  unfold SumA SumB
  have hset : (Finset.range (2 * M)).filter (fun i => i ≠ 0 ∧ 2 ∣ i)
      = ((Finset.range M).filter (fun j => j ≠ 0)).image (fun j => 2 * j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hi, hne, hdvd⟩
      obtain ⟨m, hm⟩ := hdvd
      exact ⟨m, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨j, ⟨hj, hjne⟩, rfl⟩
      exact ⟨by omega, by omega, ⟨j, rfl⟩⟩
  rw [hset, Finset.sum_image (g := fun j => 2 * j) (fun a _ b _ h => by beta_reduce at h; omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact pow_padicValNat_two_mul_succ j (Finset.mem_filter.mp hj).2

/-- Recurrence `SumB (2M) = 2 * SumB M + M`. -/
lemma B_rec (M : ℕ) : SumB (2 * M) = 2 * SumB M + M := by
  unfold SumB
  rw [range_two_mul_filter_ne M, Finset.sum_union (disjoint_even_odd M)]
  rw [Finset.sum_image (g := fun j => 2 * j) (fun a _ b _ h => by beta_reduce at h; omega),
      Finset.sum_image (g := fun j => 2 * j + 1) (fun a _ b _ h => by beta_reduce at h; omega)]
  have h1 : ∑ j ∈ (Finset.range M).filter (fun j => j ≠ 0), 2 ^ padicValNat 2 (2 * j)
      = 2 * ∑ j ∈ (Finset.range M).filter (fun j => j ≠ 0), 2 ^ padicValNat 2 j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact pow_padicValNat_two_mul j (Finset.mem_filter.mp hj).2
  have h2 : ∑ j ∈ Finset.range M, 2 ^ padicValNat 2 (2 * j + 1) = M := by
    trans ∑ j ∈ Finset.range M, (1 : ℕ)
    · apply Finset.sum_congr rfl
      intro j _
      rw [padicValNat_two_mul_add_one, pow_zero]
    · simp
  rw [h1, h2]

/-- `2 * SumB (2 ^ n) = n * 2 ^ n`. -/
lemma two_mul_SumB (n : ℕ) : 2 * SumB (2 ^ n) = n * 2 ^ n := by
  induction n with
  | zero => simp [SumB]
  | succ n ih =>
    rw [show 2 ^ (n + 1) = 2 * 2 ^ n by rw [pow_succ, mul_comm], B_rec, ih]
    ring

theorem sum_two_pow_padicValNat (n : ℕ) :
    (∑ i ∈ (Finset.range (2 ^ n)).filter (fun i => i ≠ 0 ∧ 2 ∣ i),
        2 ^ (padicValNat 2 i + 1)) = (n - 1) * 2 ^ n := by
  change SumA (2 ^ n) = (n - 1) * 2 ^ n
  rcases n with _ | n
  · simp [SumA]
  · rw [show 2 ^ (n + 1) = 2 * 2 ^ n by rw [pow_succ, mul_comm], A_even]
    rw [show (n + 1) - 1 = n by omega]
    have h := two_mul_SumB n
    calc 4 * SumB (2 ^ n) = 2 * (2 * SumB (2 ^ n)) := by ring
      _ = 2 * (n * 2 ^ n) := by rw [h]
      _ = n * (2 * 2 ^ n) := by ring

end Work.FIArea2
