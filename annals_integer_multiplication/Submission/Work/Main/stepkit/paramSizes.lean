import Mathlib
import Submission.Work.Main.defs

/-!
# Sizes of the §5.1 parameters

The parameters of one recursive step are all obtained from `b = bpar n = ⌈log₂ n⌉` by a
constant number of arithmetic operations, so their encodings still have `O(n.size)` bits:

* `bpar n`: `b ≤ n`, hence `size (bpar n) ≤ size n`;
* `ppar n = 6b`: `size` is subadditive under multiplication, and `size 6 = 3`;
* `apar n = ⌈(12d²b)^{1/4}⌉`: two square roots, then a `+1`, and `size (12d²) ≤ 26` (with `d = 1729`);
* `Tpar n = 2^{kTpar n}` with `kTpar n = ⌈log₂ ⌈4n/b⌉⌉`: `⌈4n/b⌉ ≤ 4n + 1 ≤ 4(n+1) ≤ 2^{size n + 2}`,
  so `kTpar n ≤ size n + 2` and `Tpar n ≤ 2^{size n + 2}` (note: the cruder `+3` is not enough here);
* the chunk count `nchunks n (bpar n) = ⌈n/b⌉ ≤ n` (division by zero being harmless).

Everything is elementary size arithmetic on `Nat.clog`, `Nat.sqrt` and `Nat.div`; the only
non-library ingredient is `size (m * n) ≤ size m + size n`.
-/

set_option autoImplicit false

namespace Work.Main.stepkit

/-! ## Elementary size arithmetic -/

/-- `size` is subadditive under multiplication. -/
theorem size_mul_le (m n : ℕ) : (m * n).size ≤ m.size + n.size := by
  rw [Nat.size_le]
  have hm : m < 2 ^ m.size := Nat.lt_size_self m
  have hn : n < 2 ^ n.size := Nat.lt_size_self n
  have h : m * n < 2 ^ m.size * 2 ^ n.size :=
    Nat.mul_lt_mul_of_lt_of_le hm (le_of_lt hn) (Nat.two_pow_pos _)
  rwa [← pow_add] at h

/-- Taking a square root does not increase the size. -/
theorem size_sqrt_le (m : ℕ) : m.sqrt.size ≤ m.size :=
  Nat.size_le_size (Nat.sqrt_le_self m)

/-- Adding one costs at most one bit. -/
theorem size_succ_le (m : ℕ) : (m + 1).size ≤ m.size + 1 := by
  rw [Nat.size_le]
  have h : m + 1 ≤ 2 ^ m.size := Nat.succ_le_of_lt (Nat.lt_size_self m)
  calc m + 1 ≤ 2 ^ m.size := h
    _ < 2 ^ (m.size + 1) := by rw [pow_succ]; have := Nat.two_pow_pos m.size; omega

/-! ## The parameters -/

/-- `b = ⌈log₂ n⌉ ≤ n`. -/
theorem bpar_le_self (n : ℕ) : HvdH.bpar n ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [HvdH.bpar, h]
  · rw [HvdH.bpar, Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)]
    exact le_of_lt Nat.lt_two_pow_self

/-- `p = 6b` has at most `size n + 4` bits. -/
theorem ppar_size_le (n : ℕ) : (HvdH.ppar n).size ≤ n.size + 4 := by
  have h : (HvdH.ppar n).size ≤ (6 : ℕ).size + (HvdH.bpar n).size := by
    rw [HvdH.ppar]; exact size_mul_le 6 (HvdH.bpar n)
  have h6 : (6 : ℕ).size ≤ 3 := by rw [Nat.size_le]; norm_num
  have hb : (HvdH.bpar n).size ≤ n.size := Nat.size_le_size (bpar_le_self n)
  omega

/-- `α = ⌈(12d²b)^{1/4}⌉` has at most `size n + 30` bits. -/
theorem apar_size_le (n : ℕ) : (HvdH.apar n).size ≤ n.size + 30 := by
  have h1 : (HvdH.apar n).size ≤
      (Nat.sqrt (Nat.sqrt (12 * HvdH.D ^ 2 * HvdH.bpar n - 1))).size + 1 :=
    size_succ_le (Nat.sqrt (Nat.sqrt (12 * HvdH.D ^ 2 * HvdH.bpar n - 1)))
  have h2 : (Nat.sqrt (Nat.sqrt (12 * HvdH.D ^ 2 * HvdH.bpar n - 1))).size ≤
      (12 * HvdH.D ^ 2 * HvdH.bpar n - 1).size :=
    le_trans (size_sqrt_le _) (size_sqrt_le _)
  have h3 : (12 * HvdH.D ^ 2 * HvdH.bpar n - 1).size ≤
      (12 * HvdH.D ^ 2 * HvdH.bpar n).size :=
    Nat.size_le_size (Nat.sub_le _ _)
  have h4 : (12 * HvdH.D ^ 2 * HvdH.bpar n).size ≤
      (12 * HvdH.D ^ 2).size + (HvdH.bpar n).size := size_mul_le _ _
  have h5 : (12 * HvdH.D ^ 2).size ≤ 26 := by rw [Nat.size_le]; norm_num [HvdH.D]
  have h6 : (HvdH.bpar n).size ≤ n.size := Nat.size_le_size (bpar_le_self n)
  omega

/-- `k = ⌈log₂ ⌈4n/b⌉⌉ ≤ size n + 2`, i.e. the transform length `T = 2^k` is at most `2^{size n + 2}`. -/
theorem kTpar_le_two (n : ℕ) : HvdH.kTpar n ≤ n.size + 2 := by
  have hV : (4 * n + HvdH.bpar n - 1) / HvdH.bpar n ≤ 4 * n + 1 := by
    rcases Nat.eq_zero_or_pos (HvdH.bpar n) with h0 | hpos
    · rw [h0, Nat.div_zero]; omega
    · have h : 4 * n ≤ 4 * n * HvdH.bpar n := by
        calc 4 * n = 4 * n * 1 := (mul_one _).symm
          _ ≤ 4 * n * HvdH.bpar n := Nat.mul_le_mul_left _ hpos
      have h2 : HvdH.bpar n * (4 * n + 1) = 4 * n * HvdH.bpar n + HvdH.bpar n := by ring
      have hle : 4 * n + HvdH.bpar n - 1 ≤ HvdH.bpar n * (4 * n + 1) := by omega
      exact Nat.div_le_of_le_mul hle
  have hV2 : 4 * n + 1 ≤ 2 ^ (n.size + 2) := by
    have h1 : n + 1 ≤ 2 ^ n.size := Nat.succ_le_of_lt (Nat.lt_size_self n)
    have h2 : 4 * (n + 1) ≤ 2 ^ (n.size + 2) := by
      calc 4 * (n + 1) ≤ 4 * 2 ^ n.size := Nat.mul_le_mul_left 4 h1
        _ = 2 ^ (n.size + 2) := by rw [pow_add]; ring
    omega
  calc HvdH.kTpar n = Nat.clog 2 ((4 * n + HvdH.bpar n - 1) / HvdH.bpar n) := rfl
    _ ≤ Nat.clog 2 (4 * n + 1) := Nat.clog_mono_right 2 hV
    _ ≤ n.size + 2 := Nat.clog_le_of_le_pow hV2

/-- The chunk count `⌈n/b⌉` has at most `size n + 1` bits. -/
theorem nchunks_bpar_size (n : ℕ) :
    (Work.Main.nchunks n (HvdH.bpar n)).size ≤ n.size + 1 := by
  rcases Nat.eq_zero_or_pos (HvdH.bpar n) with h0 | hpos
  · rw [Work.Main.nchunks, h0, Nat.div_zero]
    simp
  · have hle : Work.Main.nchunks n (HvdH.bpar n) ≤ n := by
      rw [Work.Main.nchunks, Nat.div_le_iff_le_mul_add_pred hpos]
      have h : n ≤ HvdH.bpar n * n := Nat.le_mul_of_pos_left n hpos
      omega
    have h2 := Nat.size_le_size hle
    omega

theorem paramSizes (n : ℕ) :
    (HvdH.bpar n).size ≤ n.size ∧ (HvdH.ppar n).size ≤ n.size + 4 ∧
    (HvdH.apar n).size ≤ n.size + 30 ∧ HvdH.Tpar n ≤ 2 ^ (n.size + 2) ∧
    (Work.Main.nchunks n (HvdH.bpar n)).size ≤ n.size + 1 :=
  ⟨Nat.size_le_size (bpar_le_self n), ppar_size_le n, apar_size_le n,
    Nat.pow_le_pow_right (by norm_num) (kTpar_le_two n), nchunks_bpar_size n⟩

end Work.Main.stepkit
