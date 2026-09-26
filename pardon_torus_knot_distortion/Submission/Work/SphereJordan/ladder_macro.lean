import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_basic

/-!
# Macro-steps on the even lattice, and the ladder index schedule

This file provides the combinatorial heart of the lattice approximation of a loop in an open set
`U ⊆ ℂ` (continued in `ladder_walk.lean` and `ladder_approx.lean`):

* `cRound` / `snap` — rounding a point of `ℂ` to the nearest point of the **even** lattice `2ℤ²`
  (scaled by a mesh `c`), so that all displacements between ladder points have even coordinates;
* `mv a k` — moving `k` unit steps from `0` towards `a` (clamped);
* `mac q j` — the **macro**: for a displacement `q` of the even lattice with
  `|q.1| + |q.2| ≤ 12`, the list of vertices of a walk of **exactly twelve** unit lattice steps
  from `0` to `q` (a monotone staircase, padded at the front by two-step spurs in the
  `x`-direction);
* `bo` — the index schedule `m ↦ (block, offset)` for the concatenation of blocks of length
  twelve (`bo m = (m / 12, m % 12)`);
* `GridStep` respects translation.
-/

namespace Work.SphereJordan

open Set Metric
open Work.Smooth.JordanSeparation

noncomputable section

/-! ## Rounding to the even lattice -/

/-- The nearest even integer to a real number. -/
def cRound (x : ℝ) : ℤ := 2 * round (x / 2)

/-- The rounding error of `cRound` is at most one. -/
theorem abs_sub_cRound (x : ℝ) : |x - (cRound x : ℝ)| ≤ 1 := by
  have h := abs_sub_round (x / 2)
  have hc : ((cRound x : ℤ) : ℝ) = 2 * ((round (x / 2) : ℤ) : ℝ) := by simp [cRound]
  rw [hc, show x - 2 * ((round (x / 2) : ℤ) : ℝ)
      = 2 * (x / 2 - ((round (x / 2) : ℤ) : ℝ)) from by ring, abs_mul]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  linarith [abs_nonneg (x / 2 - ((round (x / 2) : ℤ) : ℝ))]

/-- `cRound` produces an even integer. -/
theorem cRound_even (x : ℝ) : (cRound x).natAbs % 2 = 0 := by
  have h : (2 * round (x / 2)).natAbs = 2 * (round (x / 2)).natAbs := by
    rw [Int.natAbs_mul]; norm_num
  rw [cRound, h, mul_comm, Nat.mul_mod_left]

/-- Rounding a complex number to the nearest point of the even lattice `2ℤ²`. -/
def snap (z : ℂ) : ℤ × ℤ := (cRound z.re, cRound z.im)

theorem snap_fst_parity (z : ℂ) : (snap z).1.natAbs % 2 = 0 := cRound_even z.re

theorem snap_snd_parity (z : ℂ) : (snap z).2.natAbs % 2 = 0 := cRound_even z.im

/-- The rounding error of `snap` in the `x`-coordinate. -/
theorem snap_re (z : ℂ) : |z.re - ((snap z).1 : ℝ)| ≤ 1 := abs_sub_cRound z.re

/-- The rounding error of `snap` in the `y`-coordinate. -/
theorem snap_im (z : ℂ) : |z.im - ((snap z).2 : ℝ)| ≤ 1 := abs_sub_cRound z.im

/-! ## Moving one unit at a time towards an integer -/

/-- `mv a k` is `0` moved `k` unit steps towards `a` (clamped at `a`). -/
def mv (a : ℤ) (k : ℕ) : ℤ := if 0 ≤ a then min (k : ℤ) a else max (-(k : ℤ)) a

theorem natAbs_of_nonpos' {a : ℤ} (h : a ≤ 0) : ((a.natAbs : ℕ) : ℤ) = -a := by
  rw [show a.natAbs = (-a).natAbs from by rw [Int.natAbs_neg]]
  exact Int.natAbs_of_nonneg (by omega)

theorem mv_zero (a : ℤ) : mv a 0 = 0 := by
  unfold mv
  split_ifs with h
  · rw [Nat.cast_zero]
    exact le_antisymm (min_le_left 0 a) (le_min le_rfl h)
  · rw [Nat.cast_zero, neg_zero]
    exact le_antisymm (max_le le_rfl (by omega)) (le_max_left 0 a)

theorem mv_natAbs (a : ℤ) : mv a a.natAbs = a := by
  unfold mv
  split_ifs with h
  · exact min_eq_right Int.le_natAbs
  · rw [natAbs_of_nonpos' (by omega)]
    exact max_eq_right (by omega)

theorem mv_mem_Icc (a : ℤ) (k : ℕ) : min 0 a ≤ mv a k ∧ mv a k ≤ max 0 a := by
  unfold mv
  split_ifs with h
  · exact ⟨min_le_min (Int.natCast_nonneg k) le_rfl,
      le_trans (min_le_right _ _) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (le_max_right _ _),
      max_le (by omega) (le_max_right _ _)⟩

theorem mv_abs_le (a : ℤ) (k : ℕ) : |mv a k| ≤ |a| := by
  have h := mv_mem_Icc a k
  by_cases ha : 0 ≤ a
  · have h0 : min 0 a = 0 := le_antisymm (min_le_left 0 a) (le_min le_rfl ha)
    have h1 : max 0 a = a := max_eq_right ha
    rw [h0] at h; rw [h1] at h
    rw [abs_of_nonneg ha, abs_le]
    constructor <;> linarith [h.1, h.2]
  · have hlt : a < 0 := by omega
    have h0 : min 0 a = a := min_eq_right (le_of_lt hlt)
    have h1 : max 0 a = 0 := le_antisymm (max_le le_rfl (le_of_lt hlt)) (le_max_left 0 a)
    rw [h0] at h; rw [h1] at h
    rw [abs_of_neg hlt, abs_le]
    constructor <;> linarith [h.1, h.2]

/-- One unit step towards `a`, as long as the target has not been reached. -/
theorem mv_step (a : ℤ) {k : ℕ} (hk : k < a.natAbs) :
    mv a (k + 1) = mv a k + 1 ∨ mv a (k + 1) = mv a k - 1 := by
  have hk' : ((k : ℤ)) < |a| := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hk
  have hcast : (((k + 1 : ℕ)) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
  unfold mv
  by_cases h : 0 ≤ a
  · rw [if_pos h, if_pos h, hcast]
    have h1 : min ((k : ℤ)) a = (k : ℤ) := min_eq_left (by omega)
    have h2 : min ((k : ℤ) + 1) a = (k : ℤ) + 1 := min_eq_left (by omega)
    rw [h1, h2]
    exact Or.inl rfl
  · rw [if_neg h, if_neg h, hcast]
    have h1 : max (-((k : ℤ))) a = -((k : ℤ)) := max_eq_left (by omega)
    have h2 : max (-((k : ℤ) + 1)) a = -((k : ℤ) + 1) := max_eq_left (by omega)
    rw [h1, h2]
    exact Or.inr (by ring)

/-! ## Translation invariance of `GridStep` -/

/-- `GridStep` is invariant under left translation. -/
theorem gridStep_add (b : ℤ × ℤ) {a c : ℤ × ℤ} (h : GridStep a c) : GridStep (b + a) (b + c) := by
  simp only [GridStep, Prod.fst_add, Prod.snd_add] at h ⊢
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨by omega, Or.inl (by omega)⟩
  · exact Or.inl ⟨by omega, Or.inr (by omega)⟩
  · exact Or.inr ⟨by omega, Or.inl (by omega)⟩
  · exact Or.inr ⟨by omega, Or.inr (by omega)⟩

/-! ## The macro: twelve unit steps from `0` to `q` -/

/-- The number `12 - (|q.1| + |q.2|)`: the number of padding steps of the macro of `q`. -/
def mPad (q : ℤ × ℤ) : ℕ := 12 - (q.1.natAbs + q.2.natAbs)

/-- **The macro.**  For a displacement `q` with even coordinates and `|q.1| + |q.2| ≤ 12`, this is
the list of vertices of a sequence of exactly twelve unit lattice steps from `0` to `q`: first
`mPad q` padding steps (two-step spurs in the `x`-direction), then the monotone staircase, in which
the `x`-coordinate moves first and then the `y`-coordinate. -/
def mac (q : ℤ × ℤ) (j : ℕ) : ℤ × ℤ :=
  if j ≤ mPad q then (((j % 2 : ℕ) : ℤ), 0)
  else
    (mv q.1 (min (j - mPad q) q.1.natAbs), mv q.2 (j - mPad q - q.1.natAbs))

theorem mac_zero (q : ℤ × ℤ) : mac q 0 = 0 := by
  unfold mac
  rw [if_pos (Nat.zero_le _), Nat.zero_mod, Nat.cast_zero]
  rfl

theorem mPad_even {q : ℤ × ℤ} (h : q.1.natAbs + q.2.natAbs ≤ 12)
    (h1 : q.1.natAbs % 2 = 0) (h2 : q.2.natAbs % 2 = 0) : mPad q % 2 = 0 := by
  unfold mPad; omega

theorem mPad_compl {q : ℤ × ℤ} (h : q.1.natAbs + q.2.natAbs ≤ 12) :
    12 - mPad q = q.1.natAbs + q.2.natAbs := by
  unfold mPad; omega

theorem mac_twelve {q : ℤ × ℤ} (h : q.1.natAbs + q.2.natAbs ≤ 12) : mac q 12 = q := by
  unfold mac
  by_cases hP : 12 ≤ mPad q
  · rw [if_pos hP]
    have h0 : q.1.natAbs + q.2.natAbs = 0 := by unfold mPad at hP; omega
    have hq1 : q.1 = 0 := Int.natAbs_eq_zero.mp (by omega)
    have hq2 : q.2 = 0 := Int.natAbs_eq_zero.mp (by omega)
    rw [show q = ((0 : ℤ), (0 : ℤ)) from Prod.ext hq1 hq2]
    norm_num
  · rw [if_neg hP]
    have hs : 12 - mPad q = q.1.natAbs + q.2.natAbs := mPad_compl h
    have hs1 : min (12 - mPad q) q.1.natAbs = q.1.natAbs := min_eq_right (by omega)
    have hs2 : 12 - mPad q - q.1.natAbs = q.2.natAbs := by omega
    rw [hs1, hs2, mv_natAbs q.1, mv_natAbs q.2]

/-- **The macro consists of unit steps.** -/
theorem mac_step {q : ℤ × ℤ} (h : q.1.natAbs + q.2.natAbs ≤ 12)
    (h1 : q.1.natAbs % 2 = 0) (h2 : q.2.natAbs % 2 = 0) {j : ℕ} (hj : j < 12) :
    GridStep (mac q j) (mac q (j + 1)) := by
  have hPe : mPad q % 2 = 0 := mPad_even h h1 h2
  have hPc : 12 - mPad q = q.1.natAbs + q.2.natAbs := mPad_compl h
  unfold mac
  by_cases hj1 : j + 1 ≤ mPad q
  · -- both indices are padding steps
    rw [if_pos (by omega : j ≤ mPad q), if_pos hj1]
    rcases Nat.mod_two_eq_zero_or_one j with h' | h'
    · rw [h', show (j + 1) % 2 = 1 from by omega]
      exact Or.inr ⟨rfl, Or.inl (by norm_num)⟩
    · rw [h', show (j + 1) % 2 = 0 from by omega]
      exact Or.inr ⟨rfl, Or.inr (by norm_num)⟩
  · by_cases hjP : j ≤ mPad q
    · -- the junction `j = mPad q`
      have hjP' : j = mPad q := by omega
      rw [if_pos hjP, if_neg hj1]
      have hjpar : j % 2 = 0 := by rw [hjP', hPe]
      rw [hjpar, show j + 1 - mPad q = 1 from by omega]
      rcases Nat.eq_zero_or_pos q.1.natAbs with h0 | hpos
      · -- `q.1 = 0`: the `y`-coordinate moves
        have hmin : min 1 q.1.natAbs = 0 := by rw [h0]; rfl
        have hsub : 1 - q.1.natAbs = 1 := by omega
        rw [hmin, mv_zero, hsub]
        have hmb : 0 < q.2.natAbs := by omega
        rcases mv_step q.2 hmb with hs2 | hs2
        · rw [hs2, mv_zero]; exact Or.inl ⟨rfl, Or.inl rfl⟩
        · rw [hs2, mv_zero]; exact Or.inl ⟨rfl, Or.inr (by omega)⟩
      · -- `q.1 ≠ 0`: the `x`-coordinate moves
        have hmin : min 1 q.1.natAbs = 1 := by omega
        have hsub : 1 - q.1.natAbs = 0 := by omega
        rw [hmin, hsub, mv_zero]
        rcases mv_step q.1 hpos with hs1 | hs1
        · rw [hs1, mv_zero]; exact Or.inr ⟨rfl, Or.inl rfl⟩
        · rw [hs1, mv_zero]; exact Or.inr ⟨rfl, Or.inr (by omega)⟩
    · -- both indices are in the staircase part
      rw [if_neg hjP, if_neg hj1]
      rw [show j + 1 - mPad q = (j - mPad q) + 1 from by omega]
      by_cases hlt : j - mPad q < q.1.natAbs
      · -- the `x`-coordinate moves
        have h1' : min (j - mPad q) q.1.natAbs = j - mPad q := min_eq_left (le_of_lt hlt)
        have h2' : min ((j - mPad q) + 1) q.1.natAbs = (j - mPad q) + 1 :=
          min_eq_left (by omega)
        have h3' : j - mPad q - q.1.natAbs = 0 := by omega
        have h4' : (j - mPad q) + 1 - q.1.natAbs = 0 := by omega
        rw [h1', h2', h3', h4', mv_zero]
        rcases mv_step q.1 hlt with hs1 | hs1
        · rw [hs1]; exact Or.inr ⟨rfl, Or.inl rfl⟩
        · rw [hs1]; exact Or.inr ⟨rfl, Or.inr (by omega)⟩
      · -- the `y`-coordinate moves
        have h1' : min (j - mPad q) q.1.natAbs = q.1.natAbs := min_eq_right (by omega)
        have h2' : min ((j - mPad q) + 1) q.1.natAbs = q.1.natAbs := min_eq_right (by omega)
        have h3' : (j - mPad q) + 1 - q.1.natAbs = (j - mPad q - q.1.natAbs) + 1 := by omega
        rw [h1', h2', h3']
        have hlt2 : j - mPad q - q.1.natAbs < q.2.natAbs := by omega
        rcases mv_step q.2 hlt2 with hs2 | hs2
        · rw [hs2]; exact Or.inl ⟨rfl, Or.inl rfl⟩
        · rw [hs2]; exact Or.inl ⟨rfl, Or.inr (by omega)⟩

theorem mac_bound {q : ℤ × ℤ} (h1 : |q.1| ≤ 6) (h2 : |q.2| ≤ 6) (j : ℕ) :
    |(mac q j).1| ≤ 7 ∧ |(mac q j).2| ≤ 6 := by
  unfold mac
  split_ifs with h
  · constructor
    · have h' : (((j % 2 : ℕ) : ℤ)) = 0 ∨ (((j % 2 : ℕ) : ℤ)) = 1 := by
        rcases Nat.mod_two_eq_zero_or_one j with h'' | h''
        · exact Or.inl (by simp [h''])
        · exact Or.inr (by simp [h''])
      rcases h' with h' | h' <;> rw [h'] <;> norm_num
    · norm_num
  · exact ⟨le_trans (mv_abs_le _ _) (by linarith [abs_nonneg q.1]),
      le_trans (mv_abs_le _ _) h2⟩

/-! ## The index schedule of the concatenation of the blocks -/

/-- The block index and the offset of the `m`-th index of the concatenation of blocks of length
twelve.  Defined by recursion so that the defining equations are definitional. -/
def bo : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | m + 1 => if (bo m).2 + 1 = 12 then ((bo m).1 + 1, 0) else ((bo m).1, (bo m).2 + 1)

theorem bo_eq_div (m : ℕ) : bo m = (m / 12, m % 12) := by
  induction m with
  | zero => simp [bo]
  | succ m ih =>
    rw [bo, ih]
    have hm : m = 12 * (m / 12) + m % 12 := (Nat.div_add_mod m 12).symm
    have h2 : m % 12 ≤ 11 := by omega
    by_cases h : m % 12 + 1 = 12
    · have hdiv : (m + 1) / 12 = m / 12 + 1 := by
        conv_lhs => rw [hm]
        rw [show 12 * (m / 12) + m % 12 + 1 = (m / 12 + 1) * 12 from by omega]
        rw [Nat.mul_div_left _ (by norm_num : 0 < 12)]
      have hmod : (m + 1) % 12 = 0 := by
        conv_lhs => rw [hm]
        rw [show 12 * (m / 12) + m % 12 + 1 = (m / 12 + 1) * 12 from by omega]
        rw [Nat.mul_mod_left]
      rw [if_pos h, Prod.ext_iff]
      exact ⟨by rw [hdiv], by rw [hmod]⟩
    · have hlt : m % 12 + 1 < 12 := by omega
      have hdiv : (m + 1) / 12 = m / 12 := by
        conv_lhs => rw [hm]
        rw [show 12 * (m / 12) + m % 12 + 1 = (m % 12 + 1) + 12 * (m / 12) from by omega]
        rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 12), Nat.div_eq_of_lt hlt,
          Nat.zero_add]
      have hmod : (m + 1) % 12 = m % 12 + 1 := by
        conv_lhs => rw [hm]
        rw [show 12 * (m / 12) + m % 12 + 1 = (m % 12 + 1) + 12 * (m / 12) from by omega]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      rw [if_neg h, Prod.ext_iff]
      exact ⟨by rw [hdiv], by rw [hmod]⟩

theorem bo_fst_le (m : ℕ) : (bo m).1 ≤ m := by
  rw [bo_eq_div]; exact Nat.div_le_self m 12

theorem bo_snd_le (m : ℕ) : (bo m).2 ≤ 11 := by
  rw [bo_eq_div]; have := Nat.mod_lt m (by norm_num : 0 < 12); omega

theorem bo_zero : bo 0 = (0, 0) := rfl

theorem bo_mul_twelve (k : ℕ) : bo (k * 12) = (k, 0) := by
  rw [bo_eq_div, Nat.mul_div_left k (by norm_num : 0 < 12), Nat.mul_mod_left]

theorem bo_twelve_mul (k : ℕ) : bo (12 * k) = (k, 0) := by
  rw [bo_eq_div, Nat.mul_div_right k (by norm_num : 0 < 12), Nat.mul_mod_right]

end

end Work.SphereJordan
