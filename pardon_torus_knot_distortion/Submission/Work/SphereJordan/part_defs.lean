import Mathlib
import Submission.Work.SphereJordan.ladder_walk
import Submission.Work.Smooth.JordanSeparation.gridWalk_approx

/-!
# The partition of the unit interval, and the displacement bounds of the ladder

The partition `part N k` of `[0,1]` into `N` equal pieces, and the elementary bounds on the
displacements `dl lad k` of the even-lattice ladder of `ladder_walk.lean` (used by
`ladder_approx.lean`).
-/

namespace Work.SphereJordan

open Set Metric
open Work.Smooth.JordanSeparation

noncomputable section

/-! ## The partition of the unit interval -/

/-- The `k`-th point of the partition of the unit interval into `N` equal pieces. -/
def part (N k : ℕ) : unitInterval :=
  ⟨min ((k : ℝ) / (N : ℝ)) (1 : ℝ),
    ⟨le_min (by positivity : (0 : ℝ) ≤ (k : ℝ) / (N : ℝ)) (by norm_num : (0 : ℝ) ≤ 1),
      min_le_right _ _⟩⟩

theorem part_val {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k ≤ N) :
    ((part N k : unitInterval) : ℝ) = (k : ℝ) / (N : ℝ) := by
  have h1 : (k : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hN)]
    exact_mod_cast hk
  simp only [part]
  exact min_eq_left h1

theorem part_zero (N : ℕ) : part N 0 = 0 := by
  ext
  simp [part]

theorem part_one {N : ℕ} (hN : 0 < N) : part N N = 1 := by
  ext
  simp only [part]
  have h : ((N : ℝ) / (N : ℝ)) = 1 :=
    div_self (show ((N : ℝ)) ≠ 0 by positivity)
  rw [h, min_self]
  rfl

theorem part_of_le {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : N ≤ k) : part N k = 1 := by
  ext
  simp only [part]
  have h1 : 1 ≤ (k : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hN)]
    simpa using hk
  rw [min_eq_right h1]
  rfl

theorem part_succ_one {N : ℕ} (hN : 0 < N) : part N (N + 1) = 1 := by
  ext
  simp only [part]
  have h1 : 1 ≤ ((N + 1 : ℕ) : ℝ) / (N : ℝ) := by
    rw [le_div_iff₀ (show (0 : ℝ) < (N : ℝ) by exact_mod_cast hN)]
    push_cast
    linarith [show (0 : ℝ) < N by exact_mod_cast hN]
  rw [min_eq_right h1]
  rfl

theorem part_dist {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k < N) :
    dist (part N k) (part N (k + 1)) = 1 / (N : ℝ) := by
  rw [Subtype.dist_eq, Real.dist_eq, part_val hN (le_of_lt hk),
    part_val hN (Nat.succ_le_of_lt hk)]
  have hNne : ((N : ℝ)) ≠ 0 := by positivity
  have h : (k : ℝ) / (N : ℝ) - ((k + 1 : ℕ) : ℝ) / (N : ℝ) = -(1 / (N : ℝ)) := by
    field_simp
    push_cast
    ring
  rw [h, abs_neg, abs_of_nonneg (by positivity)]

theorem part_dist_le {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k ≤ N) :
    dist (part N k) (part N (k + 1)) ≤ 1 / (N : ℝ) := by
  rcases lt_or_eq_of_le hk with h | h
  · exact le_of_eq (part_dist hN h)
  · subst h
    rw [part_one hN, part_succ_one hN, dist_self]
    exact le_of_lt (by positivity)

/-! ## Bounds on the ladder -/

theorem two_dvd_sub_natAbs {a b : ℤ} (ha : (2 : ℤ) ∣ a) (hb : (2 : ℤ) ∣ b) :
    (a - b).natAbs % 2 = 0 := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have h : (2 * a' - 2 * b').natAbs = 2 * (a' - b').natAbs := by
    rw [show 2 * a' - 2 * b' = 2 * (a' - b') from by ring, Int.natAbs_mul]
    norm_num
  rw [h, mul_comm, Nat.mul_mod_left]

theorem snap_two_dvd (z : ℂ) : (2 : ℤ) ∣ (snap z).1 :=
  ⟨round (z.re / 2), by simp [snap, cRound]⟩

theorem snap_two_dvd' (z : ℂ) : (2 : ℤ) ∣ (snap z).2 :=
  ⟨round (z.im / 2), by simp [snap, cRound]⟩

/-- The coordinates of the displacements of the ladder are bounded by three. -/
theorem snap_diff_le {z : ℕ → ℂ} {lad : ℕ → ℤ × ℤ} (hlad : ∀ k, lad k = snap (z k))
    {k : ℕ} (hz : ‖z (k + 1) - z k‖ ≤ 1) :
    |(dl lad k).1| ≤ 3 ∧ |(dl lad k).2| ≤ 3 := by
  have hre : |(z (k + 1)).re - (z k).re| ≤ 1 := by
    have h := Complex.abs_re_le_norm (z (k + 1) - z k)
    rw [show (z (k + 1) - z k).re = (z (k + 1)).re - (z k).re from by simp] at h
    linarith
  have him : |(z (k + 1)).im - (z k).im| ≤ 1 := by
    have h := Complex.abs_im_le_norm (z (k + 1) - z k)
    rw [show (z (k + 1) - z k).im = (z (k + 1)).im - (z k).im from by simp] at h
    linarith
  have h1 : |((lad (k + 1)).1 : ℝ) - (z (k + 1)).re| ≤ 1 := by
    rw [hlad (k + 1), abs_sub_comm]; exact snap_re _
  have h2 : |((lad k).1 : ℝ) - (z k).re| ≤ 1 := by
    rw [hlad k, abs_sub_comm]; exact snap_re _
  have h3 : |((lad (k + 1)).2 : ℝ) - (z (k + 1)).im| ≤ 1 := by
    rw [hlad (k + 1), abs_sub_comm]; exact snap_im _
  have h4 : |((lad k).2 : ℝ) - (z k).im| ≤ 1 := by
    rw [hlad k, abs_sub_comm]; exact snap_im _
  have e1 : (dl lad k).1 = (lad (k + 1)).1 - (lad k).1 := rfl
  have e2 : (dl lad k).2 = (lad (k + 1)).2 - (lad k).2 := rfl
  constructor
  · rw [e1]
    have : |((lad (k + 1)).1 : ℝ) - (lad k).1|
        ≤ |((lad (k + 1)).1 : ℝ) - (z (k + 1)).re| + |(z (k + 1)).re - (z k).re|
          + |(z k).re - ((lad k).1 : ℝ)| := by
      have h := abs_sub_le (((lad (k + 1)).1 : ℝ)) ((z (k + 1)).re) ((lad k).1 : ℝ)
      have h' := abs_sub_le ((z (k + 1)).re) ((z k).re) ((lad k).1 : ℝ)
      linarith [abs_nonneg (((lad (k + 1)).1 : ℝ) - (z (k + 1)).re),
        abs_nonneg ((z (k + 1)).re - (z k).re), abs_nonneg ((z k).re - ((lad k).1 : ℝ))]
    have h2' : |(z k).re - ((lad k).1 : ℝ)| ≤ 1 := by rw [abs_sub_comm]; exact h2
    have h1' : |((lad (k + 1)).1 : ℝ) - (z (k + 1)).re| ≤ 1 := h1
    have : |((lad (k + 1)).1 - (lad k).1 : ℤ)| ≤ 3 := by
      have : |(((lad (k + 1)).1 - (lad k).1 : ℤ) : ℝ)| ≤ 3 := by
        push_cast
        linarith
      exact_mod_cast this
    exact this
  · rw [e2]
    have h3' : |(z k).im - ((lad k).2 : ℝ)| ≤ 1 := by rw [abs_sub_comm]; exact h4
    have : |(((lad (k + 1)).2 - (lad k).2 : ℤ) : ℝ)| ≤ 3 := by
      push_cast
      have h := abs_sub_le (((lad (k + 1)).2 : ℝ)) ((z (k + 1)).im) ((lad k).2 : ℝ)
      have h' := abs_sub_le ((z (k + 1)).im) ((z k).im) ((lad k).2 : ℝ)
      linarith [abs_nonneg (((lad (k + 1)).2 : ℝ) - (z (k + 1)).im),
        abs_nonneg ((z (k + 1)).im - (z k).im), abs_nonneg ((z k).im - ((lad k).2 : ℝ))]
    exact_mod_cast this

/-- The displacements of the ladder are even. -/
theorem snap_diff_parity {z : ℕ → ℂ} {lad : ℕ → ℤ × ℤ} (hlad : ∀ k, lad k = snap (z k)) (k : ℕ) :
    (dl lad k).1.natAbs % 2 = 0 ∧ (dl lad k).2.natAbs % 2 = 0 := by
  have h1 : (dl lad k).1 = (lad (k + 1)).1 - (lad k).1 := rfl
  have h2 : (dl lad k).2 = (lad (k + 1)).2 - (lad k).2 := rfl
  constructor
  · rw [h1]
    refine two_dvd_sub_natAbs ?_ ?_
    · rw [hlad (k + 1)]; exact snap_two_dvd _
    · rw [hlad k]; exact snap_two_dvd _
  · rw [h2]
    refine two_dvd_sub_natAbs ?_ ?_
    · rw [hlad (k + 1)]; exact snap_two_dvd' _
    · rw [hlad k]; exact snap_two_dvd' _


/-- **The affine parametrisation of an interval of the partition stays close to its start.** -/
theorem part_affine_dist {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : k < N) (s : unitInterval) :
    dist (part N k) (Path.affine (part N k) (part N (k + 1)) s) ≤ 1 / (N : ℝ) := by
  have hb : |((part N (k + 1) : unitInterval) : ℝ) - ((part N k : unitInterval) : ℝ)| ≤ 1 / (N : ℝ) := by
    rw [← Real.dist_eq, ← Subtype.dist_eq]
    rw [dist_comm]
    exact part_dist_le hN (le_of_lt hk)
  have ht0 : (0 : ℝ) ≤ (s : ℝ) := (s : unitInterval).2.1
  rw [Subtype.dist_eq, Real.dist_eq, Path.affine_val]
  have : ((part N k : unitInterval) : ℝ)
      - ((1 - (s : ℝ)) * ((part N k : unitInterval) : ℝ)
        + (s : ℝ) * ((part N (k + 1) : unitInterval) : ℝ))
      = (s : ℝ) * (((part N k : unitInterval) : ℝ) - ((part N (k + 1) : unitInterval) : ℝ)) := by
    ring
  rw [this, abs_mul, abs_of_nonneg ht0]
  have ht1 : (s : ℝ) ≤ 1 := (s : unitInterval).2.2
  have hab : |((part N k : unitInterval) : ℝ) - ((part N (k + 1) : unitInterval) : ℝ)| ≤ 1 / (N : ℝ) := by
    rw [abs_sub_comm]; exact hb
  calc (s : ℝ) * |((part N k : unitInterval) : ℝ) - ((part N (k + 1) : unitInterval) : ℝ)|
      ≤ 1 * |((part N k : unitInterval) : ℝ) - ((part N (k + 1) : unitInterval) : ℝ)| :=
        mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
    _ = |((part N k : unitInterval) : ℝ) - ((part N (k + 1) : unitInterval) : ℝ)| := one_mul _
    _ ≤ 1 / (N : ℝ) := hab

end

end Work.SphereJordan
