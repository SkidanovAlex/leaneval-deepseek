import Mathlib
import Submission.Work.Drive.squareDisk

/-!
# Surjectivity of the square-to-disk map `sqDisk` onto the closed unit disk

`Work.Drive.sqDisk` (in `Submission/Work/Drive/squareDisk.lean`) is the classical square-to-disk map
`(a, b) ↦ (a √(1 - b²/2), b √(1 - a²/2))` written in the square coordinates `a = 2 y 0 - 1`,
`b = 2 y 1 - 1`, cut off by a bump so as to be globally smooth.  On the unit square it coincides with
the honest formula, and here we show that it is **surjective onto the closed unit disk**.

The inverse is explicit.  Given `(p, q)` with `p² + q² ≤ 1`, put

* `s = p² + q²`, `d = p² - q²`, `R = 4 - 4 s + d²`, `w = √R`, `u = (2 - w + d)/2`, `v = (2 - w - d)/2`.

Then `|d| ≤ s ≤ 1` gives `|d| ≤ w ≤ 2 - |d|`, so `0 ≤ u, v ≤ 1`; and expanding
`u (1 - v/2) = ((2+d)² - w²)/8 = (4 + 4d + d² - R)/8 = (s + d)/2 = p²` (and symmetrically for `q²`)
shows that `A = p/√(1 - v/2)`, `B = q/√(1 - u/2)` satisfy `A² = u`, `B² = v` and
`A √(1 - B²/2) = p`, `B √(1 - A²/2) = q`.
-/


namespace Work.Drive

/-- On the square, the smooth cut-off weight `sqWeight` is exactly the square root `√(1 - b²/2)`. -/
lemma sqWeight_eq_sqrt {b : ℝ} (hb : |b| ≤ 1) : sqWeight b = Real.sqrt (1 - b ^ 2 / 2) := by
  have h2 : sqWeight b ^ 2 = 1 - b ^ 2 / 2 := sqWeight_sq hb
  have hnn : 0 ≤ sqWeight b := sqWeight_nonneg b
  rw [eq_comm, Real.sqrt_eq_cases]
  exact Or.inl ⟨by rw [← pow_two]; exact h2, hnn⟩

/-- **Inverse coordinates of the square-to-disk map.**  For `(p, q)` in the closed unit disk there
are `A, B ∈ [-1, 1]` with `A √(1 - B²/2) = p` and `B √(1 - A²/2) = q`. -/
lemma exists_coords (p q : ℝ) (hpq : p ^ 2 + q ^ 2 ≤ 1) :
    ∃ A B : ℝ, |A| ≤ 1 ∧ |B| ≤ 1 ∧
      A * Real.sqrt (1 - B ^ 2 / 2) = p ∧ B * Real.sqrt (1 - A ^ 2 / 2) = q := by
  set s : ℝ := p ^ 2 + q ^ 2 with hs
  set d : ℝ := p ^ 2 - q ^ 2 with hd
  have hs_le : s ≤ 1 := by rw [hs]; exact hpq
  have hd_le : |d| ≤ s := by
    rw [hd, hs, abs_le]; constructor <;> nlinarith [sq_nonneg p, sq_nonneg q]
  set R : ℝ := 4 - 4 * s + d ^ 2 with hR
  have hR_nonneg : 0 ≤ R := by rw [hR]; nlinarith [hs_le, sq_nonneg d]
  set w : ℝ := Real.sqrt R with hw
  have hw_sq : w ^ 2 = R := by rw [hw]; exact Real.sq_sqrt hR_nonneg
  have hd_le_w : |d| ≤ w := by
    have h : |d| ≤ Real.sqrt R := by
      rw [(Real.le_sqrt (x := |d|) (y := R) (abs_nonneg d) hR_nonneg)]
      rw [sq_abs, hR]; nlinarith [hs_le]
    rw [hw]; exact h
  have hw_le : w ≤ 2 - |d| := by
    have h : Real.sqrt R ≤ 2 - |d| := by
      rw [(Real.sqrt_le_left (x := R) (y := 2 - |d|) (by linarith [hd_le, hs_le]))]
      rw [hR]
      have : (2 - |d|) ^ 2 = 4 - 4 * |d| + d ^ 2 := by rw [sub_sq]; rw [sq_abs]; ring
      rw [this]; nlinarith [hd_le]
    rw [hw]; exact h
  set u : ℝ := (2 - w + d) / 2 with hu
  set v : ℝ := (2 - w - d) / 2 with hv
  have hu_nonneg : 0 ≤ u := by
    rw [hu]; have := neg_abs_le d; linarith
  have hu_le1 : u ≤ 1 := by
    rw [hu]; have := le_abs_self d; linarith
  have hv_nonneg : 0 ≤ v := by
    rw [hv]; have := le_abs_self d; linarith
  have hv_le1 : v ≤ 1 := by
    rw [hv]; have := neg_le_abs d; linarith
  have hp2 : p ^ 2 = u * (1 - v / 2) := by
    have key : u * (1 - v / 2) = ((2 + d) ^ 2 - R) / 8 := by
      rw [hu, hv]; ring_nf; rw [hw_sq]; ring
    rw [key, hR, hs, hd]; ring
  have hq2 : q ^ 2 = v * (1 - u / 2) := by
    have key : v * (1 - u / 2) = ((2 - d) ^ 2 - R) / 8 := by
      rw [hu, hv]; ring_nf; rw [hw_sq]; ring
    rw [key, hR, hs, hd]; ring
  have hdenv : 0 < 1 - v / 2 := by linarith
  have hdenu : 0 < 1 - u / 2 := by linarith
  refine ⟨p / Real.sqrt (1 - v / 2), q / Real.sqrt (1 - u / 2), ?_, ?_, ?_, ?_⟩
  · rw [← sq_le_one_iff_abs_le_one, div_pow, Real.sq_sqrt (le_of_lt hdenv), hp2,
      mul_div_cancel_right₀ u (ne_of_gt hdenv)]
    exact hu_le1
  · rw [← sq_le_one_iff_abs_le_one, div_pow, Real.sq_sqrt (le_of_lt hdenu), hq2,
      mul_div_cancel_right₀ v (ne_of_gt hdenu)]
    exact hv_le1
  · have hB_sq : (q / Real.sqrt (1 - u / 2)) ^ 2 = v := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hdenu), hq2]
      exact mul_div_cancel_right₀ v (ne_of_gt hdenu)
    rw [hB_sq]
    exact div_mul_cancel₀ p (ne_of_gt (Real.sqrt_pos.mpr hdenv))
  · have hA_sq : (p / Real.sqrt (1 - v / 2)) ^ 2 = u := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hdenv), hp2]
      exact mul_div_cancel_right₀ u (ne_of_gt hdenv)
    rw [hA_sq]
    exact div_mul_cancel₀ q (ne_of_gt (Real.sqrt_pos.mpr hdenu))

/-- **The square-to-disk map hits every point of the closed unit disk.** -/
theorem sqDisk_surjective (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∃ y ∈ Submission.Drive.unitBox 1, Work.Drive.sqDisk y = z := by
  have hnorm2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hns : Complex.normSq z ≤ 1 := by rw [← Complex.sq_norm]; exact hnorm2
  rw [Complex.normSq_apply] at hns
  have hpq : z.re ^ 2 + z.im ^ 2 ≤ 1 := by nlinarith [hns]
  obtain ⟨A, B, hA1, hB1, hAre, hBim⟩ := exists_coords z.re z.im hpq
  have hA := abs_le.mp hA1
  have hB := abs_le.mp hB1
  refine ⟨mk2 ((1 + A) / 2) ((1 + B) / 2), ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [mk2] <;> constructor <;> linarith
  · apply Complex.ext
    · rw [sqDisk_apply_re]
      simp only [mk2, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [show 2 * ((1 + A) / 2) - 1 = A by ring,
          show 2 * ((1 + B) / 2) - 1 = B by ring,
          sqWeight_eq_sqrt hB1, hAre]
    · rw [sqDisk_apply_im]
      simp only [mk2, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [show 2 * ((1 + A) / 2) - 1 = A by ring,
          show 2 * ((1 + B) / 2) - 1 = B by ring,
          sqWeight_eq_sqrt hA1, hBim]

end Work.Drive
