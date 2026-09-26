import Mathlib

namespace Work.Smooth.Morse.Flow

/-- One coordinate of the map `v ↦ -(1 + |v|²)⁻¹ • v` is `3`-Lipschitz with respect to the
max-metric on `ℝ × ℝ`.  This is the analytic heart of `lipschitzWith_scaled_smul`; it is proved
by an explicit algebraic estimate on the difference quotient. -/
private lemma coord_bound (x x' y y' : ℝ) :
    |-(x / (1 + (x ^ 2 + y ^ 2))) + x' / (1 + (x' ^ 2 + y' ^ 2))| ≤
      3 * max |x - x'| |y - y'| := by
  set A : ℝ := x ^ 2 + y ^ 2 with hAdef
  set B : ℝ := x' ^ 2 + y' ^ 2 with hBdef
  set d : ℝ := max |x - x'| |y - y'| with hddef
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  have hB : 0 ≤ B := by rw [hBdef]; positivity
  have hd : 0 ≤ d := by rw [hddef]; positivity
  have h1A : (0 : ℝ) < 1 + A := by linarith
  have h1B : (0 : ℝ) < 1 + B := by linarith
  have hpos : (0 : ℝ) < (1 + A) * (1 + B) := mul_pos h1A h1B
  have hx : |x - x'| ≤ d := by rw [hddef]; exact le_max_left _ _
  have hy : |y - y'| ≤ d := by rw [hddef]; exact le_max_right _ _
  have hident : -(x / (1 + A)) + x' / (1 + B)
      = (x' * (1 + A) - x * (1 + B)) / ((1 + A) * (1 + B)) := by
    field_simp
    ring
  rw [hident, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hAB : |A - B| ≤ d * (|x + x'| + |y + y'|) := by
    have hid : A - B = (x - x') * (x + x') + (y - y') * (y + y') := by
      rw [hAdef, hBdef]; ring
    rw [hid]
    calc |(x - x') * (x + x') + (y - y') * (y + y')|
        ≤ |(x - x') * (x + x')| + |(y - y') * (y + y')| := abs_add_le _ _
      _ = |x - x'| * |x + x'| + |y - y'| * |y + y'| := by rw [abs_mul, abs_mul]
      _ ≤ d * |x + x'| + d * |y + y'| := by gcongr
      _ = d * (|x + x'| + |y + y'|) := by ring
  have hS2 : (|x + x'| + |y + y'|) ^ 2 ≤ 4 * (A + B) := by
    have h1 : (x + x') ^ 2 + (y + y') ^ 2 ≤ 2 * (A + B) := by
      rw [hAdef, hBdef]; nlinarith [sq_nonneg (x - x'), sq_nonneg (y - y')]
    nlinarith [h1, sq_nonneg (|x + x'| - |y + y'|), sq_abs (x + x'), sq_abs (y + y')]
  have hterm1 : |(x' - x) * (1 + (A + B) / 2)| ≤ d * (1 + (A + B) / 2) := by
    rw [abs_mul]
    have hfac : 0 ≤ 1 + (A + B) / 2 := by linarith
    rw [abs_of_nonneg hfac]
    have : |x' - x| ≤ d := by rw [abs_sub_comm]; exact hx
    exact mul_le_mul_of_nonneg_right this hfac
  have hterm2 : |((A - B) / 2) * (x + x')| ≤ 2 * d * (A + B) := by
    have hxle : |x + x'| ≤ |x + x'| + |y + y'| := le_add_of_nonneg_right (abs_nonneg _)
    calc |((A - B) / 2) * (x + x')| = (|A - B| / 2) * |x + x'| := by
          rw [abs_mul, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (d * (|x + x'| + |y + y'|) / 2) * (|x + x'| + |y + y'|) := by gcongr
      _ = d * (|x + x'| + |y + y'|) ^ 2 / 2 := by ring
      _ ≤ d * (4 * (A + B)) / 2 := by gcongr
      _ = 2 * d * (A + B) := by ring
  have hNbound : |x' * (1 + A) - x * (1 + B)| ≤ d * (1 + (A + B) / 2) + 2 * d * (A + B) := by
    have hid : x' * (1 + A) - x * (1 + B)
        = (x' - x) * (1 + (A + B) / 2) + ((A - B) / 2) * (x + x') := by ring
    rw [hid]
    calc |(x' - x) * (1 + (A + B) / 2) + ((A - B) / 2) * (x + x')|
        ≤ |(x' - x) * (1 + (A + B) / 2)| + |((A - B) / 2) * (x + x')| := abs_add_le _ _
      _ ≤ d * (1 + (A + B) / 2) + 2 * d * (A + B) := add_le_add hterm1 hterm2
  have hsub : 1 + (A + B) / 2 + 2 * (A + B) ≤ 3 * ((1 + A) * (1 + B)) := by
    nlinarith [hA, hB]
  calc |x' * (1 + A) - x * (1 + B)|
      ≤ d * (1 + (A + B) / 2) + 2 * d * (A + B) := hNbound
    _ = d * (1 + (A + B) / 2 + 2 * (A + B)) := by ring
    _ ≤ d * (3 * ((1 + A) * (1 + B))) := mul_le_mul_of_nonneg_left hsub hd
    _ = 3 * d * ((1 + A) * (1 + B)) := by ring

/-- The map `v ↦ -(1 + |v|²)⁻¹ • v` on `ℝ × ℝ` is `3`-Lipschitz for the max-metric.

This is the elementary estimate used when normalising the gradient field along a flow. -/
theorem lipschitzWith_scaled_smul :
    LipschitzWith 3 (fun v : ℝ × ℝ => -((1 + v.1 ^ 2 + v.2 ^ 2 : ℝ)⁻¹) • v) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  rw [max_le_iff]
  constructor
  · have hL : (-((1 + v.1 ^ 2 + v.2 ^ 2 : ℝ)⁻¹) • v).1
          - (-((1 + w.1 ^ 2 + w.2 ^ 2 : ℝ)⁻¹) • w).1
        = -(v.1 / (1 + (v.1 ^ 2 + v.2 ^ 2))) + w.1 / (1 + (w.1 ^ 2 + w.2 ^ 2)) := by
      simp only [Prod.smul_fst, smul_eq_mul, neg_mul, inv_mul_eq_div]
      ring
    rw [hL]
    calc |-(v.1 / (1 + (v.1 ^ 2 + v.2 ^ 2))) + w.1 / (1 + (w.1 ^ 2 + w.2 ^ 2))|
        ≤ 3 * max |v.1 - w.1| |v.2 - w.2| := coord_bound v.1 w.1 v.2 w.2
      _ = (↑(3 : NNReal) : ℝ) * max |v.1 - w.1| |v.2 - w.2| := by norm_num
  · have hL : (-((1 + v.1 ^ 2 + v.2 ^ 2 : ℝ)⁻¹) • v).2
          - (-((1 + w.1 ^ 2 + w.2 ^ 2 : ℝ)⁻¹) • w).2
        = -(v.2 / (1 + (v.2 ^ 2 + v.1 ^ 2))) + w.2 / (1 + (w.2 ^ 2 + w.1 ^ 2)) := by
      simp only [Prod.smul_snd, smul_eq_mul, neg_mul, inv_mul_eq_div]
      ring
    rw [hL]
    rw [max_comm]
    calc |-(v.2 / (1 + (v.2 ^ 2 + v.1 ^ 2))) + w.2 / (1 + (w.2 ^ 2 + w.1 ^ 2))|
        ≤ 3 * max |v.2 - w.2| |v.1 - w.1| := coord_bound v.2 w.2 v.1 w.1
      _ = (↑(3 : NNReal) : ℝ) * max |v.2 - w.2| |v.1 - w.1| := by norm_num

end Work.Smooth.Morse.Flow
