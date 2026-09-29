import Mathlib
import Submission.Work.C17I.defs

/-!
# The lens `{z | ‖z/(z-1)‖ < r}` is a disc

`lens r = {z : ℂ | ‖z/(z-1)‖ < r}` is the region on which `Pfun ∘ φ` is given by the
convergent unlikely series (`φ z = z/(z-1)`). Here we record its elementary description:
for `0 < r < 1` it is the open disc with centre `-r²/(1-r²)` and radius `r/(1-r²)`, except
that the point `z = 1` (where `φ` is undefined and `‖z/(z-1)‖` degenerates to `0`) has to be
removed.

The characterisation follows from `|z| < r|z-1|` by squaring:
`(1-r²)(x²+y²) + 2r²x - r² < 0`, which after completing the square is
`(x + r²/(1-r²))² + y² < r²/(1-r²)²`.
-/

namespace Work.C17I

private lemma normSq_sub_one (z : ℂ) :
    Complex.normSq (z - 1) = Complex.normSq z + 1 - 2 * z.re := by
  rw [Complex.normSq_sub]; simp [Complex.normSq_one]

private lemma normSq_sub_ofReal (z : ℂ) (x : ℝ) :
    Complex.normSq (z - (x : ℂ)) = Complex.normSq z + x ^ 2 - 2 * x * z.re := by
  rw [Complex.normSq_sub]; simp [Complex.normSq_ofReal, Complex.mul_re]; ring

/-- `‖w‖ < R ↔ normSq w < R²` for `0 ≤ R`. -/
private lemma lt_iff_normSq (w : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    ‖w‖ < R ↔ Complex.normSq w < R ^ 2 := by
  rw [← Complex.sq_norm w, sq_lt_sq, abs_of_nonneg (norm_nonneg w), abs_of_nonneg hR]

/-- Squaring the inequality `‖z‖ < r‖z-1‖` (both sides nonnegative). -/
private lemma sq_norm_lt (z : ℂ) (r : ℝ) (hr0 : 0 < r) :
    ‖z‖ < r * ‖z - 1‖ ↔ Complex.normSq z < r ^ 2 * Complex.normSq (z - 1) := by
  have h1 : (0 : ℝ) ≤ r * ‖z - 1‖ := mul_nonneg (le_of_lt hr0) (norm_nonneg _)
  rw [← Complex.sq_norm z, ← Complex.sq_norm (z - 1), ← mul_pow, sq_lt_sq]
  rw [abs_of_nonneg (norm_nonneg z), abs_of_nonneg h1]

/-- The elementary real-algebra core: with `d = 1 - r²`,
`d·s + 2r²·a - r² < 0` is the completed-square form of `(a + r²/d)² + … < (r/d)²`. -/
private lemma alg_core (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (s a : ℝ) :
    (1 - r ^ 2) * s + 2 * r ^ 2 * a - r ^ 2 < 0 ↔
      s + (-(r ^ 2) / (1 - r ^ 2)) ^ 2 - 2 * (-(r ^ 2) / (1 - r ^ 2)) * a <
        (r / (1 - r ^ 2)) ^ 2 := by
  have hd : 0 < 1 - r ^ 2 := by nlinarith [sq_nonneg r]
  have hd2 : 0 < (1 - r ^ 2) ^ 2 := pow_pos hd 2
  have hkey :
      (s + (-(r ^ 2) / (1 - r ^ 2)) ^ 2 - 2 * (-(r ^ 2) / (1 - r ^ 2)) * a -
            (r / (1 - r ^ 2)) ^ 2) * (1 - r ^ 2) ^ 2
        = (1 - r ^ 2) * ((1 - r ^ 2) * s + 2 * r ^ 2 * a - r ^ 2) := by
    field_simp; ring
  have hiff :
      (s + (-(r ^ 2) / (1 - r ^ 2)) ^ 2 - 2 * (-(r ^ 2) / (1 - r ^ 2)) * a -
            (r / (1 - r ^ 2)) ^ 2 < 0)
        ↔ ((1 - r ^ 2) * s + 2 * r ^ 2 * a - r ^ 2 < 0) := by
    have h1 :
        (s + (-(r ^ 2) / (1 - r ^ 2)) ^ 2 - 2 * (-(r ^ 2) / (1 - r ^ 2)) * a -
              (r / (1 - r ^ 2)) ^ 2 < 0)
          ↔ ((s + (-(r ^ 2) / (1 - r ^ 2)) ^ 2 - 2 * (-(r ^ 2) / (1 - r ^ 2)) * a -
                (r / (1 - r ^ 2)) ^ 2) * (1 - r ^ 2) ^ 2 < 0) :=
      ⟨fun h => mul_neg_of_neg_of_pos h hd2, fun h => (neg_iff_pos_of_mul_neg h).mpr hd2⟩
    have h2 :
        ((s + (-(r ^ 2) / (1 - r ^ 2)) ^ 2 - 2 * (-(r ^ 2) / (1 - r ^ 2)) * a -
              (r / (1 - r ^ 2)) ^ 2) * (1 - r ^ 2) ^ 2 < 0)
          ↔ ((1 - r ^ 2) * ((1 - r ^ 2) * s + 2 * r ^ 2 * a - r ^ 2) < 0) := by
      rw [hkey]
    have h3 :
        ((1 - r ^ 2) * ((1 - r ^ 2) * s + 2 * r ^ 2 * a - r ^ 2) < 0)
          ↔ ((1 - r ^ 2) * s + 2 * r ^ 2 * a - r ^ 2 < 0) :=
      ⟨fun h => (pos_iff_neg_of_mul_neg h).mp hd, fun h => mul_neg_of_pos_of_neg hd h⟩
    exact h1.trans (h2.trans h3)
  exact ⟨fun hQ => by have := hiff.mpr hQ; linarith, fun h => hiff.mp (by linarith)⟩

/-- For every `z`, `‖z‖ < r‖z-1‖` is exactly membership in the disc of centre
`-r²/(1-r²)` and radius `r/(1-r²)`. -/
private lemma norm_lt_iff_ball (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (z : ℂ) :
    ‖z‖ < r * ‖z - 1‖ ↔ ‖z - ((-(r ^ 2) / (1 - r ^ 2) : ℝ) : ℂ)‖ < r / (1 - r ^ 2) := by
  have hd : 0 < 1 - r ^ 2 := by nlinarith [sq_nonneg r]
  have hR : 0 ≤ r / (1 - r ^ 2) := le_of_lt (div_pos hr0 hd)
  have hC : Complex.normSq z < r ^ 2 * Complex.normSq (z - 1) ↔
      (1 - r ^ 2) * Complex.normSq z + 2 * r ^ 2 * z.re - r ^ 2 < 0 := by
    rw [normSq_sub_one]
    constructor <;> intro h <;> nlinarith
  have hA : (1 - r ^ 2) * Complex.normSq z + 2 * r ^ 2 * z.re - r ^ 2 < 0 ↔
      Complex.normSq z + (-(r ^ 2) / (1 - r ^ 2)) ^ 2 -
          2 * (-(r ^ 2) / (1 - r ^ 2)) * z.re < (r / (1 - r ^ 2)) ^ 2 :=
    alg_core r hr0 hr1 _ _
  have hD : ‖z - ((-(r ^ 2) / (1 - r ^ 2) : ℝ) : ℂ)‖ < r / (1 - r ^ 2) ↔
      Complex.normSq z + (-(r ^ 2) / (1 - r ^ 2)) ^ 2 -
          2 * (-(r ^ 2) / (1 - r ^ 2)) * z.re < (r / (1 - r ^ 2)) ^ 2 := by
    rw [lt_iff_normSq _ hR, normSq_sub_ofReal]
  exact (sq_norm_lt z r hr0).trans (hC.trans (hA.trans hD.symm))

theorem lens_eq_ball (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Work.C17I.lens r ∩ {z : ℂ | z ≠ 1} =
      Metric.ball ((-(r ^ 2) / (1 - r ^ 2) : ℝ) : ℂ) (r / (1 - r ^ 2)) := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, lens, sw, Metric.mem_ball, dist_eq_norm]
  constructor
  · rintro ⟨h, hz1⟩
    rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hz1))] at h
    exact (norm_lt_iff_ball r hr0 hr1 z).mp h
  · intro h
    have hc := (norm_lt_iff_ball r hr0 hr1 z).mpr h
    have hn : 0 < ‖z - 1‖ :=
      pos_of_mul_pos_right (lt_of_le_of_lt (norm_nonneg z) hc) (le_of_lt hr0)
    refine ⟨?_, ?_⟩
    · rw [norm_div, div_lt_iff₀ hn]; exact hc
    · intro hz1
      subst hz1
      simp at hc
      linarith

end Work.C17I
