import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The pointwise bound on `N₀` used by the `g`-equation right-hand-side estimate

`N₀` (paper tex `\eqref{N0}`) is a sum of six products of the form
`coefficient · L₁₂(·) · (F or g or a first derivative)`, with coefficients
`3/(2α)·sin(2θ)`, `-(cos2θ - sin²θ)`, `1/α`.  Since `|sin 2θ| ≤ 1` and
`|cos2θ - sin²θ| ≤ 2` for every `θ`, and every remaining factor is bounded by `B`
in absolute value, the triangle inequality gives

`|N₀| ≤ (3/(2α) + 2 + 1/α + 3/(2α) + 2 + 2) B² = (4/α + 6) B²`.

The constant `4/α + 6` of the statement is exactly the sum of the six coefficients.
-/

namespace Work.FTS.StrongEps.gRHSBound

open scoped Real

/-- `|x - y| ≤ |x| + |y|` (the `abs_sub_le` of this Mathlib is stated with a middle point). -/
private lemma abs_sub_le_abs_add_abs (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  simpa [sub_eq_add_neg] using abs_add_le x (-y)

/-- `|a*b*c| ≤ A*B'*C` from factorwise bounds. -/
private lemma abs_mul3_le {a b c A B' C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B') (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B' * C := by
  have hA : 0 ≤ A := le_trans (abs_nonneg a) ha
  have hB : 0 ≤ B' := le_trans (abs_nonneg b) hb
  have hC : 0 ≤ C := le_trans (abs_nonneg c) hc
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul ha hb (abs_nonneg b) hA) hc (abs_nonneg c) (mul_nonneg hA hB)

/-- `|a*b*c*d| ≤ A*B'*C*D` from factorwise bounds. -/
private lemma abs_mul4_le {a b c d A B' C D : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B')
    (hc : |c| ≤ C) (hd : |d| ≤ D) : |a * b * c * d| ≤ A * B' * C * D := by
  have hA : 0 ≤ A := le_trans (abs_nonneg a) ha
  have hB : 0 ≤ B' := le_trans (abs_nonneg b) hb
  have hC : 0 ≤ C := le_trans (abs_nonneg c) hc
  have hD : 0 ≤ D := le_trans (abs_nonneg d) hd
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |a| * |b| ≤ A * B' := mul_le_mul ha hb (abs_nonneg b) hA
  have h2 : |a| * |b| * |c| ≤ A * B' * C := mul_le_mul h1 hc (abs_nonneg c) (mul_nonneg hA hB)
  exact mul_le_mul h2 hd (abs_nonneg d) (mul_nonneg (mul_nonneg hA hB) hC)

/-- Triangle inequality for the six-term combination occurring in `N₀`. -/
private lemma abs_six_le (a b c d e f : ℝ) :
    |a - b + c + d - e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 : |a - b| ≤ |a| + |b| := abs_sub_le_abs_add_abs a b
  have h2 : |a - b + c| ≤ |a| + |b| + |c| := by
    have h := abs_add_le (a - b) c
    linarith [h1, abs_nonneg c]
  have h3 : |a - b + c + d| ≤ |a| + |b| + |c| + |d| := by
    have h := abs_add_le (a - b + c) d
    linarith [h2, abs_nonneg d]
  have h4 : |a - b + c + d - e| ≤ |a| + |b| + |c| + |d| + |e| := by
    have h := abs_sub_le_abs_add_abs (a - b + c + d) e
    linarith [h3, abs_nonneg e]
  have h5 : |a - b + c + d - e - f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
    have h := abs_sub_le_abs_add_abs (a - b + c + d - e) f
    linarith [h4, abs_nonneg f]
  exact h5

theorem abs_N0_le {α B : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    {F g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hL12Fstar : |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ B)
    (hL12g : |Work.Construction.L12 g z| ≤ B)
    (hFb : |F z θ| ≤ B) (hpFb : |Work.Spaces.pth F z θ| ≤ B)
    (hDzFb : |Work.Spaces.Dz F z θ| ≤ B) (hgb : |g z θ| ≤ B)
    (hDzgb : |Work.Spaces.Dz g z θ| ≤ B)
    (hpFstb : |Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ B)
    (hDzFstb : |Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ B) :
    |Work.Construction.N0 α F g z θ| ≤ (4 / α + 6) * B ^ 2 := by
  have hα1 : (0 : ℝ) < 3 / (2 * α) := by positivity
  have hα2 : (0 : ℝ) < 1 / α := by positivity
  have hs2 : |Work.Construction.s2 θ| ≤ 1 := by
    rw [Work.Construction.s2_eq]
    exact abs_le.mpr (Real.sin_mem_Icc (2 * θ))
  have hc2m : |Work.Construction.c2m θ| ≤ 2 := by
    rw [Work.Construction.c2m_eq]
    have hc := Real.cos_mem_Icc (2 * θ)
    have hs : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have hs0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2, hs, hs0]
  have _hFuse := hFb
  -- unfold `N₀` and name its six summands
  simp only [Work.Construction.N0]
  set v1 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ with hv1
  set v2 : ℝ := Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ with hv2
  set v3 : ℝ := (1 / α) * Work.Construction.L12 g z * g z θ with hv3
  set v4 : ℝ := (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 g z
      * Work.Spaces.pth F z θ with hv4
  set v5 : ℝ := Work.Construction.c2m θ * Work.Construction.L12 g z
      * Work.Spaces.Dz F z θ with hv5
  set v6 : ℝ := Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz g z θ with hv6
  -- factorwise bounds on the six summands
  have b1 : |v1| ≤ (3 / (2 * α)) * 1 * B * B := by
    rw [hv1]
    exact abs_mul4_le (a := 3 / (2 * α)) (b := Work.Construction.s2 θ)
      (c := Work.Construction.L12 (Work.Construction.Fstar α) z)
      (d := Work.Spaces.pth (Work.Construction.Fstar α) z θ)
      (A := 3 / (2 * α)) (B' := 1) (C := B) (D := B)
      (by rw [abs_of_pos hα1]) hs2 hL12Fstar hpFstb
  have b2 : |v2| ≤ 2 * B * B := by
    rw [hv2]
    exact abs_mul3_le (a := Work.Construction.c2m θ)
      (b := Work.Construction.L12 (Work.Construction.Fstar α) z)
      (c := Work.Spaces.Dz (Work.Construction.Fstar α) z θ)
      (A := 2) (B' := B) (C := B) hc2m hL12Fstar hDzFstb
  have b3 : |v3| ≤ (1 / α) * B * B := by
    rw [hv3]
    exact abs_mul3_le (a := 1 / α) (b := Work.Construction.L12 g z) (c := g z θ)
      (A := 1 / α) (B' := B) (C := B) (by rw [abs_of_pos hα2]) hL12g hgb
  have b4 : |v4| ≤ (3 / (2 * α)) * 1 * B * B := by
    rw [hv4]
    exact abs_mul4_le (a := 3 / (2 * α)) (b := Work.Construction.s2 θ)
      (c := Work.Construction.L12 g z) (d := Work.Spaces.pth F z θ)
      (A := 3 / (2 * α)) (B' := 1) (C := B) (D := B)
      (by rw [abs_of_pos hα1]) hs2 hL12g hpFb
  have b5 : |v5| ≤ 2 * B * B := by
    rw [hv5]
    exact abs_mul3_le (a := Work.Construction.c2m θ) (b := Work.Construction.L12 g z)
      (c := Work.Spaces.Dz F z θ) (A := 2) (B' := B) (C := B) hc2m hL12g hDzFb
  have b6 : |v6| ≤ 2 * B * B := by
    rw [hv6]
    exact abs_mul3_le (a := Work.Construction.c2m θ)
      (b := Work.Construction.L12 (Work.Construction.Fstar α) z)
      (c := Work.Spaces.Dz g z θ) (A := 2) (B' := B) (C := B) hc2m hL12Fstar hDzgb
  have hmain : |v1 - v2 + v3 + v4 - v5 - v6| ≤ |v1| + |v2| + |v3| + |v4| + |v5| + |v6| :=
    abs_six_le v1 v2 v3 v4 v5 v6
  have hstep : |v1| + |v2| + |v3| + |v4| + |v5| + |v6|
      ≤ (3 / (2 * α)) * 1 * B * B + (2 * B * B) + ((1 / α) * B * B)
        + ((3 / (2 * α)) * 1 * B * B) + (2 * B * B) + (2 * B * B) := by
    linarith [b1, b2, b3, b4, b5, b6]
  have harith : (3 / (2 * α)) * 1 * B * B + (2 * B * B) + ((1 / α) * B * B)
        + ((3 / (2 * α)) * 1 * B * B) + (2 * B * B) + (2 * B * B)
      = (4 / α + 6) * B ^ 2 := by
    have hαne : α ≠ 0 := ne_of_gt hα
    field_simp
    ring
  rw [← harith]
  exact le_trans hmain hstep

end Work.FTS.StrongEps.gRHSBound
