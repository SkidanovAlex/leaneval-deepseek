import Mathlib

namespace Work.Residues

/-- Norm of the product of a real scalar with a complex number. -/
private lemma norm_real_mul_complex (a : ℝ) (x : ℂ) : ‖a * x‖ = |a| * ‖x‖ := by
  have h : ‖(a : ℂ)‖ = |a| := by simp
  rw [show a * x = (a : ℂ) * x from rfl, norm_mul, h]

/-- Linear step: `‖z - 1‖ ≤ (|a| + A ρ) t`. -/
private lemma zeta_bound {u x y A a t ρ : ℝ} (hA : 0 ≤ A)
    (hstep : u ≤ x + y) (hx : x ≤ A * t ^ 2) (hy : y = |a| * t)
    (ht2 : t ^ 2 ≤ ρ * t) :
    u ≤ (|a| + A * ρ) * t := by
  nlinarith [hstep, hx, hy, ht2, hA]

/-- `3 u² ≤ 3 (X t)²` for `0 ≤ u ≤ X t`. -/
private lemma sq_bound {u X t : ℝ} (h : u ≤ X * t) (h0 : 0 ≤ u) :
    3 * u ^ 2 ≤ 3 * (X ^ 2 * t ^ 2) := by
  have h1 : 3 * u ^ 2 ≤ 3 * (X * t) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h 2) (by norm_num : (0 : ℝ) ≤ 3)
  calc 3 * u ^ 2 ≤ 3 * (X * t) ^ 2 := h1
    _ = 3 * (X ^ 2 * t ^ 2) := by ring

/-- `v² ≤ (Y t)²` for `0 ≤ v ≤ Y t`. -/
private lemma sq_bound' {v Y t : ℝ} (h : v ≤ Y * t) (h0 : 0 ≤ v) :
    v ^ 2 ≤ Y ^ 2 * t ^ 2 := by
  calc v ^ 2 ≤ (Y * t) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = Y ^ 2 * t ^ 2 := by ring

/-- `u³ ≤ ρ X³ t²` for `0 ≤ u ≤ X t` and `t³ ≤ ρ t²`. -/
private lemma cube_bound {u X t ρ : ℝ} (hX : 0 ≤ X) (h : u ≤ X * t) (h0 : 0 ≤ u)
    (ht3 : t ^ 3 ≤ ρ * t ^ 2) :
    u ^ 3 ≤ ρ * (X ^ 3 * t ^ 2) := by
  have hX3 : 0 ≤ X ^ 3 := by positivity
  have hs : u ^ 3 ≤ (X * t) ^ 3 := pow_le_pow_left₀ h0 h 3
  have h3 : (X * t) ^ 3 ≤ ρ * (X ^ 3 * t ^ 2) := by
    calc (X * t) ^ 3 = X ^ 3 * t ^ 3 := by ring
      _ ≤ X ^ 3 * (ρ * t ^ 2) := mul_le_mul_of_nonneg_left ht3 hX3
      _ = ρ * (X ^ 3 * t ^ 2) := by ring
  linarith [hs, h3]

/-- Purely algebraic final assembly of the estimate. -/
private lemma cube_sub_sq_final (N x y u v s A B X Y t ρ : ℝ)
    (h6 : N ≤ 3 * x + 2 * y + (3 * u + v + s))
    (h1 : 3 * x ≤ 3 * (A * t ^ 2)) (h2 : 2 * y ≤ 2 * (B * t ^ 2))
    (h3 : 3 * u ≤ 3 * (X ^ 2 * t ^ 2)) (h4 : v ≤ ρ * (X ^ 3 * t ^ 2))
    (h5 : s ≤ Y ^ 2 * t ^ 2) :
    N ≤ (3 * A + 2 * B + 3 * X ^ 2 + ρ * X ^ 3 + Y ^ 2) * t ^ 2 := by
  nlinarith [h6, h1, h2, h3, h4, h5]

theorem NormCubeSubSqSharp {a b A B ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {q z w : ℂ} (hq : ‖q‖ ≤ ρ)
    (hz : ‖z - 1 - a * q‖ ≤ A * ‖q‖ ^ 2) (hw : ‖w - 1 - b * q‖ ≤ B * ‖q‖ ^ 2) :
    ‖z ^ 3 - w ^ 2 - (3 * a - 2 * b) * q‖
      ≤ (3 * A + 2 * B + 3 * (|a| + A * ρ) ^ 2 + ρ * (|a| + A * ρ) ^ 3
          + (|b| + B * ρ) ^ 2) * ‖q‖ ^ 2 := by
  set t : ℝ := ‖q‖ with ht
  set X : ℝ := |a| + A * ρ with hX
  set Y : ℝ := |b| + B * ρ with hY
  have ht0 : 0 ≤ t := by rw [ht]; exact norm_nonneg q
  have htρ : t ≤ ρ := by rw [ht]; exact hq
  have ht1 : t ≤ 1 := le_trans htρ hρ1
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have ht2 : t ^ 2 ≤ ρ * t := by nlinarith [ht0, htρ]
  have ht3 : t ^ 3 ≤ ρ * t ^ 2 := by nlinarith [ht0, htρ, ht1]
  have hz' : ‖z - 1 - a * q‖ ≤ A * t ^ 2 := by rw [ht]; exact hz
  have hw' : ‖w - 1 - b * q‖ ≤ B * t ^ 2 := by rw [ht]; exact hw
  have h1 : 3 * ‖z - 1 - a * q‖ ≤ 3 * (A * t ^ 2) :=
    mul_le_mul_of_nonneg_left hz' (by norm_num : (0 : ℝ) ≤ 3)
  have h2 : 2 * ‖w - 1 - b * q‖ ≤ 2 * (B * t ^ 2) :=
    mul_le_mul_of_nonneg_left hw' (by norm_num : (0 : ℝ) ≤ 2)
  -- bound on ‖z - 1‖
  have hζ : ‖z - 1‖ ≤ X * t := by
    have hstep : ‖z - 1‖ ≤ ‖z - 1 - a * q‖ + ‖a * q‖ := by
      have h := norm_add_le (z - 1 - a * q) (a * q)
      rwa [show (z - 1 - a * q) + a * q = z - 1 by ring] at h
    have hnn : ‖a * q‖ = |a| * t := by rw [norm_real_mul_complex, ht]
    have hb := zeta_bound hA hstep hz' hnn ht2
    rw [hX]
    exact hb
  -- bound on ‖w - 1‖
  have hη : ‖w - 1‖ ≤ Y * t := by
    have hstep : ‖w - 1‖ ≤ ‖w - 1 - b * q‖ + ‖b * q‖ := by
      have h := norm_add_le (w - 1 - b * q) (b * q)
      rwa [show (w - 1 - b * q) + b * q = w - 1 by ring] at h
    have hnn : ‖b * q‖ = |b| * t := by rw [norm_real_mul_complex, ht]
    have hb := zeta_bound hB hstep hw' hnn ht2
    rw [hY]
    exact hb
  have hζ2 : 3 * ‖z - 1‖ ^ 2 ≤ 3 * (X ^ 2 * t ^ 2) :=
    sq_bound hζ (norm_nonneg _)
  have hζ3 : ‖z - 1‖ ^ 3 ≤ ρ * (X ^ 3 * t ^ 2) :=
    cube_bound hX0 hζ (norm_nonneg _) ht3
  have hη2 : ‖w - 1‖ ^ 2 ≤ Y ^ 2 * t ^ 2 :=
    sq_bound' hη (norm_nonneg _)
  -- triangle inequality for the first two terms
  have hA1 : ‖3 * (z - 1 - a * q) - 2 * (w - 1 - b * q)‖
      ≤ 3 * ‖z - 1 - a * q‖ + 2 * ‖w - 1 - b * q‖ := by
    have h := norm_sub_le (3 * (z - 1 - a * q)) (2 * (w - 1 - b * q))
    have e1 : ‖3 * (z - 1 - a * q)‖ = 3 * ‖z - 1 - a * q‖ := by
      rw [norm_mul]; norm_num
    have e2 : ‖2 * (w - 1 - b * q)‖ = 2 * ‖w - 1 - b * q‖ := by
      rw [norm_mul]; norm_num
    linarith
  -- triangle inequality for the quadratic and cubic terms
  have hA2 : ‖3 * (z - 1) ^ 2 + (z - 1) ^ 3 - (w - 1) ^ 2‖
      ≤ 3 * ‖z - 1‖ ^ 2 + ‖z - 1‖ ^ 3 + ‖w - 1‖ ^ 2 := by
    have h := norm_sub_le (3 * (z - 1) ^ 2 + (z - 1) ^ 3) ((w - 1) ^ 2)
    have h2' := norm_add_le (3 * (z - 1) ^ 2) ((z - 1) ^ 3)
    have e1 : ‖3 * (z - 1) ^ 2‖ = 3 * ‖z - 1‖ ^ 2 := by rw [norm_mul]; norm_num
    have e2 : ‖(z - 1) ^ 3‖ = ‖z - 1‖ ^ 3 := norm_pow _ _
    have e3 : ‖(w - 1) ^ 2‖ = ‖w - 1‖ ^ 2 := norm_pow _ _
    linarith
  -- Taylor-type expansion: z = 1 + (z-1), w = 1 + (w-1)
  have hkey : z ^ 3 - w ^ 2 - (3 * a - 2 * b) * q
      = 3 * (z - 1 - a * q) - 2 * (w - 1 - b * q)
        + (3 * (z - 1) ^ 2 + (z - 1) ^ 3 - (w - 1) ^ 2) := by
    ring
  have hnorm : ‖z ^ 3 - w ^ 2 - (3 * a - 2 * b) * q‖
      ≤ 3 * ‖z - 1 - a * q‖ + 2 * ‖w - 1 - b * q‖
        + (3 * ‖z - 1‖ ^ 2 + ‖z - 1‖ ^ 3 + ‖w - 1‖ ^ 2) := by
    have h := norm_add_le (3 * (z - 1 - a * q) - 2 * (w - 1 - b * q))
                          (3 * (z - 1) ^ 2 + (z - 1) ^ 3 - (w - 1) ^ 2)
    have hg : ‖z ^ 3 - w ^ 2 - (3 * a - 2 * b) * q‖
        = ‖3 * (z - 1 - a * q) - 2 * (w - 1 - b * q)
            + (3 * (z - 1) ^ 2 + (z - 1) ^ 3 - (w - 1) ^ 2)‖ := by rw [hkey]
    rw [hg]
    linarith
  have hfin : ‖z ^ 3 - w ^ 2 - (3 * a - 2 * b) * q‖
      ≤ (3 * A + 2 * B + 3 * X ^ 2 + ρ * X ^ 3 + Y ^ 2) * t ^ 2 :=
    cube_sub_sq_final _ _ _ _ _ _ _ _ _ _ _ _ hnorm h1 h2 hζ2 hζ3 hη2
  exact hfin

end Work.Residues
