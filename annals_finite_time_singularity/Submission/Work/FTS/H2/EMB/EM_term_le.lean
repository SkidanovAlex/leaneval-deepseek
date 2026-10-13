import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.STEasyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.EMB

theorem EM_term_le {α : ℝ} {f g : ℝ → ℝ → ℝ} {z θ : ℝ} {W Hk : ℝ}
    (hS : 0 ≤ Real.sin (2 * θ)) (hWnn : 0 ≤ W) (hHknn : 0 ≤ Hk)
    (hf : ∀ a b : ℕ, a + b ≤ 4 →
      |Work.Spaces.mixed b a f z θ| ≤ 400000 * Real.sin (2 * θ) * W)
    (hgs : ∀ c d i j : ℕ, 1 ≤ i → i + j ≤ 4 → d ≤ 3 → d + 1 + c ≤ 4 →
      Real.sin (2 * θ) * |Work.Spaces.mixed c d (Work.Spaces.pth g) z θ|
          * |Work.Spaces.mixed j i g z θ|
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ 187 * ((d + 1 : ℕ) : ℝ) * Hk)
    {i j a b : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4) (ha : a ≤ i) (hb : b ≤ j) :
    |(if i + j = 4 ∧ a = 0 ∧ b = 0 then 0
        else ((i.choose a : ℝ) * (j.choose b : ℝ))) *
      (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ
        * Work.Spaces.mixed j i g z θ) * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))|
      ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) * (400000 * 935 * W * Hk) := by
  by_cases hcase : i + j = 4 ∧ a = 0 ∧ b = 0
  · rw [if_pos hcase]
    simp only [zero_mul, abs_zero]
    exact mul_nonneg (by positivity) (by positivity)
  · rw [if_neg hcase]
    -- the two index constraints needed to apply `hgs`
    have hsum : (i - a) + (j - b) ≤ 3 := by
      by_cases h4 : i + j = 4
      · have hab : 1 ≤ a + b := by
          by_contra hcon
          push_neg at hcon
          have ha0 : a = 0 := by omega
          have hb0 : b = 0 := by omega
          exact hcase ⟨h4, ha0, hb0⟩
        omega
      · omega
    have hd : i - a ≤ 3 := by omega
    have hdc : (i - a) + 1 + (j - b) ≤ 4 := by omega
    have hFle : |Work.Spaces.mixed b a f z θ| ≤ 400000 * Real.sin (2 * θ) * W :=
      hf a b (by omega)
    have hGle := hgs (j - b) (i - a) i j hi hij hd hdc
    have hwznn : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hsvnn : (0 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Real.rpow_nonneg hS _
    have hQnn : (0 : ℝ) ≤
        |Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
          * |Work.Spaces.mixed j i g z θ|
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hwznn hsvnn)
    have h400W : (0 : ℝ) ≤ 400000 * W := by positivity
    have hx5 : ((i - a + 1 : ℕ) : ℝ) ≤ 5 := by
      have h : i - a + 1 ≤ 5 := by omega
      exact_mod_cast h
    have h187 : 187 * ((i - a + 1 : ℕ) : ℝ) ≤ 935 := by nlinarith [hx5]
    have hstep1 : |Work.Spaces.mixed b a f z θ|
        * (|Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
          * |Work.Spaces.mixed j i g z θ|
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        ≤ (400000 * Real.sin (2 * θ) * W)
        * (|Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
          * |Work.Spaces.mixed j i g z θ|
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
      mul_le_mul_of_nonneg_right hFle hQnn
    have hstep3 : (400000 * W)
        * (Real.sin (2 * θ) * |Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
          * |Work.Spaces.mixed j i g z θ|
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        ≤ (400000 * W) * (187 * ((i - a + 1 : ℕ) : ℝ) * Hk) :=
      mul_le_mul_of_nonneg_left hGle h400W
    have hmain : |Work.Spaces.mixed b a f z θ|
        * (|Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
          * |Work.Spaces.mixed j i g z θ|
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
        ≤ 400000 * 935 * W * Hk := by
      calc |Work.Spaces.mixed b a f z θ|
          * (|Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
            * |Work.Spaces.mixed j i g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          ≤ (400000 * Real.sin (2 * θ) * W)
            * (|Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
              * |Work.Spaces.mixed j i g z θ|
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
            hstep1
        _ = (400000 * W)
            * (Real.sin (2 * θ) * |Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
              * |Work.Spaces.mixed j i g z θ|
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
            ring
        _ ≤ (400000 * W) * (187 * ((i - a + 1 : ℕ) : ℝ) * Hk) := hstep3
        _ ≤ (400000 * W) * (935 * Hk) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h187 hHknn) h400W
        _ = 400000 * 935 * W * Hk := by ring
    have habs : |((i.choose a : ℝ) * (j.choose b : ℝ)) *
        (Work.Spaces.mixed b a f z θ
          * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ
          * Work.Spaces.mixed j i g z θ) * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))|
        = ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (|Work.Spaces.mixed b a f z θ|
            * (|Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ|
              * |Work.Spaces.mixed j i g z θ|
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))) := by
      simp only [abs_mul]
      rw [abs_of_nonneg (Nat.cast_nonneg (i.choose a)), abs_of_nonneg (Nat.cast_nonneg (j.choose b)),
        abs_of_nonneg (sq_nonneg (Work.Spaces.w z)), abs_of_nonneg (Real.rpow_nonneg hS _)]
      ring
    rw [habs]
    exact mul_le_mul_of_nonneg_left hmain (by positivity)

end Work.FTS.H2.EMB
