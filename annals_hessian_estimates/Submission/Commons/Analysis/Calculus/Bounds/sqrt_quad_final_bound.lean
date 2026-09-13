import Mathlib.Algebra.Order.Star.Real

set_option linter.unusedVariables false

namespace Commons.Analysis.Calculus.Bounds

/-- If `0 ≤ X ≤ (3/2) s1 r²` and `s1 > 0`, `r > 0` then `√X ≤ (3/2) √s1 r`. -/
lemma sqrt_le_of_le_three_halves {s1 r X : ℝ} (hs1 : 0 < s1) (hr : 0 < r)
    (hX : X ≤ (3/2)*s1*r^2) :
    Real.sqrt X ≤ (3/2)*Real.sqrt s1*r := by
  have h9 : ((3/2)*Real.sqrt s1*r)^2 = (9/4)*s1*r^2 := by
    have hS : (Real.sqrt s1)^2 = s1 := Real.sq_sqrt (le_of_lt hs1)
    nlinarith only [hS]
  have hsq : X ≤ ((3/2)*Real.sqrt s1*r)^2 := by
    rw [h9]
    nlinarith only [hX, mul_nonneg (le_of_lt hs1) (sq_nonneg r)]
  have hnonneg : 0 ≤ (3/2)*Real.sqrt s1*r := by positivity
  calc Real.sqrt X ≤ Real.sqrt (((3/2)*Real.sqrt s1*r)^2) := Real.sqrt_le_sqrt hsq
    _ = (3/2)*Real.sqrt s1*r := Real.sqrt_sq hnonneg

theorem sqrt_quad_final_bound {s1 r C0 hh c X Z : ℝ}
    (hs1 : 0 < s1) (hr : 0 < r) (hC0 : 1 ≤ C0) (hh_pos : 0 < hh)
    (hh_le : hh ≤ 1/(16*C0)) (hc_lb : 3/(128*C0^2) ≤ c) (hc_pos : 0 < c)
    (hsum : hh^2 + c ≤ 9/(256*C0^2))
    (hXnn : 0 ≤ X) (hX : X ≤ (3/2)*s1*r^2) (hZ : 0 < Z) (hZr : Z ≤ r^2) :
    (4*hh*Real.sqrt X + Real.sqrt ((4*hh*Real.sqrt X)^2 + c*(6*s1*Z+12*X)))/c
      ≤ 68*C0^2*Real.sqrt s1*r := by
  have hC0pos : 0 < C0 := lt_of_lt_of_le zero_lt_one hC0
  have hC0nn : 0 ≤ C0 := le_of_lt hC0pos
  have hrnn : 0 ≤ r := le_of_lt hr
  have hs1nn : 0 ≤ s1 := le_of_lt hs1
  have hYnn : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hSnn : 0 ≤ Real.sqrt s1 := Real.sqrt_nonneg s1
  have hSr : 0 ≤ Real.sqrt s1 * r := mul_nonneg hSnn hrnn
  set A := 4*hh*Real.sqrt X with hA
  set D := 6*s1*Z + 12*X with hD
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hDnn : 0 ≤ D := by rw [hD]; positivity
  have hBnn : 0 ≤ c*D := mul_nonneg (le_of_lt hc_pos) hDnn
  -- basic bounds
  have hsqrtX : Real.sqrt X ≤ (3/2)*Real.sqrt s1*r :=
    sqrt_le_of_le_three_halves hs1 hr hX
  have h16 : hh*(16*C0) ≤ 1 := (le_div_iff₀ (by positivity : (0:ℝ) < 16*C0)).mp hh_le
  have hYC : hh*C0 ≤ 1/16 := by nlinarith only [h16]
  have hc_mul : 3 ≤ 128*C0^2*c := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < 128*C0^2)).mp hc_lb
    nlinarith only [h]
  -- Step 1: sqrt(A^2 + cD) ≤ A + sqrt(cD)
  have hsqrtA : Real.sqrt (A^2 + c*D) ≤ A + Real.sqrt (c*D) := by
    have hle : A^2 + c*D ≤ (A + Real.sqrt (c*D))^2 := by
      have hsq : (Real.sqrt (c*D))^2 = c*D := Real.sq_sqrt hBnn
      nlinarith only [hsq, hAnn, Real.sqrt_nonneg (c*D)]
    calc Real.sqrt (A^2 + c*D) ≤ Real.sqrt ((A + Real.sqrt (c*D))^2) :=
            Real.sqrt_le_sqrt hle
      _ = A + Real.sqrt (c*D) :=
            Real.sqrt_sq (add_nonneg hAnn (Real.sqrt_nonneg _))
  -- bounds on D
  have hZ1 : 6*s1*Z ≤ 6*s1*r^2 := by
    have := mul_le_mul_of_nonneg_left hZr (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hs1nn)
    exact this
  have hX1 : 12*X ≤ 18*s1*r^2 := by
    have := mul_le_mul_of_nonneg_left hX (by norm_num : (0:ℝ) ≤ 12)
    calc 12*X ≤ 12*((3/2)*s1*r^2) := this
      _ = 18*s1*r^2 := by ring
  have hD_le : D ≤ 24*s1*r^2 := by
    rw [hD]; linarith only [hZ1, hX1]
  -- Bound term 2A/c
  have h2A : 2*A/c ≤ 32*C0*Real.sqrt s1*r := by
    have hchain : 8*hh*Real.sqrt X*C0 ≤ 32*C0^2*Real.sqrt s1*r*c := by
      have h1 : 8*hh*Real.sqrt X*C0 ≤ Real.sqrt X/2 := by
        have hthis := mul_le_mul_of_nonneg_right hYC (by positivity : (0:ℝ) ≤ 8*Real.sqrt X)
        calc 8*hh*Real.sqrt X*C0 = (hh*C0)*(8*Real.sqrt X) := by ring
          _ ≤ (1/16)*(8*Real.sqrt X) := hthis
          _ = Real.sqrt X/2 := by ring
      have h2 : Real.sqrt X/2 ≤ 3*(Real.sqrt s1*r)/4 := by linarith only [hsqrtX]
      have h3 : 3*(Real.sqrt s1*r)/4 ≤ 32*C0^2*Real.sqrt s1*r*c := by
        have h4 : 3/4 ≤ 32*C0^2*c := by linarith only [hc_mul]
        have hthis := mul_le_mul_of_nonneg_right h4 hSr
        calc 3*(Real.sqrt s1*r)/4 = (3/4)*(Real.sqrt s1*r) := by ring
          _ ≤ (32*C0^2*c)*(Real.sqrt s1*r) := hthis
          _ = 32*C0^2*Real.sqrt s1*r*c := by ring
      exact le_trans h1 (le_trans h2 h3)
    have hchain' : (8*hh*Real.sqrt X)*C0 ≤ (32*C0*Real.sqrt s1*r*c)*C0 := by
      have hrhs : (32*C0*Real.sqrt s1*r*c)*C0 = 32*C0^2*Real.sqrt s1*r*c := by ring
      rw [hrhs]; exact hchain
    have hgoal : 8*hh*Real.sqrt X ≤ 32*C0*Real.sqrt s1*r*c :=
      (mul_le_mul_iff_of_pos_right hC0pos).mp hchain'
    rw [div_le_iff₀ hc_pos, hA]
    have hlhs : 2*(4*hh*Real.sqrt X) = 8*hh*Real.sqrt X := by ring
    have hrhs : (32*C0*Real.sqrt s1*r)*c = 32*C0*Real.sqrt s1*r*c := by ring
    rw [hlhs, hrhs]; exact hgoal
  -- Bound term sqrt(cD)/c
  have h2B : Real.sqrt (c*D)/c ≤ 32*C0*Real.sqrt s1*r := by
    rw [div_le_iff₀ hc_pos, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have hsqeq : ((32*C0*Real.sqrt s1*r)*c)^2 = 1024*C0^2*s1*r^2*c^2 := by
      rw [show ((32*C0*Real.sqrt s1*r)*c)^2
            = 1024*C0^2*(Real.sqrt s1)^2*r^2*c^2 by ring,
          Real.sq_sqrt hs1nn]
    rw [hsqeq]
    have hcm : 24 ≤ 1024*C0^2*c := by linarith only [hc_mul]
    have h1 : c*D ≤ 24*s1*r^2*c := by
      have hthis := mul_le_mul_of_nonneg_left hD_le (le_of_lt hc_pos)
      calc c*D ≤ c*(24*s1*r^2) := hthis
        _ = 24*s1*r^2*c := by ring
    have h2 : 24*s1*r^2*c ≤ 1024*C0^2*s1*r^2*c^2 := by
      have hSr2c : 0 ≤ s1*r^2*c :=
        mul_nonneg (mul_nonneg hs1nn (sq_nonneg r)) (le_of_lt hc_pos)
      have hthis := mul_le_mul_of_nonneg_right hcm hSr2c
      calc 24*s1*r^2*c = 24*(s1*r^2*c) := by ring
        _ ≤ (1024*C0^2*c)*(s1*r^2*c) := hthis
        _ = 1024*C0^2*s1*r^2*c^2 := by ring
    linarith only [h1, h2]
  -- final numeric step
  have h64 : 64*C0*Real.sqrt s1*r ≤ 68*C0^2*Real.sqrt s1*r := by
    have h64c : 64*C0 ≤ 68*C0^2 := by nlinarith only [hC0]
    calc 64*C0*Real.sqrt s1*r = (64*C0)*(Real.sqrt s1*r) := by ring
      _ ≤ (68*C0^2)*(Real.sqrt s1*r) := mul_le_mul_of_nonneg_right h64c hSr
      _ = 68*C0^2*Real.sqrt s1*r := by ring
  calc (A + Real.sqrt (A^2 + c*D))/c
      ≤ (2*A + Real.sqrt (c*D))/c := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hc_pos)
        linarith only [hsqrtA]
    _ = 2*A/c + Real.sqrt (c*D)/c := by rw [add_div]
    _ ≤ 32*C0*Real.sqrt s1*r + 32*C0*Real.sqrt s1*r := add_le_add h2A h2B
    _ = 64*C0*Real.sqrt s1*r := by ring
    _ ≤ 68*C0^2*Real.sqrt s1*r := h64

end Commons.Analysis.Calculus.Bounds