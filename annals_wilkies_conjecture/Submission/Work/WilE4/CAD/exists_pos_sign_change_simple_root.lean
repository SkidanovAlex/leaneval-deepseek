import Mathlib

namespace Work.WilE4.CAD

/-- At a simple real root of a real polynomial the polynomial takes opposite signs at two points
symmetric about the root. -/
theorem exists_pos_sign_change_simple_root {f : Polynomial ℝ} {y : ℝ} (hroot : f.IsRoot y)
    (hderiv : f.derivative.eval y ≠ 0) :
    ∃ δ > 0, f.eval (y - δ) * f.eval (y + δ) < 0 := by
  -- Factor `f = (X - C y) * q` using the root, so that `q.eval y = f.derivative.eval y ≠ 0`.
  obtain ⟨q, hq⟩ := (Polynomial.dvd_iff_isRoot).mpr hroot
  have hd : f.derivative.eval y = q.eval y := by
    conv_lhs => rw [hq]
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_sub_C]
    simp
  have hcy : q.eval y ≠ 0 := by rw [← hd]; exact hderiv
  -- `q.eval` is continuous at `y`; pick a symmetric window on which it keeps the sign of `q.eval y`.
  have hcont : ContinuousAt (fun z : ℝ => q.eval z) y := Polynomial.continuousAt q
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ :=
    hcont (|q.eval y| / 2) (div_pos (abs_pos.mpr hcy) (by norm_num))
  have hδpos : 0 < δ₀ / 2 := div_pos hδ₀pos (by norm_num)
  have h1 : |q.eval (y - δ₀ / 2) - q.eval y| < |q.eval y| / 2 := by
    have hdist : dist (y - δ₀ / 2) y < δ₀ := by
      rw [Real.dist_eq, show y - δ₀ / 2 - y = -(δ₀ / 2) by ring, abs_neg,
        abs_of_pos hδpos]
      linarith
    have h := hδ₀ hdist
    rwa [Real.dist_eq] at h
  have h2 : |q.eval (y + δ₀ / 2) - q.eval y| < |q.eval y| / 2 := by
    have hdist : dist (y + δ₀ / 2) y < δ₀ := by
      rw [Real.dist_eq, show y + δ₀ / 2 - y = δ₀ / 2 by ring, abs_of_pos hδpos]
      linarith
    have h := hδ₀ hdist
    rwa [Real.dist_eq] at h
  have hprod : 0 < q.eval (y - δ₀ / 2) * q.eval (y + δ₀ / 2) := by
    rcases lt_or_gt_of_ne hcy with hcneg | hcpos
    · have ha : q.eval (y - δ₀ / 2) < 0 := by
        have := (abs_lt.mp h1).2
        rw [abs_of_neg hcneg] at this; linarith
      have hb : q.eval (y + δ₀ / 2) < 0 := by
        have := (abs_lt.mp h2).2
        rw [abs_of_neg hcneg] at this; linarith
      exact mul_pos_of_neg_of_neg ha hb
    · have ha : 0 < q.eval (y - δ₀ / 2) := by
        have := (abs_lt.mp h1).1
        rw [abs_of_pos hcpos] at this; linarith
      have hb : 0 < q.eval (y + δ₀ / 2) := by
        have := (abs_lt.mp h2).1
        rw [abs_of_pos hcpos] at this; linarith
      exact mul_pos ha hb
  have hf_eval : ∀ z : ℝ, f.eval z = (z - y) * q.eval z := by
    intro z
    rw [hq, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  refine ⟨δ₀ / 2, hδpos, ?_⟩
  rw [hf_eval, hf_eval]
  have hrw : ((y - δ₀ / 2) - y) * q.eval (y - δ₀ / 2)
      * (((y + δ₀ / 2) - y) * q.eval (y + δ₀ / 2))
      = -(δ₀ / 2 * (δ₀ / 2) * (q.eval (y - δ₀ / 2) * q.eval (y + δ₀ / 2))) := by ring
  rw [hrw]
  have hpos : 0 < δ₀ / 2 * (δ₀ / 2) * (q.eval (y - δ₀ / 2) * q.eval (y + δ₀ / 2)) :=
    mul_pos (mul_pos hδpos hδpos) hprod
  linarith

end Work.WilE4.CAD
