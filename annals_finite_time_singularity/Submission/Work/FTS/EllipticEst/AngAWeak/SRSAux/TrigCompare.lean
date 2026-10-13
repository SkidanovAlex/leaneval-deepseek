import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.EllipticEst.AngAWeak.AngWeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak.SRSAux

theorem TrigCompare {q : ℝ} (hq : 0 < q) (θ : ℝ)
    (hθ : θ ∈ Set.Ioo (Real.pi / 4) (Real.pi / 2)) :
    Real.sin (2 * θ) ≤ 2 * (Real.pi / 2 - θ)
      ∧ (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ)
      ∧ Real.cos θ ≤ Real.pi / 2 - θ
      ∧ (2 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.cos θ
      ∧ 0 < Real.sin (2 * θ) ∧ 0 < Real.cos θ
      ∧ (2 * (Real.pi / 2 - θ)) ^ (-q) ≤ Work.FTS.EllipticEst.AngAWeak.wq q θ
      ∧ Work.FTS.EllipticEst.AngAWeak.wq q θ
          ≤ ((4 / Real.pi) * (Real.pi / 2 - θ)) ^ (-q)
      ∧ (Work.FTS.EllipticEst.AngAWeak.wq q θ)⁻¹ ≤ 1
      ∧ Real.cos θ * (Real.sin (2 * θ)) ^ 2 ≤ 4 * (Real.pi / 2 - θ) ^ 3
      ∧ (32 / Real.pi ^ 3) * (Real.pi / 2 - θ) ^ 3
          ≤ Real.cos θ * (Real.sin (2 * θ)) ^ 2
      ∧ (8 / Real.pi ^ 2) * (Real.pi / 2 - θ) ^ 2 ≤ Real.cos θ * Real.sin (2 * θ) := by
  -- Write `d := π/2 - θ` for the distance to the right endpoint; the hypotheses say
  -- `0 < d < π/4`, so all the elementary trigonometric bounds apply on `(0, π/2)`.
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hpi : 0 < Real.pi := Real.pi_pos
  have hθpos : 0 < θ := by linarith
  set d : ℝ := Real.pi / 2 - θ with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hd1 : d < Real.pi / 4 := by rw [hd]; linarith
  have hd_pi2 : d ≤ Real.pi / 2 := by linarith
  have h2d0 : 0 < 2 * d := by linarith
  have h2d1 : 2 * d ≤ Real.pi / 2 := by linarith
  have h2d_pi : 2 * d < Real.pi := by linarith
  -- `sin (2θ) = sin (2d)` and `cos θ = sin d`
  have hsin_eq : Real.sin (2 * θ) = Real.sin (2 * d) := by
    rw [hd]
    rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
  have hcos_eq : Real.cos θ = Real.sin d := by
    have h := Real.sin_pi_div_two_sub θ
    rw [hd]; exact h.symm
  have hsin_pos : 0 < Real.sin (2 * θ) := by
    rw [hsin_eq]; exact Real.sin_pos_of_pos_of_lt_pi h2d0 h2d_pi
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ2⟩
  have hsin_nn : 0 ≤ Real.sin (2 * θ) := le_of_lt hsin_pos
  have hcos_nn : 0 ≤ Real.cos θ := le_of_lt hcos_pos
  -- the four elementary linear bounds
  have h1 : Real.sin (2 * θ) ≤ 2 * d := by
    rw [hsin_eq]; exact Real.sin_le (le_of_lt h2d0)
  have h2 : (4 / Real.pi) * d ≤ Real.sin (2 * θ) := by
    rw [hsin_eq]
    have h := Real.mul_le_sin (x := 2 * d) (by linarith) h2d1
    have he : 2 / Real.pi * (2 * d) = 4 / Real.pi * d := by ring
    rw [he] at h; exact h
  have h3 : Real.cos θ ≤ d := by
    rw [hcos_eq]; exact Real.sin_le (le_of_lt hd0)
  have h4 : (2 / Real.pi) * d ≤ Real.cos θ := by
    rw [hcos_eq]; exact Real.mul_le_sin (le_of_lt hd0) hd_pi2
  have h4nn : 0 ≤ (4 / Real.pi) * d := by positivity
  refine ⟨h1, h2, h3, h4, hsin_pos, hcos_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(2d)^{-q} ≤ wq q θ`: the exponent `-q` is negative and `sin (2θ) ≤ 2d`
    have h := Real.rpow_le_rpow_of_nonpos hsin_pos h1 (by linarith : -q ≤ 0)
    simpa [Work.FTS.EllipticEst.AngAWeak.wq] using h
  · -- `wq q θ ≤ ((4/π)d)^{-q}`: the exponent `-q` is negative and `(4/π)d ≤ sin (2θ)`
    have hpos4 : 0 < (4 / Real.pi) * d := by positivity
    have h := Real.rpow_le_rpow_of_nonpos hpos4 h2 (by linarith : -q ≤ 0)
    simpa [Work.FTS.EllipticEst.AngAWeak.wq] using h
  · -- `(wq q θ)⁻¹ ≤ 1` since `wq q θ ≥ 1`
    exact inv_le_one_of_one_le₀
      (Work.FTS.EllipticEst.AngAWeak.one_le_wq hq ⟨hθpos, hθ2⟩)
  · -- `cos θ · sin(2θ)² ≤ 4d³`
    have hs2 : Real.sin (2 * θ) ^ 2 ≤ (2 * d) ^ 2 := by
      have h := mul_self_le_mul_self hsin_nn h1
      simpa [pow_two] using h
    have h := mul_le_mul h3 hs2 (sq_nonneg _) (le_of_lt hd0)
    linarith [h, show d * (2 * d) ^ 2 = 4 * d ^ 3 by ring]
  · -- `(32/π³)d³ ≤ cos θ · sin(2θ)²`
    have hs2 : ((4 / Real.pi) * d) ^ 2 ≤ Real.sin (2 * θ) ^ 2 := by
      have h := mul_self_le_mul_self h4nn h2
      simpa [pow_two] using h
    have h := mul_le_mul h4 hs2 (sq_nonneg _) hcos_nn
    linarith [h, show (2 / Real.pi) * d * ((4 / Real.pi) * d) ^ 2
        = (32 / Real.pi ^ 3) * d ^ 3 by ring]
  · -- `(8/π²)d² ≤ cos θ · sin(2θ)`
    have h := mul_le_mul h4 h2 h4nn hcos_nn
    linarith [h, show (2 / Real.pi) * d * ((4 / Real.pi) * d)
        = (8 / Real.pi ^ 2) * d ^ 2 by ring]

end Work.FTS.EllipticEst.AngAWeak.SRSAux
