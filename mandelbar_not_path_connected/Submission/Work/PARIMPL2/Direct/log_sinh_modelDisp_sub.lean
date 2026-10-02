import Mathlib
import Submission.Work.Implosion.Approx.approxEcal_step
import Submission.Work.Implosion.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- If `x` and `y` both have positive real part then the sum of their principal
arguments lies in `(-π, π]`.  (Each argument lies in `(-π/2, π/2)`.) -/
private lemma arg_add_mem_Ioc_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    x.arg + y.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
  have hx' : |x.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have hy' : |y.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy)
  have h : |x.arg + y.arg| < Real.pi := by
    calc |x.arg + y.arg| ≤ |x.arg| + |y.arg| := abs_add_le _ _
      _ < Real.pi / 2 + Real.pi / 2 := by linarith
      _ = Real.pi := by ring
  obtain ⟨hl, hr⟩ := abs_lt.mp h
  exact ⟨hl, le_of_lt hr⟩

/-- `exp (-z)` has positive real part when `‖z‖ < π/2`. -/
private lemma exp_neg_re_pos {z : ℂ} (hz : ‖z‖ < Real.pi / 2) :
    0 < (Complex.exp (-z)).re := by
  rw [Complex.exp_re]
  have him : |(-z).im| < Real.pi / 2 := by
    rw [Complex.neg_im, abs_neg]
    exact lt_of_le_of_lt (Complex.abs_im_le_norm z) hz
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ?_)
  rw [Set.mem_Ioo]
  exact abs_lt.mp him

/-- `log (exp (-z)) = -z` for `‖z‖ < π/2`. -/
private lemma log_exp_neg {z : ℂ} (hz : ‖z‖ < Real.pi / 2) :
    Complex.log (Complex.exp (-z)) = -z := by
  have him : |(-z).im| < Real.pi / 2 := by
    rw [Complex.neg_im, abs_neg]
    exact lt_of_le_of_lt (Complex.abs_im_le_norm z) hz
  obtain ⟨h1, h2⟩ := abs_lt.mp him
  exact Complex.log_exp (by linarith) (by linarith)

theorem log_sinh_modelDisp_sub (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ha : a ≠ 0)
    (hW0 : 0 < (Complex.sinh (a * u) / a).re)
    (hW1 : 0 < (Complex.sinh (a * (u + Work.Implosion.modelDisp a h u)) / a).re)
    (hA1 : 1 + Work.Implosion.dispNum1 a h u ≠ 0)
    (hA2 : 1 + Work.Implosion.dispNum2 a h u ≠ 0)
    (hA2re : 0 < (1 + Work.Implosion.dispNum2 a h u).re)
    (hE : Work.Implosion.ecalE a u ≠ 1)
    (hε : ‖a * Work.Implosion.modelDisp a h u‖ < Real.pi / 2) :
    Complex.log (Complex.sinh (a * (u + Work.Implosion.modelDisp a h u)) / a)
      - Complex.log (Complex.sinh (a * u) / a)
      = -(a * Work.Implosion.modelDisp a h u)
        - Complex.log (1 + Work.Implosion.dispNum2 a h u) := by
  -- The exact algebraic identity: `sinh(a(u+Φ))/a · (1+A₂) = sinh(a u)/a · e^{-aΦ}`.
  have hid := Work.Implosion.Approx.sinh_modelDisp_identity a h u ha hA1 hA2 hE
  have hW1ne : Complex.sinh (a * (u + Work.Implosion.modelDisp a h u)) / a ≠ 0 := by
    intro hh
    have : (0 : ℝ) < 0 := by simpa [hh] using hW1
    exact lt_irrefl 0 this
  have hW0ne : Complex.sinh (a * u) / a ≠ 0 := by
    intro hh
    have : (0 : ℝ) < 0 := by simpa [hh] using hW0
    exact lt_irrefl 0 this
  have harg1 : (Complex.sinh (a * (u + Work.Implosion.modelDisp a h u)) / a).arg
      + (1 + Work.Implosion.dispNum2 a h u).arg ∈ Set.Ioc (-Real.pi) Real.pi :=
    arg_add_mem_Ioc_of_re_pos hW1 hA2re
  have harg2 : (Complex.sinh (a * u) / a).arg
      + (Complex.exp (-(a * Work.Implosion.modelDisp a h u))).arg
        ∈ Set.Ioc (-Real.pi) Real.pi :=
    arg_add_mem_Ioc_of_re_pos hW0 (exp_neg_re_pos hε)
  have hA : Complex.log (Complex.sinh (a * (u + Work.Implosion.modelDisp a h u)) / a
        * (1 + Work.Implosion.dispNum2 a h u))
      = Complex.log (Complex.sinh (a * (u + Work.Implosion.modelDisp a h u)) / a)
        + Complex.log (1 + Work.Implosion.dispNum2 a h u) :=
    Complex.log_mul hW1ne hA2 harg1
  have hB : Complex.log (Complex.sinh (a * u) / a
        * Complex.exp (-(a * Work.Implosion.modelDisp a h u)))
      = Complex.log (Complex.sinh (a * u) / a)
        + Complex.log (Complex.exp (-(a * Work.Implosion.modelDisp a h u))) :=
    Complex.log_mul hW0ne (Complex.exp_ne_zero _) harg2
  have hC : Complex.log (Complex.exp (-(a * Work.Implosion.modelDisp a h u)))
      = -(a * Work.Implosion.modelDisp a h u) := log_exp_neg hε
  have hkey : Complex.log (Complex.sinh (a * (u + Work.Implosion.modelDisp a h u)) / a)
        + Complex.log (1 + Work.Implosion.dispNum2 a h u)
      = Complex.log (Complex.sinh (a * u) / a)
        + (-(a * Work.Implosion.modelDisp a h u)) := by
    rw [← hA, hid, hB, hC]
  calc Complex.log (Complex.sinh (a * (u + Work.Implosion.modelDisp a h u)) / a)
        - Complex.log (Complex.sinh (a * u) / a)
      = (Complex.log (Complex.sinh (a * (u + Work.Implosion.modelDisp a h u)) / a)
          + Complex.log (1 + Work.Implosion.dispNum2 a h u))
        - (Complex.log (Complex.sinh (a * u) / a)
          + Complex.log (1 + Work.Implosion.dispNum2 a h u)) := by ring
    _ = -(a * Work.Implosion.modelDisp a h u)
        - Complex.log (1 + Work.Implosion.dispNum2 a h u) := by rw [hkey]; ring

end Work.PARIMPL2.Direct
