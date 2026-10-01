/-
# ZeroFreeTables — XY/XYEngineDefs

Vocabulary for the `F`-method derivation of the order-2 `λ₁`-estimate
(`Work.ZeroFreeTables.XY.FMethodOrd2`): Heath-Brown's `K`-sum of §§5–9 evaluated with the
test function `xyT = tf72T (4/3)` of `XYDefs`, together with the elementary
identifications of `xyT`'s data (`x₀ = 3/2`, `f 0 = 64/45`) and of the Laplace transform
(`xyF`, `xyRe`) as real / oscillatory integrals.

This is the shared interface of the pieces of that derivation.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.XY

/-- Heath-Brown's `K`-sum `K(s,χ) = Σ_n Λ(n) Re(χ(n)/n^s) f(log n / L)` at the point
`s = β + i t`, with weight `f` and smoothing parameter `L`. -/
def Kxy {q : ℕ} [NeZero q] (f : ℝ → ℝ) (L β t : ℝ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
    ((χ (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (t : ℂ) * Complex.I)).re) * f (Real.log n / L)

/-- The `K`-sum of the derivation for the principal character mod `q`, at `s = β + i t`. -/
def Kxy0 (q : ℕ) [NeZero q] (f : ℝ → ℝ) (L β t : ℝ) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
    ((1 : DirichletCharacter ℂ q) (n : ZMod q) / (n : ℂ) ^ ((β : ℂ) + (t : ℂ) * Complex.I)).re *
      f (Real.log n / L)

theorem Kxy_one_eq_Kxy0 (q : ℕ) [NeZero q] (f : ℝ → ℝ) (L β t : ℝ) :
    Kxy f L β t (1 : DirichletCharacter ℂ q) = Kxy0 q f L β t := rfl

/-- The right end of `xyT`'s support is `3/2` (HB Lemma 7.2 with `λ = 4/3`). -/
theorem xyT_x0 : xyT.x₀ = 3 / 2 := by
  show 2 / (4 / 3 : ℝ) = 3 / 2
  norm_num

/-- `f 0 = 64/45` for the test function of `XYDefs`. -/
theorem xyT_f_zero : xyT.f 0 = 64 / 45 := by
  show tf72f (4 / 3) 0 = 64 / 45
  rw [tf72f_at_zero (4 / 3) (by norm_num)]
  norm_num

/-- `xyF` is the Laplace transform of `xyT`, as a real integral. -/
theorem xyF_eq_integral (x : ℝ) :
    xyF x = ∫ u in (0:ℝ)..(3 / 2), Real.exp (-(x * u)) * xyT.f u := by
  rw [xyF, TestFn_F_eq_integral, xyT_x0]

/-- `xyRe x t = Re F (x + i t)` as an oscillatory real integral. -/
theorem xyRe_eq_integral (x t : ℝ) :
    xyRe x t = ∫ u in (0:ℝ)..(3 / 2), Real.cos (t * u) * (Real.exp (-(x * u)) * xyT.f u) := by
  have h1 : ∀ u : ℝ, (-(((x : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))).re = -(x * u) := by
    intro u
    simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have h2 : ∀ u : ℝ, (-(((x : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))).im = -(t * u) := by
    intro u
    simp [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hpt : ∀ u : ℝ,
      (Complex.exp (-(((x : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))) * ((xyT.f u : ℝ) : ℂ)).re
        = Real.cos (t * u) * (Real.exp (-(x * u)) * xyT.f u) := by
    intro u
    rw [Complex.mul_re, Complex.exp_re, Complex.exp_im, h1 u, h2 u, Real.cos_neg, Real.sin_neg]
    norm_num
    ring
  have hint1 : IntervalIntegrable (fun u : ℝ =>
      Complex.exp (-(((x : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))) * ((xyT.f u : ℝ) : ℂ))
      MeasureTheory.volume (0 : ℝ) xyT.x₀ := by
    have hlin : Continuous (fun u : ℝ => -(((x : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))) := by
      fun_prop
    exact ContinuousOn.intervalIntegrable_of_Icc (le_of_lt xyT.x₀_pos)
      ((Complex.continuous_exp.comp hlin).continuousOn.mul
        (Complex.continuous_ofReal.comp_continuousOn
          (xyT.f_cont.mono (fun u hu => hu.1))))
  have hstep : (∫ u in (0:ℝ)..xyT.x₀,
        Complex.exp (-(((x : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))) * ((xyT.f u : ℝ) : ℂ)).re
      = ∫ u in (0:ℝ)..xyT.x₀,
          Real.cos (t * u) * (Real.exp (-(x * u)) * xyT.f u) := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint1]
    exact intervalIntegral.integral_congr (fun u _ => by rw [Complex.reCLM_apply, hpt u])
  calc xyRe x t = (xyT.Fc ((x : ℝ) + (t : ℝ) * Complex.I)).re := rfl
    _ = (∫ u in (0:ℝ)..xyT.x₀,
          Complex.exp (-(((x : ℂ) + (t : ℂ) * Complex.I) * (u : ℂ))) * ((xyT.f u : ℝ) : ℂ)).re := by
          rw [xyT.Fc_spec]
    _ = _ := hstep
    _ = ∫ u in (0:ℝ)..(3 / 2), Real.cos (t * u) * (Real.exp (-(x * u)) * xyT.f u) := by
          rw [xyT_x0]

end Work.ZeroFreeTables.XY
