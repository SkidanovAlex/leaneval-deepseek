import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs

/-!
# B5 (interface v2): the family `ℓ` is the standard zero section far away

`Work.RPB.B5.lagData_std` proved the `std` field of `LagFamily` against the *old* interface
`LagData CI a L` (with an unused `IsLevelData` parameter).  The assembly now uses the interface
`Work.RPB.B5.LagData CI a` of `Submission/Work/RPB/B5/LagData.lean`; this file restates and
re-proves the same statement against it.  None of the new fields (`κ`, `ρh`, the junction
hypotheses, …) are used: the proof only needs `hfar` and `hσ₂`.

Content.  The family is `ℓ τ (x,t) = lagPt W Γc Ac rho τ x t`, which is the collar
`levelPt (Γc τ σ t) σ (Ac τ σ t)` with `σ = sig x = x²/2 - 1` for `x ≤ -√2` and the `τ_π`-image of
it for `x > 0`.  Beyond the collar's far end `σ ≥ σ₂` the collar is the standard family of circles
`Γc τ σ t = √(2+2σ)·e^{i(t-π/2)}`, `Ac τ σ t = t` (`LagData.hfar`).  Since the level attached to `x`
satisfies `2 + 2·sig x = x²`, i.e. `√(2+2σ) = |x|`, the reduced coordinate of the collar point is
`e^{-it}·√(2+2σ)·e^{i(t-π/2)} = -i·√(2+2σ) = -i·|x|`, of real part `0` and imaginary part `-|x|`:
on the left half `x ≤ 0` this is exactly `stdZ x t`; on the right half the family is `τ_π` of the
reflected collar, and `τ_π` sends `q₁ = -|x|` to `q₁ = x`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Elementary complex and trigonometric identities -/

/-- `e^{-iπ/2} = -i`. -/
private lemma exp_neg_pi_div_two_mul_I :
    Complex.exp (((-(Real.pi / 2)) : ℝ) * (Complex.I : ℂ)) = -(Complex.I) := by
  rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  norm_num

/-- `e^{-it} · e^{i(t-π/2)} = -i`. -/
private lemma exp_neg_mul_exp_sub (t : ℝ) :
    Complex.exp (-(t : ℂ) * Complex.I) * Complex.exp ((t - Real.pi / 2 : ℂ) * Complex.I)
      = -(Complex.I) := by
  rw [← Complex.exp_add]
  have h : -(t : ℂ) * Complex.I + (t - Real.pi / 2 : ℂ) * Complex.I
      = (((-(Real.pi / 2)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, exp_neg_pi_div_two_mul_I]

/-- The collar point at level `σ` on the standard circle `√(2+2σ)·e^{i(t-π/2)}` with phase `t` is
the zero-section point with coordinate `-√(2+2σ)` and angle `t`. -/
private lemma levelPt_circle_stdZ (σ t : ℝ) (hσ : 0 ≤ 2 + 2 * σ) :
    Work.RPV.levelPt (((Real.sqrt (2 + 2 * σ) : ℝ) : ℂ) * Complex.exp ((t - Real.pi / 2) * Complex.I))
        σ t
      = ((-(Real.sqrt (2 + 2 * σ)), t), ((0 : ℝ), 0)) := by
  set u : ℂ := ((Real.sqrt (2 + 2 * σ) : ℝ) : ℂ) * Complex.exp ((t - Real.pi / 2) * Complex.I) with hu
  have hnorm : ‖u‖ ^ 2 = 2 + 2 * σ := by
    rw [hu, ← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    have h1 : Complex.normSq (Complex.exp ((t - Real.pi / 2) * Complex.I)) = 1 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
      simp
    rw [h1, mul_one, Real.mul_self_sqrt hσ]
  have hkey : Complex.exp (-(t : ℂ) * Complex.I) * u
      = -(((Real.sqrt (2 + 2 * σ) : ℝ)) : ℂ) * Complex.I := by
    rw [hu]
    calc Complex.exp (-(t : ℂ) * Complex.I) *
          (((Real.sqrt (2 + 2 * σ) : ℝ) : ℂ) * Complex.exp ((t - Real.pi / 2) * Complex.I))
        = (((Real.sqrt (2 + 2 * σ) : ℝ) : ℂ)) *
            (Complex.exp (-(t : ℂ) * Complex.I) * Complex.exp ((t - Real.pi / 2) * Complex.I)) := by
          ring
      _ = (((Real.sqrt (2 + 2 * σ) : ℝ) : ℂ)) * (-(Complex.I)) := by
          rw [exp_neg_mul_exp_sub t]
      _ = -(((Real.sqrt (2 + 2 * σ) : ℝ)) : ℂ) * Complex.I := by ring
  have him : (-(((Real.sqrt (2 + 2 * σ) : ℝ)) : ℂ) * Complex.I).im = -(Real.sqrt (2 + 2 * σ)) := by
    simp
  have hre : (-(((Real.sqrt (2 + 2 * σ) : ℝ)) : ℂ) * Complex.I).re = 0 := by simp
  simp only [Work.RPV.levelPt]
  rw [hkey, him, hre, hnorm]
  norm_num
  ring

/-- `τ_π` sends `((-r, s), 0)` to `((r, s+π), 0)`. -/
private lemma tau_pi_neg (r s : ℝ) : Work.RPV.tau Real.pi (((-r, s), ((0:ℝ), 0)) : Work.RPV.PS)
    = ((r, s + Real.pi), ((0:ℝ), 0)) := by
  simp only [Work.RPV.tau, Real.cos_pi, Real.sin_pi]
  norm_num

/-! ## The level `σ = sig x` determines `√(2+2σ) = |x|` -/

/-- `2 + 2·sig x = x²`. -/
private lemma two_add_two_sig (x : ℝ) : 2 + 2 * sig x = x ^ 2 := by
  simp only [sig]; ring

/-- For `x ≤ 0`, `-√(2+2·sig x) = x`. -/
private lemma neg_sqrt_two_add_two_sig (x : ℝ) (hx : x ≤ 0) :
    -(Real.sqrt (2 + 2 * sig x)) = x := by
  rw [two_add_two_sig x, Real.sqrt_sq_eq_abs, abs_of_nonpos hx, neg_neg]

/-- For `x ≥ 0`, `√(2+2·sig x) = x`. -/
private lemma pos_sqrt_two_add_two_sig (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (2 + 2 * sig x) = x := by
  rw [two_add_two_sig x, Real.sqrt_sq_eq_abs, abs_of_nonneg hx]

/-! ## The `std` field -/

theorem lagData_std_v2 (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t,
      Real.sqrt (2 + 2 * D.σ₂) ≤ |x| →
        Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho τ x t = Work.RPV.stdZ x t := by
  intro τ hτ x t hx
  have hσ₂ : 0 < D.σ₂ := D.hσ₂
  -- `√2 ≤ √(2+2σ₂) ≤ |x|`, hence `x² ≥ 2+2σ₂` and `σ = sig x ≥ σ₂`
  have hsqrt2 : Real.sqrt 2 ≤ Real.sqrt (2 + 2 * D.σ₂) := Real.sqrt_le_sqrt (by linarith)
  have hx2 : 2 + 2 * D.σ₂ ≤ x ^ 2 := by
    have h1 : (Real.sqrt (2 + 2 * D.σ₂)) ^ 2 ≤ |x| ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
    rwa [Real.sq_sqrt (by linarith), sq_abs] at h1
  have hsig : D.σ₂ ≤ sig x := by simp only [sig]; linarith
  have hσnn : (0 : ℝ) ≤ 2 + 2 * sig x := by rw [two_add_two_sig x]; positivity
  by_cases hxle : x ≤ 0
  · -- ## left half: the collar itself
    have hxle' : x ≤ -Real.sqrt 2 := by
      have h := hx; rw [abs_of_nonpos hxle] at h
      linarith
    rw [lagPt, if_pos hxle, basePt, if_pos hxle', collarPt,
      (D.hfar τ hτ (sig x) hsig t).1, (D.hfar τ hτ (sig x) hsig t).2,
      levelPt_circle_stdZ (sig x) t hσnn]
    simp only [Work.RPV.stdZ, neg_sqrt_two_add_two_sig x hxle]
  · -- ## right half: `τ_π` of the reflected collar
    have hxpos : 0 < x := not_le.mp hxle
    have hxge : Real.sqrt 2 ≤ x := by
      have h := hx; rw [abs_of_pos hxpos] at h
      linarith
    have hnxle : -x ≤ -Real.sqrt 2 := by linarith
    have hs : sig (-x) = sig x := by simp only [sig]; ring
    rw [lagPt, if_neg (not_le.mpr hxpos), basePt, if_pos hnxle, collarPt, hs,
      (D.hfar τ hτ (sig x) hsig (t - Real.pi)).1,
      (D.hfar τ hτ (sig x) hsig (t - Real.pi)).2,
      levelPt_circle_stdZ (sig x) (t - Real.pi) hσnn, tau_pi_neg]
    simp only [Work.RPV.stdZ, pos_sqrt_two_add_two_sig x hxpos.le, sub_add_cancel]

end Work.RPB.B5
