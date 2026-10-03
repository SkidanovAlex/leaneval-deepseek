import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup

/-!
# `Work.Pert.Ksub2.exp_ne_one_of_tauC_bounded`

**The gate `Qm ξ α` contains no pole of `τ_f` whenever `τ_f` maps the whole gate into a bounded
ball.**  Here `τ_f w = σ / (1 - exp (-2πi α w))` (`Work.Pert.tauC`) is the universal cover
`ℂ → ℂ ∖ {0, σ}` of Lemma A.1.5, so its poles are exactly the points where
`exp (-2πi α w) = 1`; the two gate regions `Qm`, `Qp` of §4.2 are open subsets of the `w`-plane on
which the lift `F_f = liftF` of `f` is a near-translation.

The statement is a genuine *dynamical* fact (it is what lets `PertData` know that the gate of a
perturbation carries no fixed point of the deck translation):

*if `w` is such a pole then, since `Qm ξ α` is open, the whole punctured disc around `w` lies in
the gate, and along `z = w - s/α` (`s > 0` small, `α ≠ 0`) the modulus of `τ_f` blows up:
`exp (-2πi α z) = exp (2πi s)`, so `‖τ_f z‖ = ‖σ‖ / ‖1 - exp(2πi s)‖`, and
`‖1 - exp (2πi s)‖ = 2 |sin (π s)| ≤ 2 π s → 0`.  Choosing `s` small enough (`s ≤ ‖σ‖/(4π rr)`)
forces `‖τ_f z‖ > rr`, contradicting the hypothesis that the gate is mapped into the ball of
radius `rr`.*

The only analytic input is Mathlib's `Complex.norm_exp_I_mul_ofReal_sub_one`,
`‖exp (I x) - 1‖ = ‖2 sin (x/2)‖`, which for real `s` gives `‖1 - exp (2πi s)‖ = 2|sin (π s)|`.
-/

namespace Work.Pert.Ksub2

open MandelDim Complex

noncomputable section

/-- The lower gate `Qm ξ α = Qreg (some (ξ - 1/α)) (some (-ξ))` is open (an intersection of two
open cones). -/
private lemma isOpen_Qm (ξ₁ : ℝ) (α : ℂ) : IsOpen (Work.Pert.Qm ξ₁ α) := by
  have h1 : IsOpen {z : ℂ | -|(z - ((ξ₁ : ℂ) - 1 / α)).im| < (z - ((ξ₁ : ℂ) - 1 / α)).re} :=
    isOpen_lt (continuous_abs.comp
        (Complex.continuous_im.comp (continuous_id.sub continuous_const))).neg
      (Complex.continuous_re.comp (continuous_id.sub continuous_const))
  have h2 : IsOpen {z : ℂ | (z - (-(ξ₁ : ℂ))).re < |(z - (-(ξ₁ : ℂ))).im|} :=
    isOpen_lt (Complex.continuous_re.comp (continuous_id.sub continuous_const))
      (continuous_abs.comp (Complex.continuous_im.comp (continuous_id.sub continuous_const)))
  have h3 : Work.Pert.Qm ξ₁ α =
      {z : ℂ | -|(z - ((ξ₁ : ℂ) - 1 / α)).im| < (z - ((ξ₁ : ℂ) - 1 / α)).re} ∩
        {z : ℂ | (z - (-(ξ₁ : ℂ))).re < |(z - (-(ξ₁ : ℂ))).im|} := by
    ext z
    simp [Work.Pert.Qm, MandelDim.Qreg]
  rw [h3]
  exact h1.inter h2

/-- **Exact modulus on the real axis.**  For real `s`,
`‖1 - exp (2πi s)‖ = 2 |sin (π s)|`. -/
private lemma norm_one_sub_exp_two_pi_I_ofReal (s : ℝ) :
    ‖1 - Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))‖ = 2 * |Real.sin (Real.pi * s)| := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * s)
  rw [show (2 * Real.pi * s) / 2 = Real.pi * s from by ring] at h
  have harg : 2 * (Real.pi : ℂ) * Complex.I * (s : ℂ)
      = Complex.I * ((2 * Real.pi * s : ℝ) : ℂ) := by
    push_cast; ring
  rw [norm_sub_rev, harg, h, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

theorem exp_ne_one_of_tauC_bounded {σ α : ℂ} {rr ξ : ℝ} (hrr : 0 < rr) (hσ : σ ≠ 0)
    (hα : α ≠ 0) {w : ℂ} (hw : w ∈ Work.Pert.Qm ξ α)
    (hτQ : ∀ z ∈ Work.Pert.Qm ξ α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) :
    Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1 := by
  intro hE
  -- the gate is open, hence contains a ball around `w`
  have hOpen : IsOpen (Work.Pert.Qm ξ α) := isOpen_Qm ξ α
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp hOpen) w hw
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hσpos : 0 < ‖σ‖ := norm_pos_iff.mpr hσ
  -- the step size `s`
  set s : ℝ := min (‖σ‖ / (4 * Real.pi * rr)) (min (r * ‖α‖ / 2) (1 / 4)) with hsdef
  have hs_pos : 0 < s := by
    rw [hsdef]
    exact lt_min (div_pos hσpos (by positivity))
      (lt_min (div_pos (mul_pos hr hαpos) (by norm_num)) (by norm_num))
  have hs_le1 : s ≤ ‖σ‖ / (4 * Real.pi * rr) := by
    rw [hsdef]; exact min_le_left _ _
  have hs_le2 : s ≤ r * ‖α‖ / 2 := by
    rw [hsdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hs_le3 : s ≤ 1 / 4 := by
    rw [hsdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- `z = w - s/α` is still in the gate
  have hz_mem : w - (s : ℂ) / α ∈ Work.Pert.Qm ξ α := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : w - (s : ℂ) / α - w = -((s : ℂ) / α) := by ring
    rw [hsub, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs_pos]
    rw [div_lt_iff₀ hαpos]
    nlinarith [hs_le2, hr, hαpos]
  -- at `z` the exponential takes the value `exp (2πi s)`
  have hexp : Complex.exp (-(2 * Real.pi * Complex.I * α * (w - (s : ℂ) / α)))
      = Complex.exp (2 * Real.pi * Complex.I * (s : ℂ)) := by
    have harg : -(2 * Real.pi * Complex.I * α * (w - (s : ℂ) / α))
        = -(2 * Real.pi * Complex.I * α * w) + 2 * Real.pi * Complex.I * (s : ℂ) := by
      field_simp
      ring
    rw [harg, Complex.exp_add, hE, one_mul]
  have hτ : Work.Pert.tauC σ α (w - (s : ℂ) / α)
      = σ / (1 - Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))) := by
    rw [Work.Pert.tauC, hexp]
  have hnorm : ‖1 - Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))‖
      = 2 * |Real.sin (Real.pi * s)| :=
    norm_one_sub_exp_two_pi_I_ofReal s
  -- numerical bounds on the denominator
  have hlin : 2 * |Real.sin (Real.pi * s)| ≤ 2 * (Real.pi * s) := by
    have h3 : |Real.sin (Real.pi * s)| ≤ Real.pi * s := by
      calc |Real.sin (Real.pi * s)| ≤ |Real.pi * s| := Real.abs_sin_le_abs
        _ = Real.pi * s := abs_of_nonneg (by positivity)
    linarith
  have hupp : ‖1 - Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))‖ < ‖σ‖ / rr := by
    rw [hnorm]
    have h2πs : 2 * (Real.pi * s) < ‖σ‖ / rr := by
      rw [lt_div_iff₀ hrr]
      have hb : s * (4 * Real.pi * rr) ≤ ‖σ‖ :=
        (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi * rr)).mp hs_le1
      nlinarith [hb, hσpos, hrr, Real.pi_pos, hs_pos]
    linarith
  have hpos : 0 < ‖1 - Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))‖ := by
    rw [hnorm]
    have h1 : 0 < Real.pi * s := by positivity
    have h2 : Real.pi * s < Real.pi := by nlinarith [Real.pi_pos, hs_le3]
    have h3 : 0 < Real.sin (Real.pi * s) := Real.sin_pos_of_pos_of_lt_pi h1 h2
    rw [abs_of_pos h3]; linarith
  -- `|τ_f z| > rr`, contradicting the hypothesis
  have hbig : rr < ‖Work.Pert.tauC σ α (w - (s : ℂ) / α)‖ := by
    rw [hτ, norm_div]
    refine (lt_div_iff₀ hpos).mpr ?_
    have h2 : ‖1 - Complex.exp (2 * Real.pi * Complex.I * (s : ℂ))‖ * rr < ‖σ‖ :=
      (lt_div_iff₀ hrr).mp hupp
    nlinarith [h2]
  have hmem := hτQ (w - (s : ℂ) / α) hz_mem
  rw [Metric.mem_ball, dist_zero_right] at hmem
  linarith

end

end Work.Pert.Ksub2
