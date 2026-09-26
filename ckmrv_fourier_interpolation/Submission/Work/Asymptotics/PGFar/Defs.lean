/-
# The `q`-expansion dictionary for the far-region pair gate

This module fixes the two local parameters used throughout the far-region analysis of
`Work.Asymptotics.pair_gate_far`:

* `nomeQ w = e^{2πi w}` (`Work.Kernels.qParamFun`), the classical nome;
* `nomeE w = e^{πi w}` (`Work.Residues.Ept`), its square root,

together with their elementary norm identities and the strip predicate `Strip` on which all the
quantitative estimates of this chapter are stated.

`Strip w` means `|Re w| ≤ 1/2` and `2 ≤ Im w`: the fundamental strip in the `T`-direction at
height `≥ 2`, where `‖nomeQ w‖ ≤ rhoStrip = e^{-4π}` is extremely small.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.Kaxis24_pair_gate

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-- The nome `q = e^{2πi w}`. -/
def nomeQ (w : UpperHalfPlane) : ℂ := Work.Kernels.qParamFun w

/-- The square root of the nome, `e = e^{πi w}`. -/
def nomeE (w : UpperHalfPlane) : ℂ := Work.Residues.Ept w

/-- The fundamental strip of the far region: `|Re w| ≤ 1/2` and `2 ≤ Im w`. -/
def Strip (w : UpperHalfPlane) : Prop := |w.re| ≤ 1 / 2 ∧ 2 ≤ w.im

lemma nomeQ_def (w : UpperHalfPlane) : nomeQ w = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)) := rfl

lemma nomeE_def (w : UpperHalfPlane) : nomeE w = Complex.exp ((Real.pi : ℂ) * Complex.I * (w : ℂ)) := rfl

lemma nomeE_sq (w : UpperHalfPlane) : nomeQ w = nomeE w ^ 2 := by
  rw [nomeQ_def, nomeE_def, sq, ← Complex.exp_add]
  congr 1
  ring

lemma norm_nomeE (w : UpperHalfPlane) : ‖nomeE w‖ = Real.exp (-(Real.pi * w.im)) :=
  Work.Residues.norm_Ept w

lemma norm_nomeQ (w : UpperHalfPlane) : ‖nomeQ w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
  rw [nomeQ_def, Complex.norm_exp]
  congr 1
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (w : ℂ)
      = ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (w : ℂ)) by push_cast; ring]
  rw [Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

/-- `rhoStrip = e^{-4π}`, the value of `‖nomeQ‖` on the lower boundary of the strip. -/
def rhoStrip : ℝ := Real.exp (-(4 * Real.pi))

lemma rhoStrip_pos : 0 < rhoStrip := Real.exp_pos _

lemma norm_nomeQ_le_rhoStrip (w : UpperHalfPlane) (h : 2 ≤ w.im) : ‖nomeQ w‖ ≤ rhoStrip :=
  le_of_eq_of_le (norm_nomeQ w) (Real.exp_le_exp.mpr (by nlinarith [h, Real.pi_pos]))

lemma norm_nomeE_le (w : UpperHalfPlane) (h : 2 ≤ w.im) : ‖nomeE w‖ ≤ Real.exp (-(2 * Real.pi)) :=
  le_of_eq_of_le (norm_nomeE w) (Real.exp_le_exp.mpr (by nlinarith [h, Real.pi_pos]))

lemma norm_nomeQ_sq (w : UpperHalfPlane) : ‖nomeQ w‖ = ‖nomeE w‖ ^ 2 := by
  rw [nomeE_sq, norm_pow]

/-- `(t + 1/2) e^{-2π t} ≤ (5/2) e^{-4π}` for `t ≥ 2`. -/
lemma add_half_mul_exp_le (t : ℝ) (ht : 2 ≤ t) :
    (t + 1 / 2) * Real.exp (-(2 * Real.pi * t)) ≤ (5 / 2) * rhoStrip := by
  have h1 : t + 1 / 2 ≤ (5 / 2) * Real.exp (2 * Real.pi * (t - 2)) := by
    have h2 : 1 + 2 * Real.pi * (t - 2) ≤ Real.exp (2 * Real.pi * (t - 2)) := by
      have := Real.add_one_le_exp (2 * Real.pi * (t - 2))
      linarith
    have h3 : 0 ≤ t - 2 := by linarith
    have h4 : (5 / 2) * (1 + 2 * Real.pi * (t - 2)) = 5 / 2 + (5 * Real.pi) * (t - 2) := by ring
    have h5 : t + 1 / 2 ≤ 5 / 2 + (5 * Real.pi) * (t - 2) := by
      nlinarith [Real.pi_gt_three, h3]
    calc t + 1 / 2 ≤ 5 / 2 + (5 * Real.pi) * (t - 2) := h5
      _ = (5 / 2) * (1 + 2 * Real.pi * (t - 2)) := h4.symm
      _ ≤ (5 / 2) * Real.exp (2 * Real.pi * (t - 2)) := by linarith
  calc (t + 1 / 2) * Real.exp (-(2 * Real.pi * t))
      ≤ (5 / 2) * Real.exp (2 * Real.pi * (t - 2)) * Real.exp (-(2 * Real.pi * t)) := by
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = (5 / 2) * rhoStrip := by
        rw [rhoStrip, mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- On the strip, `‖w‖ ‖nomeQ w‖ ≤ 3 rhoStrip`.  This is the only place where the boundedness of the
real part is used: `‖w‖ ≤ Im w + 1/2` and `(t+1/2) e^{-2πt}` decreases for `t ≥ 2`. -/
lemma norm_w_mul_nomeQ_le (w : UpperHalfPlane) (h : Strip w) :
    ‖(w : ℂ)‖ * ‖nomeQ w‖ ≤ 3 * rhoStrip := by
  obtain ⟨hre, him⟩ := h
  have hnorm : ‖(w : ℂ)‖ ≤ w.im + 1 / 2 := by
    rw [Complex.norm_def, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    have h2 : w.re * w.re + w.im * w.im ≤ (w.im + 1 / 2) * (w.im + 1 / 2) := by
      nlinarith [abs_le.mp hre]
    calc Real.sqrt (w.re * w.re + w.im * w.im) ≤ Real.sqrt ((w.im + 1 / 2) * (w.im + 1 / 2)) :=
          Real.sqrt_le_sqrt h2
      _ = w.im + 1 / 2 := by
            rw [Real.sqrt_mul_self (by linarith)]
  have hq : ‖nomeQ w‖ = Real.exp (-(2 * Real.pi * w.im)) := norm_nomeQ w
  calc ‖(w : ℂ)‖ * ‖nomeQ w‖ ≤ (w.im + 1 / 2) * Real.exp (-(2 * Real.pi * w.im)) := by
        rw [hq]
        exact mul_le_mul_of_nonneg_right hnorm (Real.exp_nonneg _)
    _ ≤ (5 / 2) * rhoStrip := add_half_mul_exp_le w.im him
    _ ≤ 3 * rhoStrip := by linarith [rhoStrip_pos]

/-- `rhoStrip = e^{-4π} ≤ 1/280000`.  Proved from `e^{3.14} ≥ 23.1` (a 12-term Taylor sum) and
`3.14 ≤ π`: `e^{4π} ≥ e^{12.56} = (e^{3.14})^4 ≥ 23.1^4 ≥ 280000`. -/
lemma rhoStrip_le : rhoStrip ≤ 1 / 280000 := by
  rw [rhoStrip, show (1 : ℝ) / 280000 = (280000 : ℝ)⁻¹ by norm_num, Real.exp_neg]
  rw [inv_le_inv₀ (Real.exp_pos _) (by norm_num)]
  have h1 : (12.56 : ℝ) ≤ 4 * Real.pi := by nlinarith [Real.pi_gt_d20]
  refine le_trans ?_ (Real.exp_le_exp.mpr h1)
  have h314 : (3.14 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_d20]
  have hsum : (23.1 : ℝ) ≤ Real.exp 3.14 := by
    have h := Real.sum_le_exp_of_nonneg (x := (3.14 : ℝ)) (by norm_num) 12
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hpow : (23.1 : ℝ) ^ 4 ≤ (Real.exp 3.14) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hsum 4
  have hexp : (Real.exp 3.14) ^ 4 = Real.exp 12.56 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hexp] at hpow
  linarith

/-- Elementary strip facts: with `Q = ‖nomeQ w‖`, `R = ‖(w:ℂ)‖` and `Strip w` one has
`Q ≤ 1/280000`, `R Q ≤ 3/280000` and `(1+R)Q ≤ 4/280000`. -/
lemma strip_facts (w : UpperHalfPlane) (hw : Strip w) :
    ‖nomeQ w‖ ≤ 1 / 280000 ∧ ‖(w : ℂ)‖ * ‖nomeQ w‖ ≤ 3 / 280000
      ∧ (1 + ‖(w : ℂ)‖) * ‖nomeQ w‖ ≤ 4 / 280000 := by
  have hQle : ‖nomeQ w‖ ≤ rhoStrip := norm_nomeQ_le_rhoStrip w hw.2
  have hRQ : ‖(w : ℂ)‖ * ‖nomeQ w‖ ≤ 3 * rhoStrip := norm_w_mul_nomeQ_le w hw
  have hrho : rhoStrip ≤ 1 / 280000 := rhoStrip_le
  refine ⟨by linarith, by linarith, ?_⟩
  nlinarith [hQle, hrho, hRQ]


end

end Work.Asymptotics
