import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs

/-!
# Helpers for GM Lemma 8.3 (`Work.GM.S3.R_l4`)

`Rfun W v = Σ_{t ∈ W} |v|^{it}`; for `v = e^τ` this is `Gfun W τ = Σ_{t ∈ W} e^{i t τ}`, and the
L⁴ bound of GM Lemma 8.3 is proved by writing `‖Gfun W τ‖^4` as the quadruple sum of the
exponentials `e^{i τ (t₁+t₂-t₃-t₄)}` and applying Poisson-summation-free Fourier decay of a bump.
-/

namespace Work.GM.S3

open MeasureTheory Finset Complex
open scoped BigOperators
open Submission.GM (Rfun energy Separated)

/-- `G(τ) = Σ_{t ∈ W} e^{iτt}`: the `τ = log v` form of `Rfun`. -/
noncomputable def Gfun (W : Finset ℝ) (τ : ℝ) : ℂ :=
  ∑ t ∈ W, cexp (I * ((t * τ : ℝ) : ℂ))

theorem Gfun_continuous (W : Finset ℝ) : Continuous (Gfun W) := by
  unfold Gfun
  refine continuous_finsetSum _ (fun t ht => ?_)
  have h1 : Continuous (fun τ : ℝ => (I * (t : ℂ)) * (τ : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  refine (Complex.continuous_exp.comp ?_)
  convert h1 using 2 with τ
  push_cast
  ring

theorem norm_Gfun_le_card (W : Finset ℝ) (τ : ℝ) : ‖Gfun W τ‖ ≤ (W.card : ℝ) := by
  calc ‖Gfun W τ‖ ≤ ∑ t ∈ W, ‖cexp (I * ((t * τ : ℝ) : ℂ))‖ := by
        simpa only [Gfun] using norm_sum_le (s := W)
          (f := fun t => cexp (I * ((t * τ : ℝ) : ℂ)))
    _ = ∑ _t ∈ W, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Complex.norm_exp]
        simp
    _ = (W.card : ℝ) := by simp

/-- `Rfun W (e^τ) = Gfun W τ`. -/
theorem Rfun_eq_Gfun_exp (W : Finset ℝ) (τ : ℝ) :
    Rfun W (Real.exp τ) = Gfun W τ := by
  unfold Gfun
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [show (|Real.exp τ| : ℝ) = Real.exp τ from abs_of_pos (Real.exp_pos τ)]
  have hlog : Complex.log (((Real.exp τ : ℝ)) : ℂ) = ((τ : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.log_re, Complex.ofReal_re, Real.log_exp]
    · rw [Complex.log_im, Complex.arg_ofReal_of_nonneg (Real.exp_pos τ).le]
      simp
  have hne : (((Real.exp τ : ℝ)) : ℂ) ≠ 0 := by simp
  rw [Complex.cpow_def, if_neg hne, hlog]
  congr 1
  push_cast
  ring

/-- `Rfun W ·` is continuous on the positive reals (it is `Gfun W ∘ log` there). -/
theorem Rfun_continuousOn_Ioi (W : Finset ℝ) :
    ContinuousOn (fun v : ℝ => Rfun W v) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun v : ℝ => Gfun W (Real.log v)) (Set.Ioi 0) :=
    (Gfun_continuous W).comp_continuousOn
      (Real.continuousOn_log.mono (by intro x hx; exact ne_of_gt hx))
  refine hcont.congr ?_
  intro v hv
  show Rfun W v = Gfun W (Real.log v)
  calc Rfun W v = Rfun W (Real.exp (Real.log v)) := by rw [Real.exp_log hv]
    _ = Gfun W (Real.log v) := Rfun_eq_Gfun_exp W (Real.log v)

/-- Change of variables `v = e^τ`: `∫_1^2 g = ∫_0^{log 2} e^τ g(e^τ) dτ`. -/
theorem integral_exp_subst (g : ℝ → ℝ) :
    (∫ v in (1 : ℝ)..2, g v) = ∫ τ in (0 : ℝ)..(Real.log 2), Real.exp τ * g (Real.exp τ) := by
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
      (a := (0 : ℝ)) (b := Real.log 2) (f := Real.exp) (f' := Real.exp) (g := g)
      Real.continuous_exp.continuousOn
      (fun x hx => Real.hasDerivAt_exp x)
      (fun x hx => (Real.exp_pos x).le)
  rw [Real.exp_zero, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  exact h.symm

/-- The quadruple set `W × W × W × W` (as in the definition of `energy`). -/
def Quad (W : Finset ℝ) : Finset (ℝ × ℝ × ℝ × ℝ) := W ×ˢ W ×ˢ W ×ˢ W

/-- The additive frequency `q₁ + q₂ - q₃ - q₄` of a quadruple. -/
def qs (q : ℝ × ℝ × ℝ × ℝ) : ℝ := q.1 + q.2.1 - q.2.2.1 - q.2.2.2

theorem Quad_card (W : Finset ℝ) : (Quad W).card = W.card ^ 4 := by
  rw [Quad, Finset.card_product, Finset.card_product, Finset.card_product]
  ring

theorem energy_eq_filter (W : Finset ℝ) :
    ((Quad W).filter (fun q => |qs q| ≤ 1)).card = energy W := by
  classical
  unfold Submission.GM.energy Quad qs
  rfl

theorem one_le_energy {W : Finset ℝ} (hW : W.Nonempty) : 1 ≤ energy W := by
  have h := card_mul_self_le_energy W
  have hc : 1 ≤ W.card := hW.card_pos
  have h2 : 1 ≤ W.card * W.card := by nlinarith
  exact le_trans h2 h

end Work.GM.S3
