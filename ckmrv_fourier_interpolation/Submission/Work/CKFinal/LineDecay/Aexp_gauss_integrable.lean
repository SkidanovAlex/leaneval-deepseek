import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.continuationDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.paperLayer_agreement

namespace Work.CKFinal.LineDecay

open MeasureTheory

/-- `t ↦ t ^ k * exp (-(c * t))` is integrable on `[1, ∞)` for `c > 0` and any `k : ℕ`.
This is the standard half-line decay of a polynomial times an exponential; it follows from the
`Γ`-integral `∫_0^∞ x ^{s-1} e^{-b x} dx = Γ s / b ^ s`. -/
private lemma integrableOn_pow_mul_exp_neg_mul_Ici_one {c : ℝ} (hc : 0 < c) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(c * t))) (Set.Ici 1) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := c)
    (by have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k; linarith) (by norm_num) hc
  refine (h.congr_fun ?_ measurableSet_Ioi).mono_set ?_
  · intro x hx
    simp only [Real.rpow_natCast, Real.rpow_one, neg_mul]
  · intro x hx
    simp only [Set.mem_Ioi, Set.mem_Ici] at hx ⊢
    linarith

private lemma integrableOn_exp_neg_mul_Ici_one {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(c * t))) (Set.Ici 1) := by
  refine (integrableOn_pow_mul_exp_neg_mul_Ici_one hc 0).congr_fun ?_ measurableSet_Ici
  intro x hx
  simp

private lemma integrableOn_mul_exp_neg_mul_Ici_one {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t * Real.exp (-(c * t))) (Set.Ici 1) := by
  refine (integrableOn_pow_mul_exp_neg_mul_Ici_one hc 1).congr_fun ?_ measurableSet_Ici
  intro x hx
  simp

theorem Aexp_gauss_integrable (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (τ : UpperHalfPlane) {r : ℝ} (hr : 2 < r^2) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
      * Work.Asymptotics.gaussWeight r t) (Set.Ici 1) := by
  have hr2 : 0 < r ^ 2 := by linarith
  have hc1 : 0 < Real.pi * r ^ 2 := mul_pos Real.pi_pos hr2
  have hc2 : 0 < Real.pi * (r ^ 2 - 2) := mul_pos Real.pi_pos (by linarith)
  set B : ℝ → ℝ := fun t : ℝ =>
      ‖Work.Asymptotics.Gcusp ℓ d 0 0 τ‖ * Real.exp (-(Real.pi * r ^ 2 * t))
        + ‖Work.Asymptotics.Gcusp ℓ d 0 1 τ‖ * (t * Real.exp (-(Real.pi * r ^ 2 * t)))
        + ‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖ * Real.exp (-(Real.pi * (r ^ 2 - 2) * t))
        + ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖ * (t * Real.exp (-(Real.pi * (r ^ 2 - 2) * t)))
    with hBdef
  have hB : MeasureTheory.IntegrableOn B (Set.Ici 1) := by
    rw [hBdef]
    have h0 : MeasureTheory.IntegrableOn (fun t : ℝ =>
        ‖Work.Asymptotics.Gcusp ℓ d 0 0 τ‖ * Real.exp (-(Real.pi * r ^ 2 * t))) (Set.Ici 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_exp_neg_mul_Ici_one hc1) _
    have h1 : MeasureTheory.IntegrableOn (fun t : ℝ =>
        ‖Work.Asymptotics.Gcusp ℓ d 0 1 τ‖ * (t * Real.exp (-(Real.pi * r ^ 2 * t)))) (Set.Ici 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_mul_exp_neg_mul_Ici_one hc1) _
    have h2 : MeasureTheory.IntegrableOn (fun t : ℝ =>
        ‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖ * Real.exp (-(Real.pi * (r ^ 2 - 2) * t))) (Set.Ici 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_exp_neg_mul_Ici_one hc2) _
    have h3 : MeasureTheory.IntegrableOn (fun t : ℝ =>
        ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖ * (t * Real.exp (-(Real.pi * (r ^ 2 - 2) * t)))) (Set.Ici 1) :=
      MeasureTheory.Integrable.const_mul (integrableOn_mul_exp_neg_mul_Ici_one hc2) _
    exact MeasureTheory.IntegrableOn.add (MeasureTheory.IntegrableOn.add
      (MeasureTheory.IntegrableOn.add h0 h1) h2) h3
  have hf : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t) (MeasureTheory.volume.restrict (Set.Ici 1)) := by
    have hcont : Continuous (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t) := by
      unfold Work.Asymptotics.Aexp Work.Asymptotics.gaussWeight
      fun_prop
    exact hcont.aestronglyMeasurable.restrict
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ici 1)),
      ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
        * Work.Asymptotics.gaussWeight r t‖ ≤ B t := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun t ht => ?_)
    have ht1 : 1 ≤ t := ht
    have hnormt : ‖(t : ℂ)‖ = t := by
      exact (RCLike.norm_ofReal t).trans (abs_of_nonneg (by linarith))
    have hexpn : ‖Complex.exp (2 * Real.pi * t)‖ = Real.exp (2 * Real.pi * t) := by
      have harg : (2 : ℂ) * (Real.pi : ℂ) * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) := by
        push_cast; ring
      rw [harg, Complex.norm_exp, Complex.ofReal_re]
    have hExp : Real.exp (2 * Real.pi * t) * Real.exp (-(Real.pi * r ^ 2 * t))
        = Real.exp (-(Real.pi * (r ^ 2 - 2) * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hA : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ ‖Work.Asymptotics.Gcusp ℓ d 0 0 τ‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 τ‖
          + Real.exp (2 * Real.pi * t) * (‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖
            + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖) := by
      rw [Work.Asymptotics.Aexp]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, norm_mul, Complex.norm_I, hnormt, mul_one]
      · rw [norm_mul, hexpn]
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_mul, norm_mul, Complex.norm_I, hnormt, mul_one]
    calc ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
          * Work.Asymptotics.gaussWeight r t‖
        = ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
            * Real.exp (-(Real.pi * r ^ 2 * t)) := by
          rw [norm_mul, Work.Asymptotics.norm_gaussWeight]
      _ ≤ (‖Work.Asymptotics.Gcusp ℓ d 0 0 τ‖ + t * ‖Work.Asymptotics.Gcusp ℓ d 0 1 τ‖
            + Real.exp (2 * Real.pi * t) * (‖Work.Asymptotics.Gcusp ℓ d 1 0 τ‖
              + t * ‖Work.Asymptotics.Gcusp ℓ d 1 1 τ‖))
            * Real.exp (-(Real.pi * r ^ 2 * t)) :=
          mul_le_mul_of_nonneg_right hA (Real.exp_nonneg _)
      _ = B t := by
          simp only [hBdef]
          rw [← hExp]
          ring
  exact MeasureTheory.Integrable.mono' hB hf hbound

end Work.CKFinal.LineDecay
