import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.HkSqAux.LogCoord
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_prod_shift
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.HkSqAux

theorem integral_shift_le {α : ℝ} {k : ℕ} {δ : ℝ}
    (hJac : ∀ s ζ p₁ p₂ : ℝ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac (s - p₁) (ζ - p₂))
    {f : ℝ → ℝ → ℝ} (hF : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad) (p : ℝ × ℝ) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)))
      ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
          * ENNReal.ofReal (Work.Spaces.HkSq α k f) := by
  set r : ENNReal := ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) with hr
  have hrne : r ≠ ⊤ := by rw [hr]; exact ENNReal.ofReal_ne_top
  -- the two shifts in the log coordinates
  have hz : ∀ s : ℝ, Work.FTS.StrongEps.zShift (Real.exp s) p.1 = Real.exp (s - p.1) := by
    intro s
    rw [Work.FTS.StrongEps.zShift, ← Real.exp_add, sub_eq_add_neg]
  have hth : ∀ ζ : ℝ, Work.FTS.StrongEps.thShift (Real.arctan (Real.exp ζ)) p.2
      = Real.arctan (Real.exp (ζ - p.2)) := by
    intro ζ
    rw [Work.FTS.StrongEps.thShift, Real.tan_arctan, ← Real.exp_add, sub_eq_add_neg]
  -- Step 1: replace the closed intervals by the open ones (null sets)
  have hIθ : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)))
      = fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) :=
    funext fun z => (MeasureTheory.setLIntegral_congr (f := fun θ : ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ p.2)))
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2))).symm
  rw [hIθ]
  have hIz : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)) :=
    (MeasureTheory.setLIntegral_congr (f := fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
          (Work.FTS.StrongEps.thShift θ p.2)))
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
  rw [hIz]
  -- Step 2: the log-coordinate substitution
  rw [lintegral_quad_log_subst (fun z θ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Work.FTS.StrongEps.zShift z p.1)
        (Work.FTS.StrongEps.thShift θ p.2)))]
  -- Step 3: the shifts become translations
  simp only [hz, hth]
  -- Step 4: translation invariance of the Lebesgue integral
  rw [lintegral_prod_shift_mul (fun s ζ => ENNReal.ofReal (logJac s ζ))
        (fun s ζ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
          (Real.arctan (Real.exp ζ)))) p.1 p.2]
  -- Step 5: the pointwise comparison coming from `hJac`
  have hpt : ∀ s ζ : ℝ,
      ENNReal.ofReal (logJac (s + p.1) (ζ + p.2))
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ)))
        ≤ r * (ENNReal.ofReal (logJac s ζ)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ)))) := by
    intro s ζ
    have h := hJac (s + p.1) (ζ + p.2) p.1 p.2
    rw [add_sub_cancel_right, add_sub_cancel_right] at h
    have h1 : ENNReal.ofReal (logJac (s + p.1) (ζ + p.2))
        ≤ r * ENNReal.ofReal (logJac s ζ) := by
      rw [hr, ← ENNReal.ofReal_mul (Real.exp_pos (δ * (|p.1| + |p.2|))).le]
      exact ENNReal.ofReal_le_ofReal h
    calc ENNReal.ofReal (logJac (s + p.1) (ζ + p.2))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
                (Real.arctan (Real.exp ζ)))
        ≤ (r * ENNReal.ofReal (logJac s ζ))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
                (Real.arctan (Real.exp ζ))) := mul_le_mul_of_nonneg_right h1 bot_le
      _ = r * (ENNReal.ofReal (logJac s ζ)
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
                (Real.arctan (Real.exp ζ)))) := by ring
  refine le_trans (MeasureTheory.lintegral_mono fun s =>
    MeasureTheory.lintegral_mono fun ζ => hpt s ζ) ?_
  -- Step 6: pull the constant `r` out of the two integrals
  rw [show (∫⁻ s, ∫⁻ ζ, r * (ENNReal.ofReal (logJac s ζ)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ)))))
        = r * ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (logJac s ζ)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ))) from ?_]
  · -- Step 7: identify the remaining integral with `ofReal (HkSq α k f)`
    rw [← ofReal_HkSq_eq_logIntegral α k hF hcont]
  · rw [← MeasureTheory.lintegral_const_mul' r
        (fun s => ∫⁻ ζ, ENNReal.ofReal (logJac s ζ)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ)))) hrne]
    refine MeasureTheory.lintegral_congr fun s => ?_
    exact MeasureTheory.lintegral_const_mul' r
      (fun ζ => ENNReal.ofReal (logJac s ζ)
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
            (Real.arctan (Real.exp ζ)))) hrne

end Work.FTS.StrongEps.HkSqAux
