/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/DiffAux/lintegral_shift_le_gen`

The **general form** of the shift bound `HkSqAux.integral_shift_le`: for an arbitrary real-valued
profile `V : ℝ → ℝ → ℝ` (no measurability, no integrability, no continuity hypothesis) and any
shift `p = (p₁, p₂)`, the iterated `lintegral` of `ENNReal.ofReal (V (zShift z p₁) (thShift θ p₂))`
over the quadrant `Iz × Iθ` is bounded by `e^{δ(|p₁|+|p₂|)}` times the corresponding integral of
`V` itself, provided only the log-coordinate Jacobian `logJac` satisfies the shift estimate

  `logJac s ζ ≤ e^{δ(|p₁|+|p₂|)} · logJac (s - p₁) (ζ - p₂)`.

The proof is the measure-theoretic computation of `integral_shift_le`: in the log coordinates
`s = log z`, `ζ = log tan θ` the two shifts become the translations `s ↦ s - p₁`, `ζ ↦ ζ - p₂`;
the change of variables `lintegral_quad_log_subst` turns the quadrant integral into a plane
integral with the Jacobian weight `logJac`, translation invariance moves the shift onto the
Jacobian factor, and the hypothesis `hJac` bounds the quotient.  The difference from
`integral_shift_le` is only in the last step: here the remaining plane integral is converted
*back* to the quadrant integral of `V` (`hgen` below) instead of being identified with `HkSq`,
so no `HkMem`/`ContinuousOn` hypothesis is needed.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.HkSqAux.LogCoord
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_prod_shift
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.StrongEps.DiffAux

theorem lintegral_shift_le_gen {δ : ℝ}
    (hJac : ∀ s ζ p₁ p₂ : ℝ, Work.FTS.StrongEps.HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac (s - p₁) (ζ - p₂))
    {V : ℝ → ℝ → ℝ} (p : ℝ × ℝ) :
    (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      ≤ ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|)))
        * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (V z θ)) := by
  -- the two shifts in the log coordinates are the translations `s ↦ s - p₁`, `ζ ↦ ζ - p₂`
  have hz : ∀ s : ℝ, Work.FTS.StrongEps.zShift (Real.exp s) p.1 = Real.exp (s - p.1) := by
    intro s
    rw [Work.FTS.StrongEps.zShift, ← Real.exp_add, sub_eq_add_neg]
  have hth : ∀ ζ : ℝ, Work.FTS.StrongEps.thShift (Real.arctan (Real.exp ζ)) p.2
      = Real.arctan (Real.exp (ζ - p.2)) := by
    intro ζ
    rw [Work.FTS.StrongEps.thShift, Real.tan_arctan, ← Real.exp_add, sub_eq_add_neg]
  -- the same integral, without the shift, in log coordinates
  have hgen : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (V z θ))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ))) := by
    have hIθ0 : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (V z θ))
        = fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (V z θ) :=
      funext fun z => (MeasureTheory.setLIntegral_congr (f := fun θ : ℝ => ENNReal.ofReal (V z θ))
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2))).symm
    rw [hIθ0]
    have hIz0 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (V z θ))
        = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (V z θ) :=
      (MeasureTheory.setLIntegral_congr (f := fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (V z θ))
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
    rw [hIz0]
    exact Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst (fun z θ => ENNReal.ofReal (V z θ))
  set r : ENNReal := ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) with hr
  have hrne : r ≠ ⊤ := by rw [hr]; exact ENNReal.ofReal_ne_top
  -- replace the closed intervals by the open ones on the left-hand side (null sets)
  have hIθ : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      = fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :=
    funext fun z => (MeasureTheory.setLIntegral_congr (f := fun θ : ℝ =>
      ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2))).symm
  rw [hIθ]
  have hIz : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) :=
    (MeasureTheory.setLIntegral_congr (f := fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
  rw [hIz]
  -- the log-coordinate substitution, which is *exactly* the shift in the new variables
  rw [Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst (fun z θ =>
      ENNReal.ofReal (V (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)))]
  simp only [hz, hth]
  -- translation invariance of the plane integral: move the shift onto the Jacobian weight
  rw [Work.FTS.StrongEps.HkSqAux.lintegral_prod_shift_mul
        (fun s ζ => ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ))
        (fun s ζ => ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))) p.1 p.2]
  -- the pointwise comparison coming from `hJac`
  have hpt : ∀ s ζ : ℝ,
      ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac (s + p.1) (ζ + p.2))
          * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))
        ≤ r * (ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))) := by
    intro s ζ
    have h := hJac (s + p.1) (ζ + p.2) p.1 p.2
    rw [add_sub_cancel_right, add_sub_cancel_right] at h
    have h1 : ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac (s + p.1) (ζ + p.2))
        ≤ r * ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ) := by
      rw [hr, ← ENNReal.ofReal_mul (Real.exp_pos (δ * (|p.1| + |p.2|))).le]
      exact ENNReal.ofReal_le_ofReal h
    calc ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac (s + p.1) (ζ + p.2))
            * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))
        ≤ (r * ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ))
            * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ))) :=
          mul_le_mul_of_nonneg_right h1 bot_le
      _ = r * (ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
            * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))) := by ring
  refine le_trans (MeasureTheory.lintegral_mono fun s =>
    MeasureTheory.lintegral_mono fun ζ => hpt s ζ) ?_
  -- pull the constant `r` out of the two integrals
  rw [show (∫⁻ s, ∫⁻ ζ, r * (ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
        * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))))
      = r * ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
        * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ))) from ?_]
  · -- identify the remaining plane integral with the quadrant integral of `V`
    rw [hgen]
  · rw [← MeasureTheory.lintegral_const_mul' r
        (fun s => ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))) hrne]
    refine MeasureTheory.lintegral_congr fun s => ?_
    exact MeasureTheory.lintegral_const_mul' r
      (fun ζ => ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
        * ENNReal.ofReal (V (Real.exp s) (Real.arctan (Real.exp ζ)))) hrne

end Work.FTS.StrongEps.DiffAux
