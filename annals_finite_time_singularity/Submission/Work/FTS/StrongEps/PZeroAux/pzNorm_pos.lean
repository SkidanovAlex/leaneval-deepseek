import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.BumpDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.PZeroAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Positivity of `pzNorm = L₁₂(bump)(0)`

`pzNorm = ∫_{0}^{∞} ∫_{0}^{π/2} K(θ) bump(s,θ)/s dθ ds`.  The angular integrand `K θ · bump s θ / s`
is nonnegative everywhere (the profile `bump` is nonnegative and the weight `K = 3 sin θ cos²θ` is
nonnegative on the support window `(π/4, 3π/8)` of `bump` in `θ`), and it is *strictly* positive on
the rectangle `(5/8, 7/8) × (π/4, 3π/8)`, a set of positive measure contained in the domain of
integration.  Hence the double integral is strictly positive.

The only analytic ingredient is the continuity of the *parameter* integral
`s ↦ ∫_θ K θ · bump s θ / s` on `(0,∞)`, which follows from the parametric-continuity lemma
`continuousOn_integral_of_compact_support` (the integrand is jointly continuous where `s ≠ 0`,
vanishes for `θ` outside the compact support window `[0, π/2]` of `bump` in `θ`, and the parameter
`s > 0` keeps the division regular).
-/

namespace PzNormAux

/-! ### Elementary nonnegativity of the angular weight -/

/-- `K(θ) = 3 sin θ cos²θ ≥ 0` on `[0, π/2]`. -/
theorem K_nonneg {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  nlinarith [h1, h2]

/-- `K(θ) = 3 sin θ cos²θ > 0` on `(0, π/2)`. -/
theorem K_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have h2 : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  positivity

/-! ### The angular integrand of `L₁₂dens K bump` -/

/-- The angular integrand `(s,θ) ↦ K θ · bump s θ / s` of `L₁₂dens K bump`. -/
def KB (s θ : ℝ) : ℝ := Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s

/-- `KB` vanishes for `θ` outside the angular window `Iθ = [0, π/2]` (the support of `bump` in `θ`
is `[π/4, 3π/8] ⊂ Iθ`). -/
theorem KB_eq_zero_of_not_mem_Iθ {s θ : ℝ} (hθ : θ ∉ Work.Spaces.Iθ) : KB s θ = 0 := by
  have hth : Work.FTS.StrongEps.bump s θ = 0 := by
    rw [Work.FTS.StrongEps.bump_eq_zero_iff]
    rw [Work.Spaces.Iθ, Set.mem_Icc, not_and_or, not_le, not_le] at hθ
    rcases hθ with h | h
    · exact Or.inr (Or.inr (Or.inl (by linarith [Real.pi_pos])))
    · exact Or.inr (Or.inr (Or.inr (by linarith [Real.pi_pos])))
  rw [KB, hth, mul_zero, zero_div]

/-- `KB` is nonnegative everywhere: off the support of `bump` it vanishes, and on the support
`K θ > 0`, `bump s θ > 0` and `s > 0`. -/
theorem KB_nonneg (s θ : ℝ) : 0 ≤ KB s θ := by
  rcases eq_or_ne (Work.FTS.StrongEps.bump s θ) 0 with hb | hb
  · rw [KB, hb, mul_zero, zero_div]
  · have hbpos : 0 < Work.FTS.StrongEps.bump s θ :=
      lt_of_le_of_ne (Work.FTS.StrongEps.bump_nonneg s θ) (Ne.symm hb)
    obtain ⟨hz, hθ⟩ := Work.FTS.StrongEps.bump_ne_zero_iff.mp hb
    have hK : 0 < Work.Spaces.K θ :=
      K_pos ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    rw [KB]
    exact le_of_lt (div_pos (mul_pos hK hbpos) (by linarith [hz.1]))

/-! ### The angular density as a parameter integral -/

/-- `L₁₂dens K bump s` is the full-line parameter integral of `KB s`. -/
theorem L12dens_eq (s : ℝ) :
    Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s = ∫ θ, KB s θ := by
  rw [Work.FM.L12dens]
  rw [show (fun θ => Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s)
      = (fun θ => KB s θ) from rfl]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun θ hθ => KB_eq_zero_of_not_mem_Iθ hθ)

/-- Continuity of the parameter integral `s ↦ ∫_θ K θ · bump s θ / s` on `(0, ∞)`. -/
theorem continuousOn_Kbump_integral :
    ContinuousOn (fun s => ∫ θ, KB s θ) (Set.Ioi 0) := by
  refine continuousOn_integral_of_compact_support (μ := volume) (s := Set.Ioi 0)
    (k := Work.Spaces.Iθ) isCompact_Icc ?_ ?_
  · have hKcont : Continuous (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
      simp only [Work.Spaces.K]; fun_prop
    have hBcont : Continuous (fun p : ℝ × ℝ => Work.FTS.StrongEps.bump p.1 p.2) :=
      (Work.FTS.StrongEps.contDiff_bump 1).continuous
    exact ((hKcont.mul hBcont).continuousOn).div continuous_fst.continuousOn
      (fun p hp => ne_of_gt hp.1)
  · intro p x _ hx
    exact KB_eq_zero_of_not_mem_Iθ hx

/-- `L₁₂dens K bump` is continuous on `(0, ∞)`. -/
theorem continuousOn_L12dens :
    ContinuousOn (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
      (Set.Ioi 0) :=
  continuousOn_Kbump_integral.congr (fun s _ => L12dens_eq s)

/-! ### Nonnegativity and vanishing -/

/-- `L₁₂dens K bump` is nonnegative. -/
theorem L12dens_nonneg (s : ℝ) :
    0 ≤ Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s := by
  rw [L12dens_eq s]
  exact integral_nonneg (fun θ => KB_nonneg s θ)

/-- `L₁₂dens K bump` vanishes where the radial cut-off `zCut` does (i.e. off `(1/2, 1)`). -/
theorem L12dens_eq_zero_of_zCut_zero {s : ℝ}
    (hs : Work.FTS.StrongEps.zCut s = 0) :
    Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s = 0 := by
  rw [L12dens_eq s]
  have h : (fun θ => KB s θ) = fun _ => (0 : ℝ) := by
    funext θ
    have : Work.FTS.StrongEps.bump s θ = 0 := by
      rw [Work.FTS.StrongEps.bump, hs, zero_mul]
    rw [KB, this, mul_zero, zero_div]
  rw [h, integral_zero]

theorem L12dens_eq_zero_of_le {s : ℝ} (hs : s ≤ 1 / 2) :
    Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s = 0 :=
  L12dens_eq_zero_of_zCut_zero (Work.FTS.StrongEps.zCut_eq_zero_iff.mpr (Or.inl hs))

theorem L12dens_eq_zero_of_ge {s : ℝ} (hs : 1 ≤ s) :
    Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s = 0 :=
  L12dens_eq_zero_of_zCut_zero (Work.FTS.StrongEps.zCut_eq_zero_iff.mpr (Or.inr hs))

/-! ### Strict positivity on the inner box -/

/-- `L₁₂dens K bump s > 0` for `s ∈ (5/8, 7/8)`: the angular integrand is nonnegative, integrable on
`Iθ`, and strictly positive on the angular box `(π/4, 3π/8)`, a set of positive measure. -/
theorem L12dens_pos_of_inner {s : ℝ} (hs : s ∈ Set.Ioo ((5 : ℝ) / 8) (7 / 8)) :
    0 < Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s := by
  rw [L12dens_eq s]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Work.Spaces.Iθ) (fun θ hθ => KB_eq_zero_of_not_mem_Iθ hθ)]
  refine (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun θ => KB_nonneg s θ)) ?_).mpr ?_
  · have hKs : Continuous (fun θ => Work.Spaces.K θ) := by
      simp only [Work.Spaces.K]; fun_prop
    have hbs : Continuous (fun θ => Work.FTS.StrongEps.bump s θ) :=
      (Work.FTS.StrongEps.contDiff_bump 1).continuous.comp
        (continuous_const.prodMk continuous_id)
    exact ((hKs.mul hbs).div_const s).integrableOn_Icc
  · have hsub : Set.Ioo (Real.pi / 4) (3 * Real.pi / 8) ⊆
        Function.support (fun θ => KB s θ) ∩ Work.Spaces.Iθ := by
      intro θ hθ
      refine ⟨?_, ?_⟩
      · rw [Function.mem_support]
        have hbpos : 0 < Work.FTS.StrongEps.bump s θ :=
          Work.FTS.StrongEps.bump_pos_iff.mpr
            ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hθ⟩
        have hK : 0 < Work.Spaces.K θ :=
          K_pos ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
        have hspos : 0 < s := by linarith [hs.1]
        intro hzero
        rw [KB] at hzero
        have : 0 < Work.Spaces.K θ * Work.FTS.StrongEps.bump s θ / s :=
          div_pos (mul_pos hK hbpos) hspos
        linarith
      · rw [Work.Spaces.Iθ, Set.mem_Icc]
        exact ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
    have hpos : 0 < (volume : Measure ℝ) (Set.Ioo (Real.pi / 4) (3 * Real.pi / 8)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
    exact lt_of_lt_of_le hpos (measure_mono hsub)

/-! ### Integrability on `(0, ∞)` and positivity of the supporting set -/

/-- `L₁₂dens K bump` is integrable on `(0, ∞)`: it is continuous there and supported in the compact
interval `[1/2, 1]`. -/
theorem integrableOn_L12dens :
    IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
      (Set.Ioi 0) := by
  have hIcc : IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
      (Set.Icc ((1 : ℝ) / 2) 1) :=
    (continuousOn_L12dens.mono
      (fun s hs => lt_of_lt_of_le (by norm_num) hs.1)).integrableOn_compact isCompact_Icc
  have hind : Integrable ((Set.Icc ((1 : ℝ) / 2) 1).indicator
      (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hIcc
  have hEq : (Set.Icc ((1 : ℝ) / 2) 1).indicator
        (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
      =ᵐ[volume] (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s) := by
    refine Eventually.of_forall (fun s => ?_)
    by_cases hs : s ∈ Set.Icc ((1 : ℝ) / 2) 1
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with h | h
      · exact (L12dens_eq_zero_of_le (le_of_lt h)).symm
      · exact (L12dens_eq_zero_of_ge (le_of_lt h)).symm
  exact (hind.congr hEq).integrableOn

/-- The supporting set of `L₁₂dens K bump` inside `(0, ∞)` has positive measure: it contains the
interval `(5/8, 7/8)` on which the function is strictly positive. -/
theorem support_L12dens_pos :
    0 < (volume : Measure ℝ)
      (Function.support (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
        ∩ Set.Ioi 0) := by
  have hsub : Set.Ioo ((5 : ℝ) / 8) (7 / 8) ⊆
      Function.support (fun s => Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s)
        ∩ Set.Ioi 0 := by
    intro s hs
    exact ⟨by rw [Function.mem_support]; exact ne_of_gt (L12dens_pos_of_inner hs),
      by rw [Set.mem_Ioi]; linarith [hs.1]⟩
  have hpos : 0 < (volume : Measure ℝ) (Set.Ioo ((5 : ℝ) / 8) (7 / 8)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by norm_num)
  exact lt_of_lt_of_le hpos (measure_mono hsub)

end PzNormAux

theorem pzNorm_pos : 0 < Work.FTS.StrongEps.pzNorm := by
  have hpz : Work.FTS.StrongEps.pzNorm =
      ∫ s in Set.Ioi 0, Work.FM.L12dens Work.Spaces.K Work.FTS.StrongEps.bump s := by
    rw [Work.FTS.StrongEps.pzNorm, Work.Construction.L12, Work.FM.L12]
  rw [hpz]
  exact (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun s => PzNormAux.L12dens_nonneg s))
    PzNormAux.integrableOn_L12dens).mpr PzNormAux.support_L12dens_pos

end Work.FTS.StrongEps.PZeroAux
