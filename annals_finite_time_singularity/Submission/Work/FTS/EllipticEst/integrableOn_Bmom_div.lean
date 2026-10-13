import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.integrableOn_slice_l2
import Submission.Work.FTS.EllipticEst.PsiInt_sq_mul_w_le_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter
open scoped Real Topology

/-- The angular `L²`-slice `A s = ∫_θ (D_z^j F s θ · w(s)/sin(2θ)^{η/2})²` is the dominating
quantity: by Cauchy–Schwarz (`PsiInt_sq_mul_w_le_open`) it controls the radial moment
`Bmom F j s = PsiInt F j s`, and `integrableOn_slice_l2` shows that it is integrable on every
compact subinterval of `(0,∞)`. -/
theorem integrableOn_Bmom_div (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s / s) (Set.Icc a b) := by
  intro a b ha hab
  -- The dominating quantity: the angular `L²`-slice of the `j`-th weighted `D_z`-summand.
  set A : ℝ → ℝ := fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.DzIter j F s θ * (Work.Spaces.w s / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    with hAdef
  -- (1) `A` is integrable on `[a,b]` (indeed on all of `Iz`).
  have hAint : MeasureTheory.IntegrableOn A (Set.Icc a b) :=
    integrableOn_slice_l2 α k hF hmem j hj a b ha hab
  have hA0 : ∀ s : ℝ, 0 ≤ A s := fun s => integral_nonneg fun θ => sq_nonneg _
  -- (2) Pointwise bound: for `s > 0`, `|Bmom F j s / s| ≤ √(π/2)·(A s + 1)`.
  have hpt : ∀ s : ℝ, 0 < s → ‖Work.FTS.EllipticEst.Bmom F j s / s‖
      ≤ Real.sqrt (Real.pi / 2) * (A s + 1) := by
    intro s hs
    have hcs := PsiInt_sq_mul_w_le_open F hF j hs
      (integrableOn_zSummand α k hF hmem j hj (Set.mem_Ici.mpr (le_of_lt hs)))
    -- `s·w(s) ≥ 1`, hence `w(s)²·s² ≥ 1`
    have hws : 1 ≤ s * Work.Spaces.w s := by
      have heq : s * Work.Spaces.w s = (1 + s) ^ 2 / s := by
        rw [Work.Spaces.w]
        field_simp
      rw [heq, le_div_iff₀ hs]
      nlinarith [sq_nonneg s]
    have hws2 : 1 ≤ (Work.Spaces.w s) ^ 2 * s ^ 2 := by
      have h := mul_le_mul hws hws (by norm_num) (le_trans zero_le_one hws)
      have he : (s * Work.Spaces.w s) * (s * Work.Spaces.w s)
          = (Work.Spaces.w s) ^ 2 * s ^ 2 := by ring
      linarith [h, he]
    have hinv : 1 / s ^ 2 ≤ (Work.Spaces.w s) ^ 2 := by
      rw [div_le_iff₀ (pow_pos hs 2)]
      exact hws2
    -- Cauchy–Schwarz, with the factor `1/s` absorbed by `s·w(s) ≥ 1`
    have hstep : (PsiInt F j s / s) ^ 2 ≤ (PsiInt F j s) ^ 2 * (Work.Spaces.w s) ^ 2 := by
      rw [div_pow, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [one_div] at hinv
      exact hinv
    have hsq : (PsiInt F j s / s) ^ 2 ≤ (Real.pi / 2) * A s := le_trans hstep hcs
    have hsqrt1 : |PsiInt F j s / s| ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (A s) := by
      rw [← Real.sqrt_sq_eq_abs]
      calc Real.sqrt ((PsiInt F j s / s) ^ 2)
          ≤ Real.sqrt ((Real.pi / 2) * A s) := Real.sqrt_le_sqrt hsq
        _ = Real.sqrt (Real.pi / 2) * Real.sqrt (A s) := Real.sqrt_mul (by positivity) _
    have hsqrt2 : Real.sqrt (A s) ≤ A s + 1 := by
      have h := Real.sq_sqrt (hA0 s)
      nlinarith [h, Real.sqrt_nonneg (A s), sq_nonneg (Real.sqrt (A s) - 1 / 2)]
    rw [Work.FTS.EllipticEst.Bmom, Real.norm_eq_abs]
    calc |PsiInt F j s / s| ≤ Real.sqrt (Real.pi / 2) * Real.sqrt (A s) := hsqrt1
      _ ≤ Real.sqrt (Real.pi / 2) * (A s + 1) :=
          mul_le_mul_of_nonneg_left hsqrt2 (Real.sqrt_nonneg _)
  -- (3) The dominating function `s ↦ √(π/2)·(A s + 1)` is integrable on `[a,b]`.
  have hdom : MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt (Real.pi / 2) * (A s + 1))
      (Set.Icc a b) := by
    have h1 : MeasureTheory.IntegrableOn (fun s : ℝ => A s + 1) (Set.Icc a b) :=
      hAint.add (MeasureTheory.integrableOn_const (s := Set.Icc a b) (C := (1 : ℝ))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    exact h1.const_mul _
  -- (4) Measurability of the target function, by Fubini from the joint measurability of the
  -- uncurried angular integrand on the open quadrant.
  have hmeas : AEStronglyMeasurable (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s / s)
      (volume.restrict (Set.Icc a b)) := by
    have hsin : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ := by
      unfold Work.Elliptic.sinCos2
      fun_prop
    have hjoint : AEStronglyMeasurable
        (fun p : ℝ × ℝ => Work.Spaces.DzIter j F p.1 p.2 * Work.Elliptic.sinCos2 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
      have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j F p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hF.DzIter j).continuousOn
      have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hsin.comp continuous_snd).continuousOn
      exact Work.Spaces.aesm_of_continuousOn_Qd _ (h1.mul h2)
    have hB : AEStronglyMeasurable (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s)
        (volume.restrict Work.Spaces.Iz) := by
      have h := hjoint.integral_prod_right' (μ := volume.restrict Work.Spaces.Iz)
        (ν := volume.restrict Work.Spaces.Iθ)
      simpa only [Work.FTS.EllipticEst.Bmom, Work.FTS.EllipticEst.PsiInt] using h
    have hle : (volume.restrict (Set.Icc a b)) ≤ (volume.restrict Work.Spaces.Iz) :=
      MeasureTheory.Measure.restrict_mono
        (fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)) le_rfl
    have hB2 : AEStronglyMeasurable (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s)
        (volume.restrict (Set.Icc a b)) := hB.mono_measure hle
    have h2 : AEStronglyMeasurable (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s * s⁻¹)
        (volume.restrict (Set.Icc a b)) :=
      hB2.mul (measurable_inv.aestronglyMeasurable :
        AEStronglyMeasurable (fun s : ℝ => s⁻¹) (volume.restrict (Set.Icc a b)))
    have he : (fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s / s)
        = fun s : ℝ => Work.FTS.EllipticEst.Bmom F j s * s⁻¹ := by
      funext s
      exact div_eq_mul_inv _ _
    rw [he]
    exact h2
  -- (5) Domination gives integrability.
  refine hdom.mono' hmeas ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun s hs => hpt s (lt_of_lt_of_le ha hs.1)

end Work.FTS.EllipticEst
