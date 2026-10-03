import Mathlib
import Submission.Work.Pert.V5.Basics
import Submission.Work.Pert.V5.Facts

/-!
# The affine marginal integral

Both marginals `mgA Ξ α` and `mgB Ξ` of the gate, restricted to a horizontal line
`ξ ↦ ξ + i y`, are *affine* in `ξ`:

* `mgA Ξ α (ξ + i y) = ξ + KA`  (slope `+1`),  `KA = -Ξ + Re (1/α) + |y + Im (1/α)|`,
* `mgB Ξ (ξ + i y) = KB - ξ`     (slope `-1`),  `KB = |y| - Ξ`.

Hence `1/mgA` and `1/mgB` are (the derivatives of) logarithms of these affine functions,
and the integral over `[x, x₀]` is the difference of the corresponding logarithms.  The
positivity hypotheses guarantee that both denominators stay positive on the whole segment
(`mgA` is increasing, `mgB` decreasing).
-/

namespace Work.Pert.V5

noncomputable section

theorem integral_marg_affine {Ξ C₂ : ℝ} {α : ℂ} {x x₀ y : ℝ}
    (hxx : x ≤ x₀)
    (hApos : 0 < Work.Pert.V5.mgA Ξ α ((x : ℂ) + (y : ℂ) * Complex.I))
    (hBpos : 0 < Work.Pert.V5.mgB Ξ ((x₀ : ℂ) + (y : ℂ) * Complex.I)) :
    (∫ ξ in x..x₀, (C₂ * Real.sqrt 2 *
          (1 / Work.Pert.V5.mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)
         + 1 / Work.Pert.V5.mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) + 1 / 31))
      = C₂ * Real.sqrt 2 *
          (Real.log (Work.Pert.V5.mgA Ξ α ((x₀ : ℂ) + (y : ℂ) * Complex.I)
                     / Work.Pert.V5.mgA Ξ α ((x : ℂ) + (y : ℂ) * Complex.I))
         + Real.log (Work.Pert.V5.mgB Ξ ((x : ℂ) + (y : ℂ) * Complex.I)
                     / Work.Pert.V5.mgB Ξ ((x₀ : ℂ) + (y : ℂ) * Complex.I)))
        + (x₀ - x) / 31 := by
  -- The two affine constants.
  set KA : ℝ := -Ξ + (1 / α).re + |y + (1 / α).im| with hKA
  set KB : ℝ := |y| - Ξ with hKB
  -- The marginals on the horizontal line are affine.
  have hAeq : ∀ ξ : ℝ, mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I) = ξ + KA := by
    intro ξ
    rw [mgA_re_im, hKA]
    ring
  have hBeq : ∀ ξ : ℝ, mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I) = KB - ξ := by
    intro ξ
    rw [mgB_re_im, hKB]
  -- Positivity on the segment.
  have hxA : 0 < x + KA := by rw [← hAeq x]; exact hApos
  have hx₀B : 0 < KB - x₀ := by rw [← hBeq x₀]; exact hBpos
  -- Differentiability of the antiderivative on the segment.
  have hder : ∀ ξ ∈ Set.uIcc x x₀,
      HasDerivAt (fun ξ : ℝ => C₂ * Real.sqrt 2 *
          (Real.log (mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I))
           - Real.log (mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I))) + ξ / 31)
        (C₂ * Real.sqrt 2 * (1 / mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)
           + 1 / mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) + 1 / 31) ξ := by
    intro ξ hξ
    rw [Set.uIcc_of_le hxx] at hξ
    have hAξ : (0 : ℝ) < ξ + KA := by linarith [hξ.1, hxA]
    have hBξ : (0 : ℝ) < KB - ξ := by linarith [hξ.2, hx₀B]
    have hAder : HasDerivAt (fun ξ : ℝ => Real.log (mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)))
        (1 / mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)) ξ := by
      have hbase : HasDerivAt (fun ξ : ℝ => ξ + KA) (1 : ℝ) ξ :=
        (hasDerivAt_id ξ).add_const KA
      have hlog : HasDerivAt (fun ξ : ℝ => Real.log (ξ + KA)) (1 / (ξ + KA)) ξ :=
        hbase.log (ne_of_gt hAξ)
      have hfun : (fun ξ : ℝ => Real.log (mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)))
          = fun ξ : ℝ => Real.log (ξ + KA) := by
        funext ξ; rw [hAeq ξ]
      have hval : (1 / mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)) = (1 / (ξ + KA)) := by
        rw [hAeq ξ]
      rw [hfun, hval]
      exact hlog
    have hBder : HasDerivAt (fun ξ : ℝ => Real.log (mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)))
        (-(1 / mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I))) ξ := by
      have hbase : HasDerivAt (fun ξ : ℝ => KB - ξ) (-1) ξ :=
        (hasDerivAt_id ξ).const_sub KB
      have hlog : HasDerivAt (fun ξ : ℝ => Real.log (KB - ξ)) ((-1) / (KB - ξ)) ξ :=
        hbase.log (ne_of_gt hBξ)
      have hfun : (fun ξ : ℝ => Real.log (mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)))
          = fun ξ : ℝ => Real.log (KB - ξ) := by
        funext ξ; rw [hBeq ξ]
      have hval : (-(1 / mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I))) = ((-1) / (KB - ξ)) := by
        rw [hBeq ξ]; ring
      rw [hfun, hval]
      exact hlog
    have hfd := hAder.sub hBder
    have hgm := hfd.const_mul (C₂ * Real.sqrt 2)
    have hlin : HasDerivAt (fun ξ : ℝ => ξ / 31) (1 / 31) ξ :=
      (hasDerivAt_id ξ).div_const 31
    have hG0 := hgm.add hlin
    refine hG0.congr_deriv ?_
    ring
  -- Integrability of the integrand on the segment.
  have hInt : IntervalIntegrable (fun ξ : ℝ => C₂ * Real.sqrt 2 *
      (1 / mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)
       + 1 / mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) + 1 / 31)
      MeasureTheory.volume x x₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hxx]
    have hA : ContinuousOn (fun ξ : ℝ => (1 : ℝ) / mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I))
        (Set.Icc x x₀) := by
      have hf : ContinuousOn (fun ξ : ℝ => mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I))
          (Set.Icc x x₀) := by
        have : (fun ξ : ℝ => mgA Ξ α ((ξ : ℂ) + (y : ℂ) * Complex.I)) = fun ξ : ℝ => ξ + KA := by
          funext ξ; rw [hAeq ξ]
        rw [this]
        exact continuousOn_id.add continuousOn_const
      exact continuousOn_const.div hf
        (fun ξ hξ => by rw [hAeq ξ]; exact ne_of_gt (by linarith [hξ.1, hxA]))
    have hB : ContinuousOn (fun ξ : ℝ => (1 : ℝ) / mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I))
        (Set.Icc x x₀) := by
      have hf : ContinuousOn (fun ξ : ℝ => mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I))
          (Set.Icc x x₀) := by
        have : (fun ξ : ℝ => mgB Ξ ((ξ : ℂ) + (y : ℂ) * Complex.I)) = fun ξ : ℝ => KB - ξ := by
          funext ξ; rw [hBeq ξ]
        rw [this]
        exact continuousOn_const.sub continuousOn_id
      exact continuousOn_const.div hf
        (fun ξ hξ => by rw [hBeq ξ]; exact ne_of_gt (by linarith [hξ.2, hx₀B]))
    exact ((hA.add hB).const_mul (C₂ * Real.sqrt 2)).add_const (1 / 31)
  -- Fundamental theorem of calculus.
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hInt
  rw [hFTC]
  -- Reduce the two logarithms of the ratios.
  have hsplitA : Real.log (mgA Ξ α ((x₀ : ℂ) + (y : ℂ) * Complex.I)
        / mgA Ξ α ((x : ℂ) + (y : ℂ) * Complex.I))
      = Real.log (mgA Ξ α ((x₀ : ℂ) + (y : ℂ) * Complex.I))
        - Real.log (mgA Ξ α ((x : ℂ) + (y : ℂ) * Complex.I)) :=
    Real.log_div (by rw [hAeq x₀]; exact ne_of_gt (by linarith))
      (by rw [hAeq x]; exact ne_of_gt hxA)
  have hsplitB : Real.log (mgB Ξ ((x : ℂ) + (y : ℂ) * Complex.I)
        / mgB Ξ ((x₀ : ℂ) + (y : ℂ) * Complex.I))
      = Real.log (mgB Ξ ((x : ℂ) + (y : ℂ) * Complex.I))
        - Real.log (mgB Ξ ((x₀ : ℂ) + (y : ℂ) * Complex.I)) :=
    Real.log_div (by rw [hBeq x]; exact ne_of_gt (by linarith [hxx, hx₀B]))
      (by rw [hBeq x₀]; exact ne_of_gt hx₀B)
  rw [hsplitA, hsplitB]
  ring

end

end Work.Pert.V5
