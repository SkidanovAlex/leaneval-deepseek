import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Recur
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `JepsTransfer/LogInt.lean` — log-side integrability from the quadrant

The transfer estimate `logPair_conv_transfer` is stated on the log plane, so it needs the
integrability of `Q y * G y ^ 2` there.  For the weights and profiles of the chapter this is the
quadrant integrability transported by the log-coordinate substitution: for
`Q = logW w` and `G = logPull g` the two integrals

  `∫⁻ y, ofReal (logW w y * logPull g y ^ 2)`   and
  `∫⁻ z ∈ Iz, ∫⁻ θ ∈ Iθ, ofReal (w z θ * g z θ ^ 2)`

are the same (`HkSqAux.lintegral_quad_log_subst`), so a finite quadrant lintegral makes the
log-side function Bochner-integrable.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The log-plane lintegral of a leaf weight times the square of a pulled-back profile is the
quadrant lintegral of the weight times the square of the profile. -/
theorem lintegral_logW_sq_eq (w : ℝ → ℝ → ℝ) (g : Fn)
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hgm : AEMeasurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g)) :
    (∫⁻ y : ℝ × ℝ, ENNReal.ofReal
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g y) ^ 2))
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (w z θ * g z θ ^ 2) := by
  -- the pointwise identification of the two plane integrands
  have hfun : (fun y : ℝ × ℝ => ENNReal.ofReal
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g y) ^ 2))
      = fun y : ℝ × ℝ => ENNReal.ofReal
          (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
            * ((fun z θ => w z θ * g z θ ^ 2)
                (Real.exp y.1) (Real.arctan (Real.exp y.2)))) := by
    funext y
    congr 1
    simp only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull_apply]
    ring
  have hae : AEMeasurable (fun y : ℝ × ℝ => ENNReal.ofReal
      (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
        * ((fun z θ => w z θ * g z θ ^ 2)
            (Real.exp y.1) (Real.arctan (Real.exp y.2))))) MeasureTheory.volume := by
    rw [← hfun]
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (hwm.aemeasurable.mul (hgm.pow_const 2))
  rw [hfun]
  -- the plane integral of the uncurried function is the product integral
  have hprod : (∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
        * ((fun z θ => w z θ * g z θ ^ 2) (Real.exp y.1) (Real.arctan (Real.exp y.2)))))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ
        * ((fun z θ => w z θ * g z θ ^ 2) (Real.exp s) (Real.arctan (Real.exp ζ)))) :=
    MeasureTheory.lintegral_prod _ hae
  rw [hprod]
  -- split the Jacobian factor off the `ofReal`
  have hsplit : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ
        * ((fun z θ => w z θ * g z θ ^ 2) (Real.exp s) (Real.arctan (Real.exp ζ)))))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * ENNReal.ofReal ((fun z θ => w z θ * g z θ ^ 2)
              (Real.exp s) (Real.arctan (Real.exp ζ))) := by
    refine MeasureTheory.lintegral_congr (fun s =>
      MeasureTheory.lintegral_congr (fun ζ => ?_))
    exact ENNReal.ofReal_mul (Work.FTS.StrongEps.HkSqAux.logJac_nonneg s ζ)
  rw [hsplit]
  -- undo the log-coordinate substitution
  rw [← Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
    (fun z θ => ENNReal.ofReal (w z θ * g z θ ^ 2))]
  -- the open quadrant carries the same measure as `Iz × Iθ`
  have hIθ : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (w z θ * g z θ ^ 2))
      = fun z : ℝ => ∫⁻ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal (w z θ * g z θ ^ 2) :=
    funext fun z => (MeasureTheory.setLIntegral_congr
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
        (b := Real.pi / 2))).symm
  rw [hIθ]
  exact MeasureTheory.setLIntegral_congr
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))

/-- **Log-side integrability of `logW w · (logPull g)²` from the quadrant lintegral.** -/
theorem integrable_logW_sq_of_lintegral {w : ℝ → ℝ → ℝ} {g : Fn}
    (hw0 : ∀ y : ℝ × ℝ, 0 ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
    (hwm : Measurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w))
    (hgm : AEMeasurable (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g))
    (hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (w z θ * g z θ ^ 2)) ≠ ⊤) :
    Integrable (fun y : ℝ × ℝ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g y) ^ 2) := by
  have hnn : 0 ≤ᵐ[MeasureTheory.volume] (fun y : ℝ × ℝ =>
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
        * (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logPull g y) ^ 2) :=
    Eventually.of_forall fun y => mul_nonneg (hw0 y) (sq_nonneg _)
  refine ⟨?_, ?_⟩
  · exact (hwm.aemeasurable.mul (hgm.pow_const 2)).aestronglyMeasurable
  · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hnn]
    rw [lintegral_logW_sq_eq w g hw0 hwm hgm]
    exact lt_top_iff_ne_top.mpr hfin

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT
