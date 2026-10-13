/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/HkSqAux/LogCoord.lean`

The `H^k`-square `HkSq α k f = ∫ z ∈ [0,∞), ∫ θ ∈ [0,π/2], HkIntegrand α k f z θ` is, in the
log coordinates `z = e^s`, `θ = arctan (e^ζ)`, an integral over the plane:

  `HkSq α k f = ∫_s ∫_ζ logJac s ζ · HkIntegrand α k f (e^s) (arctan (e^ζ))`,

where `logJac s ζ = e^s · kappa ζ` is the Jacobian of the substitution.  This is
`ofReal_HkSq_eq_logIntegral`; it is the identity that turns the shift bounds of the two weights
(`wdiv_shift_le`, `Wt_shift_le`) and of the Jacobian (`logJac_shift_le`) into the boundedness of
`J_ε` on `H^k`.

The proof converts the iterated Bochner integral into an iterated `lintegral` (using the
integrability hypothesis `HkMem α k f`), replaces `[0,∞)` and `[0,π/2]` by the open sets
`(0,∞)` and `(0,π/2)` (a null-set change), and then applies the two change-of-variables formulas
`lintegral_arctan_exp_subst_gen` and `lintegral_exp_subst_gen`.  The continuity hypothesis on the
integrand is exactly what is needed to pull the Jacobian factor `e^s` out of the `ζ`-integral.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_arctan_exp_subst_gen
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_exp_subst_gen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.HkSqAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem continuous_kappa : Continuous kappa := by
  unfold kappa
  refine Continuous.div Real.continuous_exp ?_ (fun ζ => ?_)
  · exact continuous_const.add (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  · positivity

/-- **The `H^k`-square as a log-coordinate integral.** -/
theorem ofReal_HkSq_eq_logIntegral (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ}
    (hF : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2)
      Work.FTS.StrongEps.Quad) :
    ENNReal.ofReal (Work.Spaces.HkSq α k f)
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (logJac s ζ)
          * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
              (Real.arctan (Real.exp ζ))) := by
  have hnn : ∀ z θ, 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f
  -- (1) the iterated Bochner integral as an iterated `lintegral`
  have h1 : ENNReal.ofReal (Work.Spaces.HkSq α k f)
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ) := by
    rw [Work.Spaces.HkSq]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.2
      (Eventually.of_forall fun z => integral_nonneg fun θ => hnn z θ)]
    exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ici
      (fun z hz => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hF.1 z hz)
        (Eventually.of_forall fun θ => hnn z θ))
  rw [h1]
  -- (2) replace the closed intervals by the open ones (null sets)
  have hIθ : (fun z : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      = fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ) := by
    funext z
    exact (MeasureTheory.setLIntegral_congr (f := fun θ : ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2))).symm
  rw [hIθ]
  have hIz : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      = ∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ) :=
    (MeasureTheory.setLIntegral_congr (f := fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))).symm
  rw [hIz]
  -- (3) the `θ`-substitution
  have hθ : (fun z : ℝ => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
      = fun z : ℝ => ∫⁻ ζ, ENNReal.ofReal (kappa ζ)
        * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z (Real.arctan (Real.exp ζ))) := by
    funext z
    exact lintegral_arctan_exp_subst_gen
      (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z θ))
  rw [hθ]
  -- (4) the `z`-substitution
  rw [lintegral_exp_subst_gen (fun z : ℝ => ∫⁻ ζ, ENNReal.ofReal (kappa ζ)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z (Real.arctan (Real.exp ζ))))]
  -- (5) move the factor `ofReal (exp s)` inside the `ζ`-integral and identify the Jacobian
  refine MeasureTheory.lintegral_congr fun s => ?_
  have hcontζ : Continuous fun ζ : ℝ =>
      Work.Spaces.HkIntegrand α k f (Real.exp s) (Real.arctan (Real.exp ζ)) :=
    hcont.comp_continuous
      (Continuous.prodMk continuous_const (Real.continuous_arctan.comp Real.continuous_exp))
      (fun ζ => ⟨Real.exp_pos s, Real.arctan_pos.2 (Real.exp_pos ζ),
        Real.arctan_lt_pi_div_two _⟩)
  have hmeas : Measurable fun ζ : ℝ => ENNReal.ofReal (kappa ζ)
      * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (Real.exp s)
          (Real.arctan (Real.exp ζ))) :=
    (ENNReal.measurable_ofReal.comp continuous_kappa.measurable).mul
      (ENNReal.measurable_ofReal.comp hcontζ.measurable)
  rw [(MeasureTheory.lintegral_const_mul (ENNReal.ofReal (Real.exp s)) hmeas).symm]
  refine MeasureTheory.lintegral_congr fun ζ => ?_
  rw [logJac, ENNReal.ofReal_mul (Real.exp_pos s).le]
  ring

end Work.FTS.StrongEps.HkSqAux
