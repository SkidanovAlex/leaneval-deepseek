/-
# `HkMem` from a pointwise exponential bound on the `H^k`-integrand

`Work.Spaces.HkMem α k f` asks for the two iterated `H^k`-integrals of `f` to be
honest: every angular slice `θ ↦ HkIntegrand α k f z θ`, `z ∈ Iz`, is integrable on
`Iθ`, and the `z`-integral `z ↦ ∫_θ HkIntegrand α k f z θ` is integrable on `Iz`.

Both facts are elementary consequences of two inputs:

* `SmoothNbhd f`, which makes the integrand a.e. strongly measurable on the quadrant
  and on each slice (see `Work.Coercivity.aesm_HkIntegrand_slice` and
  `Work.Coercivity.aesm_uncurry_HkIntegrand`);
* a pointwise bound `HkIntegrand ≤ C·exp(-z/2)` on the domain, with the integrand
  nonnegative, which dominates the slices by a constant (the angular interval has
  finite measure) and dominates the `z`-integral by an integrable function of `z`
  (the exponential `exp(-z/2)` is integrable on `[0,∞)`).

No use is made of the sign of `C`: the nonnegativity of the integrand together with
monotonicity of the integral already forces the derived domination to hold.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.R1G.GTest
import Submission.Work.Coercivity.HkMem_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.R1G

set_option linter.unusedVariables false

/-- **`HkMem` from an exponential bound.**  A `SmoothNbhd` function whose `H^k`-integrand
is pointwise dominated by `C·exp(-(z/2))` on the domain belongs to `H^k`. -/
theorem HkMem_of_expBound {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothNbhd f)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ ≤ C * Real.exp (-(z / 2))) :
    Work.Spaces.HkMem α k f := by
  have haesm_slice := Work.Coercivity.aesm_HkIntegrand_slice α k hsm
  have haesm_joint := Work.Coercivity.aesm_uncurry_HkIntegrand α k hsm
  have hIθfin : volume Work.Spaces.Iθ < ⊤ := by
    simp only [Work.Spaces.Iθ]; exact isCompact_Icc.measure_lt_top
  have hIzmeas : MeasurableSet Work.Spaces.Iz := by simp [Work.Spaces.Iz]
  have hIθmeas : MeasurableSet Work.Spaces.Iθ := by simp [Work.Spaces.Iθ]
  -- `z ↦ exp(-(z/2))` is integrable on `Iz = [0,∞)`.
  have hexp : IntegrableOn (fun z : ℝ => Real.exp (-(z / 2))) Work.Spaces.Iz := by
    change IntegrableOn (fun z : ℝ => Real.exp (-(z / 2))) (Set.Ici 0)
    refine (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun x : ℝ => Real.exp (-(x / 2))) (b := 0) (by simp)).mpr ?_
    have h0 := exp_neg_integrableOn_Ioi (a := 0) (b := (1 / 2 : ℝ)) (by norm_num)
    convert h0 using 2
    ring_nf
  constructor
  · -- every angular slice is integrable: bounded on the finite-measure set `Iθ`
    intro z hz
    refine IntegrableOn.of_bound hIθfin (haesm_slice z hz) (C * Real.exp (-(z / 2))) ?_
    filter_upwards [ae_restrict_mem hIθmeas] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k f z θ)]
    exact h z hz θ hθ
  · -- the `z`-integral is dominated by an integrable multiple of `exp(-(z/2))`
    have hbound : ∀ᵐ z ∂volume.restrict Work.Spaces.Iz,
        ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ‖
          ≤ C * volume.real Work.Spaces.Iθ * Real.exp (-(z / 2)) := by
      filter_upwards [ae_restrict_mem hIzmeas] with z hz
      have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
        integral_nonneg_of_ae (ae_restrict_of_forall_mem hIθmeas
          (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      calc ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ
          ≤ ∫ θ in Work.Spaces.Iθ, C * Real.exp (-(z / 2)) :=
            integral_mono_of_nonneg
              (ae_restrict_of_forall_mem hIθmeas
                (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))
              (integrable_const _)
              (ae_restrict_of_forall_mem hIθmeas (fun θ hθ => h z hz θ hθ))
        _ = C * volume.real Work.Spaces.Iθ * Real.exp (-(z / 2)) := by
            rw [setIntegral_const]; ring
    refine Integrable.mono' (hexp.const_mul (C * volume.real Work.Spaces.Iθ)) ?_ hbound
    exact haesm_joint.integral_prod_right'

end Work.R1G
