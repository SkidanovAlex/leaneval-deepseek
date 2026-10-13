/-
# `(C₀ f)² ≤ 16·|D_θ f|²_{ℋ⁰}` on the open quadrant

`C0 f = L₁₂(Transport f)(0)` is the constant of the projector-derivative term `Z7` of the
`D_z`-decomposition of `𝓛_Γ^T`.  It is controlled by the *angular* derivative alone:

  `(C₀ f)² ≤ 16 · |D_θ f|²_{ℋ⁰}`,

uniformly in `α` and without any hypothesis on `f` beyond smoothness on the open quadrant
and `HkMem α 0 (D_θ f)`.

This is the open-quadrant (`SmoothOpen`, the class of a localised datum) port of
`Work.FTS.CoercivityFix.Transfer.E2norm.C0_sq_le_HkSq0`, which is stated for the frozen
class `SmoothQuad` (`C^∞` up to the boundary of the closed quadrant).  The only
class-dependent step of that proof is the almost-everywhere strong measurability of the
Cauchy–Schwarz factor `B = D_θ f · w/sin(2θ)^{η/2}`; with `SmoothOpen` it comes from
`SmoothOpen.Dth` (continuity of `D_θ f` on the open quadrant) and
`Work.Spaces.aesm_of_continuousOn_Qd` instead of `SmoothQuad.DthIter`.

The proof is a single Cauchy–Schwarz on the product measure `(volume|Iz) ⊗ (volume|Iθ)`:

`C0 f = ∫∫ 3 K(θ) D_θ f(z,θ)/(z(1+z)) dθ dz = ∫∫ A·B`, with

`A(z,θ) = 3 K(θ)·z/(1+z)³·sin(2θ)^{η/2}`,  `B(z,θ) = D_θ f(z,θ)·w(z)/sin(2θ)^{η/2}`,

whose squares are integrable (`A²` is a product of two explicitly bounded one-dimensional
factors — `A_sq_prod_le` — and `B²` is exactly `HkIntegrand α 0 (D_θ f)`).  The constant
`16` is the crude product `(1/16)·162 = 10.125 ≤ 16` of `∫_z (z/(1+z)³)² = 1/30` and
`∫_θ 9 K(θ)² sin(2θ)^η ≤ 162`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Transfer.E2_norm
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.C0_eq_density
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Coercivity.sq_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The angular factor `3 K(θ)·z/(1+z)³·sin(2θ)^{η/2}` of the Cauchy–Schwarz weight. -/
private noncomputable def cwA (p : ℝ × ℝ) : ℝ :=
  3 * Work.Spaces.K p.2 * (p.1 / (1 + p.1) ^ 3)
    * (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)

/-- The `D_θ f`-factor of the Cauchy–Schwarz weight.  Its square is exactly
`HkIntegrand α 0 (D_θ f)`. -/
private noncomputable def cwB (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Work.Spaces.Dth f p.1 p.2
    * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))

/-- The product measure `(volume|Iz) ⊗ (volume|Iθ)`. -/
private noncomputable def cwμ : Measure (ℝ × ℝ) :=
  (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)

/-! ## Elementary facts about the two weights -/

/-- `Iθ` agrees a.e. with its interior, so angular identities need only hold on
`(0, π/2)`. -/
private theorem Iθ_restrict_congr : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
  (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm

/-- `cwA` is measurable (it is a product of measurable functions; the `sin(2θ)^{η/2}`
factor is measurable because `x ↦ x^{η/2}` is continuous, `η/2 > 0`). -/
private theorem cwA_measurable : Measurable cwA := by
  have hK : Measurable (fun p : ℝ × ℝ => Work.Spaces.K p.2) := by
    apply Continuous.measurable
    show Continuous fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2
    fun_prop
  have hrat : Measurable (fun p : ℝ × ℝ => p.1 / (1 + p.1) ^ 3) :=
    measurable_fst.div ((measurable_const.add measurable_fst).pow_const 3)
  have hrpow : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) :=
    (Real.continuous_rpow_const (by norm_num [Work.Spaces.eta])).measurable.comp
      ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2)).measurable)
  exact ((hK.const_mul 3).mul hrat).mul hrpow

/-- `cwB f` is a.e. strongly measurable on the product measure as soon as `f` is `C^∞` on
the **open** quadrant: `D_θ f` is continuous there, and the complement of the open quadrant
inside `Iz ×ˢ Iθ` is null. -/
private theorem cwB_aesm {f : ℝ → ℝ → ℝ} (hO : Work.FTS.EllipticEst.SmoothOpen f) :
    AEStronglyMeasurable (cwB f) cwμ := by
  have hDth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hO.Dth).continuousOn
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2) cwμ :=
    Work.Spaces.aesm_of_continuousOn_Qd _ hDth
  have h2 : Measurable (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) := by
    have hw : Measurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) := by
      show Measurable fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2
      exact ((measurable_const.add measurable_fst).pow_const 2).div
        (measurable_fst.pow_const 2)
    have hrpow : Measurable (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) :=
      (Real.continuous_rpow_const (by norm_num [Work.Spaces.eta])).measurable.comp
        ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.sin (2 * p.2)).measurable)
    exact hw.div hrpow
  exact h1.mul h2.aestronglyMeasurable

/-- The pointwise identity underlying the Cauchy–Schwarz decomposition (for `z > 0` and
`θ` in the interior of `Iθ`). -/
private theorem cwA_mul_cwB {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    3 * Work.Spaces.K θ * Work.Spaces.Dth f z θ / (z * (1 + z))
      = cwA (z, θ) * cwB f (z, θ) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsne : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hs _)
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 : ℝ) + z ≠ 0 := by positivity
  simp only [cwA, cwB, Work.Spaces.w]
  field_simp

/-! ## `B²` integrates to `HkSq α 0 (D_θ f)` -/

/-- At `k = 0` the `ℋ⁰`-integrand of `D_θ f` is *definitionally* the square of
`D_θ f · w/ sin(2θ)^{η/2}`, and the iterated integral of that square is `HkSq α 0 (D_θ f)`.
The only place the smoothness class enters is the a.e. strong measurability. -/
private theorem B_sq_prod_eq_HkSq_O (α : ℝ) {f : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen f)
    (hmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f)) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (Work.Spaces.Dth f p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      ∫ p, (Work.Spaces.Dth f p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))
        = Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by
  have hpt : ∀ z θ : ℝ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dth f) z θ
      = (Work.Spaces.Dth f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    intro z θ
    simp only [Work.Spaces.HkIntegrand]
    simp
  have hAE : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.Dth f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hb : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => cwB f p * cwB f p) cwμ :=
      (cwB_aesm hO).mul (cwB_aesm hO)
    simpa only [cwB, cwμ, pow_two] using hb
  obtain ⟨hint, hval⟩ := Work.Spaces.integrable_prod_of_iterated
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
    (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => (Work.Spaces.Dth f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (fun z θ => sq_nonneg _) hAE
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      (hmem.1 z hz).congr (Filter.Eventually.of_forall fun θ => hpt z θ))
    (by
      have heq : (fun a : ℝ => ∫ b, (Work.Spaces.Dth f a b
              * (Work.Spaces.w a / (Real.sin (2 * b)) ^ (Work.Spaces.eta / 2))) ^ 2
                ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          = fun a : ℝ => ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.Dth f) a θ := by
        funext a
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun b => (hpt a b).symm)
      rw [heq]
      exact hmem.2)
  refine ⟨hint, ?_⟩
  rw [hval]
  simp only [Work.Spaces.HkSq]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  exact (hpt a b).symm

/-! ## The target -/

/-- **The `ℋ⁰`-bound for `C0` on the open quadrant**:
`(C0 f)² ≤ 16·|D_θ f|²_{ℋ⁰}` for `f` smooth on `(0,∞) × (0,π/2)` whose angular derivative
lies in `ℋ⁰`. -/
theorem C0_sq_le_HkSq0_O {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f)) :
    (Work.Coercivity.C0 f) ^ 2 ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by
  have hA2 : Integrable (fun p : ℝ × ℝ => cwA p ^ 2) cwμ := by
    simpa only [cwA, cwμ] using
      Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le.1
  have hA2le : ∫ p, cwA p ^ 2 ∂cwμ ≤ 16 := by
    simpa only [cwA, cwμ] using
      Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le.2
  have hB2 : Integrable (fun p : ℝ × ℝ => cwB f p ^ 2) cwμ := by
    simpa only [cwB, cwμ] using (B_sq_prod_eq_HkSq_O α hO hmem).1
  have hB2val : ∫ p, cwB f p ^ 2 ∂cwμ = Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by
    simpa only [cwB, cwμ] using (B_sq_prod_eq_HkSq_O α hO hmem).2
  have hABint : Integrable (fun p : ℝ × ℝ => cwA p * cwB f p) cwμ := by
    refine MeasureTheory.Integrable.mono' ((hA2.add hB2).const_mul (1 / 2))
      (cwA_measurable.aestronglyMeasurable.mul (cwB_aesm hO)) ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    show |cwA p| * |cwB f p| ≤ 1 / 2 * (cwA p ^ 2 + cwB f p ^ 2)
    nlinarith [two_mul_le_add_sq (|cwA p|) (|cwB f p|), sq_abs (cwA p), sq_abs (cwB f p)]
  have hC0 : Work.Coercivity.C0 f = ∫ p, cwA p * cwB f p ∂cwμ := by
    rw [Work.FTS.CoercivityFix.Transfer.E2norm.C0_eq_density f]
    have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          3 * Work.Spaces.K θ * Work.Spaces.Dth f z θ / (z * (1 + z)))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, cwA (z, θ) * cwB f (z, θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hpos
      · subst h0
        simp [cwA, cwB]
      · refine MeasureTheory.integral_congr_ae ?_
        rw [MeasureTheory.Measure.restrict_congr_set Iθ_restrict_congr]
        exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
          (fun θ hθ => cwA_mul_cwB hpos hθ)
    rw [h1, cwμ]
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => cwA p * cwB f p) hABint).symm
  calc (Work.Coercivity.C0 f) ^ 2
      = (∫ p, cwA p * cwB f p ∂cwμ) ^ 2 := by rw [hC0]
    _ ≤ (∫ p, cwA p ^ 2 ∂cwμ) * (∫ p, cwB f p ^ 2 ∂cwμ) :=
        Work.Coercivity.sq_integral_mul_le cwμ cwA (cwB f)
          cwA_measurable.aestronglyMeasurable (cwB_aesm hO) hA2 hB2
    _ = (∫ p, cwA p ^ 2 ∂cwμ) * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by rw [hB2val]
    _ ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) :=
        mul_le_mul_of_nonneg_right hA2le (Work.Spaces.HkSq_nonneg α 0 _)

end Work.FTS.StrongEps.EpsE4Thr.E2O
