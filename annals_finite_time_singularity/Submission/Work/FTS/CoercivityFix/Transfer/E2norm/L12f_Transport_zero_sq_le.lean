import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.H2.Qang_sq_leQ
import Submission.Work.FTS.H2.QangAux
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.C0D_le
import Submission.Work.Coercivity.sq_integral_mul_le
import Submission.Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.C0_eq_density
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.theta_A2_int_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.z_A1_sq_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.B_sq_prod_eq_HkSq
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.A_sq_prod_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# `(L₁₂(Transport f)(0))² ≤ 16·|D_θ f|²_{ℋⁿ}`

The `L₁₂`-zero-mode `C0 f = L₁₂(Transport f)(0)` — the constant of the projector term of
`𝓛_Γ^T` — is controlled by the *angular* derivative `D_θ f` alone, uniformly in `α ∈ (0,1]`
and in `n ≤ 3`.  The proof is a single Cauchy–Schwarz on the product measure
`(volume|Iz) ⊗ (volume|Iθ)`:

`C0 f = ∫∫ 3 K(θ) D_θ f(z,θ)/(z(1+z)) dθ dz = ∫∫ A·B`, with

`A(z,θ) = 3 K(θ)·z/(1+z)³·sin(2θ)^{η/2}`,  `B(z,θ) = D_θ f(z,θ)·w(z)/sin(2θ)^{η/2}`,

whose squares are integrable (`A²` is a product of two explicitly bounded factors and
`B² = HkIntegrand α 0 (D_θ f)` is exactly a summand of the `ℋⁿ` integrand).  The constant
`16` is the crude product of the two one-dimensional bounds
`∫_z (z/(1+z)³)² ≤ 1/16` and `∫_θ 9 K(θ)² sin(2θ)^η ≤ 162`.

The three numerical/structural inputs are proved in the sibling modules `C0_eq_density`
(the unfolding of `C0`), `A_sq_prod_le` and `B_sq_prod_eq_HkSq`.
-/

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

/-- `cwB f` is a.e. strongly measurable on the product measure as soon as `f` is smooth on
the open quadrant. -/
private theorem cwB_aesm {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad f) :
    AEStronglyMeasurable (cwB f) cwμ := by
  have hDth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (hsm.DthIter 1).continuousOn.mono (fun p hp => by
      refine ⟨?_, ?_⟩
      · have h1 : (0 : ℝ) < p.1 := hp.1
        show (-1 : ℝ) < p.1
        linarith
      · exact hp.2)
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

/-! ## The Cauchy–Schwarz bound -/

/-- **The `ℋ⁰`-bound for `C0`**: `(C0 f)² ≤ 16 |D_θ f|²_{ℋ⁰}` for a smooth `f` whose
angular derivative lies in `ℋ⁰`. -/
private theorem C0_sq_le_HkSq0 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f)
    (hmem : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f)) :
    (Work.Coercivity.C0 f) ^ 2 ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by
  have hA2 : Integrable (fun p : ℝ × ℝ => cwA p ^ 2) cwμ := by
    simpa only [cwA, cwμ] using A_sq_prod_le.1
  have hA2le : ∫ p, cwA p ^ 2 ∂cwμ ≤ 16 := by
    simpa only [cwA, cwμ] using A_sq_prod_le.2
  have hB2 : Integrable (fun p : ℝ × ℝ => cwB f p ^ 2) cwμ := by
    simpa only [cwB, cwμ] using (B_sq_prod_eq_HkSq α hsm hmem).1
  have hB2val : ∫ p, cwB f p ^ 2 ∂cwμ = Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by
    simpa only [cwB, cwμ] using (B_sq_prod_eq_HkSq α hsm hmem).2
  have hABint : Integrable (fun p : ℝ × ℝ => cwA p * cwB f p) cwμ := by
    refine MeasureTheory.Integrable.mono' ((hA2.add hB2).const_mul (1 / 2))
      (cwA_measurable.aestronglyMeasurable.mul (cwB_aesm hsm)) ?_
    filter_upwards with p
    rw [Real.norm_eq_abs, abs_mul]
    show |cwA p| * |cwB f p| ≤ 1 / 2 * (cwA p ^ 2 + cwB f p ^ 2)
    nlinarith [two_mul_le_add_sq (|cwA p|) (|cwB f p|), sq_abs (cwA p), sq_abs (cwB f p)]
  have hC0 : Work.Coercivity.C0 f = ∫ p, cwA p * cwB f p ∂cwμ := by
    rw [C0_eq_density f]
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
          cwA_measurable.aestronglyMeasurable (cwB_aesm hsm) hA2 hB2
    _ = (∫ p, cwA p ^ 2 ∂cwμ) * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := by rw [hB2val]
    _ ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) :=
        mul_le_mul_of_nonneg_right hA2le (Work.Spaces.HkSq_nonneg α 0 _)

/-! ## The target -/

theorem L12f_Transport_zero_sq_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.Nonlin.CoerAdm α f →
        (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
          ≤ C * Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
  refine ⟨16, by norm_num, ?_⟩
  intro α hα hα1 n hn f hf
  have hsm : Work.FTS.LocData.SmoothQuad f := hf.reg.1
  have hmem0 : Work.Spaces.HkMem α 0 (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α 0 (by linarith)
      (Work.FTS.GalerkinFix.RegQ.regQ_mono hf.reg (by norm_num))
  have hmemn : Work.Spaces.HkMem α n (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityFix.E2Bound.HkMem_dth_of_RegQ_ge α n (by linarith)
      (Work.FTS.GalerkinFix.RegQ.regQ_mono hf.reg (by omega))
  have hmono : Work.Spaces.HkSq α 0 (Work.Spaces.Dth f)
      ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.zero_le n) hmemn
  have hkey := C0_sq_le_HkSq0 (α := α) hsm hmem0
  change (Work.Coercivity.C0 f) ^ 2 ≤ 16 * Work.Spaces.HkSq α n (Work.Spaces.Dth f)
  calc (Work.Coercivity.C0 f) ^ 2 ≤ 16 * Work.Spaces.HkSq α 0 (Work.Spaces.Dth f) := hkey
    _ ≤ 16 * Work.Spaces.HkSq α n (Work.Spaces.Dth f) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)

end Work.FTS.CoercivityFix.Transfer.E2norm
