/-
Copyright: work module for the Elgindi finite-time singularity project (Annals 194 (3) 2021,
§"Elliptic Regularity Estimates").

# The angular self-form of `L₀` for an `a.e.`-regular (honest) slice

The `θ`-slice of the solution is only known to be `C^∞` on the *open* interval `(0, π/2)`,
continuous on `[0, π/2]`, with vanishing endpoint values and `σ`-square-integrable second
derivative (`σ = sEta = sin(2θ)^{-η}`).  In that class the smooth-`Icc` lemma
`Work.FTS.EllipticEst.Lzero_self_form` does not apply (`C²` on the closed interval is not
implied), but the identity

  `∫_{Iθ} L₀(v) v = ∫_{Iθ} (v')² + (1/2) ∫_{Iθ} (v/cos θ)² - 6 ∫_{Iθ} v²`

still holds, by the *open-interval* fundamental theorem of calculus
(`Work.FTS.EllipticEst.Honest.integral_Ioo_eq_sub_of_tendsto`) applied to the antiderivative
`F θ = -(v'θ)(v θ) + (1/2) tan θ · v(θ)²`, whose derivative is the integrand and which vanishes
at both endpoints.

The hypotheses are exactly the ones available in the `H²`-estimate for almost every `z`, and the
weighted integrability hypothesis (with `sEta ≥ 1` on `(0,π/2)`) supplies the integrability of
`v''`, hence — through Newton–Lebesgue — the linear vanishing of `v` at `π/2`, the boundedness of
`v'`, of `v` and of `v / cos θ`, and the integrability of the remaining pieces of the
antiderivative's derivative (the last one being delegated as `Lzero1MulSelfIntegrable`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Lzero_self_form
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceDerivBound
import Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceULinearRight
import Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceUDivCosBdd
import Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceAntiderivDeriv
import Submission.Work.FTS.EllipticEst.Honest.SelfAux.SliceTendstoAntiderivZero
import Submission.Work.FTS.EllipticEst.H2W.AeProof.Lzero1MulSelfIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeProof

set_option maxHeartbeats 1000000

/-- **The angular self-form of `L₀` for a slice that is smooth on the open interval only.**
For `f` of class `C^∞` on `(0, π/2)`, continuous on `[0, π/2]`, with `f 0 = 0`, `f (π/2) = 0`
and `σ`-square-integrable second derivative (`σ = sEta`), the pairing of `Lzero1 f` with `f` is
the quadratic form `∫ (f')² + (1/2) ∫ (f/cos)² - 6 ∫ f²`. -/
private theorem sliceSelfForm (f : ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n f (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv f t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 f θ * f θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2)
        + (1 / 2) * (∫ θ in Work.Spaces.Iθ, (f θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) := by
  have hlt : (0 : ℝ) < Real.pi / 2 := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- ### 1. Integrability of `f''` on the open interval.
  have hsq : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => deriv f t) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_sq_of_integrableOn_mul_sEta f hint
  have habs : MeasureTheory.IntegrableOn
      (fun θ : ℝ => |deriv (fun t : ℝ => deriv f t) θ|) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.sliceLim_integrableOn_abs_of_integrableOn_sq f hsq
  have hf2 : MeasureTheory.IntegrableOn
      (fun θ : ℝ => deriv (fun t : ℝ => deriv f t) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Integrable.mono' habs
      (measurable_deriv (fun t : ℝ => deriv f t)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => le_of_eq (Real.norm_eq_abs _))
  -- ### 2. The endpoint limits of `f`, from continuity on the closed interval.
  have hmem0' : Set.Ioo (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlt),
      eventually_mem_nhdsWithin] with s hs hs'
    exact ⟨hs', hs⟩
  have hmem0 : Set.Icc (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    mem_of_superset hmem0' (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hmempi' : Set.Ioo (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) := by
    rw [← nhdsWithin_Ioo_eq_nhdsLT hlt]
    exact self_mem_nhdsWithin
  have hmempi : Set.Icc (0 : ℝ) (Real.pi / 2)
      ∈ nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) :=
    mem_of_superset hmempi' (fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  have hlim0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcw : ContinuousWithinAt f (Set.Icc (0 : ℝ) (Real.pi / 2)) 0 :=
      hcont.continuousWithinAt ⟨le_rfl, hlt.le⟩
    have hle : nhdsWithin (0 : ℝ) (Set.Ioi 0)
        ≤ nhdsWithin (0 : ℝ) (Set.Icc 0 (Real.pi / 2)) := nhdsWithin_le_iff.mpr hmem0
    simpa [h0] using hcw.mono_left hle
  have hlimpi : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    have hcw : ContinuousWithinAt f (Set.Icc (0 : ℝ) (Real.pi / 2)) (Real.pi / 2) :=
      hcont.continuousWithinAt ⟨by linarith, le_rfl⟩
    have hle : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))
        ≤ nhdsWithin (Real.pi / 2) (Set.Icc 0 (Real.pi / 2)) := nhdsWithin_le_iff.mpr hmempi
    simpa [h1] using hcw.mono_left hle
  -- ### 3. The bounds `M` (for `f'`), `B` (for `f`) and `K` (for `f / cos`).
  obtain ⟨M, hM0, hM⟩ :=
    Work.FTS.EllipticEst.Honest.SelfAux.SliceDerivBound f (hsm 2) hf2
  have hlin : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M * (Real.pi / 2 - θ) :=
    Work.FTS.EllipticEst.Honest.SelfAux.SliceULinearRight f (hsm 1) hM hlimpi
  have hB : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M * (Real.pi / 2) := fun θ hθ =>
    (hlin θ hθ).trans (mul_le_mul_of_nonneg_left (by linarith [hθ.1]) hM0)
  obtain ⟨K, hK⟩ := Work.FTS.EllipticEst.Honest.SelfAux.SliceUDivCosBdd f hB hlin
  obtain ⟨hl0, hlpi⟩ :=
    Work.FTS.EllipticEst.Honest.SelfAux.SliceTendstoAntiderivZero f hlim0 hlimpi hM hB hK
  -- ### 4. Integrability of `Lzero1 f · f` (delegated) and of the three quadratic pieces.
  have hLint : MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    Lzero1MulSelfIntegrable (hsm 2) hB hM hK habs
  have hderiv_cont : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm 2).continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hsq_int : MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (M ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact ((hderiv_cont.pow 2).aemeasurable measurableSet_Ioo).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM θ hθ) 2
  have hu2_int : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ ((M * (Real.pi / 2)) ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact (((hsm 1).continuousOn.pow 2).aemeasurable measurableSet_Ioo).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB θ hθ) 2
  have hdiv_cont : ContinuousOn (fun θ => f θ / Real.cos θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm 1).continuousOn.div Real.continuous_cos.continuousOn
      (fun θ hθ => ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩))
  have hdiv2_int : MeasureTheory.IntegrableOn (fun θ => (f θ / Real.cos θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (K ^ 2) ?_
    · rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
    · exact ((hdiv_cont.pow 2).aemeasurable measurableSet_Ioo).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hK θ hθ) 2
  -- ### 5. The fundamental theorem of calculus on the open interval.
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun s => -(deriv f s) * f s + (1 / 2) * Real.tan s * (f s) ^ 2)
        (Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2
          - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2) θ :=
    fun θ hθ => Work.FTS.EllipticEst.Honest.SelfAux.SliceAntiderivDeriv f hθ
      ((hsm 2).contDiffAt (isOpen_Ioo.mem_nhds hθ))
  have h_ab : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := hLint.sub hsq_int
  have h_abc : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2
        - (1 / 2) * (f θ / Real.cos θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    h_ab.sub (hdiv2_int.const_mul (1 / 2))
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2
        - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) :=
    h_abc.add (hu2_int.const_mul 6)
  have hzero : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2
        - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2) = 0 := by
    have h := Work.FTS.EllipticEst.Honest.integral_Ioo_eq_sub_of_tendsto hlt hderiv hGint hl0 hlpi
    simpa using h
  have hsplit : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 f θ * f θ - (deriv f θ) ^ 2
        - (1 / 2) * (f θ / Real.cos θ) ^ 2 + 6 * (f θ) ^ 2)
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 f θ * f θ)
        - (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv f θ) ^ 2)
        - (1 / 2) * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ / Real.cos θ) ^ 2)
        + 6 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2) := by
    rw [integral_add h_abc (hu2_int.const_mul 6),
      integral_sub h_ab (hdiv2_int.const_mul (1 / 2)),
      integral_sub hLint hsq_int, integral_const_mul, integral_const_mul]
  have hmain : (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 f θ * f θ)
      = (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv f θ) ^ 2)
        + (1 / 2) * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2) := by
    linarith [hzero, hsplit]
  -- ### 6. Transfer the four integrals from `(0, π/2)` to `Iθ = [0, π/2]`.
  have e1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.Lzero1 f θ * f θ)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 f θ * f θ := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e2 : (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv f θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e3 : (∫ θ in Work.Spaces.Iθ, (f θ / Real.cos θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ / Real.cos θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  have e4 : (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2)
      = ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (f θ) ^ 2 := by
    simp only [Work.Spaces.Iθ]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
  rw [e1, e2, e3, e4]
  exact hmain

theorem AeSliceSelfForm (u : ℝ → ℝ → ℝ) (z : ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2)))
    (h0 : u z 0 = 0) (h1 : u z (Real.pi / 2) = 0)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t : ℝ => deriv (fun θ' => u z θ') t) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Lzero u z θ * u z θ)
      = (∫ θ in Work.Spaces.Iθ, (deriv (fun θ' => u z θ') θ) ^ 2)
        + (1 / 2) * (∫ θ in Work.Spaces.Iθ, (u z θ / Real.cos θ) ^ 2)
        - 6 * (∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2) := by
  have hL : ∀ θ : ℝ, Work.Elliptic.Lzero u z θ
      = Work.FTS.EllipticEst.Lzero1 (fun θ' : ℝ => u z θ') θ := by
    intro θ
    rw [Work.Elliptic.Lzero_eq_deriv, Work.FTS.EllipticEst.Lzero1]
  simp only [hL]
  exact sliceSelfForm (fun θ' : ℝ => u z θ') hsm hcont h0 h1 hint

end Work.FTS.EllipticEst.H2W.AeProof
