import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.TraceAux
import Submission.Work.FTS.EllSol.PkgK5.TraceEngine.agmonCutChainPos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5.TraceEngine

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The positivity-free Agmon cut chain -/

/-- The `m`-level Agmon chain of `InterpTraceCore`, without the positivity hypothesis on `m`:
the degenerate case is removed by applying the positive version to `m + δ·sin²(2θ)` and letting
`δ → 0⁺`. -/
theorem agmonChainShift
    (hAgmon : ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (1 / 200) * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
          + 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ))
    {m P A B : ℝ → ℝ}
    (hm : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt m (2 * P θ) θ)
    (hP : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt P (A θ + B θ) θ)
    (hAB : ContinuousOn (fun θ : ℝ => A θ + B θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hmnn : ∀ θ : ℝ, 0 ≤ m θ)
    (hAnn : ∀ θ : ℝ, 0 ≤ A θ)
    (hCS : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), P θ ^ 2 ≤ m θ * A θ)
    (htr0 : Filter.Tendsto m (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htr1 : Filter.Tendsto m (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : MeasureTheory.IntegrableOn (fun θ : ℝ => A θ
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hmI : MeasureTheory.IntegrableOn (fun θ : ℝ => m θ
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ : ℝ => B θ
      * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (1 / 200) * (∫ θ in Work.Spaces.Iθ, A θ * Work.FTS.EllipticEst.thEta θ)
      ≤ 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, m θ * Work.FTS.EllipticEst.thEta θ)
        - ∫ θ in Work.Spaces.Iθ, B θ * Work.FTS.EllipticEst.thEta θ := by
  -- the σ-integrable bounded angular factors
  have hσint : MeasureTheory.IntegrableOn Work.FTS.EllipticEst.thEta Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableOn_thEta.1
  have hsint0 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (Real.sin (2 * θ)) ^ 2) Work.Spaces.Iθ :=
    hσint.mul_continuousOn
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2).continuousOn)
      isCompact_Icc
  have hsint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    hsint0.congr (Filter.Eventually.of_forall (fun θ => by ring))
  have hcint0 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (4 * (Real.cos (2 * θ)) ^ 2)) Work.Spaces.Iθ :=
    hσint.mul_continuousOn
      ((continuous_const.mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2)).continuousOn)
      isCompact_Icc
  have hcint : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    hcint0.congr (Filter.Eventually.of_forall (fun θ => by ring))
  have h4int0 : MeasureTheory.IntegrableOn (fun θ : ℝ => Work.FTS.EllipticEst.thEta θ
      * (4 * Real.cos (4 * θ))) Work.Spaces.Iθ :=
    hσint.mul_continuousOn
      ((continuous_const.mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).continuousOn)
      isCompact_Icc
  have h4int : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ :=
    h4int0.congr (Filter.Eventually.of_forall (fun θ => by ring))
  -- the slack constant and the target value
  set Λ : ℝ := 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ,
        (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      - (∫ θ in Work.Spaces.Iθ, (4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)
      + (199 / 200) * (∫ θ in Work.Spaces.Iθ,
        (4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) with hΛ
  set M0 : ℝ := 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ,
        m θ * Work.FTS.EllipticEst.thEta θ)
      - ∫ θ in Work.Spaces.Iθ, B θ * Work.FTS.EllipticEst.thEta θ with hM0
  have hlim : Filter.Tendsto (fun δ : ℝ => M0 + δ * Λ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds M0) := by
    have h0 : Filter.Tendsto (fun δ : ℝ => δ * Λ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (0 * Λ)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul tendsto_const_nhds
    have h1 : Filter.Tendsto (fun δ : ℝ => M0 + δ * Λ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (M0 + 0 * Λ)) := tendsto_const_nhds.add h0
    simpa using h1
  -- the per-δ bound
  have key : ∀ δ : ℝ, 0 < δ → (1 / 200) * (∫ θ in Work.Spaces.Iθ,
        A θ * Work.FTS.EllipticEst.thEta θ) ≤ M0 + δ * Λ := by
    intro δ hδ
    -- the regularised data
    set mm : ℝ → ℝ := fun θ => m θ + δ * (Real.sin (2 * θ)) ^ 2 with hmm
    set PP : ℝ → ℝ := fun θ => P θ + δ * Real.sin (4 * θ) with hPP
    set AA : ℝ → ℝ := fun θ => A θ + δ * (4 * (Real.cos (2 * θ)) ^ 2) with hAA
    set BB : ℝ → ℝ := fun θ => B θ
      + δ * (4 * Real.cos (4 * θ) - 4 * (Real.cos (2 * θ)) ^ 2) with hBB
    -- σ-integrability of the shifted summands
    have hmmI : MeasureTheory.IntegrableOn (fun θ : ℝ => mm θ
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
      rw [hmm]
      have h' : (fun θ : ℝ => (m θ + δ * (Real.sin (2 * θ)) ^ 2)
          * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => m θ * Work.FTS.EllipticEst.thEta θ
            + δ * ((Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
        funext θ; ring
      rw [h']
      exact hmI.add (hsint.const_mul δ)
    have hAAI : MeasureTheory.IntegrableOn (fun θ : ℝ => AA θ
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
      rw [hAA]
      have h' : (fun θ : ℝ => (A θ + δ * (4 * (Real.cos (2 * θ)) ^ 2))
          * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => A θ * Work.FTS.EllipticEst.thEta θ
            + δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) := by
        funext θ; ring
      rw [h']
      exact hA.add (hcint.const_mul δ)
    have hBBI : MeasureTheory.IntegrableOn (fun θ : ℝ => BB θ
        * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := by
      rw [hBB]
      have h' : (fun θ : ℝ => (B θ + δ * (4 * Real.cos (4 * θ)
          - 4 * (Real.cos (2 * θ)) ^ 2)) * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => B θ * Work.FTS.EllipticEst.thEta θ
            + δ * ((4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)
            - δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) := by
        funext θ; ring
      rw [h']
      exact (hB.add (h4int.const_mul δ)).sub (hcint.const_mul δ)
    -- the derivative facts
    have hmm' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt mm (2 * PP θ) θ := by
      intro θ hθ
      have h := (hm θ hθ).add ((hasDerivAt_sinSq θ).const_mul δ)
      have hs4 : Real.sin (4 * θ) = 2 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
        rw [show (4 : ℝ) * θ = 2 * (2 * θ) by ring, Real.sin_two_mul]
      have hv : 2 * P θ + δ * (4 * Real.sin (2 * θ) * Real.cos (2 * θ))
          = 2 * (P θ + δ * Real.sin (4 * θ)) := by
        rw [hs4]; ring
      rw [hv] at h
      exact h
    have hPP' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt PP (AA θ + BB θ) θ := by
      intro θ hθ
      have h := (hP θ hθ).add ((hasDerivAt_sinFour θ).const_mul δ)
      have hv : A θ + B θ + δ * (4 * Real.cos (4 * θ))
          = (A θ + δ * (4 * (Real.cos (2 * θ)) ^ 2))
            + (B θ + δ * (4 * Real.cos (4 * θ) - 4 * (Real.cos (2 * θ)) ^ 2)) := by ring
      rw [hv] at h
      exact h
    have hAB' : ContinuousOn (fun θ : ℝ => AA θ + BB θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have hc : Continuous (fun θ : ℝ => 4 * Real.cos (4 * θ)) :=
        continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      have hcont : ContinuousOn (fun θ : ℝ => (A θ + B θ) + δ * (4 * Real.cos (4 * θ)))
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hAB.add (hc.const_mul δ).continuousOn
      refine hcont.congr (fun θ _ => ?_)
      rw [hAA, hBB]; ring
    have hmpos' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < mm θ := by
      intro θ hθ
      rw [hmm]
      have hs : 0 < (Real.sin (2 * θ)) ^ 2 :=
        pow_pos (Work.FTS.EllipticEst.sin_two_pos hθ) 2
      nlinarith [hmnn θ, hδ, hs]
    have hCS' : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), PP θ ^ 2 ≤ mm θ * AA θ := by
      intro θ hθ
      rw [hmm, hPP, hAA]
      have hm0 : 0 ≤ m θ := hmnn θ
      have hA0 : 0 ≤ A θ := hAnn θ
      have hPbd : |P θ| ≤ Real.sqrt (m θ) * Real.sqrt (A θ) := by
        have h1 : P θ ^ 2 ≤ (Real.sqrt (m θ) * Real.sqrt (A θ)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hm0, Real.sq_sqrt hA0]
          exact hCS θ hθ
        calc |P θ| = Real.sqrt (P θ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt ((Real.sqrt (m θ) * Real.sqrt (A θ)) ^ 2) := Real.sqrt_le_sqrt h1
          _ = |Real.sqrt (m θ) * Real.sqrt (A θ)| := Real.sqrt_sq_eq_abs _
          _ = Real.sqrt (m θ) * Real.sqrt (A θ) :=
              abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      have hw : 0 ≤ Real.sin (2 * θ) := (Work.FTS.EllipticEst.sin_two_pos hθ).le
      have hs4 : Real.sin (4 * θ) = 2 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
        rw [show (4 : ℝ) * θ = 2 * (2 * θ) by ring, Real.sin_two_mul]
      have hstep1 : |P θ + δ * Real.sin (4 * θ)|
          ≤ |P θ| + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|) := by
        calc |P θ + δ * Real.sin (4 * θ)|
            ≤ |P θ| + |δ * Real.sin (4 * θ)| := abs_add_le _ _
          _ = |P θ| + δ * |Real.sin (4 * θ)| := by rw [abs_mul, abs_of_pos hδ]
          _ = |P θ| + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|) := by
              rw [hs4, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
                abs_of_nonneg hw]
      have hstep2 : (P θ + δ * Real.sin (4 * θ)) ^ 2
          ≤ (Real.sqrt (m θ) * Real.sqrt (A θ)
            + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|)) ^ 2 := by
        have hb : 0 ≤ Real.sqrt (m θ) * Real.sqrt (A θ)
            + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|) := by positivity
        have h1 : |P θ + δ * Real.sin (4 * θ)| ≤ Real.sqrt (m θ) * Real.sqrt (A θ)
            + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|) := by linarith [hstep1, hPbd]
        calc (P θ + δ * Real.sin (4 * θ)) ^ 2
            = |P θ + δ * Real.sin (4 * θ)| ^ 2 := (sq_abs _).symm
          _ ≤ (Real.sqrt (m θ) * Real.sqrt (A θ)
                + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|)) ^ 2 := by
              rw [pow_two, pow_two]
              exact mul_self_le_mul_self (abs_nonneg _) h1
      have hstep3 : (Real.sqrt (m θ) * Real.sqrt (A θ)
            + δ * (2 * Real.sin (2 * θ) * |Real.cos (2 * θ)|)) ^ 2
          ≤ (m θ + δ * (Real.sin (2 * θ)) ^ 2)
            * (A θ + δ * (4 * (Real.cos (2 * θ)) ^ 2)) := by
        have h1 : Real.sqrt (m θ) ^ 2 = m θ := Real.sq_sqrt hm0
        have h2 : Real.sqrt (A θ) ^ 2 = A θ := Real.sq_sqrt hA0
        have h3 : |Real.cos (2 * θ)| ^ 2 = (Real.cos (2 * θ)) ^ 2 := sq_abs _
        have hgen : ∀ u v w c e : ℝ, (u * v + e * (2 * w * c)) ^ 2
            = (u ^ 2 + e * w ^ 2) * (v ^ 2 + 4 * e * c ^ 2)
              - e * (2 * c * u - w * v) ^ 2 := by
          intro u v w c e; ring
        have hgen' := hgen (Real.sqrt (m θ)) (Real.sqrt (A θ)) (Real.sin (2 * θ))
          |Real.cos (2 * θ)| δ
        rw [h1, h2, h3] at hgen'
        rw [hgen']
        have hnn : 0 ≤ δ * (2 * |Real.cos (2 * θ)| * Real.sqrt (m θ)
            - Real.sin (2 * θ) * Real.sqrt (A θ)) ^ 2 :=
          mul_nonneg hδ.le (sq_nonneg _)
        linarith
      exact le_trans hstep2 hstep3
    -- the chain applied to the regularised data
    have htr0' : Filter.Tendsto mm (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hc : Continuous (fun θ : ℝ => δ * (Real.sin (2 * θ)) ^ 2) :=
        continuous_const.mul
          ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2)
      have h1 : Filter.Tendsto (fun θ : ℝ => δ * (Real.sin (2 * θ)) ^ 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa [hmm] using htr0.add h1
    have htr1' : Filter.Tendsto mm (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
        (nhds 0) := by
      have hc : Continuous (fun θ : ℝ => δ * (Real.sin (2 * θ)) ^ 2) :=
        continuous_const.mul
          ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2)
      have h1 : Filter.Tendsto (fun θ : ℝ => δ * (Real.sin (2 * θ)) ^ 2)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
        have h0 : (Real.sin (2 * (Real.pi / 2))) ^ 2 = 0 := by
          rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]; norm_num
        have hgoal : Filter.Tendsto (fun θ : ℝ => δ * (Real.sin (2 * θ)) ^ 2)
            (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
            (nhds (δ * (Real.sin (2 * (Real.pi / 2))) ^ 2)) :=
          (hc.tendsto (Real.pi / 2)).mono_left
            (nhdsWithin_le_nhds : 𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2) ≤ 𝓝 (Real.pi / 2))
        simpa [h0] using hgoal
      simpa [hmm] using htr1.add h1
    have hshift := agmonCutChainPos hAgmon (m := mm) (P := PP) (A := AA) (B := BB)
      hmm' hPP' hAB' hmpos' hCS' htr0' htr1' hAAI hmmI hBBI
    -- the three integral identities
    have eAA : (∫ θ in Work.Spaces.Iθ, AA θ * Work.FTS.EllipticEst.thEta θ)
        = (∫ θ in Work.Spaces.Iθ, A θ * Work.FTS.EllipticEst.thEta θ)
          + δ * (∫ θ in Work.Spaces.Iθ,
              (4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) := by
      rw [hAA]
      rw [show (fun θ : ℝ => (A θ + δ * (4 * (Real.cos (2 * θ)) ^ 2))
            * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => A θ * Work.FTS.EllipticEst.thEta θ
            + δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) from by
        funext θ; ring]
      rw [MeasureTheory.integral_add hA (hcint.const_mul δ), MeasureTheory.integral_const_mul]
    have emm : (∫ θ in Work.Spaces.Iθ, mm θ * Work.FTS.EllipticEst.thEta θ)
        = (∫ θ in Work.Spaces.Iθ, m θ * Work.FTS.EllipticEst.thEta θ)
          + δ * (∫ θ in Work.Spaces.Iθ,
              (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
      rw [hmm]
      rw [show (fun θ : ℝ => (m θ + δ * (Real.sin (2 * θ)) ^ 2)
            * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => m θ * Work.FTS.EllipticEst.thEta θ
            + δ * ((Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) from by
        funext θ; ring]
      rw [MeasureTheory.integral_add hmI (hsint.const_mul δ), MeasureTheory.integral_const_mul]
    have eBB : (∫ θ in Work.Spaces.Iθ, BB θ * Work.FTS.EllipticEst.thEta θ)
        = (∫ θ in Work.Spaces.Iθ, B θ * Work.FTS.EllipticEst.thEta θ)
          + δ * (∫ θ in Work.Spaces.Iθ,
              (4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)
          - δ * (∫ θ in Work.Spaces.Iθ,
              (4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ) := by
      have hI2 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
          δ * ((4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)) Work.Spaces.Iθ :=
        h4int.const_mul δ
      have hI3 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
          -(δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ)))
          Work.Spaces.Iθ := (hcint.const_mul δ).neg
      have hI23 : MeasureTheory.IntegrableOn (fun θ : ℝ =>
          δ * ((4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)
            + (-(δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ))))
          Work.Spaces.Iθ := hI2.add hI3
      rw [hBB]
      rw [show (fun θ : ℝ => (B θ + δ * (4 * Real.cos (4 * θ)
            - 4 * (Real.cos (2 * θ)) ^ 2)) * Work.FTS.EllipticEst.thEta θ)
          = fun θ : ℝ => B θ * Work.FTS.EllipticEst.thEta θ
            + (δ * ((4 * Real.cos (4 * θ)) * Work.FTS.EllipticEst.thEta θ)
              + (-(δ * ((4 * (Real.cos (2 * θ)) ^ 2) * Work.FTS.EllipticEst.thEta θ)))) from by
        funext θ; ring]
      rw [MeasureTheory.integral_add hB hI23]
      rw [MeasureTheory.integral_add hI2 hI3]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_neg,
        MeasureTheory.integral_const_mul]
      ring
    rw [eAA, emm, eBB] at hshift
    rw [hM0, hΛ]
    linarith [hshift]
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact key δ hδ)

end Work.FTS.EllSol.PkgK5.TraceEngine
