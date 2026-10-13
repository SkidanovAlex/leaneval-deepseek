/-
Copyright: work module for the Elgindi finite-time singularity project.

# The "cut chain" positivity lemma

Given the one-dimensional weighted Agmon inequality `hAgmon` (the statement of the sibling
`Work.FTS.EllSol.PkgK5.TraceEngine.sliceAgmonOpenCoreExplicit`, with the sharp constants
`1/200` and `2η`), together with a chain of profiles

  `m' = 2P`,  `P' = A + B`,  `m > 0` on `(0, π/2)`,  `P² ≤ m·A`,

and the endpoint vanishing `m → 0` at `0⁺` and `(π/2)⁻`, one gets

  `(1/200) ∫_{Iθ} A·σ ≤ 2η ∫_{Iθ} m·σ − ∫_{Iθ} B·σ`,   `σ = thEta = sin(2θ)^{-η}`.

**Proof.**  The whole content is the Agmon inequality applied to `f = √m` — the function
supplied by the sibling `Work.FTS.EllSol.PkgK5.InterpTrace.sqrt_m_calc`, which gives
`√m ∈ C²(0, π/2)`, `(√m)′² ≤ A` and `(√m)′² + √m·(√m)″ = A + B` pointwise on `(0, π/2)`.
Writing `I1 = ∫ (√m)′²σ`, `I2 = ∫ √m(√m)″σ`, `SA = ∫Aσ`, `SB = ∫Bσ`, `SM = ∫mσ`, Agmon reads

  `I1/200 ≤ −I2 + 2η·SM`,

while the pointwise identities give `I1 ≤ SA` and `I2 = SA + SB − I1`.  Substituting:

  `I1/200 ≤ −(SA + SB − I1) + 2η·SM`  ⟹  `SA + SB ≤ (199/200)I1 + 2η·SM ≤ (199/200)SA + 2η·SM`,

i.e. exactly `SA/200 ≤ 2η·SM − SB`.

The only measure-theoretic work is that the three integrands of the Agmon hypothesis have to be
produced for `f = √m`: the endpoint set `Iθ \ (0,π/2) = {0, π/2}` is null, so
`volume.restrict Iθ = volume.restrict (Ioo 0 (π/2))`, and on the open interval the identities
above turn `(√m)′²σ`, `(√m)²σ` and `√m(√m)″σ` into `A`-dominated, `m`-equal and
`(A + B − (√m)′²)`-equal integrands.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllSol.PkgK5.InterpTrace.sqrt_m_calc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open MeasureTheory Set Filter
open scoped Real Topology

local notation "σ" => Work.FTS.EllipticEst.thEta

theorem agmonCutChainPos {m P A B : ℝ → ℝ}
    (hAgmon : ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
      (1 / 200) * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        ≤ - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.thEta θ)
          + 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ))
    (hm : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt m (2 * P θ) θ)
    (hP : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt P (A θ + B θ) θ)
    (hAB : ContinuousOn (fun θ : ℝ => A θ + B θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (hmpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < m θ)
    (hCS : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), P θ ^ 2 ≤ m θ * A θ)
    (htr0 : Filter.Tendsto m (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htr1 : Filter.Tendsto m (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : MeasureTheory.IntegrableOn (fun θ : ℝ => A θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hmI : MeasureTheory.IntegrableOn (fun θ : ℝ => m θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn (fun θ : ℝ => B θ * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    (1 / 200) * (∫ θ in Work.Spaces.Iθ, A θ * Work.FTS.EllipticEst.thEta θ)
      ≤ 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, m θ * Work.FTS.EllipticEst.thEta θ)
        - ∫ θ in Work.Spaces.Iθ, B θ * Work.FTS.EllipticEst.thEta θ := by
  classical
  set g : ℝ → ℝ := fun θ => Real.sqrt (m θ) with hg
  -- The pointwise facts about `√m` supplied by the sibling `sqrt_m_calc`.
  have hSMC := Work.FTS.EllSol.PkgK5.InterpTrace.sqrt_m_calc hm hP hAB hmpos hCS
  have hC2g : ContDiffOn ℝ 2 g (Set.Ioo (0:ℝ) (Real.pi/2)) := by rw [hg]; exact hSMC.1
  have hderivsq_le : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), (deriv g θ)^2 ≤ A θ := by
    intro θ hθ; rw [hg]; exact hSMC.2.1 θ hθ
  have hident : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
      (deriv g θ)^2 + g θ * deriv (deriv g) θ = A θ + B θ := by
    intro θ hθ; rw [hg]; exact hSMC.2.2 θ hθ
  -- The closed interval differs from the open interval by a null set.
  have hsub : Set.Ioo (0:ℝ) (Real.pi/2) ⊆ Work.Spaces.Iθ := by
    intro θ hθ; rw [Work.Spaces.Iθ, Set.mem_Icc]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσnn : ∀ θ, θ ∈ Set.Ioo (0:ℝ) (Real.pi/2) → 0 ≤ σ θ :=
    fun θ hθ => Work.FTS.EllipticEst.thEta_nonneg (hsub hθ)
  have hμ : (volume : Measure ℝ).restrict Work.Spaces.Iθ
      = (volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2)) := by
    rw [Work.Spaces.Iθ]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := (0:ℝ)) (b := Real.pi/2))).symm
  have hmem : Set.Ioo (0:ℝ) (Real.pi/2)
      ∈ MeasureTheory.ae ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
    rw [hμ]; exact MeasureTheory.self_mem_ae_restrict measurableSet_Ioo
  -- Continuity of the weight and of the two profiles on the open interval.
  have hσcont : ContinuousOn σ (Set.Ioo (0:ℝ) (Real.pi/2)) := by
    unfold Work.FTS.EllipticEst.thEta
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      left
      exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])).ne'
  have hmcont : ContinuousOn m (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    fun θ hθ => (hm θ hθ).continuousAt.continuousWithinAt
  have hPcont : ContinuousOn P (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    fun θ hθ => (hP θ hθ).continuousAt.continuousWithinAt
  have hderivg : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2), deriv g θ = P θ / Real.sqrt (m θ) := by
    intro θ hθ
    have h := (hm θ hθ).sqrt (hmpos θ hθ).ne'
    rw [hg]
    rw [h.deriv]
    exact mul_div_mul_left (P θ) (Real.sqrt (m θ)) (by norm_num)
  -- Endpoint vanishing of `√m`, from `m → 0`.
  have hlim0 : Filter.Tendsto g (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    rw [hg]
    have h := (Real.continuous_sqrt.tendsto 0).comp htr0
    simpa [Function.comp_def, Real.sqrt_zero] using h
  have hlim1 : Filter.Tendsto g (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    rw [hg]
    have h := (Real.continuous_sqrt.tendsto 0).comp htr1
    simpa [Function.comp_def, Real.sqrt_zero] using h
  -- The a.e. identities of the three Agmon integrands.
  have haeI1 : (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ)
      ≤ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] (fun θ : ℝ => A θ * σ θ) := by
    filter_upwards [hmem] with θ hθ
    exact mul_le_mul_of_nonneg_right (hderivsq_le θ hθ) (hσnn θ hθ)
  have haeI2 : (fun θ : ℝ => g θ * deriv (deriv g) θ * σ θ)
      =ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (A θ + B θ - (deriv g θ) ^ 2) * σ θ) := by
    filter_upwards [hmem] with θ hθ
    have h1 := hident θ hθ
    have h2 : g θ * deriv (deriv g) θ = A θ + B θ - (deriv g θ) ^ 2 := by linarith
    rw [h2]
  have haeI3 : (fun θ : ℝ => (g θ) ^ 2 * σ θ)
      =ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ] (fun θ : ℝ => m θ * σ θ) := by
    filter_upwards [hmem] with θ hθ
    rw [hg]
    rw [Real.sq_sqrt (le_of_lt (hmpos θ hθ))]
  -- Integrability of the three Agmon integrands for `f = √m`.
  have hInt2 : MeasureTheory.IntegrableOn (fun θ : ℝ => (g θ) ^ 2 * σ θ) Work.Spaces.Iθ := by
    have hae : (fun θ : ℝ => m θ * σ θ) =ᵐ[(volume : Measure ℝ).restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (g θ) ^ 2 * σ θ) := by
      filter_upwards [hmem] with θ hθ
      rw [hg]
      rw [Real.sq_sqrt (le_of_lt (hmpos θ hθ))]
    exact hmI.congr hae
  have hABI : Integrable (fun θ : ℝ => (A θ + B θ) * σ θ)
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
    have h := hA.add hB
    refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [Pi.add_apply]
    ring
  have hInt1 : MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ) Work.Spaces.Iθ := by
    have hsqrtcont : ContinuousOn (fun θ : ℝ => Real.sqrt (m θ)) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      Real.continuous_sqrt.comp_continuousOn hmcont
    have hdivcont : ContinuousOn (fun θ : ℝ => P θ / Real.sqrt (m θ))
        (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      hPcont.div hsqrtcont (fun θ hθ => (Real.sqrt_pos.mpr (hmpos θ hθ)).ne')
    have hGcont : ContinuousOn (fun θ : ℝ => (P θ / Real.sqrt (m θ)) ^ 2 * σ θ)
        (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      (hdivcont.pow 2).mul hσcont
    have hGasm : AEStronglyMeasurable (fun θ : ℝ => (P θ / Real.sqrt (m θ)) ^ 2 * σ θ)
        ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      hGcont.aestronglyMeasurable measurableSet_Ioo
    have hAoo : Integrable (fun θ : ℝ => A θ * σ θ)
        ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      hA.mono_set hsub
    have hbound : ∀ᵐ θ ∂((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))),
        ‖(P θ / Real.sqrt (m θ)) ^ 2 * σ θ‖ ≤ A θ * σ θ := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      have hm0 : 0 < m θ := hmpos θ hθ
      have hs0 : 0 ≤ σ θ := hσnn θ hθ
      have hsq : (P θ / Real.sqrt (m θ)) ^ 2 = P θ ^ 2 / m θ := by
        rw [div_pow, Real.sq_sqrt (le_of_lt hm0)]
      have hle : (P θ / Real.sqrt (m θ)) ^ 2 ≤ A θ := by
        rw [hsq, div_le_iff₀ hm0]
        linarith [hCS θ hθ]
      have hnn : 0 ≤ (P θ / Real.sqrt (m θ)) ^ 2 * σ θ := mul_nonneg (sq_nonneg _) hs0
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_right hle hs0
    have hGint : Integrable (fun θ : ℝ => (P θ / Real.sqrt (m θ)) ^ 2 * σ θ)
        ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      hAoo.mono' hGasm hbound
    have hae : (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ)
        =ᵐ[(volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))]
        (fun θ : ℝ => (P θ / Real.sqrt (m θ)) ^ 2 * σ θ) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      rw [hderivg θ hθ]
    have hIoo : Integrable (fun θ : ℝ => (deriv g θ) ^ 2 * σ θ)
        ((volume : Measure ℝ).restrict (Set.Ioo (0:ℝ) (Real.pi/2))) :=
      hGint.congr hae.symm
    rw [MeasureTheory.IntegrableOn, hμ]
    exact hIoo
  have hInt3 : MeasureTheory.IntegrableOn (fun θ : ℝ => g θ * deriv (deriv g) θ * σ θ)
      Work.Spaces.Iθ := by
    have hbase : Integrable (fun θ : ℝ => (A θ + B θ - (deriv g θ) ^ 2) * σ θ)
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
      have h := hABI.sub hInt1
      refine h.congr (Filter.Eventually.of_forall (fun θ => ?_))
      simp only [Pi.sub_apply]
      ring
    refine hbase.congr ?_
    filter_upwards [hmem] with θ hθ
    have h1 := hident θ hθ
    have h2 : g θ * deriv (deriv g) θ = A θ + B θ - (deriv g θ) ^ 2 := by linarith
    rw [h2]
  -- The Agmon inequality for `f = √m`.
  have hAgm := hAgmon g hC2g hlim0 hlim1 hInt1 hInt2 hInt3
  have hsplit : (∫ θ in Work.Spaces.Iθ, (A θ + B θ) * σ θ)
      = (∫ θ in Work.Spaces.Iθ, A θ * σ θ) + (∫ θ in Work.Spaces.Iθ, B θ * σ θ) := by
    calc (∫ θ in Work.Spaces.Iθ, (A θ + B θ) * σ θ)
        = (∫ θ in Work.Spaces.Iθ, (A θ * σ θ + B θ * σ θ)) :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
      _ = (∫ θ in Work.Spaces.Iθ, A θ * σ θ) + (∫ θ in Work.Spaces.Iθ, B θ * σ θ) :=
            MeasureTheory.integral_add hA hB
  have hI1le : (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * σ θ)
      ≤ (∫ θ in Work.Spaces.Iθ, A θ * σ θ) := MeasureTheory.integral_mono_ae hInt1 hA haeI1
  have hI3eq : (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * σ θ)
      = (∫ θ in Work.Spaces.Iθ, m θ * σ θ) := MeasureTheory.integral_congr_ae haeI3
  have hI2eq : (∫ θ in Work.Spaces.Iθ, g θ * deriv (deriv g) θ * σ θ)
      = (∫ θ in Work.Spaces.Iθ, A θ * σ θ) + (∫ θ in Work.Spaces.Iθ, B θ * σ θ)
        - (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * σ θ) := by
    calc (∫ θ in Work.Spaces.Iθ, g θ * deriv (deriv g) θ * σ θ)
        = (∫ θ in Work.Spaces.Iθ, (A θ + B θ - (deriv g θ) ^ 2) * σ θ) :=
            MeasureTheory.integral_congr_ae haeI2
      _ = (∫ θ in Work.Spaces.Iθ, ((A θ + B θ) * σ θ - (deriv g θ) ^ 2 * σ θ)) :=
            MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
      _ = (∫ θ in Work.Spaces.Iθ, (A θ + B θ) * σ θ)
            - (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * σ θ) :=
            MeasureTheory.integral_sub hABI hInt1
      _ = ((∫ θ in Work.Spaces.Iθ, A θ * σ θ) + (∫ θ in Work.Spaces.Iθ, B θ * σ θ))
            - (∫ θ in Work.Spaces.Iθ, (deriv g θ) ^ 2 * σ θ) := by
            rw [hsplit]
  -- The final arithmetic.
  have hfin : (1 / 200) * (∫ θ in Work.Spaces.Iθ, A θ * σ θ)
      ≤ 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, m θ * σ θ)
        - (∫ θ in Work.Spaces.Iθ, B θ * σ θ) := by
    rw [hI2eq, hI3eq] at hAgm
    linarith
  exact hfin

end Work.FTS.EllSol.PkgK5.TraceEngine
