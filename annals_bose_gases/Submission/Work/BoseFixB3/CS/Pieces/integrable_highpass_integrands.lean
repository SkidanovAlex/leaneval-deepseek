import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseFixB3.HighMassAux.parseval_L1L2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

open MeasureTheory Filter Metric
open scoped Real Topology BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Integrability of the high-pass pairings

The integrand
`p ↦ (conj(kinFT 1_{Λ(ℓ)} p) * kinFT ψ p).re`
is a pointwise pairing of two Fourier transforms: `kinFT 1_{Λ(ℓ)}` and `kinFT ψ` are both `L²`
(Plancherel: the cube indicator is `L¹ ∩ L²`, and `ψ` is continuous with compact support), so
their pointwise product is `L¹` by Cauchy–Schwarz (`L2.integrable_inner`).  This is exactly the
content of `Work.BoseFixB3.HighMassAux.integrable_inner_kinFT`; the only extra work here is
(a) the `L¹ ∩ L²` membership of the cube indicator for *every* `ℓ : ℝ` and of `ψ`, and
(b) removing the multiplier `1 - f(‖p‖/κ)`, which is bounded by `1` because `0 ≤ f ≤ 1`. -/

/-- `acube ℓ` has finite volume for every real `ℓ`: for `ℓ ≤ 0` the cube is empty. -/
private lemma volume_acube_lt_top (ℓ : ℝ) :
    (volume : Measure E3) (Submission.BoseGases.acube ℓ) < ⊤ := by
  by_cases hℓ : 0 ≤ ℓ
  · exact Submission.BoseGases.acube_lt_top ℓ hℓ
  · have hempty : Submission.BoseGases.acube ℓ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have h0 : y 0 ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hy 0
      simp only [Set.mem_Icc] at h0
      exact absurd (by linarith [h0.1, h0.2]) (not_le.mpr (not_le.mp hℓ))
    rw [hempty, measure_empty]
    exact ENNReal.zero_lt_top

/-- The complexified indicator of the centred cube `Λ(ℓ)` lies in `L¹ ∩ L²` for every real `ℓ`. -/
private lemma cubInd_memLp (ℓ : ℝ) :
    MemLp (fun z : E3 =>
        (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ)) 1 volume
      ∧ MemLp (fun z : E3 =>
        (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ)) 2
        volume := by
  set u : E3 → ℂ := fun z =>
    (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ) with hu
  have hcube : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  have hueq : u = (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℂ)) := by
    funext z
    rw [hu]
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  have hIntOnC : IntegrableOn (fun _ : E3 => (1 : ℂ)) (Submission.BoseGases.acube ℓ) volume :=
    IntegrableOn.of_bound (volume_acube_lt_top ℓ) aestronglyMeasurable_const 1
      (by filter_upwards with z; simp)
  have hIntOnR : IntegrableOn (fun _ : E3 => (1 : ℝ)) (Submission.BoseGases.acube ℓ) volume :=
    IntegrableOn.of_bound (volume_acube_lt_top ℓ) aestronglyMeasurable_const 1
      (by filter_upwards with z; simp)
  have hint : Integrable u := by
    rw [hueq]
    exact (integrable_indicator_iff hcube).2 hIntOnC
  have hEqi : (fun x : E3 => ‖u x‖ ^ 2)
      = fun x : E3 => (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) x := by
    funext x
    rw [hu]
    by_cases hx : x ∈ Submission.BoseGases.acube ℓ
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hsqi : Integrable (fun x : E3 => ‖u x‖ ^ 2) := by
    rw [hEqi]
    exact (integrable_indicator_iff hcube).2 hIntOnR
  have hmem1 : MemLp u 1 volume := memLp_one_iff_integrable.mpr hint
  have hmem2 : MemLp u 2 volume :=
    (memLp_two_iff_integrable_sq_norm hint.aestronglyMeasurable).2 hsqi
  exact ⟨hu ▸ hmem1, hu ▸ hmem2⟩

/-- `0 ≤ f s` for FS's cut-off. -/
private lemma fc_nonneg (fc : Work.BoseBoxFix.LowCut) (s : ℝ) : 0 ≤ fc.f s := by
  rcases le_total s 2 with h | h
  · have := fc.anti h
    rw [fc.zero 2 le_rfl] at this
    exact this
  · rw [fc.zero s h]

/-- `f s ≤ 1` for FS's cut-off. -/
private lemma fc_le_one (fc : Work.BoseBoxFix.LowCut) (s : ℝ) : fc.f s ≤ 1 := by
  rcases le_total s 1 with h | h
  · rw [fc.one s h]
  · have := fc.anti h
    rw [fc.one 1 le_rfl] at this
    exact this

theorem integrable_highpass_integrands {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hcont : Continuous ψ) (hcs : HasCompactSupport ψ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (starRingEnd ℂ (Submission.BoseGases.kinFT
          (fun z : EuclideanSpace ℝ (Fin 3) =>
            (((Submission.BoseGases.acube ℓ).indicator (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) z : ℝ) : ℂ)) p)
          * Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p).re)
      ∧ Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (1 - fc.f (‖p‖ / κ)) * (starRingEnd ℂ (Submission.BoseGases.kinFT
          (fun z : EuclideanSpace ℝ (Fin 3) =>
            (((Submission.BoseGases.acube ℓ).indicator (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) z : ℝ) : ℂ)) p)
          * Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p).re) := by
  obtain ⟨hu1, hu2⟩ := cubInd_memLp ℓ
  have hψ1 : MemLp ψ 1 volume := hcont.memLp_of_hasCompactSupport hcs
  have hψ2 : MemLp ψ 2 volume := hcont.memLp_of_hasCompactSupport hcs
  have hv1 : MemLp (fun z : E3 => (ψ z : ℂ)) 1 volume := hψ1.ofReal
  have hv2 : MemLp (fun z : E3 => (ψ z : ℂ)) 2 volume := hψ2.ofReal
  -- the pairing `⟪kinFT 1_Λ, kinFT ψ⟫` is integrable (Cauchy–Schwarz on the two `L²` transforms)
  have hinner := Work.BoseFixB3.HighMassAux.integrable_inner_kinFT hu1 hu2 hv1 hv2
  have hreal : Integrable (fun p : E3 =>
      (starRingEnd ℂ (Submission.BoseGases.kinFT
        (fun z : E3 =>
          (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ)) p)
        * Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) p).re) := by
    have heq : (fun p : E3 => (inner ℂ (Submission.BoseGases.kinFT
        (fun z : E3 =>
          (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ)) p)
        (Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) p)).re)
        = fun p : E3 => (starRingEnd ℂ (Submission.BoseGases.kinFT
        (fun z : E3 =>
          (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ)) p)
        * Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) p).re := by
      funext p
      rw [RCLike.inner_apply, mul_comm]
    rw [← heq]
    exact hinner.re
  refine ⟨hreal, ?_⟩
  -- the high-pass multiplier is bounded, so it preserves integrability
  have hcontcut : Continuous (fun p : E3 => fc.f (‖p‖ / κ)) :=
    fc.smooth.continuous.comp (continuous_norm.div_const κ)
  have hasm : AEStronglyMeasurable (fun p : E3 => 1 - fc.f (‖p‖ / κ)) volume :=
    (continuous_const.sub hcontcut).aestronglyMeasurable
  have hbound : ∀ᵐ p : E3 ∂volume, ‖1 - fc.f (‖p‖ / κ)‖ ≤ 1 := by
    filter_upwards with p
    have h1 : fc.f (‖p‖ / κ) ≤ 1 := fc_le_one fc _
    have h0 : 0 ≤ fc.f (‖p‖ / κ) := fc_nonneg fc _
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  exact hreal.bdd_mul hasm hbound

end Work.BoseFixB3.CS.Pieces
