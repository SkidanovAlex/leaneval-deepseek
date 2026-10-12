import Mathlib.Analysis.Fourier.Notation
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Pieces.integrable_highpass_integrands
import Submission.Work.BoseFixB3.CS.Pieces.integrable_ind_mul_lowMult
import Submission.Work.BoseFixB3.HighMassAux.lowMult_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

noncomputable section
open MeasureTheory Filter Metric
open scoped Real Topology BigOperators FourierTransform

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- For `ψ` continuous with compact support, vanishing outside the ball of radius `ℓ/2` (so
that `1_{Λ(ℓ)}ψ = ψ`), the difference between `ψ` and its low-momentum part
`f_L(√−Δ)ψ = lowMult fc κ ℓ ψ` integrates on the box to a *boundary-layer pairing*: the
multiplier `f(‖p‖/κ)` cancels against the `1` of the identity, leaving the weight
`1 − f(‖p‖/κ)`, supported in `‖p‖ ≥ κ`.

Intended proof: `HighMassAux.lowMult_pairing` with `φ = 1_{Λ(ℓ)}` (so the first `kinFT` factor
is that of the box indicator, and `lowMult` is applied to `Ψ = ψ`) gives
`∫_Λ lowMult = (2π)⁻³∫_p (conj(kinFT 1_Λ p)·f(‖p‖/κ)·kinFT(1_Λψ) p).re`; the companion
`HighMassAux.parseval_L1L2` with `u = 1_Λ`, `v = ψ` gives
`∫_Λ ψ = (2π)⁻³∫_p (conj(kinFT 1_Λ p)·kinFT ψ p).re`.  Subtracting (both `p`-integrands are
integrable) and using `1_Λψ = ψ` (`Submission.BoseGases.mem_acube_of_norm_le`, from the support
hypothesis) together with `∫_x 1_Λ x · F x = ∫ x in Λ, F x` gives the claim. -/
theorem highpass_difference {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {ψ : E3 → ℝ} (hcont : Continuous ψ) (hcs : HasCompactSupport ψ)
    (hsupp : ∀ y : E3, ℓ / 2 ≤ ‖y‖ → ψ y = 0) :
    ∫ x in Submission.BoseGases.acube ℓ, (ψ x - Work.BoseBoxFix.lowMult fc κ ℓ ψ x)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          (1 - fc.f (‖p‖ / κ)) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT
              (fun z : E3 =>
                (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ)) p)
            * Submission.BoseGases.kinFT (fun z : E3 => (ψ z : ℂ)) p).re := by
  -- the two complex functions of the target and the real box indicator
  let U : E3 → ℂ := fun z : E3 =>
    (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ)
  let V : E3 → ℂ := fun z : E3 => (ψ z : ℂ)
  let ind0 : E3 → ℝ := (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ))
  have hind0eq : ind0 = (Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) := rfl
  have hUind : (fun z : E3 => (ind0 z : ℂ)) = U := rfl
  have hkind : (fun z : E3 => (ψ z : ℂ)) = V := rfl
  have hUid : U = (fun z : E3 =>
      (((Submission.BoseGases.acube ℓ).indicator (fun _ : E3 => (1 : ℝ)) z : ℝ) : ℂ)) := rfl
  have hVid : V = (fun z : E3 => (ψ z : ℂ)) := rfl
  -- integrability / Lᵖ facts
  have hac : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  have hvol : volume (Submission.BoseGases.acube ℓ) ≠ ⊤ :=
    (Submission.BoseGases.acube_lt_top ℓ hℓ.le).ne
  have hind0_1 : MemLp ind0 1 volume :=
    memLp_indicator_const 1 hac (1 : ℝ) (Or.inr hvol)
  have hind0_2 : MemLp ind0 2 volume :=
    memLp_indicator_const 2 hac (1 : ℝ) (Or.inr hvol)
  have hind0_int : Integrable ind0 := memLp_one_iff_integrable.mp hind0_1
  have hψ_int : Integrable ψ := hcont.integrable_of_hasCompactSupport hcs
  have hψ_intOn : IntegrableOn ψ (Submission.BoseGases.acube ℓ) := hψ_int.integrableOn
  have hψ1 : MemLp ψ 1 volume := hcont.memLp_of_hasCompactSupport hcs
  have hψ2 : MemLp ψ 2 volume := hcont.memLp_of_hasCompactSupport hcs
  have hψ_aesm : AEStronglyMeasurable ψ volume := hψ1.aestronglyMeasurable
  obtain ⟨Cψ, hCψ⟩ := hcs.exists_bound_of_continuous hcont
  -- the box indicator has compact support
  have hind0_cs : HasCompactSupport ind0 := by
    refine HasCompactSupport.of_support_subset_isCompact
      (Work.UBBInputs9.B.acube_isCompact ℓ) ?_
    intro x hx
    by_contra hxc
    refine hx ?_
    show Set.indicator (Submission.BoseGases.acube ℓ) (fun _ : E3 => (1 : ℝ)) x = 0
    exact Set.indicator_of_notMem hxc _
  -- the momentum cut-off has compact support (it vanishes for `‖p‖ ≥ 2κ`)
  have hcut_cs : HasCompactSupport (fun p : E3 => fc.f (‖p‖ / κ)) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E3) (2 * κ)) ?_
    intro p hp
    have hp' : 2 * κ < ‖p‖ := by
      have h1 : ¬ (p ∈ Metric.closedBall (0 : E3) (2 * κ)) := hp
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
      exact not_le.mp h1
    exact fc.zero _ ((le_div_iff₀ hκ).mpr hp'.le)
  -- `1_{Λ(ℓ)}ψ = ψ` : the support hypothesis
  have hkinψ : (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ)) = V := by
    show (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator ψ z : ℝ) : ℂ))
      = (fun z : E3 => (ψ z : ℂ))
    funext z
    by_cases hz : z ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      have hnorm : ℓ / 2 ≤ ‖z‖ := by
        by_contra hlt
        push_neg at hlt
        exact hz (Submission.BoseGases.mem_acube_of_norm_le hℓ.le hlt.le)
      rw [hsupp z hnorm]
  -- x-side integrability
  have hA2 : Integrable (fun x : E3 => ind0 x * ψ x) :=
    hind0_int.mul_bdd hψ_aesm (Eventually.of_forall hCψ)
  have hB2 : Integrable (fun x : E3 => ind0 x * Work.BoseBoxFix.lowMult fc κ ℓ ψ x) :=
    integrable_ind_mul_lowMult (fc := fc) (κ := κ) (ℓ := ℓ) hκ hℓ hcont
  -- p-side integrability
  have hInts := integrable_highpass_integrands (fc := fc) (κ := κ) (ℓ := ℓ) hcont hcs
  have hA_int : Integrable (fun p : E3 =>
      (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
        * Submission.BoseGases.kinFT V p).re) := by
    have h := hInts.1
    simpa only [← hUid, ← hVid] using h
  have hC_int : Integrable (fun p : E3 =>
      (1 - fc.f (‖p‖ / κ)) * (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
        * Submission.BoseGases.kinFT V p).re) := by
    have h := hInts.2
    simpa only [← hUid, ← hVid] using h
  have hB_int : Integrable (fun p : E3 =>
      (starRingEnd ℂ (Submission.BoseGases.kinFT U p) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
        * Submission.BoseGases.kinFT V p).re) := by
    refine (hA_int.sub hC_int).congr (Eventually.of_forall (fun p => ?_))
    simp only [Pi.sub_apply]
    have hfac : (starRingEnd ℂ (Submission.BoseGases.kinFT U p) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT V p).re
        = fc.f (‖p‖ / κ)
          * (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
              * Submission.BoseGases.kinFT V p).re := by
      rw [show starRingEnd ℂ (Submission.BoseGases.kinFT U p)
            * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) * Submission.BoseGases.kinFT V p
          = ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
            * (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
                * Submission.BoseGases.kinFT V p) from by ring,
        Complex.re_ofReal_mul]
    rw [hfac]
    ring
  -- the two pairing identities
  have hpar : (∫ x : E3, ind0 x * ψ x)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
            * Submission.BoseGases.kinFT V p).re := by
    have h := HighMassAux.parseval_L1L2 (u := ind0) (v := ψ) hind0_1 hind0_2 hψ1 hψ2
    simpa only [hUind, hkind] using h
  have hpair : (∫ x : E3, ind0 x * Work.BoseBoxFix.lowMult fc κ ℓ ψ x)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
            * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
            * Submission.BoseGases.kinFT V p).re := by
    have h := HighMassAux.lowMult_pairing (fc := fc) (κ := κ) (ℓ := ℓ) hℓ
      (φ := ind0) hind0_int hind0_cs hψ_intOn hcut_cs
    simpa only [hUind, hkinψ] using h
  -- the box integral is the whole-space pairing of the indicator
  have hLHS : (∫ x in Submission.BoseGases.acube ℓ,
        (ψ x - Work.BoseBoxFix.lowMult fc κ ℓ ψ x))
      = (∫ x : E3, ind0 x * ψ x)
        - ∫ x : E3, ind0 x * Work.BoseBoxFix.lowMult fc κ ℓ ψ x := by
    rw [← MeasureTheory.integral_indicator hac]
    rw [← MeasureTheory.integral_sub hA2 hB2]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Submission.BoseGases.acube ℓ
    · simp only [hind0eq, Set.indicator_of_mem hx, one_mul]
    · simp only [hind0eq, Set.indicator_of_notMem hx, zero_mul, sub_zero]
  -- the momentum-space difference is the high-pass pairing
  have hP : (∫ p : E3,
          (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
            * Submission.BoseGases.kinFT V p).re)
      - (∫ p : E3,
          (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
            * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
            * Submission.BoseGases.kinFT V p).re)
      = ∫ p : E3,
          (1 - fc.f (‖p‖ / κ)) * (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
            * Submission.BoseGases.kinFT V p).re := by
    rw [← MeasureTheory.integral_sub hA_int hB_int]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    have hfac : (starRingEnd ℂ (Submission.BoseGases.kinFT U p) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
          * Submission.BoseGases.kinFT V p).re
        = fc.f (‖p‖ / κ)
          * (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
              * Submission.BoseGases.kinFT V p).re := by
      rw [show starRingEnd ℂ (Submission.BoseGases.kinFT U p)
            * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) * Submission.BoseGases.kinFT V p
          = ((fc.f (‖p‖ / κ) : ℝ) : ℂ)
            * (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
                * Submission.BoseGases.kinFT V p) from by ring,
        Complex.re_ofReal_mul]
    rw [hfac]
    ring
  have hstep : (∫ x : E3, ind0 x * ψ x)
        - ∫ x : E3, ind0 x * Work.BoseBoxFix.lowMult fc κ ℓ ψ x
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          (1 - fc.f (‖p‖ / κ)) * (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
            * Submission.BoseGases.kinFT V p).re := by
    rw [hpar, hpair, ← mul_sub, hP]
  show (∫ x in Submission.BoseGases.acube ℓ,
        (ψ x - Work.BoseBoxFix.lowMult fc κ ℓ ψ x))
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          (1 - fc.f (‖p‖ / κ)) * (starRingEnd ℂ (Submission.BoseGases.kinFT U p)
            * Submission.BoseGases.kinFT V p).re
  rw [hLHS, hstep]

end Work.BoseFixB3.CS.Pieces

/-- The same statement under the caller's requested name `Work.BoseFixB3.CS.Pieces.highpass_difference`
(the declaration above carries the doubly-qualified name produced by the file's namespace header). -/
theorem highpass_difference {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hcont : Continuous ψ) (hcs : HasCompactSupport ψ)
    (hsupp : ∀ y : EuclideanSpace ℝ (Fin 3), ℓ / 2 ≤ ‖y‖ → ψ y = 0) :
    ∫ x in Submission.BoseGases.acube ℓ, (ψ x - Work.BoseBoxFix.lowMult fc κ ℓ ψ x)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          (1 - fc.f (‖p‖ / κ)) * ((starRingEnd ℂ) (Submission.BoseGases.kinFT
              (fun z : EuclideanSpace ℝ (Fin 3) =>
                (((Submission.BoseGases.acube ℓ).indicator
                  (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) z : ℝ) : ℂ)) p)
            * Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) p).re :=
  _root_.Work.BoseFixB3.CS.Pieces.Work.BoseFixB3.CS.Pieces.highpass_difference
    hκ hℓ hcont hcs hsupp
