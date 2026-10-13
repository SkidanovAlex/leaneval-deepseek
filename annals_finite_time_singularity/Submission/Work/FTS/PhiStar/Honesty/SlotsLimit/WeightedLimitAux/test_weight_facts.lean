import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux

open scoped MeasureTheory ENNReal Topology
open MeasureTheory Set Filter

/-- A function which is bounded on a compact set `K` and vanishes off `K` is globally
integrable. -/
private lemma integrable_of_isCompact_bdd {g : ℝ × ℝ → ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hcont : ContinuousOn g K) (C : ℝ) (hbdd : ∀ x ∈ K, ‖g x‖ ≤ C)
    (hext : ∀ x, x ∉ K → g x = 0) : Integrable g volume := by
  classical
  have hmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hsm : AEStronglyMeasurable g (volume.restrict K) :=
    hcont.aestronglyMeasurable_of_isCompact hK hmeas
  have hae : ∀ᵐ x ∂(volume.restrict K), ‖g x‖ ≤ C := by
    filter_upwards [self_mem_ae_restrict hmeas] with x hx using hbdd x hx
  exact (IntegrableOn.of_bound hK.measure_lt_top hsm C hae).integrable_of_forall_notMem_eq_zero
    hext

theorem test_weight_facts {ρ : ℝ → ℝ → ℝ}
    (hρpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < ρ p.1 p.2)
    (hρcont : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0)
    {φ : ℝ → ℝ → ℝ} (hφ : Work.FTS.PhiStar.Honesty.SlotsLimit.TestQ0 φ) :
    IntegrableOn (fun p : ℝ × ℝ => (φ p.1 p.2 / ρ p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 ∧
    AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1 p.2 / ρ p.1 p.2)
      (volume.restrict Work.FTS.EllipticEst.Q0) ∧
    IntegrableOn (fun p : ℝ × ℝ => (φ p.1 p.2) ^ 2) Work.FTS.EllipticEst.Q0 ∧
    AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1 p.2)
      (volume.restrict Work.FTS.EllipticEst.Q0) ∧
    (∃ M : ℝ, ∀ p : ℝ × ℝ, |φ p.1 p.2| ≤ M) ∧
    MeasureTheory.Measure.restrict volume Work.FTS.EllipticEst.Q0
        (tsupport (fun p : ℝ × ℝ => φ p.1 p.2)) < ∞ := by
  classical
  -- `K` is the (compact) support of the test function, strictly inside the quadrant.
  set K : Set (ℝ × ℝ) := tsupport (Function.uncurry φ) with hKdef
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := hφ.tsupp
  have hKcpt : IsCompact K := hφ.cpt
  have hφcont : ContinuousOn (Function.uncurry φ) Work.FTS.EllipticEst.Q0 :=
    hφ.continuous.continuousOn
  have hcontK : ContinuousOn (Function.uncurry φ) K := hφcont.mono hKsub
  -- `φ` and `1/ρ` are bounded on `K`.
  obtain ⟨Mφ, hMφ⟩ := hKcpt.exists_bound_of_continuousOn hcontK
  have hρne : ∀ p ∈ K, Function.uncurry ρ p ≠ 0 :=
    fun p hp => ne_of_gt (hρpos p (hKsub hp))
  obtain ⟨Mρ, hMρ⟩ := hKcpt.exists_bound_of_continuousOn ((hρcont.mono hKsub).inv₀ hρne)
  set A : ℝ := max Mφ 0 with hAdef
  set B : ℝ := max Mρ 0 with hBdef
  have hA0 : 0 ≤ A := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  -- Pointwise bounds on `K`.
  have hbd : ∀ p ∈ K, ‖φ p.1 p.2 / ρ p.1 p.2‖ ≤ A * B := by
    intro p hp
    have h1' : ‖φ p.1 p.2‖ ≤ A := le_trans (hMφ p hp) (le_max_left _ _)
    have h2' : ‖(ρ p.1 p.2)⁻¹‖ ≤ B := le_trans (hMρ p hp) (le_max_left _ _)
    rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul h1' h2' (norm_nonneg _) hA0
  have hbd_div : ∀ p ∈ K, ‖(φ p.1 p.2 / ρ p.1 p.2) ^ 2‖ ≤ (A * B) ^ 2 := by
    intro p hp
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd p hp) 2
  have hbd_phi : ∀ p ∈ K, ‖(φ p.1 p.2) ^ 2‖ ≤ A ^ 2 := by
    intro p hp
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (le_trans (hMφ p hp) (le_max_left _ _)) 2
  -- Vanishing off `K`.
  have hzero : ∀ p ∉ K, φ p.1 p.2 = 0 := by
    intro p hp
    by_contra h
    exact hp (subset_tsupport (Function.uncurry φ) (Function.mem_support.2 h))
  -- Continuity on `K`.
  have hcont_div : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2 / ρ p.1 p.2) K :=
    hcontK.div (hρcont.mono hKsub) hρne
  -- Integrability on `K` and hence globally.
  have hInt1 : Integrable (fun p : ℝ × ℝ => (φ p.1 p.2 / ρ p.1 p.2) ^ 2) volume :=
    integrable_of_isCompact_bdd hKcpt (hcont_div.pow 2) _ hbd_div
      (fun p hp => by simp [hzero p hp])
  have hInt3 : Integrable (fun p : ℝ × ℝ => (φ p.1 p.2) ^ 2) volume :=
    integrable_of_isCompact_bdd hKcpt (hcontK.pow 2) _ hbd_phi
      (fun p hp => by simp [hzero p hp])
  -- Measurability on the quadrant.
  have hdivQ : ContinuousOn (fun p : ℝ × ℝ => φ p.1 p.2 / ρ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ContinuousOn.div hφcont hρcont (fun p hp => ne_of_gt (hρpos p hp))
  refine ⟨hInt1.integrableOn, ?_, hInt3.integrableOn, ?_, ?_, ?_⟩
  · exact hdivQ.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  · exact hφcont.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  · obtain ⟨Cφ, hCφ⟩ := hφ.cpt.exists_bound_of_continuous hφ.continuous
    exact ⟨max Cφ 0, fun p => by
      have h := hCφ p
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)⟩
  · refine lt_of_le_of_lt (Measure.restrict_apply_le (μ := volume) Work.FTS.EllipticEst.Q0
      (tsupport (fun p : ℝ × ℝ => φ p.1 p.2))) ?_
    exact hKcpt.measure_lt_top

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
