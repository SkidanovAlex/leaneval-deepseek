import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option maxHeartbeats 1600000

theorem HkIntegrand_zmul_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (φ : ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ b ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] φ z| ≤ K) →
      ContDiffOn ℝ Work.Stability.smoothOrder φ (Set.Ioi (-1)) →
      ∀ g : ℝ → ℝ → ℝ, Work.FTS.EllipticEst.SmoothOpen g →
        (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
            ≤ C * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α k g z θ) ∧
        (Work.Spaces.HkMem α k g →
          Work.Spaces.HkMem α k (fun z θ => φ z * g z θ) ∧
          Work.Spaces.HkSq α k (fun z θ => φ z * g z θ)
            ≤ C * (1 + K) ^ 2 * Work.Spaces.HkSq α k g) := by
  refine ⟨zmulConst k, zmulConst_pos k, ?_⟩
  intro α φ K hK hB hsm g hg
  constructor
  · exact zmul_quad α k φ g hK hB hsm hg
  · intro hm
    set c : ℝ := zmulConst k * (1 + K) ^ 2 with hcdef
    have hcnn : 0 ≤ c := by
      rw [hcdef]
      exact mul_nonneg (zmulConst_pos k).le (sq_nonneg _)
    have hF : Work.FTS.EllipticEst.SmoothOpen (fun z θ => φ z * g z θ) :=
      smoothOpen_zmul hsm hg
    have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
          ≤ c * Work.Spaces.HkIntegrand α k g z θ := by
      intro z hz θ hθ
      rw [hcdef]
      exact zmul_quad α k φ g hK hB hsm hg z hz θ hθ
    refine ⟨hkMem_of_open_dominated α k hcnn hF hm hpt, ?_⟩
    -- integrate the pointwise bound, angular variable first
    have hinner : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ)
          ≤ c * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
      intro z hz
      have hle : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
          Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ
            ≤ c * Work.Spaces.HkIntegrand α k g z θ := by
        rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
        exact Filter.Eventually.of_forall fun θ hθ => hpt z hz θ hθ
      have := MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α k (fun z θ => φ z * g z θ) z θ)
        ((hm.1 z hz).const_mul c) hle
      rwa [MeasureTheory.integral_const_mul] at this
    have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ)
        ≤ ∫ z in Work.Spaces.Iz,
            c * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ ((hm.2).const_mul c) ?_
      · exact Filter.Eventually.of_forall fun z =>
          MeasureTheory.integral_nonneg fun θ =>
            Work.Spaces.HkIntegrand_nonneg α k (fun z θ => φ z * g z θ) z θ
      · exact (MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici).mpr
          (Filter.Eventually.of_forall fun z hz => hinner z hz)
    calc Work.Spaces.HkSq α k (fun z θ => φ z * g z θ)
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (fun z θ => φ z * g z θ) z θ := rfl
      _ ≤ ∫ z in Work.Spaces.Iz,
            c * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ) := houter
      _ = c * ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k g z θ := MeasureTheory.integral_const_mul c _
      _ = zmulConst k * (1 + K) ^ 2 * Work.Spaces.HkSq α k g := by
          simp only [hcdef, Work.Spaces.HkSq]

end Work.FTS.StrongPersist.L3Aux
