import Mathlib
import Submission.Work.KMTPlan.A6.HHCore
import Submission.Work.KMTPlan.A6.memLp_kmtProj
import Submission.Work.KMTPlan.A6.kmtProj_l2_bound_finset
import Submission.Work.KMTPlan.A6.tsum_mul_le_of_finset_sq_le
import Submission.Work.KMTPlan.A6.hhVanishingF
import Submission.Work.KMTAreas.A7.ProjBound

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems

theorem highHighCase (P : ℤ[X]) (hd : 2 ≤ P.natDegree) (r : ℝ≥0) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hvanF : Work.KMTPlan.Sub.VanishingF) (hvanG : Work.KMTPlan.Sub.VanishingG)
    (hbesF : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTPlan.Sub.BesselF ρ)
    (hbesG : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTPlan.Sub.BesselG ρ P)
    (hNA : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTPlan.Sub.NonAliasingSize ρ)
    (hlog : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (c : ℝ), 0 < c → ∀ R : ℝ, 1 ≤ R →
      Work.KMTPlan.Sub.LogGain ρ c R)
    (hgood : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / (4 * (C₀ : ℝ)) → ∀ R : ℝ, 1 ≤ R →
      Work.KMTPlan.Sub.GoodScaleArith C₀ ρ R) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      Work.KMTPlan.PieceBoundOn ρ P C₀ 2 2 1 r
        (fun l₁ l₂ k₁ k₂ =>
          (2 : ℝ) ^ (-(c * (Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ))))
        Work.KMTPlan.CaseHH := by
  obtain ⟨cI, hcI, hIρ⟩ := hI
  refine ⟨cI / 2, by linarith, ?_⟩
  refine ⟨min 1 (1 / (4 * (C₀ : ℝ))), ?_, ?_⟩
  · positivity
  · intro ρ hρ hρle
    have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_left _ _)
    have hρ4 : ρ ≤ 1 / (4 * (C₀ : ℝ)) := le_trans hρle (min_le_right _ _)
    obtain ⟨CI, hIbound⟩ := hIρ ρ hρ hρ1
    exact hh_main
      (fun ρ l k f hf => memLp_kmtProj ρ l k hf)
      (fun ρ S => kmtProj_l2_bound_finset ρ S)
      (fun φ ψ Pm (inst : DecidablePred Pm) Bφ Bψ u v h1 h2 =>
        @tsum_mul_le_of_finset_sq_le φ ψ Pm inst Bφ Bψ u v h1 h2)
      (fun ρ R C hρ' hρ1' hR1 hRC hNA' hvanF' => hhVanishingF ρ R C hρ' hρ1' hR1 hRC hNA' hvanF')
      (fun ρ R C hρ' hρ1' hR1 hRC hNA' hvanG' => hhVanishingG ρ R C hρ' hρ1' hR1 hRC hNA' hvanG')
      P hd r hr C₀ hC₀ ρ hρ hρ1 cI hcI CI hIbound hvanF hvanG
      (hbesF ρ hρ hρ1) (hbesG ρ hρ hρ1) (hNA ρ hρ hρ1)
      (fun c hc R hR => hlog ρ hρ hρ1 c hc R hR)
      (fun R hR => hgood ρ hρ hρ4 R hR)

end Work.KMTPlan.A6
