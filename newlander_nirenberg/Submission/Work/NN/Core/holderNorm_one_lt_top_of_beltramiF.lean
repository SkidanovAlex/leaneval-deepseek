import Mathlib
import Submission.Work.NN.Core.beltrami_theta_fixedpoint
import Submission.Work.NN.Core.beltrami_theta_setup
import Submission.Work.NN.Core.beltrami_theta_est
import Submission.Work.NN.Core.beltrami_L2_identify_holder
import Submission.Work.NN.Core.contDiff_one_bmPotential_of_holder
import Submission.Work.NN.Core.bmPot_diff_continuous
import Submission.Work.NN.Core.czB_holderNorm_bound_holder
import Submission.Work.NN.Core.holderNorm_one_lt_top_of_wirtinger
import Submission.Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul
import Submission.Work.NN.Core.beltrami_theta_fixedpoint_holderF
import Submission.Work.NN.Core.beltrami_L2_identify_holder_cont

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

/-- The Beltrami equation `∂̄W = c ∂W + G` with `C^{0,α}`-coefficients that are small in `C^{0,α}`
and merely *continuous* data `G` (vanishing at infinity, with finite `C^{0,α}`-norm) has solutions
`W` whose `C^{1,α}`-norm is finite on `polydisc 0 ρ`.

The proof is the two-step scheme of `Work.NN.Core.holderNorm_one_of_beltrami_small`, with the
`C¹`-regularity hypothesis on `G` removed: `Work.NN.Core.beltrami_theta_fixedpoint_holder` provides
the `C^{0,α}` fixed point `F` of the potential equation, and
`Work.NN.Core.beltrami_L2_identify_holder_cont` identifies it with `∂̄W`. -/
theorem holderNorm_one_lt_top_of_beltramiF {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) : ∃ δ : ℝ, 0 < δ ∧ ∀ (c : Fin n → Fin n → (Fin n → ℂ) → ℂ) (G : Fin n → (Fin n → ℂ) → ℂ) (W : (Fin n → ℂ) → ℂ), (∀ k j, ContDiff ℝ ⊤ (c k j)) → (∀ k j, HasCompactSupport (c k j)) → (∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) → (∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal δ) → (∀ k, Continuous (G k)) → (∀ k, HasCompactSupport (G k)) → (∀ k, Work.CR.Flat.holderNorm 0 α (G k) Set.univ < ⊤) → ContDiff ℝ 1 W → HasCompactSupport W → (∀ k z, Work.CR.Flat.dbarCoord k W z = (∑ j, c k j z * Work.CR.Flat.dCoord j W z) + G k z) → Work.CR.Flat.holderNorm 1 α W (Work.CR.Flat.polydisc 0 ρ) < ⊤ := by
  -- the two smallness thresholds
  obtain ⟨δ₁, hδ₁pos, hfix⟩ := beltrami_theta_fixedpoint_holderF (n := n) hn hα0 hα1 hρ
  obtain ⟨δ₂, hδ₂pos, hident⟩ := beltrami_L2_identify_holder_cont (n := n) hn hα0 hα1 hρ
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro c G W hc_sm hc_cs hc_supp hc_small hG_c hG_cs hG_fin hW_sm hW_cs heq
  have hc₁ : ∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal δ₁ :=
    fun k j => (hc_small k j).trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hc₂ : ∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal δ₂ :=
    fun k j => (hc_small k j).trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
  -- the fixed point `F`
  obtain ⟨F, hF_cs, hF_fin, hF_eq⟩ := hfix c G hc_sm hc_cs hc_supp hc₁ hG_c hG_cs hG_fin
  -- identification: `∂̄W = F`
  have hWbar : ∀ j z, Work.CR.Flat.dbarCoord j W z = F j z :=
    hident c G W F hc_sm hc_cs hc_supp hc₂ hG_c hG_cs hG_fin hW_sm hW_cs heq hF_cs hF_fin hF_eq
  -- a support radius for `F`
  obtain ⟨R, hR0, hR⟩ := BTheta.exists_radius_all_of_hasCompactSupport (n := n) hF_cs
  -- the Calderón–Zygmund bound for `∂ (bmPotential F)`
  obtain ⟨C₃, hC₃, hbound₃⟩ := czB_holderNorm_bound_holder (n := n) hn hα0 hα1 R hR0
  have hBfin : ∀ i : Fin n, Work.CR.Flat.holderNorm 0 α (fun z =>
      Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z) Set.univ < ⊤ := by
    intro i
    refine lt_of_le_of_lt (hbound₃ F hF_fin hF_cs hR i) ?_
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    exact ENNReal.sum_lt_top.mpr (fun j _ => hF_fin j)
  -- `bmPotential F = bmGamma n * W`
  have hbm : Work.CR.Flat.Cauchy.bmPotential F
      = fun z => Work.CR.Flat.Cauchy.bmGamma n * W z := by
    have hFeq : (fun j z => Work.CR.Flat.dbarCoord j W z) = F :=
      funext (fun j => funext (fun z => hWbar j z))
    have h2 : Work.CR.Flat.Cauchy.bmPotential F
        = Work.CR.Flat.Cauchy.bmPotential (fun j z => Work.CR.Flat.dbarCoord j W z) := by
      rw [hFeq]
    rw [h2]
    funext z
    exact (bmPotential_dbarCoord_eq_bmGamma_mul (n := n) hn hW_sm hW_cs z).symm
  -- hence `∂ᵢW = γ⁻¹ ∂ᵢ (bmPotential F)`
  have hdW : ∀ i z, Work.CR.Flat.dCoord i W z = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹ *
      Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z := by
    intro i z
    have hderiv : fderiv ℝ (Work.CR.Flat.Cauchy.bmPotential F) z
        = (Work.CR.Flat.Cauchy.bmGamma n) • fderiv ℝ W z := by
      rw [hbm]
      exact fderiv_const_mul ((hW_sm.differentiable (by norm_num)).differentiableAt)
        (Work.CR.Flat.Cauchy.bmGamma n)
    have hγ : Work.CR.Flat.Cauchy.bmGamma n ≠ 0 :=
      Work.CR.Flat.Cauchy.bmGamma_ne_zero_of (Work.CR.Flat.Cauchy.integrable_bmWeight hn).2
    have hkey : Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential F) z
        = Work.CR.Flat.Cauchy.bmGamma n * Work.CR.Flat.dCoord i W z := by
      simp only [Work.CR.Flat.dCoord, hderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hkey, ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]
  exact holderNorm_one_lt_top_of_wirtinger hα0 hα1 hρ hW_sm hW_cs hBfin hdW hWbar hF_fin

end

end Work.NN.Core
