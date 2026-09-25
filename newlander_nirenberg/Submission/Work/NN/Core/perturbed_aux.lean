import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.bmPotential_gain
import Submission.Work.NN.Core.bmPotential_dbarDefect_eq
import Submission.Work.NN.Core.bmPotential_dbarCoord_eq_bmGamma_mul
import Submission.Work.NN.Core.Lcoef_uniform_estimate_on
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_univ_ne_top_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.NN.Core.holderNorm_const_mul_le
import Submission.Work.NN.Core.flatMulNorm
import Submission.Work.NN.Core.holderNorm_one_lt_top_of_wirtinger
import Submission.Work.NN.Core.czB_holderNorm_bound_holder
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.NN.Core.dbarCn_dirDeriv_comm
import Submission.Work.NN.Core.isInvertible_one_add_and_inverse_norm_le

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter

noncomputable section

variable {n : ℕ}

/-! ## §A.  Basic regularity and support facts for the compactly supported function -/

/-- A function which is `C^m` on the (open) polydisc `polydisc 0 ρ` and vanishes off the smaller
closed polydisc `polydisc 0 ρ'` (with `ρ' < ρ` coordinatewise) is globally `C^m`. -/
lemma contDiff_of_contDiffOn_of_vanishing {m : ℕ} {ρ ρ' : Fin n → ℝ} (hρ' : ∀ j, ρ' j < ρ j)
    {v : Cn n → ℂ} (hv : ContDiffOn ℝ ((m : ℕ) : WithTop ENat) v (Work.CR.Flat.polydisc 0 ρ))
    (hvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → v z = 0) :
    ContDiff ℝ ((m : ℕ) : WithTop ENat) v := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ Work.CR.Flat.polydisc 0 ρ
  · exact (hv.contDiffWithinAt hz).contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hz)
  · rw [Work.CR.Flat.mem_polydisc] at hz
    push Not at hz
    obtain ⟨i, hi⟩ := hz
    have hiρ : ρ i ≤ ‖z i‖ := by simpa using hi
    have hopen : IsOpen {w : Cn n | ρ' i < ‖w i‖} :=
      isOpen_lt continuous_const ((continuous_apply i).norm)
    have hev : v =ᶠ[𝓝 z] (fun _ => (0 : ℂ)) := by
      filter_upwards [hopen.mem_nhds (lt_of_lt_of_le (hρ' i) hiρ)] with w hw
      exact hvan w ⟨i, le_of_lt hw⟩
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev

/-- The support of such a `v` is compact. -/
lemma hasCompactSupport_of_vanishing {ρ' : Fin n → ℝ} {v : Cn n → ℂ}
    (hvan : ∀ z, (∃ i, ρ' i ≤ ‖z i‖) → v z = 0) : HasCompactSupport v := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact
    (K := Metric.closedBall 0 (∑ i : Fin n, ρ' i)) (isCompact_closedBall _ _) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hcon
  rw [not_le] at hcon
  refine hz (hvan z ?_)
  by_contra hc
  push Not at hc
  have h1 : ‖z‖ ≤ ∑ i : Fin n, ‖z i‖ := by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    exact fun i => Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  have h2 : ∑ i : Fin n, ‖z i‖ ≤ ∑ i : Fin n, ρ' i :=
    Finset.sum_le_sum fun i _ => le_of_lt (hc i)
  linarith

/-- The closed condition `{z | ∃ i, ρ i ≤ ‖z i‖}` lies in the closure of the open condition
`{z | ∃ i, ρ i < ‖z i‖}` (scale the `i`-th coordinate by `1 + δ`, or if it vanishes displace it). -/
lemma subset_closure_of_exists_lt_norm {ρ : Fin n → ℝ} :
    {z : Cn n | ∃ i, ρ i ≤ ‖z i‖} ⊆ closure {z : Cn n | ∃ i, ρ i < ‖z i‖} := by
  intro z hz
  by_cases hlt : ∃ i, ρ i < ‖z i‖
  · exact subset_closure hlt
  · push Not at hlt
    obtain ⟨i, hi⟩ := hz
    have heq : ‖z i‖ = ρ i := le_antisymm (hlt i) hi
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := ε / (‖z i‖ + 1) with hδ
    have hδpos : 0 < δ := by rw [hδ]; positivity
    have hδlt : δ * ‖z i‖ < ε := by
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < ‖z i‖ + 1)]
      nlinarith [norm_nonneg (z i), hε]
    by_cases hzi : z i = 0
    · have hρ0 : ρ i = 0 := by rw [← heq, hzi, norm_zero]
      refine ⟨Function.update z i ((δ / 2) • (1 : ℂ)), ⟨i, ?_⟩, ?_⟩
      · rw [Function.update_apply]
        simp only [if_true]
        rw [norm_smul, Real.norm_eq_abs, norm_one, mul_one,
          abs_of_pos (by linarith : (0 : ℝ) < δ / 2), hρ0]
        linarith
      · rw [dist_eq_norm, norm_sub_rev]
        have hsub : Function.update z i ((δ / 2) • (1 : ℂ)) - z
            = Pi.single i ((δ / 2) • (1 : ℂ)) := by
          ext k
          rw [Pi.sub_apply, Pi.single_apply, Function.update_apply]
          by_cases hk : k = i
          · subst hk; simp [hzi]
          · simp [hk]
        rw [hsub, Pi.norm_single, norm_smul, Real.norm_eq_abs, norm_one, mul_one,
          abs_of_pos (by linarith : (0 : ℝ) < δ / 2)]
        have hz0 : ‖z i‖ = 0 := by rw [hzi, norm_zero]
        have hδeq : δ = ε := by rw [hδ, hz0]; norm_num
        have : δ / 2 < ε := by rw [hδeq]; linarith
        linarith
    · have hzn : 0 < ‖z i‖ := norm_pos_iff.mpr hzi
      refine ⟨Function.update z i ((1 + δ) • z i), ⟨i, ?_⟩, ?_⟩
      · rw [Function.update_apply]
        simp only [if_true]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 1 + δ)]
        nlinarith
      · rw [dist_eq_norm, norm_sub_rev]
        have hsub : Function.update z i ((1 + δ) • z i) - z = Pi.single i (δ • z i) := by
          ext k
          rw [Pi.sub_apply, Pi.single_apply, Function.update_apply]
          by_cases hk : k = i
          · subst hk; simp [add_smul, one_smul]
          · simp [hk]
        rw [hsub, Pi.norm_single, norm_smul, Real.norm_eq_abs, abs_of_pos hδpos]
        exact hδlt

/-- If a continuous function vanishes on the open set `{z | ∃ i, ρ i < ‖z i‖}`, it also vanishes
on its closure `{z | ∃ i, ρ i ≤ ‖z i‖}`. -/
lemma eq_zero_of_cont_of_vanishing {ρ : Fin n → ℝ} {g : Cn n → ℂ} (hg : Continuous g)
    (h : ∀ z, (∃ i, ρ i < ‖z i‖) → g z = 0) :
    ∀ z, (∃ i, ρ i ≤ ‖z i‖) → g z = 0 := by
  have hcl : IsClosed {z : Cn n | g z = 0} := isClosed_eq hg continuous_const
  have hsub : {z : Cn n | ∃ i, ρ i < ‖z i‖} ⊆ {z : Cn n | g z = 0} := fun z hz => h z hz
  intro z hz
  exact closure_minimal hsub hcl (subset_closure_of_exists_lt_norm hz)


end

end Work.NN.Core
