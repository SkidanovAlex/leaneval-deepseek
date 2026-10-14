import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.CoercivityFix.Assembly.AnsatzDefs
import Submission.Work.FTS.CoercivityFix.Assembly.ProdDeriv
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

set_option autoImplicit false

/-! ## Smoothness of the bumps -/



theorem contDiff_hA (δ : ℝ) : ContDiff ℝ Work.Stability.smoothOrder (hA δ) := by
  have h : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => (θ - th0) / δ) :=
    (contDiff_id.sub contDiff_const).div_const δ
  have h2 : ContDiff ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => Work.Stability.chi ((θ - th0) / δ)) :=
    Work.Stability.chi_contDiff.comp h
  exact h2

theorem contDiff_vthIter_hA (δ : ℝ) (i : ℕ) :
    ContDiff ℝ Work.Stability.smoothOrder (vthIter i (hA δ)) :=
  contDiff_vthIter (hA δ) (contDiff_hA δ) i

/-! ## The supports -/




theorem support_hA {δ : ℝ} (hδ : 0 < δ) :
    Function.support (hA δ) ⊆ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ) := by
  intro θ hθ
  by_contra hcon
  rw [Set.mem_Icc, not_and_or] at hcon
  have hθ' : θ < th0 - 2 * δ ∨ th0 + 2 * δ < θ := hcon.imp not_le.mp not_le.mp
  have hlt : 2 ≤ |(θ - th0) / δ| := by
    rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ]
    rcases hθ' with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have h0 : hA δ θ = 0 := by rw [hA, Work.Stability.chi_eq_zero hlt]
  exact hθ h0

/-- The iterated `D_θ`-derivatives of `hA δ` are supported in `[θ₀ - 2δ, θ₀ + 2δ]`. -/
theorem support_vthIter_hA (δ : ℝ) (hδ : 0 < δ) (i : ℕ) :
    Function.support (vthIter i (hA δ)) ⊆ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ) := by
  induction i with
  | zero => simpa [vthIter_zero] using support_hA hδ
  | succ i ih =>
      intro θ hθ
      have hθ' : θ ∈ Function.support (vth (vthIter i (hA δ))) := by
        simpa [vthIter_succ] using hθ
      have hd : deriv (vthIter i (hA δ)) θ ≠ 0 := by
        intro h0
        exact hθ' (by simp [vth, h0])
      have h2 : θ ∈ tsupport (vthIter i (hA δ)) := support_deriv_subset hd
      have h4 : closure (Function.support (vthIter i (hA δ)))
          ⊆ closure (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) := closure_mono ih
      have h5 : θ ∈ closure (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) := h4 h2
      rwa [closure_Icc] at h5

theorem vthIter_hA_eq_zero {δ : ℝ} (hδ : 0 < δ) {i : ℕ} {θ : ℝ}
    (hθ : θ ∉ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) :
    vthIter i (hA δ) θ = 0 :=
  Function.notMem_support.mp fun h => hθ (support_vthIter_hA δ hδ i h)

/-! ## The two slot integrability facts -/


/-- `S^i_q = ∫_θ (D_θ^i h)² sin(2θ)^{-q}` is an honest integral for every real `q`: the
integrand is supported in `[θ₀ - 2δ, θ₀ + 2δ] ⊂ (0, π/2)` where `sin(2θ) > 0`. -/
theorem integrableOn_vthIter_sq (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (i : ℕ) (q : ℝ) :
    IntegrableOn (fun θ => (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      Work.Spaces.Iθ := by
  have hsin : ∀ θ ∈ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := hθ
    rw [th0] at h1 h2
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) (by
      have := Real.pi_gt_three
      linarith)
  have hcont : ContinuousOn (fun θ => (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) := by
    have h1 : ContinuousOn (fun θ : ℝ => (vthIter i (hA δ) θ) ^ 2)
        (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) :=
      (((contDiff_vthIter_hA δ i).continuous).continuousOn).pow 2
    have hsincont : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
      Real.continuous_sin.comp (continuous_const.mul continuous_id)
    have h2 : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-q))
        (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) :=
      (hsincont.continuousOn.rpow_const
        (fun θ hθ => Or.inl (ne_of_gt (hsin θ hθ))))
    exact h1.mul h2
  have hInt : IntegrableOn (fun θ => (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)) := hcont.integrableOn_compact isCompact_Icc
  have hzero : ∀ θ, θ ∉ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ) →
      (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q) = 0 := by
    intro θ hθ
    rw [vthIter_hA_eq_zero hδ0 hθ, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
  have hglob : Integrable
      (fun θ => (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      (volume : Measure ℝ) := by
    have h1 : Integrable ((Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)).indicator
        (fun θ => (vthIter i (hA δ) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-q)))
        (volume : Measure ℝ) :=
      (integrable_indicator_iff measurableSet_Icc).mpr hInt
    refine h1.congr ?_
    filter_upwards with θ
    by_cases hθ : θ ∈ Set.Icc (th0 - 2 * δ) (th0 + 2 * δ)
    · rw [Set.indicator_of_mem hθ]
    · rw [Set.indicator_of_notMem hθ, hzero θ hθ]
  exact hglob.integrableOn

end Work.FTS.CoercivityFix.Assembly
