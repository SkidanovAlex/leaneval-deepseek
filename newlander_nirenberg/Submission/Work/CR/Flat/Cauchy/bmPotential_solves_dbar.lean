import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmKerEps_dbarCoord_integral
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_of_eps
import Submission.Work.CR.Flat.Cauchy.integrable_bmWeight
import Submission.Work.CR.Flat.Cauchy.bmPot_dbarCoord

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- `∂̄` of a translate of a function: differentiating `y ↦ f (z + y)` at `x` is the same as
differentiating `f` at `z + x`. -/
lemma dbarCoord_comp_add {n : ℕ} (k : Fin n) {f : (Fin n → ℂ) → ℂ} {z x : Fin n → ℂ}
    (hf : DifferentiableAt ℝ f (z + x)) :
    dbarCoord k (fun y => f (z + y)) x = dbarCoord k f (z + x) := by
  have hshift : HasFDerivAt (fun y : Fin n → ℂ => z + y)
      (ContinuousLinearMap.id ℝ (Fin n → ℂ)) x :=
    (hasFDerivAt_id x).const_add z
  have h := (hf.hasFDerivAt).comp x hshift
  simp only [Function.comp_def, ContinuousLinearMap.id_comp] at h
  rw [dbarCoord, dbarCoord, h.fderiv, ContinuousLinearMap.comp_id]

/-- **Bochner–Martinelli formula for the flat `∂̄`-equation on a polydisc.**  With
`bmKernel j x = \bar x_j / ‖x‖^{2n}` (Euclidean norm on `ℂⁿ = Fin n → ℂ`, see
`Submission/Work/CR/Flat/Cauchy/bmDefs.lean`) and `bmPotential f z = Σ_j ∫ bmKernel j (ζ-z) f_j ζ dζ`,
there is a normalising constant `γ ≠ 0` such that for every closed `(0,1)`-form `f`
(`IsClosedForm f`, components `C¹`, supported in the closed half-size polydisc) one has
`∂̄_j (bmPotential f) = γ · f_j` on the open half-size polydisc `polydisc c (r/2)`. -/
theorem bmPotential_solves_dbar {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j) :
    ∃ γ : ℂ, γ ≠ 0 ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (f j)) →
      (∀ j z, (∃ k, r k / 2 ≤ ‖z k - c k‖) → f j z = 0) → IsClosedForm f →
      ∀ j, ∀ z : Fin n → ℂ, (∀ k, ‖z k - c k‖ < r k / 2) →
        dbarCoord j (bmPotential f) z = γ * f j z := by
  have hgamma : bmGamma n ≠ 0 := bmGamma_ne_zero_of (integrable_bmWeight hn).2
  refine ⟨bmGamma n, hgamma, ?_⟩
  intro f hf hsupp hclosed j z hz
  -- the radius of a ball containing the support of the data
  set ρ : ℝ := ∑ k, r k / 2 with hρdef
  set R : ℝ := ρ + ‖c‖ + 1 with hRdef
  have hρnn : 0 ≤ ρ := by
    rw [hρdef]
    exact Finset.sum_nonneg fun k _ => by have := hr k; linarith
  have hRpos : 0 < R := by
    have : 0 ≤ ‖c‖ := norm_nonneg c
    rw [hRdef]; linarith
  -- the components vanish outside the closed ball of radius `R`
  have hsuppR : ∀ k : Fin n, ∀ y : Fin n → ℂ, R ≤ ‖y‖ → f k y = 0 := by
    intro k y hy
    refine hsupp k y ?_
    by_contra hcon
    push_neg at hcon
    have h1 : ‖y - c‖ ≤ ∑ m, ‖y m - c m‖ := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun m _ => norm_nonneg _)]
      exact fun m => Finset.single_le_sum (fun m _ => norm_nonneg _) (Finset.mem_univ m)
    have h2 : ∑ m, ‖y m - c m‖ < ρ := by
      rw [hρdef]
      exact Finset.sum_lt_sum (fun m _ => le_of_lt (hcon m))
        ⟨⟨0, hn⟩, Finset.mem_univ _, hcon ⟨0, hn⟩⟩
    have h3 : ‖y‖ ≤ ‖y - c‖ + ‖c‖ := by
      calc ‖y‖ = ‖(y - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - c‖ + ‖c‖ := norm_add_le _ _
    rw [hRdef] at hy
    linarith
  -- `z` lies in the ball of radius `R`
  have hzR : ‖z‖ < R := by
    have h1 : ‖z - c‖ ≤ ∑ m, ‖z m - c m‖ := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun m _ => norm_nonneg _)]
      exact fun m => Finset.single_le_sum (fun m _ => norm_nonneg _) (Finset.mem_univ m)
    have h2 : ∑ m, ‖z m - c m‖ < ρ := by
      rw [hρdef]
      exact Finset.sum_lt_sum (fun m _ => le_of_lt (hz m))
        ⟨⟨0, hn⟩, Finset.mem_univ _, hz ⟨0, hn⟩⟩
    have h3 : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
      calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
    rw [hRdef]
    linarith
  -- the Bochner–Martinelli formula for a compactly supported test function
  have hkey : ∀ g : (Fin n → ℂ) → ℂ, ContDiff ℝ 1 g → (∀ x : Fin n → ℂ, 2 * R ≤ ‖x‖ → g x = 0) →
      ∑ k, ∫ x, bmKernel k x * dbarCoord k g x = bmGamma n * g 0 := by
    intro g hg hgs
    exact bmKernel_divergence_of_eps hn (by linarith) hg hgs (integrable_bmWeight hn).1
      (fun ε hε => bmKerEps_dbarCoord_integral hn (by linarith) hg hgs hε)
  -- rewrite the potential as `bmPot` and differentiate under the integral
  have hpot : dbarCoord j (bmPotential f) z = dbarCoord j (bmPot f) z := by
    have hfun : bmPotential f = bmPot f := funext fun w => bmPotential_eq_bmPot f w
    rw [hfun]
  rw [hpot, bmPot_dbarCoord hn hf hRpos hsuppR j z]
  -- use closedness of the form and the compact support of the `j`-th slice
  have hstep : (∑ k, ∫ x, bmKernel k x * dbarCoord j (f k) (z + x))
      = ∑ k, ∫ x, bmKernel k x * dbarCoord k (fun y => f j (z + y)) x := by
    refine Finset.sum_congr rfl fun k _ => ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show bmKernel k x * dbarCoord j (f k) (z + x)
      = bmKernel k x * dbarCoord k (fun y => f j (z + y)) x
    have hdj : DifferentiableAt ℝ (f j) (z + x) :=
      ((hf j).differentiable one_ne_zero).differentiableAt
    rw [dbarCoord_comp_add k hdj, hclosed k j (z + x)]
  rw [hstep]
  -- apply the Bochner–Martinelli formula to the slice
  have hslice_cd : ContDiff ℝ 1 (fun y : Fin n → ℂ => f j (z + y)) :=
    (hf j).comp (contDiff_const.add contDiff_id)
  have hslice_supp : ∀ x : Fin n → ℂ, 2 * R ≤ ‖x‖ → f j (z + x) = 0 := by
    intro x hx
    refine hsuppR j (z + x) ?_
    have h1 : ‖x‖ ≤ ‖z + x‖ + ‖z‖ := by
      calc ‖x‖ = ‖(z + x) - z‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖z + x‖ + ‖z‖ := norm_sub_le _ _
    linarith
  rw [hkey (fun y => f j (z + y)) hslice_cd hslice_supp]
  simp

end Work.CR.Flat.Cauchy
