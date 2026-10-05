import Mathlib
import Submission.Work.RPB.B5.RhoPerDefs

namespace Work.RPB.B5

theorem hasDerivAt_rhoe_comp_sig_kappa (ρe : ℝ → ℝ → ℝ → ℝ) (τ t κ : ℝ)
    (hdiff : ∀ σ : ℝ, |σ| ≤ κ / 4 → deriv (fun s : ℝ => ρe τ t s) σ < 0)
    {x : ℝ} (hx : |Work.RPB.B5.sig x| ≤ κ / 4) :
    HasDerivAt (fun y : ℝ => ρe τ t (Work.RPB.B5.sig y)) (deriv (fun s : ℝ => ρe τ t s) (Work.RPB.B5.sig x) * x) x := by
  have hneg : deriv (fun s : ℝ => ρe τ t s) (Work.RPB.B5.sig x) < 0 := hdiff _ hx
  have hd : DifferentiableAt ℝ (fun s : ℝ => ρe τ t s) (Work.RPB.B5.sig x) := by
    by_contra h
    rw [deriv_zero_of_not_differentiableAt h] at hneg
    exact lt_irrefl 0 hneg
  have hsig : HasDerivAt Work.RPB.B5.sig x x := by
    unfold Work.RPB.B5.sig
    simpa using ((hasDerivAt_pow 2 x).div_const 2).sub_const 1
  have hcomp := (hd.hasDerivAt).comp x hsig
  rw [show ((fun s : ℝ => ρe τ t s) ∘ Work.RPB.B5.sig) =
        (fun y : ℝ => ρe τ t (Work.RPB.B5.sig y)) from rfl] at hcomp
  exact hcomp

end Work.RPB.B5
