import Mathlib
import Submission.Work.TMComp.RealCartanDefs
import Submission.Work.TMComp.RealCartan.rcCircleAverage_normSq
import Submission.Work.TMComp.RealCartan.rcExistsMaxOnFrontier

/-!
# The maximum principle for functions satisfying the circle mean value inequality

Let `Ω ⊆ ℂ` be open and bounded, let `V : ℂ → ℝ` be continuous on `closure Ω` and satisfy the
sub-mean-value inequality on circles,
`V z ≤ circleAverage V z r` whenever `r > 0` and `closedBall z r ⊆ Ω`,
and let `V ≤ C` on the frontier of `Ω`.  Then `V ≤ C` on all of `Ω`.

The proof is the standard one.  For `ε > 0` the perturbation `W_ε = V + ε * ‖·‖²` satisfies the
*strict* mean value inequality: indeed `V z ≤ circleAverage V z r` and the average of `‖·‖²`
over the circle of radius `r` around `z` is `‖z‖² + r²`, so that

`W_ε z ≤ circleAverage V z r + ε * ‖z‖² < circleAverage V z r + ε * (‖z‖² + r²)
       = circleAverage W_ε z r`.

Hence (by `rcExistsMaxOnFrontier`) `W_ε` attains its maximum over the compact set `closure Ω` at a
point `z*` of the frontier.  Choosing `R` with `Ω ⊆ closedBall 0 R` and using `V ≤ C` on the
frontier gives `V z ≤ W_ε z ≤ W_ε z* = V z* + ε * ‖z*‖² ≤ C + ε * R²` for every `ε > 0`, and
letting `ε → 0` yields `V z ≤ C`.
-/

open Metric Set

namespace Work.TMComp.RealCartan

/-- A function satisfying the sub-mean-value inequality, perturbed by `ε * ‖·‖²`, satisfies the
strict mean value inequality. -/
theorem rcSubMVP_perturb {Ω : Set ℂ} (hΩ : IsOpen Ω) {V : ℂ → ℝ}
    (hVc : ContinuousOn V (closure Ω))
    (hVmean : ∀ z ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
      V z ≤ Real.circleAverage V z r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ z ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.closedBall z r ⊆ Ω ∧
      (fun w => V w + ε * ‖w‖ ^ 2) z < Real.circleAverage (fun w => V w + ε * ‖w‖ ^ 2) z r := by
  intro z hz
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.isOpen_iff.mp hΩ z hz
  have hr : 0 < ρ / 2 := by linarith
  have hball : Metric.closedBall z (ρ / 2) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hρ
  refine ⟨ρ / 2, hr, hball, ?_⟩
  -- `V` is continuous on the circle, hence circle integrable there.
  have hcontV : ContinuousOn V (Metric.sphere z |ρ / 2|) := by
    rw [abs_of_pos hr]
    exact hVc.mono (fun x hx => subset_closure (hball (Metric.sphere_subset_closedBall hx)))
  have hciV : CircleIntegrable V z (ρ / 2) := hcontV.circleIntegrable'
  have hci2 : CircleIntegrable (fun w : ℂ => ε * ‖w‖ ^ 2) z (ρ / 2) := by
    apply ContinuousOn.circleIntegrable'
    fun_prop
  -- The circle average of `W_ε` is the sum of the two circle averages.
  have hkey : Real.circleAverage (fun w : ℂ => V w + ε * ‖w‖ ^ 2) z (ρ / 2)
      = Real.circleAverage V z (ρ / 2) + ε * (‖z‖ ^ 2 + (ρ / 2) ^ 2) := by
    rw [Real.circleAverage_fun_add hciV hci2]
    rw [show (fun w : ℂ => ε * ‖w‖ ^ 2) = (fun w : ℂ => ε • ‖w‖ ^ 2) from by
          funext w; exact (smul_eq_mul ε (‖w‖ ^ 2)).symm]
    rw [Real.circleAverage_fun_smul, smul_eq_mul]
    rw [rcCircleAverage_normSq]
  rw [hkey]
  have hmi : V z ≤ Real.circleAverage V z (ρ / 2) := hVmean z hz (ρ / 2) hr hball
  have hpos : 0 < ε * (ρ / 2) ^ 2 := by positivity
  linarith

theorem rcMaxPrincipleOn {Ω : Set ℂ} (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω)
    {V : ℂ → ℝ} (hVc : ContinuousOn V (closure Ω)) {C : ℝ}
    (hVmean : ∀ z ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
      V z ≤ Real.circleAverage V z r)
    (hbd : ∀ ζ ∈ frontier Ω, V ζ ≤ C) :
    ∀ z ∈ Ω, V z ≤ C := by
  intro z hz
  -- A radius bounding `Ω`.
  obtain ⟨R₀, hR₀⟩ := hbdd.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hsub : Ω ⊆ Metric.closedBall (0 : ℂ) R := by
    intro w hw
    have h1 : dist w 0 ≤ R₀ := by
      have h := hR₀ hw
      rwa [Metric.mem_closedBall] at h
    rw [Metric.mem_closedBall]
    exact le_trans h1 (le_max_left _ _)
  have hclo : closure Ω ⊆ Metric.closedBall (0 : ℂ) R :=
    closure_minimal hsub Metric.isClosed_closedBall
  have hnorm : ∀ w ∈ closure Ω, ‖w‖ ≤ R := by
    intro w hw
    have h1 := hclo hw
    rwa [Metric.mem_closedBall, dist_zero_right] at h1
  -- It suffices to prove `V z ≤ C + δ` for every `δ > 0`.
  refine le_of_forall_pos_le_add (fun δ hδ => ?_)
  set ε : ℝ := δ / (R ^ 2 + 1) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hWc : ContinuousOn (fun w : ℂ => V w + ε * ‖w‖ ^ 2) (closure Ω) := by
    apply hVc.add
    exact (continuous_const.mul (continuous_norm.pow 2)).continuousOn
  obtain ⟨zstar, hzstar_front, hzstar_max⟩ :=
    rcExistsMaxOnFrontier hΩ hbdd ⟨z, hz⟩ hWc (rcSubMVP_perturb hΩ hVc hVmean hεpos)
  have h1a : V z + ε * ‖z‖ ^ 2 ≤ V zstar + ε * ‖zstar‖ ^ 2 := hzstar_max z (subset_closure hz)
  have h1b : 0 ≤ ε * ‖z‖ ^ 2 := by positivity
  have h2 : V zstar ≤ C := hbd zstar hzstar_front
  have h3 : ‖zstar‖ ≤ R := hnorm zstar (frontier_subset_closure hzstar_front)
  have h4 : ε * ‖zstar‖ ^ 2 ≤ ε * R ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h3 2) hεpos.le
  have h5 : ε * R ^ 2 ≤ δ := by
    rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < R ^ 2 + 1)]
    nlinarith [sq_nonneg R]
  linarith

end Work.TMComp.RealCartan
