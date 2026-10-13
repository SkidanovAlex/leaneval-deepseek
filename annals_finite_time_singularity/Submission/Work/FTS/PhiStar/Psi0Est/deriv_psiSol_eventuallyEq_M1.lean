import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Psi0Est.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Psi0Est

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The first derivative of the model `ψ = psiSol α` is the explicit function `M1 α` in a
neighbourhood of each endpoint.

`psiSol α θ = sin(2θ)·(Kc α + wZer α θ)` and `wZer' = qfun α` (by the FTC,
`intervalIntegral.integral_hasDerivAt_right`, at every point where `qfun α` is continuous,
in particular at every `θ ∈ (-1/2,0)` and `θ ∈ (π/2, π/2+1/2)`), so the product rule gives
`deriv (psiSol α) θ = 2cos(2θ)(Kc α + wZer α θ) + sin(2θ)·qfun α θ = M1 α θ` for
`θ ≠ 0, π/2` in that interval (this is `dthU_psiSol` divided by `sin 2θ`).  At the endpoints
the same product rule applies since the coefficient of `qfun α θ` is `sin(2θ₀) = 0`, so the
junk value of `qfun` at `0` and at `π/2` is irrelevant.  Hence `deriv (psiSol α)` agrees with
`M1 α` in a full neighbourhood of each endpoint. -/
theorem deriv_psiSol_eventuallyEq_M1 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hq0 : Filter.Tendsto (Work.FTS.PhiStar.Psi0Est.qfun α) (nhds 0) (nhds 0))
    (hqπ : Filter.Tendsto (Work.FTS.PhiStar.Psi0Est.qfun α) (nhds (Real.pi / 2)) (nhds 0)) :
    Filter.EventuallyEq (nhds 0) (deriv (Work.FTS.PhiStar.psiSol α))
      (Work.FTS.PhiStar.Psi0Est.M1 α) ∧
    Filter.EventuallyEq (nhds (Real.pi / 2)) (deriv (Work.FTS.PhiStar.psiSol α))
      (Work.FTS.PhiStar.Psi0Est.M1 α) := by
  -- `qfun` is continuous at the two endpoints, with the values `0` and `0` (which are also
  -- its junk values at `0` and `π/2`), so it is continuous wherever it is defined there.
  have hq0v : qfun α 0 = 0 := by simp [qfun]
  have hqπv : qfun α (Real.pi / 2) = 0 := by simp [qfun, Pfun, Gzero]
  have hc0 : ContinuousAt (qfun α) 0 := by rw [ContinuousAt, hq0v]; exact hq0
  have hcπ : ContinuousAt (qfun α) (Real.pi / 2) := by rw [ContinuousAt, hqπv]; exact hqπ
  -- continuity at any point where `sin` and `cos` do not vanish
  have hfun_cont : ∀ x : ℝ, Real.cos x ≠ 0 → Real.sin x ≠ 0 → ContinuousAt (qfun α) x := by
    intro x hcos hsin
    have hG : ContinuousAt (Gzero α) x := (continuous_Gzero α (le_of_lt hα)).continuousAt
    have hP : ContinuousAt (Pfun α) x := by
      have h : ContinuousAt (fun t : ℝ => Gzero α t / (2 * Real.cos t ^ 3)) x :=
        hG.div (by fun_prop) (by
          have h3 : Real.cos x ^ 3 ≠ 0 := pow_ne_zero 3 hcos
          simpa using mul_ne_zero two_ne_zero h3)
      exact h
    have hq : ContinuousAt (fun t : ℝ => Pfun α t / (Real.sin t) ^ 2) x :=
      hP.div (by fun_prop) (pow_ne_zero 2 hsin)
    exact hq
  -- continuity of `qfun` on `[-1/2, π/2+1/2]` (where `sin`, `cos` vanish only at `0`, `π/2`)
  have hcont_off : ∀ x : ℝ, -(1 / 2) ≤ x → x ≤ Real.pi / 2 + 1 / 2 → x ≠ 0 → x ≠ Real.pi / 2 →
      ContinuousAt (qfun α) x := by
    intro x h1 h2 hx0 hxπ
    have hsin : Real.sin x ≠ 0 := by
      rcases lt_or_gt_of_ne hx0 with hx | hx
      · exact ne_of_lt (Real.sin_neg_of_neg_of_neg_pi_lt hx (by linarith [h1, Real.pi_gt_three]))
      · exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx (by linarith [h2, Real.pi_gt_three]))
    have hcos : Real.cos x ≠ 0 := by
      rcases lt_or_gt_of_ne hxπ with hx | hx
      · exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [h1, Real.pi_gt_three], hx⟩)
      · exact ne_of_lt (Real.cos_neg_of_pi_div_two_lt_of_lt hx (by linarith [h2, Real.pi_gt_three]))
    exact hfun_cont x hcos hsin
  have hcontOn_closed : ContinuousOn (qfun α) (Set.Icc (-(1 / 2)) (Real.pi / 2 + 1 / 2)) := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact hc0.continuousWithinAt
    by_cases hxπ : x = Real.pi / 2
    · rw [hxπ]; exact hcπ.continuousWithinAt
    · exact (hcont_off x hx.1 hx.2 hx0 hxπ).continuousWithinAt
  have hcontOn_open : ContinuousOn (qfun α) (Set.Ioo (-(1 / 2)) (Real.pi / 2 + 1 / 2)) := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact hc0.continuousWithinAt
    by_cases hxπ : x = Real.pi / 2
    · rw [hxπ]; exact hcπ.continuousWithinAt
    · exact (hcont_off x (le_of_lt hx.1) (le_of_lt hx.2) hx0 hxπ).continuousWithinAt
  -- `wZer' = qfun` on the whole neighbourhood `(-1/2, π/2+1/2)`, endpoints included
  have hkey : ∀ θ : ℝ, -(1 / 2) < θ → θ < Real.pi / 2 + 1 / 2 →
      HasDerivAt (wZer α) (qfun α θ) θ := by
    intro θ h1 h2
    have hsub : Set.uIcc (0:ℝ) θ ⊆ Set.Icc (-(1 / 2)) (Real.pi / 2 + 1 / 2) := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · exact ⟨by linarith, by linarith⟩
      · exact ⟨by linarith, by linarith [Real.pi_pos]⟩
    have hint : IntervalIntegrable (qfun α) volume 0 θ :=
      (hcontOn_closed.mono hsub).intervalIntegrable
    have hcont : ContinuousAt (qfun α) θ := by
      by_cases hθ0 : θ = 0
      · rw [hθ0]; exact hc0
      by_cases hθπ : θ = Real.pi / 2
      · rw [hθπ]; exact hcπ
      · exact hcont_off θ (le_of_lt h1) (le_of_lt h2) hθ0 hθπ
    have hmeas : StronglyMeasurableAtFilter (qfun α) (nhds θ) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcontOn_open θ ⟨h1, h2⟩
    exact intervalIntegral.integral_hasDerivAt_right (f := qfun α) (a := 0) (b := θ)
      hint hmeas hcont
  -- hence the product rule gives the announced formula on the whole neighbourhood
  have hderiv : ∀ θ : ℝ, -(1 / 2) < θ → θ < Real.pi / 2 + 1 / 2 →
      deriv (psiSol α) θ = M1 α θ := by
    intro θ h1 h2
    have hw := hkey θ h1 h2
    have hd : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
      have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      have h := hlin.sin
      have hval : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
      rw [hval] at h
      exact h
    have hmul := hd.mul (hw.const_add (Kc α))
    have hfun : psiSol α = (fun t : ℝ => Real.sin (2 * t)) * (fun t : ℝ => Kc α + wZer α t) :=
      rfl
    rw [hfun, hmul.deriv]
    simp only [M1]
  constructor
  · show ∀ᶠ θ in nhds (0:ℝ), deriv (psiSol α) θ = M1 α θ
    rw [Filter.eventually_iff]
    refine mem_of_superset (isOpen_Ioo.mem_nhds
      (show (0:ℝ) ∈ Set.Ioo (-(1 / 2)) (1 / 2) from ⟨by norm_num, by norm_num⟩)) ?_
    intro θ hθ
    exact hderiv θ hθ.1 (by linarith [hθ.2, Real.pi_pos])
  · show ∀ᶠ θ in nhds (Real.pi / 2), deriv (psiSol α) θ = M1 α θ
    rw [Filter.eventually_iff]
    have hmem : (Real.pi / 2) ∈ Set.Ioo (Real.pi / 2 - 1 / 2) (Real.pi / 2 + 1 / 2) :=
      ⟨by linarith, by linarith⟩
    refine mem_of_superset (isOpen_Ioo.mem_nhds hmem) ?_
    intro θ hθ
    exact hderiv θ (by linarith [hθ.1, Real.pi_pos]) hθ.2

end Work.FTS.PhiStar.Psi0Est
