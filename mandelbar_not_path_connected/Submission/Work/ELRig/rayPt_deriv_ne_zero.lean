import Mathlib
import Submission.Work.ELRig.analyticOn_rayPt_of_analytic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Filter Set
open scoped Topology

/-!
# The dynamic rays depend nontrivially on their level

For a dynamical Nakane datum `hN : Work.EL.DynB c φ` and a Böttcher coordinate `φ` which is
analytic on the escape set, the level-`t` point `Work.EL.rayPt hN θ t` of the dynamic ray of
angle `θ` has nonvanishing derivative in `t` for every `t > 1`.

The proof is the inverse-function-theorem computation of
`Submission/Work/ELRig/analyticOn_rayPt_of_analytic.lean` read backwards.  Write
`w = rayPoint θ t = t · e^{2πiθ}` and `g = invBottcher hN`, so that `rayPt hN θ t = g w` for
`t > 1` (`invBottcher_rayPoint`) and `φ (g w) = w` near `w` (`invBottcher_spec`).  Since the
level enters the ray point through the complex-linear map `s ↦ s · e^{2πiθ}`, the chain rule
(`HasDerivAt.scomp`, at the level of an `ℝ`-curve in `ℂ` composed with a `ℂ`-analytic map)
gives

  `deriv (rayPt hN θ ·) t = e^{2πiθ} · deriv g w`,

and `deriv g w ≠ 0` because `φ ∘ g =ᶠ[𝓝 w] id` forces
`deriv φ (g w) · deriv g w = 1` (the chain rule at `w`, in `deriv_comp` form).
-/

/-- **The derivative of the dynamic ray in the level never vanishes** (for level `> 1`). -/
theorem rayPt_deriv_ne_zero {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (han : AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c)) (θ : ℝ) :
    ∀ t : ℝ, 1 < t → deriv (fun s : ℝ => Work.EL.rayPt hN θ s) t ≠ 0 := by
  intro t ht
  -- the direction `z₀ = e^{2πiθ}`, so that `rayPoint θ s = s · z₀` and `rayPoint θ t =: w`
  set z₀ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) with hz₀
  have hz₀ne : z₀ ≠ 0 := Complex.exp_ne_zero _
  have hray : ∀ s : ℝ, Work.Top.NakaneData.rayPoint θ s = (s : ℂ) * z₀ := fun s => rfl
  set w : ℂ := (t : ℂ) * z₀ with hw
  have hw1 : 1 < ‖w‖ := by
    rw [hw, ← hray t, Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith : (0:ℝ) < t)]
    exact ht
  -- the inverse Böttcher coordinate is analytic at `w`
  have hg_an : AnalyticAt ℂ (invBottcher hN) w := analyticAt_invBottcher hN han hw1
  have hg_d : HasDerivAt (invBottcher hN) (deriv (invBottcher hN) w) w :=
    hg_an.differentiableAt.hasDerivAt
  have hh_d : HasDerivAt (fun s : ℝ => (s : ℂ) * z₀) z₀ t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
    simpa using h1.mul_const z₀
  -- the chain rule along the `ℝ`-curve `s ↦ s · z₀`
  have hchain := hg_d.scomp t hh_d
  have heq : (fun s : ℝ => Work.EL.rayPt hN θ s)
      =ᶠ[𝓝 t] (invBottcher hN ∘ fun s : ℝ => (s : ℂ) * z₀) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    simp only [Function.comp_apply]
    rw [invBottcher_rayPoint hN hs, hray s]
  have hderiv_eq : deriv (fun s : ℝ => Work.EL.rayPt hN θ s) t
      = z₀ * deriv (invBottcher hN) w := by
    have h2 := (Filter.EventuallyEq.deriv_eq heq).trans hchain.deriv
    simpa [Function.comp_def, smul_eq_mul] using h2
  -- `φ ∘ invBottcher =ᶠ[𝓝 w] id`, so the derivative of `invBottcher` at `w` is nonzero
  have hφ_an : AnalyticAt ℂ φ (invBottcher hN w) :=
    han _ (invBottcher_spec hN hw1).1
  have hcomp2 := deriv_comp (x := w) (h₂ := φ) (h := invBottcher hN)
    hφ_an.differentiableAt hg_an.differentiableAt
  have hL : deriv (fun u : ℂ => φ (invBottcher hN u)) w = 1 := by
    have heq2 : (fun u : ℂ => φ (invBottcher hN u)) =ᶠ[𝓝 w] id := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw1] with u hu
      exact (invBottcher_spec hN hu).2
    rw [Filter.EventuallyEq.deriv_eq heq2, deriv_id]
  have hprod : deriv φ (invBottcher hN w) * deriv (invBottcher hN) w = 1 := by
    rw [← hcomp2]
    simpa [Function.comp_def] using hL
  have hne : deriv (invBottcher hN) w ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact zero_ne_one hprod
  rw [hderiv_eq]
  exact mul_ne_zero hz₀ne hne

end Work.ELRig
