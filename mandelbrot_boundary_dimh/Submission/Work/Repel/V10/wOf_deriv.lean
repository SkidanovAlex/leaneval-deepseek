import Mathlib
import Submission.Work.Repel.V10.chain_v9_chase
import Submission.Work.Repel.exists_piExp_eq_of_ball

/-!
# `Work.Repel.wOf_deriv`

`V.wOf u'` is the (unique, on `ball wt₀ ρ₀`) lift of `φ₁ u' / s` under `π = exp (2πi ·)`:
`π (wOf u') = φ₁ u' / s` (`V.wOf_spec`).  Differentiating this identity with respect to `u'`
(the right-hand side is holomorphic in `u'`, and `wOf` is differentiable on the open set
`W 0 = ball cbase ρ`) gives the chain rule

`(π)'(wOf u') · (wOf)'(u') = (φ₁)'(u') / s`,

that is, using `(π)'(w) = 2πi · π w` (`norm_deriv_piExp`),

`2π ‖π (wOf u')‖ · ‖(wOf)'(u')‖ = ‖(φ₁)'(u')‖ / ‖s‖`,

which is the stated derivative bound.  This is step 15 of the §6 ledger
(`NOTES_chain_returns_v9_design.md`, row "derivative bounds", the `dw₁/du'` factor).
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

theorem wOf_deriv (V : Work.Repel.V10) {u' : ℂ} (hu' : u' ∈ V.W 0) :
    ‖deriv V.wOf u'‖ = ‖deriv V.P₁.φ u'‖ /
      (‖V.s‖ * 2 * Real.pi * ‖MandelDim.piExp (V.wOf u')‖) := by
  -- `W 0 = ball cbase ρ` is a neighbourhood of `u'`
  have hWopen : V.W 0 ∈ 𝓝 u' := by
    rw [V.hbase]
    exact Metric.isOpen_ball.mem_nhds (by rwa [V.hbase] at hu')
  -- the three differentiability inputs of the chain rule
  have hdw : DifferentiableAt ℂ V.wOf u' := V.wOf_differentiableOn.differentiableAt hWopen
  have hdφ : DifferentiableAt ℂ V.P₁.φ u' := by
    have hmem : u' ∈ V.P₁.Dφ := V.hsub₁ (by rwa [V.hbase] at hu')
    exact V.P₁.φ_holo.differentiableAt (V.P₁.Dφ_open.mem_nhds hmem)
  have hdpi : DifferentiableAt ℂ MandelDim.piExp (V.wOf u') := by
    unfold MandelDim.piExp; fun_prop
  -- `π ∘ wOf` and `φ₁ / s` agree near `u'`, hence have the same derivative
  have hEq : (fun z => MandelDim.piExp (V.wOf z)) =ᶠ[𝓝 u'] (fun z => V.P₁.φ z / V.s) := by
    filter_upwards [hWopen] with z hz
    exact (V.wOf_spec hz).2
  have h1 : deriv (fun z => MandelDim.piExp (V.wOf z)) u' = deriv (fun z => V.P₁.φ z / V.s) u' :=
    hEq.deriv_eq
  have h2 : deriv (fun z => MandelDim.piExp (V.wOf z)) u'
      = deriv MandelDim.piExp (V.wOf u') * deriv V.wOf u' :=
    deriv_comp u' hdpi hdw
  have h3 : deriv (fun z => V.P₁.φ z / V.s) u' = deriv V.P₁.φ u' / V.s := deriv_div_const V.s
  have hkey : deriv MandelDim.piExp (V.wOf u') * deriv V.wOf u' = deriv V.P₁.φ u' / V.s := by
    rw [h2, h3] at h1; exact h1
  -- take norms, and use `‖(π)'(w)‖ = 2π ‖π w‖`
  have hkey' : ‖deriv MandelDim.piExp (V.wOf u')‖ * ‖deriv V.wOf u'‖
      = ‖deriv V.P₁.φ u'‖ / ‖V.s‖ := by
    have := congrArg norm hkey
    simpa [norm_mul, norm_div] using this
  rw [Work.Repel.norm_deriv_piExp] at hkey'
  have hs0 : ‖V.s‖ ≠ 0 := norm_ne_zero_iff.mpr V.hs
  have hpi0 : ‖MandelDim.piExp (V.wOf u')‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)
  have hD0 : ‖V.s‖ * 2 * Real.pi * ‖MandelDim.piExp (V.wOf u')‖ ≠ 0 := by
    apply mul_ne_zero _ hpi0
    apply mul_ne_zero _ Real.pi_ne_zero
    apply mul_ne_zero hs0
    norm_num
  have hfin : ‖deriv V.wOf u'‖ * (‖V.s‖ * 2 * Real.pi * ‖MandelDim.piExp (V.wOf u')‖)
      = ‖deriv V.P₁.φ u'‖ := by
    have h := congrArg (fun x => x * ‖V.s‖) hkey'
    rw [div_mul_cancel₀ _ hs0] at h
    nlinarith [h]
  rw [eq_div_iff hD0]
  exact hfin

end Work.Repel
