import Mathlib
import Submission.Work.Pert.pert2v2.LowChart

namespace Work.Pert.pert2v2

open Filter Set
open scoped Topology

/-- **Openness of the clause set of the low chart.**  The set of points `w ∈ V` satisfying the
crux's clause (`Work.Pert.pert2v2.Clause`: the `f`-walk of `φ w` stays in `Df`, the `m`-th iterate
lands in `τ '' Qp'`, and one further return step `F (invOn τ Qp' (f^[m] (φ w)))` stays in `Qp'`)
together with the residual `‖Φp (invOn τ Qp' (f^[m] (φ w))) - m - dlow - Ψ w‖ < δ` is open.

Prove it *pointwise*, using the two continuity lemmas proved in `LowChart.lean`
(`pert2v2.continuousAt_iterate_phi`, `pert2v2.continuousAt_invOn_iterate`) and the openness of
`τ '' Qp'` (`pert2v2.EfFloorDiffV2.mem_nhds_image_of_deriv_ne_zero`); no global continuity is
needed.  This is exactly what makes the low chart `Ulow` of the two-piece return map an admissible
chart. -/
theorem isOpen_clauseSet {f F τ Φp Ψ φ : ℂ → ℂ} {Df Qp' V : Set ℂ} {m : ℕ} {dlow : ℂ} {δ : ℝ}
    (hQp' : IsOpen Qp') (hτ : DifferentiableOn ℂ τ Qp') (hinjτ : Set.InjOn τ Qp')
    (hτne : ∀ z ∈ Qp', deriv τ z ≠ 0)
    (hV : IsOpen V) (hφ : DifferentiableOn ℂ φ V) (hDf : IsOpen Df) (hf : DifferentiableOn ℂ f Df)
    (hF : ContinuousOn F Qp') (hΦp : ContinuousOn Φp Qp') (hΨ : ContinuousOn Ψ V) :
    IsOpen ({w : ℂ | w ∈ V ∧ Work.Pert.pert2v2.Clause f Df F τ φ Qp' m w} ∩
      {w : ℂ | ‖Φp (Work.Pert.invOn τ Qp' (f^[m] (φ w))) - (m : ℂ) - dlow - Ψ w‖ < δ}) := by
  rw [isOpen_iff_mem_nhds]
  rintro w₀ ⟨⟨hwV, hclause⟩, hres⟩
  rw [Clause] at hclause
  obtain ⟨hwalk, hland, hret⟩ := hclause
  -- ### the elementary continuity facts at `w₀`
  -- the partial walk-maps
  have hstep : ∀ j : ℕ, j ≤ m → ContinuousAt (fun w : ℂ => f^[j] (φ w)) w₀ := fun j hj =>
    continuousAt_iterate_phi (m := j) hV hφ hDf hf hwV (fun i hi => hwalk i (hi.trans hj))
  have hiter : ContinuousAt (fun w : ℂ => f^[m] (φ w)) w₀ := hstep m le_rfl
  -- the chosen preimage of the landing value
  have hpre : Work.Pert.invOn τ Qp' (f^[m] (φ w₀)) ∈ Qp' := Work.Pert.invOn_mem hland
  have hinv : ContinuousAt (fun w : ℂ => Work.Pert.invOn τ Qp' (f^[m] (φ w))) w₀ :=
    continuousAt_invOn_iterate hQp' hτ hinjτ hτne hV hφ hDf hf hwV hwalk hland
  -- the landing value lies in the *open* set `τ '' Qp'`
  have hτQp' : τ '' Qp' ∈ 𝓝 (f^[m] (φ w₀)) := by
    obtain ⟨ς, hςQ, hςτ⟩ := hland
    simpa only [hςτ] using
      EfFloorDiffV2.mem_nhds_image_of_deriv_ne_zero hQp' hτ hςQ (hτne ς hςQ)
  -- ### the clause holds eventually
  have hwalk_ev : ∀ᶠ w in 𝓝 w₀, ∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df := by
    have hfin : ∀ᶠ w in 𝓝 w₀, ∀ i : Fin (m + 1), f^[i.val] (φ w) ∈ Df := by
      rw [Filter.eventually_all]
      intro i
      exact (hstep i.val (Nat.le_of_lt_succ i.isLt)).tendsto.eventually
        (hDf.mem_nhds (hwalk i.val (Nat.le_of_lt_succ i.isLt)))
    exact hfin.mono fun w hw j hj => hw ⟨j, Nat.lt_succ_of_le hj⟩
  have hland_ev : ∀ᶠ w in 𝓝 w₀, f^[m] (φ w) ∈ τ '' Qp' :=
    hiter.tendsto.eventually hτQp'
  have hret_ev : ∀ᶠ w in 𝓝 w₀, F (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Qp' :=
    ((hF.continuousAt (hQp'.mem_nhds hpre)).comp
        (g := F) (f := fun w : ℂ => Work.Pert.invOn τ Qp' (f^[m] (φ w))) hinv).tendsto.eventually
      (hQp'.mem_nhds hret)
  have hclause_ev : ∀ᶠ w in 𝓝 w₀, Clause f Df F τ φ Qp' m w := by
    show ∀ᶠ w in 𝓝 w₀, ((∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df) ∧ f^[m] (φ w) ∈ τ '' Qp' ∧
      F (Work.Pert.invOn τ Qp' (f^[m] (φ w))) ∈ Qp')
    exact hwalk_ev.and (hland_ev.and hret_ev)
  -- ### the residual inequality holds eventually (strict inequality, continuous left-hand side)
  have hΦp_inv : ContinuousAt (fun w : ℂ =>
      Φp (Work.Pert.invOn τ Qp' (f^[m] (φ w)))) w₀ :=
    (hΦp.continuousAt (hQp'.mem_nhds hpre)).comp
      (g := Φp) (f := fun w : ℂ => Work.Pert.invOn τ Qp' (f^[m] (φ w))) hinv
  have hΨ_c : ContinuousAt Ψ w₀ := hΨ.continuousAt (hV.mem_nhds hwV)
  have hres_c : ContinuousAt (fun w : ℂ =>
      Φp (Work.Pert.invOn τ Qp' (f^[m] (φ w))) - (m : ℂ) - dlow - Ψ w) w₀ :=
    ((hΦp_inv.sub continuous_const.continuousAt).sub continuous_const.continuousAt).sub hΨ_c
  have hres_ev : ∀ᶠ w in 𝓝 w₀,
      ‖Φp (Work.Pert.invOn τ Qp' (f^[m] (φ w))) - (m : ℂ) - dlow - Ψ w‖ < δ :=
    hres_c.norm.tendsto.eventually (Iio_mem_nhds hres)
  -- ### assemble
  refine Filter.mem_of_superset (Filter.inter_mem ?_ hres_ev) (fun w hw => hw)
  exact Filter.mem_of_superset (Filter.inter_mem (hV.mem_nhds hwV) hclause_ev)
    (fun w hw => hw)

end Work.Pert.pert2v2
