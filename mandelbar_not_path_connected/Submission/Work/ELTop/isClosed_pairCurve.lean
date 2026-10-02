import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.Top.closure_paramRay_subset

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.style.haveILetI false

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ}

/-!
# The curve of a co-landing pair is closed

The curve of a co-landing pair `P` is `R(P.a) ∪ {P.y} ∪ R(P.b)`.  Each of the two landing rays
`R(θ)`, together with its landing point, is closed: the closure of the ray is `R(θ) ∪ {y}`
because

* off the filled Julia set the ray already contains every limit point (a point of the closure
  lying outside `K` lies on the ray itself, `Work.Top.closure_paramRay_inter_compl`), while
* a limit point `z` inside `K` forces the levels of the approaching ray points to tend to `1`:
  the potential is continuous and vanishes on `K`, so along the ray, where the potential is
  `log t`, the level must tend to `1`; the landing hypothesis then gives `z = y`.

Consequently `Work.EL.pairCurve P` is the union of two closed sets.
-/

/-- For a point `w` of the ray of angle `θ`, the exponential of its potential is *the level* at
which `w` sits on the ray, and the ray point at that level is `w` again. -/
theorem exp_pot_rayPt_eq (hN : Work.EL.DynB c φ) {θ : ℝ} {w : ℂ}
    (hw : w ∈ Work.EL.paramRay hN θ) :
    Work.EL.rayPt hN θ (Real.exp (Work.EL.pot hN w)) = w := by
  obtain ⟨hwK, t, ht, hΦw⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hw
  have hnorm : ‖Work.EL.dynPhi c φ w‖ = t := by
    rw [hΦw, Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
  have hpotw : Work.EL.pot hN w = Real.log t := by
    rw [Work.EL.pot_of_notMem hN hwK, hnorm]
  rw [hpotw, Real.exp_log (by linarith)]
  refine hN.injOn_Phi (Work.EL.rayPt_notMem_K hN ht) hwK ?_
  rw [Work.Top.NakaneData.Phi_rayPt hN ht, hΦw]

/-- **A ray accumulates in the filled Julia set only at its landing point.**  If the ray of angle
`θ` lands at `y`, then every point of `K c` which is a limit of points of the ray is `y`. -/
theorem eq_landing_of_mem_closure (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) {z : ℂ}
    (hz : z ∈ closure (Work.EL.paramRay hN θ)) (hzK : z ∈ Work.EL.K c) : z = y := by
  haveI hF : (𝓝[Work.EL.paramRay hN θ] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
  have hpot0 : Work.EL.pot hN z = 0 := Work.EL.pot_of_mem hN hzK
  -- the exponential of the potential tends to `1` (it is continuous at `z`, where it vanishes)
  have h1 : Tendsto (fun w : ℂ => Real.exp (Work.EL.pot hN w))
      (𝓝[Work.EL.paramRay hN θ] z) (𝓝 1) := by
    have hc : Continuous (fun w : ℂ => Real.exp (Work.EL.pot hN w)) := by
      have hpot : Continuous (Work.EL.pot hN) := hN.continuous_potential
      exact Real.continuous_exp.comp hpot
    have hstep : Tendsto (fun w : ℂ => Real.exp (Work.EL.pot hN w)) (𝓝 z) (𝓝 1) := by
      have h' := (hc.continuousAt (x := z)).tendsto
      rwa [hpot0, Real.exp_zero] at h'
    exact hstep.mono_left inf_le_left
  -- along the ray the levels tend to `1⁺`
  have hlev : Tendsto (fun w : ℂ => Real.exp (Work.EL.pot hN w))
      (𝓝[Work.EL.paramRay hN θ] z) (𝓝[Set.Ioi (1 : ℝ)] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h1, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [Set.mem_Ioi, Real.one_lt_exp_iff]
    exact (Work.Top.NakaneData.potential_pos_iff hN w).mpr
      ((Work.EL.paramRay_subset_compl hN θ) hw)
  -- the ray points at those levels converge to the landing point `y`
  have h2 : Tendsto (fun w : ℂ => Work.EL.rayPt hN θ (Real.exp (Work.EL.pot hN w)))
      (𝓝[Work.EL.paramRay hN θ] z) (𝓝 y) := h.comp hlev
  have h3 : Tendsto (fun w : ℂ => w) (𝓝[Work.EL.paramRay hN θ] z) (𝓝 y) :=
    h2.congr' (eventually_of_mem self_mem_nhdsWithin fun w hw => exp_pot_rayPt_eq hN hw)
  have h4 : Tendsto (fun w : ℂ => w) (𝓝[Work.EL.paramRay hN θ] z) (𝓝 z) :=
    Filter.Tendsto.mono_left tendsto_id inf_le_left
  exact tendsto_nhds_unique h4 h3

/-- The closure of a landing ray is contained in the ray together with its landing point. -/
theorem closure_paramRay_subset_union (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) :
    closure (Work.EL.paramRay hN θ) ⊆ Work.EL.paramRay hN θ ∪ {y} := by
  intro z hz
  by_cases hzp : z ∈ Work.EL.paramRay hN θ
  · exact Or.inl hzp
  · refine Or.inr ?_
    have hzK : z ∈ Work.EL.K c := by
      rcases Work.Top.closure_paramRay_subset hN θ hz with h' | h'
      · exact absurd h' hzp
      · exact h'
    rw [Set.mem_singleton_iff]
    exact eq_landing_of_mem_closure hN h hz hzK

/-- **A parameter ray together with its landing point is closed.** -/
theorem isClosed_paramRay_union_singleton_aux (hN : Work.EL.DynB c φ) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) : IsClosed (Work.EL.paramRay hN θ ∪ {y}) := by
  rw [← closure_subset_iff_isClosed, closure_union, closure_singleton]
  intro z hz
  rcases hz with hz | hzy
  · exact closure_paramRay_subset_union hN h hz
  · exact Or.inr hzy

theorem isClosed_pairCurve {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) :
    IsClosed (Work.EL.pairCurve P) := by
  have h1 := isClosed_paramRay_union_singleton_aux hN P.lands_a
  have h2 := isClosed_paramRay_union_singleton_aux hN P.lands_b
  have hEq : Work.EL.pairCurve P
      = (Work.EL.paramRay hN P.a ∪ {P.y}) ∪ (Work.EL.paramRay hN P.b ∪ {P.y}) := by
    ext z
    rw [Work.EL.mem_pairCurve_iff P z]
    simp only [Set.mem_union, Set.mem_singleton_iff]
    tauto
  rw [hEq]
  exact h1.union h2

end Work.ELTop
