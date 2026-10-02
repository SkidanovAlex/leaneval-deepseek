/-
# The two sides of a co-landing pair are open

`Work.EL.pairSide P` and `Work.EL.pairSideNear P` are the connected components of the complement
of the pair curve `Work.EL.pairCurve P = R(a) ∪ {y} ∪ R(b)` containing the ray points of level
`2` in the two cyclic arcs `(a, b)` and `(b, a)`.  Since `ℂ` is locally connected, a connected
component of an *open* set is open; so it is enough to know that the pair curve is closed.

`pairCurve P` is the union of the two closed sets `{y} ∪ R(a)` and `{y} ∪ R(b)`:

* `Work.Top.closure_paramRay_subset` shows that the closure of a parameter ray only adds points
  of the connectedness locus `K c`;
* on the other hand a point of `K c` which is a limit of points of the ray must be the landing
  point: the potential of a point of the ray is `log t` at level `t`, and the potential is
  continuous, so a limit in `K c` (where the potential is `0`) can only be approached at levels
  `t → 1⁺`, where the ray points converge to the landing point `y` (`LandsN`).

This is the openness half of (T6) of `NOTES_LEAD_mandelbar_EL_F_contracts.md` §2.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_mem_K
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

/-- **A ray accumulates in the filled Julia set only at its landing point.**  If the ray of angle
`θ` lands at `y`, then every point of `K c` which is a limit of points of the ray is `y`.

Indeed, along the ray the potential is `log t` at level `t`; the potential is continuous and
vanishes exactly on `K c`, so a limit point in `K c` can only be approached at levels tending to
`1`; and at levels tending to `1⁺` the ray points converge to `y` by the landing hypothesis. -/
theorem eq_landing_of_mem_closure_aux {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) {z : ℂ}
    (hz : z ∈ closure (Work.EL.paramRay hN θ)) (hzK : z ∈ Work.EL.K c) : z = y := by
  have hF : (𝓝[Work.EL.paramRay hN θ] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
  have hpotz : Work.EL.pot hN z = 0 := Work.EL.pot_of_mem hN hzK
  -- the exponential of the potential tends to `1` along the ray (it is continuous at `z`, where
  -- the potential vanishes)
  have h1 : Tendsto (fun w : ℂ => Real.exp (Work.EL.pot hN w))
      (𝓝[Work.EL.paramRay hN θ] z) (𝓝 1) := by
    have hc : Continuous (fun w : ℂ => Real.exp (Work.EL.pot hN w)) := by
      have hpot : Continuous (Work.EL.pot hN) := hN.continuous_potential
      exact Real.continuous_exp.comp hpot
    have hstep : Tendsto (fun w : ℂ => Real.exp (Work.EL.pot hN w)) (𝓝 z) (𝓝 1) := by
      have h := (hc.continuousAt (x := z)).tendsto
      rwa [hpotz, Real.exp_zero] at h
    exact hstep.mono_left inf_le_left
  -- along the ray, `rayPt θ (exp (pot w)) = w` (the exponential undoes the logarithm of the
  -- level)
  have hagree : ∀ w ∈ Work.EL.paramRay hN θ,
      Work.EL.rayPt hN θ (Real.exp (Work.EL.pot hN w)) = w := by
    intro w hw
    obtain ⟨hwK, t, ht, hΦw⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hw
    have hnorm : ‖Work.EL.dynPhi c φ w‖ = t := by
      rw [hΦw, Work.Top.NakaneData.norm_rayPoint, abs_of_pos (by linarith)]
    have hpotw : Work.EL.pot hN w = Real.log t := by
      rw [Work.EL.pot_of_notMem hN hwK, hnorm]
    rw [hpotw, Real.exp_log (by linarith)]
    refine hN.injOn_Phi (Work.EL.rayPt_notMem_K hN ht) hwK ?_
    rw [Work.Top.NakaneData.Phi_rayPt hN ht, hΦw]
  -- composing with the landing hypothesis: the ray points converge to `y`
  have h2 : Tendsto (fun w : ℂ => Work.EL.rayPt hN θ (Real.exp (Work.EL.pot hN w)))
      (𝓝[Work.EL.paramRay hN θ] z) (𝓝 y) := by
    refine h.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h1, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [Set.mem_Ioi, Real.one_lt_exp_iff]
    exact (Work.Top.NakaneData.potential_pos_iff hN w).mpr
      ((Work.EL.paramRay_subset_compl hN θ) hw)
  have h3 : Tendsto (fun w : ℂ => w) (𝓝[Work.EL.paramRay hN θ] z) (𝓝 y) :=
    h2.congr' (eventually_of_mem self_mem_nhdsWithin fun w hw => hagree w hw)
  have h4 : Tendsto (fun w : ℂ => w) (𝓝[Work.EL.paramRay hN θ] z) (𝓝 z) :=
    Filter.Tendsto.mono_left tendsto_id inf_le_left
  haveI : (𝓝[Work.EL.paramRay hN θ] z).NeBot := hF
  exact tendsto_nhds_unique h4 h3

/-- **A parameter ray together with its landing point is closed.**  The closure of the ray adds
only points of `K c`, and the only such point is the landing point. -/
theorem isClosed_singleton_union_paramRay {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {θ : ℝ}
    {y : ℂ} (h : Work.EL.LandsN hN θ y) : IsClosed ({y} ∪ Work.EL.paramRay hN θ) := by
  rw [← closure_subset_iff_isClosed, closure_union, closure_singleton]
  intro w hw
  rcases hw with hwy | hw
  · exact Or.inl hwy
  · rcases Work.Top.closure_paramRay_subset hN θ hw with hA | hK
    · exact Or.inr hA
    · exact Or.inl (by rw [Set.mem_singleton_iff]; exact eq_landing_of_mem_closure_aux h hw hK)

/-- **The pair curve is closed**: it is the union of the two closed sets `{y} ∪ R(a)` and
`{y} ∪ R(b)`. -/
theorem isClosed_pairCurve_local {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) : IsClosed (Work.EL.pairCurve P) := by
  have h1 := isClosed_singleton_union_paramRay (h := P.lands_a)
  have h2 := isClosed_singleton_union_paramRay (h := P.lands_b)
  have hEq : Work.EL.pairCurve P
      = ({P.y} ∪ Work.EL.paramRay hN P.a) ∪ ({P.y} ∪ Work.EL.paramRay hN P.b) := by
    ext z
    simp only [Work.EL.pairCurve, Work.EL.RawPair.curve, Set.mem_union, Set.mem_singleton_iff]
    tauto
  rw [hEq]
  exact h1.union h2

theorem isOpen_pairSide {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (P : Work.EL.CoPair hN) :
    IsOpen (Work.EL.pairSide P) ∧ IsOpen (Work.EL.pairSideNear P) := by
  have hcl : IsClosed (Work.EL.pairCurve P) := isClosed_pairCurve_local P
  exact ⟨hcl.isOpen_compl.connectedComponentIn, hcl.isOpen_compl.connectedComponentIn⟩

end Work.ELTop
