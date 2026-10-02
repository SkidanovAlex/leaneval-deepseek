/-
# The inverse dynamical Böttcher coordinate at a mandelbar parameter

For `c` in the mandelbar (the connectedness locus of `T_c(z) = z̄² + c`) the dynamical Böttcher
coordinate `φ_c = dynPhiOf c` of `T_c` is a homeomorphism of the escaping set onto the exterior
of the unit disc (`Work.SeedDyn.dynBottcherHomeo`).  This file extracts from it the inverse
coordinate `Ψ = φ_c^{-1}` on `{w | 1 < ‖w‖}` together with the four analytic/topological
properties on which the downstream landing and equator-leak arguments depend:

* `Ψ` is complex differentiable on `{w | 1 < ‖w‖}` (it is in fact analytic there, as the inverse
  of the analytic map `φ_c` with nowhere vanishing derivative — this is
  `Work.ELRig.analyticAt_invBottcher`);
* `Ψ` is injective, maps into the escaping set, and is a right inverse of `φ_c`;
* the image of a small neighbourhood of the unit circle lies close to the frontier of the
  escaping set — the *extension to the boundary* of the inverse Böttcher coordinate, in the
  form used by the endgame:
  `∀ ε > 0, ∃ r > 1, ∀ w, 1 < ‖w‖ < r → infDist (Ψ w) (frontier (escapingSet c)) ≤ ε`.

## Main results

* `Work.LandLeaves.greenFun_eq_log_norm`
* `Work.LandLeaves.invBottcher_norm_le`
* `Work.LandLeaves.exists_gap_of_isCompact`
* `Work.LandLeaves.exists_gap_infDist_frontier`
* `Work.LandLeaves.bottcherInverse`
-/
import Mathlib
import Submission.Work.Bottcher.All
import Submission.Work.SeedDyn.Main
import Submission.Work.ELRig.analyticOn_rayPt_of_analytic
import Submission.Work.ELRig.analyticOnNhd_dynBottcher
import Submission.Work.NAKANE.GreenJoint
import Submission.Work.Escape.Mandelbar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open scoped Topology ComplexConjugate

noncomputable section

/-! ## The Green function along the inverse Böttcher coordinate -/

/-- The modulus of a Böttcher coordinate is `exp` of the Green function
(`Work.ParamRays.IsDynBottcher_modulus`); consequently, at a point `z` whose image `φ z = w` is
known, the Green function of `z` is the logarithm of `‖w‖`. -/
theorem greenFun_eq_log_norm {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ)
    {z w : ℂ} (hz : Work.ParamRays.Escaping c z) (hzw : φ z = w) :
    Work.ParamRays.greenFun c z = Real.log ‖w‖ := by
  have h1 : ‖φ z‖ = Real.exp (Work.ParamRays.greenFun c z) :=
    Work.ParamRays.IsDynBottcher_modulus h hz
  rw [hzw] at h1
  rw [h1, Real.log_exp]

/-! ## The inverse Böttcher coordinate stays bounded near the unit circle -/

/-- **A priori bound for the inverse Böttcher coordinate.**  For `1 < ‖w‖ < 2` the point
`Ψ w = φ_c^{-1}(w)` is bounded by a constant depending only on `c` and `φ`.

This is the tangency `φ z ~ z` at infinity (`IsDynBottcher.2.2`, with `ε = 1/2`), which says that
outside a large compact set `‖z‖ ≤ 2‖φ z‖ = 2‖w‖ < 4`. -/
theorem invBottcher_norm_le {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < 2 →
      ‖Work.ELRig.invBottcher hN w‖ ≤ R := by
  have h := hφ.2.2 (1 / 2) (by norm_num)
  obtain ⟨K, hKc, hKsub⟩ := Filter.mem_cocompact.mp h
  obtain ⟨C, hC⟩ := hKc.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max C 4 + 1, by linarith [le_max_right C 4], ?_⟩
  intro w hw1 hw2
  obtain ⟨-, hzw⟩ := Work.ELRig.invBottcher_spec hN hw1
  have hbdd : ‖Work.ELRig.invBottcher hN w‖ ≤ max C 4 := by
    by_contra hcon
    have hzC : max C 4 < ‖Work.ELRig.invBottcher hN w‖ := lt_of_not_ge hcon
    have hmem : Work.ELRig.invBottcher hN w ∉ K := by
      intro hK
      have h1 := hC hK
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      linarith [le_max_left C 4]
    have h2 : ‖φ (Work.ELRig.invBottcher hN w) - Work.ELRig.invBottcher hN w‖ ≤
        (1 / 2) * ‖Work.ELRig.invBottcher hN w‖ := hKsub hmem
    rw [hzw] at h2
    have h3 : ‖Work.ELRig.invBottcher hN w‖ ≤
        ‖w‖ + ‖w - Work.ELRig.invBottcher hN w‖ := by
      calc ‖Work.ELRig.invBottcher hN w‖
          = ‖w - (w - Work.ELRig.invBottcher hN w)‖ := by ring_nf
        _ ≤ ‖w‖ + ‖w - Work.ELRig.invBottcher hN w‖ := norm_sub_le _ _
    linarith [le_max_right C 4]
  linarith

/-! ## A positivity gap on a compact set -/

/-- **A positive continuous function on a compact set is bounded below by a positive
constant.**  (The empty case is handled separately.) -/
theorem exists_gap_of_isCompact {c : ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hpos : ∀ z ∈ K, 0 < Work.ParamRays.greenFun c z) :
    ∃ δ > 0, ∀ z ∈ K, δ ≤ Work.ParamRays.greenFun c z := by
  have hGcont : Continuous fun z : ℂ => Work.ParamRays.greenFun c z :=
    (Work.Escape.continuous_green_Tantibar c).congr
      (fun z => Work.Bottcher.Contraction.green_eq_greenFun c z)
  rcases K.eq_empty_or_nonempty with h | hne
  · refine ⟨1, one_pos, ?_⟩
    intro z hz
    rw [h] at hz
    exact absurd hz (Set.notMem_empty z)
  · obtain ⟨z₀, hz₀K, hmin⟩ := hK.exists_isMinOn hne hGcont.continuousOn
    refine ⟨Work.ParamRays.greenFun c z₀ / 2, by linarith [hpos z₀ hz₀K], ?_⟩
    intro z hzK
    have h1 : Work.ParamRays.greenFun c z₀ ≤ Work.ParamRays.greenFun c z :=
      (isMinOn_iff.mp hmin) z hzK
    linarith [hpos z₀ hz₀K]

/-- **The Green function is bounded below away from the frontier of the escaping set.**

For every `ε > 0` there is `δ > 0` such that every escaping point `z` with `‖z‖ ≤ M` and
`infDist z (frontier (escapingSet c)) ≥ ε` satisfies `δ ≤ G_c z`.

Equivalently: an escaping point which is at distance at least `ε` from the frontier of the escaping
set cannot have small Green function.  The frontier of the (open) escaping set is
`closure (escapingSet c) ∩ (escapingSet c)ᶜ`, so the alternative is that `z` lies at distance `≥ ε`
from `closure (escapingSet c)`, i.e. deep inside the filled Julia set — but then it does not
escape.  Compactness of `{z | ‖z‖ ≤ M, infDist z (frontier …) ≥ ε} ∩ closure (escapingSet c)` and
continuity of `G_c` (`Work.NAKANE.continuous_greenFun`) finish the argument. -/
theorem exists_gap_infDist_frontier {c : ℂ} {M ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : ℂ, Work.ParamRays.Escaping c z → ‖z‖ ≤ M →
      ε ≤ Metric.infDist z (frontier (Work.ParamRays.escapingSet c)) →
      δ ≤ Work.ParamRays.greenFun c z := by
  let T : Set ℂ := closure (Work.ParamRays.escapingSet c) ∩
      {z : ℂ | ‖z‖ ≤ M ∧ ε ≤ Metric.infDist z (frontier (Work.ParamRays.escapingSet c))}
  have hclosed : IsClosed T :=
    isClosed_closure.inter ((isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const
        (Metric.continuous_infDist_pt (frontier (Work.ParamRays.escapingSet c)))))
  have hsub : T ⊆ Metric.closedBall 0 M := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz.2.1
  have hcomp : IsCompact T :=
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 M) hclosed hsub
  have hpos : ∀ z ∈ T, 0 < Work.ParamRays.greenFun c z := by
    intro z hz
    by_contra hcon
    push Not at hcon
    have hzero : Work.ParamRays.greenFun c z = 0 :=
      le_antisymm hcon (Work.ParamRays.greenFun_nonneg c z)
    have hbdd : Work.ParamRays.BoundedOrbit c z :=
      (Work.ParamRays.greenFun_eq_zero_iff c z).mp hzero
    have hnotesc : z ∉ Work.ParamRays.escapingSet c :=
      fun h => (Work.ParamRays.escaping_iff_not_bounded c z).mp h hbdd
    have hfront : z ∈ frontier (Work.ParamRays.escapingSet c) := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨hz.1, subset_closure hnotesc⟩
    have hle := Metric.infDist_le_dist_of_mem (x := z) hfront
    rw [dist_self] at hle
    linarith [hz.2.2, hle, hε]
  obtain ⟨δ, hδpos, hδ⟩ := exists_gap_of_isCompact hcomp hpos
  exact ⟨δ, hδpos, fun z hesc hzM hdist => hδ z ⟨subset_closure hesc, hzM, hdist⟩⟩

theorem bottcherInverse (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) : ∃ (φ Ψ : ℂ → ℂ), Work.ParamRays.IsDynBottcher c φ ∧ DifferentiableOn ℂ Ψ {w : ℂ | 1 < ‖w‖} ∧ Set.InjOn Ψ {w : ℂ | 1 < ‖w‖} ∧ (∀ w : ℂ, 1 < ‖w‖ → Work.ParamRays.Escaping c (Ψ w)) ∧ (∀ w : ℂ, 1 < ‖w‖ → φ (Ψ w) = w) ∧ (∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 1 < r ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < r → Metric.infDist (Ψ w) (frontier (Work.ParamRays.escapingSet c)) ≤ ε) := by
  -- the canonical dynamical Böttcher coordinate of `T_c` and its Nakane datum
  have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    (Work.SeedDyn.isDynBottcherHomeo hc).1
  have hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c) := Work.SeedDyn.dynB hc
  have han : AnalyticOnNhd ℂ (Work.ParamRays.dynPhiOf c) (Work.Bottcher.EscapeSet c) :=
    Work.ELRig.analyticOnNhd_dynBottcher hφ
  refine ⟨Work.ParamRays.dynPhiOf c, Work.ELRig.invBottcher hN, hφ, ?_, ?_, ?_, ?_, ?_⟩
  · -- complex differentiability of the inverse: it is analytic on the exterior disc
    intro w hw
    exact ((Work.ELRig.analyticAt_invBottcher hN han hw).differentiableAt).differentiableWithinAt
  · -- injectivity
    intro w hw w' hw' h
    have h1 := (Work.ELRig.invBottcher_spec hN hw).2
    have h2 := (Work.ELRig.invBottcher_spec hN hw').2
    calc w = Work.ParamRays.dynPhiOf c (Work.ELRig.invBottcher hN w) := h1.symm
      _ = Work.ParamRays.dynPhiOf c (Work.ELRig.invBottcher hN w') := by rw [h]
      _ = w' := h2
  · -- the inverse maps into the escaping set
    intro w hw
    have h := (Work.ELRig.invBottcher_spec hN hw).1
    rw [Work.Bottcher.Contraction.escapeSet_eq_escapingSet c] at h
    exact h
  · -- the inverse is a right inverse
    intro w hw
    exact (Work.ELRig.invBottcher_spec hN hw).2
  · -- the inverse maps a neighbourhood of the unit circle close to the frontier
    intro ε hε
    obtain ⟨R, -, hR⟩ := invBottcher_norm_le hN hφ
    obtain ⟨δ, hδpos, hδ⟩ := exists_gap_infDist_frontier (c := c) (M := R) hε
    refine ⟨min 2 (Real.exp (min δ 1 / 2)), ?_, ?_⟩
    · have hδ1 : (0 : ℝ) < min δ 1 := lt_min hδpos one_pos
      exact lt_min (by norm_num) (Real.one_lt_exp_iff.mpr (by linarith))
    · intro w hw hwr
      have hw2 : ‖w‖ < 2 := lt_of_lt_of_le hwr (min_le_left _ _)
      have hesc : Work.ParamRays.Escaping c (Work.ELRig.invBottcher hN w) := by
        have h := (Work.ELRig.invBottcher_spec hN hw).1
        rw [Work.Bottcher.Contraction.escapeSet_eq_escapingSet c] at h
        exact h
      have hmod : Work.ParamRays.greenFun c (Work.ELRig.invBottcher hN w) = Real.log ‖w‖ :=
        greenFun_eq_log_norm hφ hesc (Work.ELRig.invBottcher_spec hN hw).2
      have hlogr : Real.log (min 2 (Real.exp (min δ 1 / 2))) ≤ δ := by
        have hpos1 : (0 : ℝ) < min 2 (Real.exp (min δ 1 / 2)) :=
          lt_min (by norm_num) (Real.exp_pos _)
        have h1 : Real.log (min 2 (Real.exp (min δ 1 / 2))) ≤
            Real.log (Real.exp (min δ 1 / 2)) := Real.log_le_log hpos1 (min_le_right _ _)
        rw [Real.log_exp] at h1
        have h2 : min δ 1 / 2 ≤ δ := by linarith [min_le_left δ 1]
        linarith
      have hGlt : Work.ParamRays.greenFun c (Work.ELRig.invBottcher hN w) < δ := by
        rw [hmod]
        have hwpos : (0 : ℝ) < ‖w‖ := lt_trans zero_lt_one hw
        have h1 := Real.log_lt_log hwpos hwr
        linarith
      by_contra hcon
      push Not at hcon
      have hle := hδ _ hesc (hR w hw hw2) (le_of_lt hcon)
      linarith

end

end Work.LandLeaves
