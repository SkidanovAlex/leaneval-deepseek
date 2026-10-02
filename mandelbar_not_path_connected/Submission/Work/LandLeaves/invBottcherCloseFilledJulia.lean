/-
# The inverse Böttcher coordinate is close to the filled Julia set near the unit circle

For `c` in the mandelbar, the inverse dynamical Böttcher coordinate `Ψ = invBottcher (dynB hc)`
maps a neighbourhood of the unit circle arbitrarily close (in the metric of `ℂ`) to the filled
Julia set `filledJulia c = K c`:

> for every `ε > 0` there is `ρ` with `1 < ρ ≤ 2` such that `1 < ‖w‖ < ρ` implies
> `dist (Ψ w) (filledJulia c) ≤ ε`.

Equivalently (which is how the endgame uses it) the image of a small neighbourhood of the unit
circle is within `ε` of a *point* of `K c`, not merely of the set: `invBottcherCloseFilledJulia`
produces the point `y ∈ K c`.

## Route

The inverse Böttcher coordinate is the plain inverse of the Böttcher homeomorphism
(`Work.LandLeaves.bottcherInverse`), so this is the extension of the inverse Böttcher coordinate
to the boundary, in the metric form used downstream.  The ingredients, all proved in
`Submission/Work/LandLeaves/bottcherInverse.lean`, are

* `Work.LandLeaves.invBottcher_norm_le`: `‖Ψ w‖` is bounded for `1 < ‖w‖ < 2`;
* `Work.LandLeaves.greenFun_eq_log_norm`: `G_c (Ψ w) = log ‖w‖`, so `G_c (Ψ w) → 0` as
  `‖w‖ → 1⁺`;
* `Work.LandLeaves.exists_gap_infDist_frontier`: an escaping point of bounded modulus at distance
  `≥ ε` from `frontier (escapingSet c)` has Green function bounded below by `δ(ε) > 0`.

Choosing `ρ` so that `log ρ < δ(ε)` shows that `Ψ w` comes within `ε` of the frontier of the
escaping set.  The frontier of an *open* set does not meet it (`IsOpen.frontier_eq`), so it is
contained in the closed filled Julia set; as the frontier is closed and nonempty
(`nonempty_frontier_iff`, using `Work.ParamRays.e0_mem` and `0 ∈ K c` for `c ∈ M*`), the infimum
of the distance is attained there (`IsClosed.exists_infDist_eq_dist`), which gives the point
`y ∈ K c`.

## Main results

* `Work.LandLeaves.frontier_escapingSet_subset_filledJulia`
* `Work.LandLeaves.nonempty_frontier_escapingSet`
* `Work.LandLeaves.invBottcher_infDist_frontier_le`
* `Work.LandLeaves.invBottcherCloseFilledJulia`
-/
import Mathlib
import Submission.Work.LandLeaves.bottcherInverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Set Metric
open scoped Topology ComplexConjugate

noncomputable section

/-! ## The frontier of the escaping set lies in the filled Julia set -/

/-- The frontier of the (open) escaping set does not meet the escaping set, hence lies in the
filled Julia set `K c = (escapingSet c)ᶜ`. -/
theorem frontier_escapingSet_subset_filledJulia (c : ℂ) :
    frontier (Work.ParamRays.escapingSet c) ⊆ Work.ParamRays.filledJulia c := by
  have hopen : IsOpen (Work.ParamRays.escapingSet c) := by
    rw [← Work.Bottcher.Contraction.escapeSet_eq_escapingSet c]
    exact Work.Bottcher.Contraction.isOpen_escapeSet c
  intro x hx
  have hxs : x ∉ Work.ParamRays.escapingSet c := by
    rw [hopen.frontier_eq] at hx
    exact hx.2
  have hmem : x ∈ (Work.ParamRays.escapingSet c)ᶜ := hxs
  rw [← Work.ParamRays.compl_filledJulia c, compl_compl] at hmem
  exact hmem

/-- The frontier of the escaping set is nonempty: the escaping set is nonempty
(`Work.ParamRays.e0_mem`) and not all of `ℂ` (the critical point `0` lies in `K c` because
`c ∈ M*`), and `ℂ` is connected. -/
theorem nonempty_frontier_escapingSet (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    (frontier (Work.ParamRays.escapingSet c)).Nonempty := by
  rw [nonempty_frontier_iff]
  refine ⟨⟨Work.ParamRays.e0 c, Work.ParamRays.e0_mem c⟩, ?_⟩
  intro h
  have h0 : (0 : ℂ) ∈ Work.ParamRays.escapingSet c := by rw [h]; trivial
  have hbdd : Work.ParamRays.BoundedOrbit c 0 :=
    (Work.ParamRays.mem_mandelbar_iff_bounded c).mp hc
  exact ((Work.ParamRays.escaping_iff_not_bounded c 0).mp h0) hbdd

/-! ## The inverse Böttcher coordinate comes close to the frontier -/

/-- **The inverse Böttcher coordinate maps a neighbourhood of the unit circle close to the
frontier of the escaping set.**  This is the last clause of `Work.LandLeaves.bottcherInverse`,
isolated for the inverse coordinate `Work.ELRig.invBottcher (Work.SeedDyn.dynB hc)` itself. -/
theorem invBottcher_infDist_frontier_le (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 1 < ρ ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < ρ →
      Metric.infDist (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc) w)
        (frontier (Work.ParamRays.escapingSet c)) ≤ ε := by
  let hN : Work.EL.DynB c (Work.ParamRays.dynPhiOf c) := Work.SeedDyn.dynB hc
  have hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
    (Work.SeedDyn.isDynBottcherHomeo hc).1
  obtain ⟨R, -, hR⟩ := invBottcher_norm_le hN hφ
  obtain ⟨δ, hδpos, hδ⟩ := exists_gap_infDist_frontier (c := c) (M := R) hε
  refine ⟨min 2 (Real.exp (min δ 1 / 2)), ?_, ?_⟩
  · refine lt_min (by norm_num) ?_
    rw [Real.one_lt_exp_iff]
    have h := lt_min hδpos one_pos
    linarith
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

/-! ## The main statement -/

theorem invBottcherCloseFilledJulia (c : ℂ) (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < ρ →
      ∃ y ∈ Work.ParamRays.filledJulia c, ‖y - Work.ELRig.invBottcher (Work.SeedDyn.dynB hc) w‖ ≤ ε := by
  intro ε hε
  obtain ⟨ρ₀, hρ₀one, hρ₀⟩ := invBottcher_infDist_frontier_le c hc hε
  refine ⟨min ρ₀ 2, lt_min hρ₀one (by norm_num), min_le_right _ _, ?_⟩
  intro w hw hwr
  have hwr₀ : ‖w‖ < ρ₀ := lt_of_lt_of_le hwr (min_le_left _ _)
  have hinf : Metric.infDist (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc) w)
      (frontier (Work.ParamRays.escapingSet c)) ≤ ε := hρ₀ w hw hwr₀
  obtain ⟨y, hyfront, hydist⟩ := (isClosed_frontier (s := Work.ParamRays.escapingSet c)).exists_infDist_eq_dist
    (nonempty_frontier_escapingSet c hc) (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc) w)
  refine ⟨y, frontier_escapingSet_subset_filledJulia c hyfront, ?_⟩
  have h1 : dist (Work.ELRig.invBottcher (Work.SeedDyn.dynB hc) w) y ≤ ε := by
    rw [← hydist]
    exact hinf
  simpa [dist_comm, dist_eq_norm] using h1

end

end Work.LandLeaves
