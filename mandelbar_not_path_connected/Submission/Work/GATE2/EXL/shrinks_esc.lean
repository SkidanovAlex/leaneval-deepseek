import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.isOpen_pairSide

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2.EXL

/-! ## Angle arithmetic for the nest pairs -/

/-- The lower nest angle `βₙ` is strictly below the upper nest angle `βₙ'`. -/
theorem bAng_lt_bAng' (n : ℕ) : Work.ELNest.bAng n < Work.ELNest.bAng' n := by
  have h1 : Work.ELNest.bAng n < Work.ELNest.alpha1 := by
    rw [Work.ELNest.bAng]
    have h0 : 0 < Work.ELNest.alpha1 - Work.ELNest.beta0 := by
      norm_num [Work.ELNest.alpha1, Work.ELNest.beta0]
    have hp : 0 < (1024 : ℝ) ^ n := by positivity
    have := div_pos h0 hp
    linarith
  have h2 : Work.ELNest.alpha2 < Work.ELNest.bAng' n := by
    rw [Work.ELNest.bAng']
    have h0 : 0 < Work.ELNest.beta0' - Work.ELNest.alpha2 := by
      norm_num [Work.ELNest.beta0', Work.ELNest.alpha2]
    have hp : 0 < (1024 : ℝ) ^ n := by positivity
    have := div_pos h0 hp
    linarith
  have h3 : Work.ELNest.alpha1 < Work.ELNest.alpha2 := by
    norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]
  linarith

/-- The upper nest angle `βₙ'` is strictly below `βₙ + 1`. -/
theorem bAng'_lt_bAng_add_one (n : ℕ) : Work.ELNest.bAng' n < Work.ELNest.bAng n + 1 := by
  have h1 : Work.ELNest.bAng' n ≤ Work.ELNest.beta0' := by
    rw [Work.ELNest.bAng']
    have h0 : 0 ≤ Work.ELNest.beta0' - Work.ELNest.alpha2 := by
      norm_num [Work.ELNest.beta0', Work.ELNest.alpha2]
    have hp : (1 : ℝ) ≤ (1024 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have := div_le_self h0 hp
    linarith
  have h2 : Work.ELNest.beta0 ≤ Work.ELNest.bAng n := by
    rw [Work.ELNest.bAng]
    have h0 : 0 ≤ Work.ELNest.alpha1 - Work.ELNest.beta0 := by
      norm_num [Work.ELNest.alpha1, Work.ELNest.beta0]
    have hp : (1 : ℝ) ≤ (1024 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have := div_le_self h0 hp
    linarith
  have h3 : Work.ELNest.beta0' < Work.ELNest.beta0 + 1 := by
    norm_num [Work.ELNest.beta0, Work.ELNest.beta0']
  linarith

/-- **The escaping part of the nest region shrinks to `z₁`.**  For every `ε > 0` and every
sufficiently large level `n`, the points of the nest region
`pairSideNear P0 ∩ pairSideNear (Q n)` whose potential is below a level `g = g n > 0` lie within
`ε` of the parabolic point `z₁`.

The `K`-part of the statement is the field `Z1Nest.shrinks`; the passage from `K` to the
sublevel set `{pot < g}` is by compactness of the sublevel sets of the potential, using that the
two pairs form the frontier of the two near sides (`frontier_pairSideNear`) and that a pair curve
meets `K` only in its landing point (`pairCurve_inter_K_subset`). -/
theorem shrinks_esc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (z₁ : ℂ) (Pa : Set ℂ)
    (nest : Work.EL.Z1Nest hN z₁ Pa)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (hQy : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ‖(nest.Q n).y - z₁‖ < ε) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ g : ℝ, 0 < g ∧
      ∀ z : ℂ, z ∈ Work.EL.pairSideNear nest.P0 → z ∈ Work.EL.pairSideNear (nest.Q n) →
        Work.EL.pot hN z < g → ‖z - z₁‖ < ε := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := nest.shrinks ε hε
  obtain ⟨N₂, hN₂⟩ := hQy ε hε
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn
  -- angle data of the two pairs
  have hP0ab : nest.P0.a < nest.P0.b := by
    rw [nest.P0_spec.1, nest.P0_spec.2.1]
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hP0b1 : nest.P0.b < nest.P0.a + 1 := by
    rw [nest.P0_spec.1, nest.P0_spec.2.1]
    norm_num [Work.EL.alpha1, Work.EL.alpha2]
  have hQab : (nest.Q n).a < (nest.Q n).b := by
    rw [hQa n, hQb n]
    exact bAng'_lt_bAng_add_one n
  have hQb1 : (nest.Q n).b < (nest.Q n).a + 1 := by
    rw [hQa n, hQb n]
    linarith [bAng_lt_bAng' n]
  -- the pair curves are the frontiers of the near sides
  have hfrP0 : frontier (Work.EL.pairSideNear nest.P0) = Work.EL.pairCurve nest.P0 :=
    Work.ELTop.frontier_pairSideNear hN nest.P0 hP0ab hP0b1
  have hfrQ : frontier (Work.EL.pairSideNear (nest.Q n)) = Work.EL.pairCurve (nest.Q n) :=
    Work.ELTop.frontier_pairSideNear hN (nest.Q n) hQab hQb1
  have hopenP0 : IsOpen (Work.EL.pairSideNear nest.P0) :=
    (Work.ELTop.isOpen_pairSide hN nest.P0).2
  have hopenQ : IsOpen (Work.EL.pairSideNear (nest.Q n)) :=
    (Work.ELTop.isOpen_pairSide hN (nest.Q n)).2
  have hclP0 : closure (Work.EL.pairSideNear nest.P0)
      = Work.EL.pairSideNear nest.P0 ∪ Work.EL.pairCurve nest.P0 := by
    rw [closure_eq_interior_union_frontier, hopenP0.interior_eq, hfrP0]
  have hclQ : closure (Work.EL.pairSideNear (nest.Q n))
      = Work.EL.pairSideNear (nest.Q n) ∪ Work.EL.pairCurve (nest.Q n) := by
    rw [closure_eq_interior_union_frontier, hopenQ.interior_eq, hfrQ]
  -- the closure of the nest region
  have hclsub : closure (Work.EL.pairSideNear nest.P0 ∩ Work.EL.pairSideNear (nest.Q n))
      ⊆ (Work.EL.pairSideNear nest.P0 ∪ Work.EL.pairCurve nest.P0)
        ∩ (Work.EL.pairSideNear (nest.Q n) ∪ Work.EL.pairCurve (nest.Q n)) := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have h := closure_mono (Set.inter_subset_left :
        Work.EL.pairSideNear nest.P0 ∩ Work.EL.pairSideNear (nest.Q n)
          ⊆ Work.EL.pairSideNear nest.P0) hz
      rwa [hclP0] at h
    · have h := closure_mono (Set.inter_subset_right :
        Work.EL.pairSideNear nest.P0 ∩ Work.EL.pairSideNear (nest.Q n)
          ⊆ Work.EL.pairSideNear (nest.Q n)) hz
      rwa [hclQ] at h
  -- (i) the `K`-points of the closure of the nest region are close to `z₁`
  have hKsub : closure (Work.EL.pairSideNear nest.P0 ∩ Work.EL.pairSideNear (nest.Q n))
      ∩ Work.EL.K c ⊆ Metric.ball z₁ ε := by
    rintro z ⟨hzcl, hzK⟩
    obtain ⟨hP0u, hQu⟩ := hclsub hzcl
    rcases hP0u with hP0s | hP0c
    · rcases hQu with hQs | hQc
      · simpa [Metric.mem_ball, Complex.dist_eq] using hN₁ n hn₁ z hzK hQs hP0s
      · have hzy : z = (nest.Q n).y := by
          have hmem := Work.ELTop.pairCurve_inter_K_subset hN (nest.Q n) ⟨hQc, hzK⟩
          simpa using hmem
        rw [hzy, Metric.mem_ball, Complex.dist_eq]
        exact hN₂ n hn₂
    · have hzy : z = z₁ := by
        have hmem := Work.ELTop.pairCurve_inter_K_subset hN nest.P0 ⟨hP0c, hzK⟩
        have hzy0 : z = nest.P0.y := by simpa using hmem
        rw [hzy0, nest.P0_spec.2.2]
      rw [hzy]
      exact Metric.mem_ball_self hε
  -- (ii) for a small potential level the whole piece of the region is close to `z₁`
  have hstep : ∃ g : ℝ, 0 < g ∧
      closure (Work.EL.pairSideNear nest.P0 ∩ Work.EL.pairSideNear (nest.Q n))
        ∩ {z : ℂ | Work.EL.pot hN z ≤ g} ⊆ Metric.ball z₁ ε := by
    by_contra hcon
    rw [not_exists] at hcon
    have hex : ∀ k : ℕ, ∃ z : ℂ,
        z ∈ closure (Work.EL.pairSideNear nest.P0 ∩ Work.EL.pairSideNear (nest.Q n)) ∧
        Work.EL.pot hN z ≤ 1 / ((k : ℝ) + 1) ∧ z ∉ Metric.ball z₁ ε := by
      intro k
      have hk : ¬ (closure (Work.EL.pairSideNear nest.P0 ∩ Work.EL.pairSideNear (nest.Q n))
          ∩ {z : ℂ | Work.EL.pot hN z ≤ 1 / ((k : ℝ) + 1)} ⊆ Metric.ball z₁ ε) := by
        intro hsub
        exact hcon (1 / ((k : ℝ) + 1)) ⟨by positivity, hsub⟩
      obtain ⟨z, hzS, hzb⟩ := Set.not_subset.mp hk
      exact ⟨z, hzS.1, hzS.2, hzb⟩
    choose x hxmem hxpot hxnot using hex
    have hx_mem : ∀ k : ℕ,
        x k ∈ closure (Work.EL.pairSideNear nest.P0 ∩ Work.EL.pairSideNear (nest.Q n))
          ∩ {z : ℂ | Work.EL.pot hN z ≤ 1} := by
      intro k
      refine ⟨hxmem k, ?_⟩
      refine le_trans (hxpot k) ?_
      rw [div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hC : IsCompact (closure (Work.EL.pairSideNear nest.P0 ∩ Work.EL.pairSideNear (nest.Q n))
        ∩ {z : ℂ | Work.EL.pot hN z ≤ 1}) :=
      (Work.EL.isCompact_le_pot hN 1).inter_left isClosed_closure
    obtain ⟨a, haC, φ₀, hφmono, hφtend⟩ := hC.tendsto_subseq (x := x) hx_mem
    have haS : a ∈ closure (Work.EL.pairSideNear nest.P0 ∩ Work.EL.pairSideNear (nest.Q n)) :=
      haC.1
    have hpot_tend : Filter.Tendsto (fun k : ℕ => Work.EL.pot hN (x (φ₀ k))) Filter.atTop
        (nhds (Work.EL.pot hN a)) :=
      hN.continuous_potential.continuousAt.tendsto.comp hφtend
    have hle_ev : ∀ᶠ k : ℕ in Filter.atTop,
        Work.EL.pot hN (x (φ₀ k)) ≤ (1 : ℝ) / ((k : ℝ) + 1) :=
      Filter.Eventually.of_forall fun k => by
        have h1 : Work.EL.pot hN (x (φ₀ k)) ≤ 1 / ((φ₀ k : ℝ) + 1) := hxpot (φ₀ k)
        have h2 : (1 : ℝ) / ((φ₀ k : ℝ) + 1) ≤ (1 : ℝ) / ((k : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by
            have hk := hφmono.id_le k
            have hk' : (k : ℝ) ≤ (φ₀ k : ℝ) := by exact_mod_cast hk
            linarith)
        linarith
    have hapot_le : Work.EL.pot hN a ≤ 0 :=
      le_of_tendsto_of_tendsto hpot_tend
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hle_ev
    have hapot : Work.EL.pot hN a = 0 := le_antisymm hapot_le (Work.EL.pot_nonneg hN a)
    have haK : a ∈ Work.EL.K c := (Work.EL.pot_eq_zero_iff hN a).mp hapot
    have ha_lt : ‖a - z₁‖ < ε := by
      have h := hKsub ⟨haS, haK⟩
      rwa [Metric.mem_ball, Complex.dist_eq] at h
    have hnorm_tend : Filter.Tendsto (fun k : ℕ => ‖x (φ₀ k) - z₁‖) Filter.atTop
        (nhds ‖a - z₁‖) := by
      have hsub : Filter.Tendsto (fun k : ℕ => x (φ₀ k) - z₁) Filter.atTop (nhds (a - z₁)) :=
        hφtend.sub tendsto_const_nhds
      exact continuous_norm.continuousAt.tendsto.comp hsub
    have hge_ev : ∀ᶠ k : ℕ in Filter.atTop, ε ≤ ‖x (φ₀ k) - z₁‖ :=
      Filter.Eventually.of_forall fun k => by
        have h := hxnot (φ₀ k)
        rw [Metric.mem_ball, not_lt] at h
        rwa [Complex.dist_eq] at h
    have hge : ε ≤ ‖a - z₁‖ :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hnorm_tend hge_ev
    linarith
  obtain ⟨g, hgpos, hgsub⟩ := hstep
  refine ⟨g, hgpos, ?_⟩
  intro z hzP hzQ hzpot
  have h := hgsub ⟨subset_closure ⟨hzP, hzQ⟩, le_of_lt hzpot⟩
  rwa [Metric.mem_ball, Complex.dist_eq] at h

end Work.GATE2.EXL
