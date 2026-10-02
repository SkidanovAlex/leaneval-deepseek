/-
# Joint continuity of the critical Böttcher coordinate

The **main theorem** of the NAKANE area: the canonical critical Böttcher coordinate
`(c, z) ↦ varphiCrit c z` is *jointly continuous* on
`jointDomain = {(c,z) | z ∈ critDomain c}`.

This is the input GATE asks for (`NOTES_LEAD_mandelbar_residuals.md` §2.3: "Böttcher joint
continuity `(c,z) ↦ φ_c z` on `{G_c z > G_c 0}`"), and it also gives the continuity of the
parameter Böttcher map `Φ c = φ_c(c)` (`Work.NAKANE.PhiContinuity`).

## The argument (why it is not formal)

`φ_c(z)` is the `4^N`-th root of the explicit, jointly continuous function
`W(c,z) := bottcher c ((pMap c)^[N] z)` (valid once `p_c^N z` is in the far region), but the
choice of the root is a `μ_{4^N}`-valued "monodromy" which is not *a priori* continuous in `c`.
The proof transports the root choice along a **chain of balls** from the base point `(c₀,z₀)` to a
point where `φ_c` is known explicitly (a far point `z₁`, where `φ_c(z₁) = bottcher c z₁`):

1. take a path inside `critDomain c₀` from `z₀` to a far point `z₁`
   (`Work.NAKANE.Topological.exists_path_to_far`), a uniform margin `η` around it
   (`IsCompact.exists_cthickening_subset_open`), and a chain of small balls
   `B_0, …, B_m` along it (`Work.NAKANE.Topological.ballChain_exists`), with `ctr 0 = z₀`,
   `ctr m = z₁`, consecutive balls overlapping;
2. `Work.NAKANE.BottcherJoint.exists_gap_of_isCompact` gives a uniform escape gap `s > 0` on the
   chain (for parameters in a ball around `c₀`), and `Work.NAKANE.BottcherJoint.exists_far_iterate`
   gives `N` with `farRadius C < ‖(pMap c)^[N] z‖` for all `z` in the chain;
3. on each `U_i := ball c₀ ε × B_i` the function `W` is continuous and nonvanishing, so it has a
   continuous `4^N`-th root `σ_i` (`Work.NAKANE.BottcherJoint.exists_root_of_continuousOn`);
4. **rescue of the root choice**: on the overlap `B_i ∩ B_{i+1}` the ratio `σ_i / σ_{i+1}` is
   continuous and its `4^N`-th power is `1`, hence it is a *constant* `λ_i`
   (`Work.NAKANE.Topological.eq_of_continuousOn_pow_eq_one`); multiplying `σ_i` by the constant
   `a_i` with `a_{i+1} = a_i λ_i` makes consecutive roots agree on the overlaps, and `a_0` is
   normalised so that `φ_{c₀}(z₀) = a_0 σ_0 (c₀, z₀)`;
5. the class `z ↦ φ_c(z) / (a_i σ_i(c,z))` is continuous on `B_i` and takes values in the
   `4^N`-th roots of unity, so it is *constant on `B_i`* (again
   `eq_of_continuousOn_pow_eq_one`), and the compatibility in (4) shows that the constant is the
   same for all `i`: it is `κ(c) := φ_c(z₁)/(a_m σ_m(c, z₁))`;
6. **`κ` is independent of `c`**: `κ(c) = bottcher c z₁ / (a_m σ_m(c,z₁))` is continuous in `c` on
   `ball c₀ ε` (both factors are) and takes values in `μ_{4^N}`, so it is constant; and
   `κ(c₀) = 1` by the normalisation in (4);
7. hence `φ_c(z) = a_0 σ_0(c,z)` for all `(c,z)` in the neighbourhood
   `ball c₀ ε × B_0`, which is *jointly continuous*: this is the local formula
   `exists_local_joint_formula`, and joint continuity follows.

## Main results

* `Work.NAKANE.exists_local_joint_formula` : locally, `φ_c(z)` agrees with a jointly continuous
  function.
* `Work.NAKANE.continuousAt_jointVarphi`, `Work.NAKANE.continuousOn_jointVarphi` : joint
  continuity on `jointDomain`.
* `Work.NAKANE.continuousOn_jointVarphi_of_isCritBottcher` : the same for *any* family of critical
  Böttcher coordinates (by uniqueness).
* `Work.NAKANE.continuous_varphiCrit_self` : continuity of `c ↦ φ_c(c)`.
-/
import Submission.Work.NAKANE.Defs
import Submission.Work.NAKANE.GreenJoint
import Submission.Work.NAKANE.Topological.ballChain_exists
import Submission.Work.NAKANE.Topological.exists_path_to_far
import Submission.Work.NAKANE.Topological.eq_of_continuousOn_pow_eq_one
import Submission.Work.NAKANE.BottcherJoint.exists_gap_of_isCompact
import Submission.Work.NAKANE.BottcherJoint.exists_far_iterate
import Submission.Work.NAKANE.BottcherJoint.exists_root_of_continuousOn
import Submission.Work.NAKANE.BottcherFar.mem_critDomain_of_farRadius_lt
import Submission.Work.NAKANE.BottcherFar.jointVarphi_eq_jointBottcher_of_far
import Submission.Work.NAKANE.BottcherFar.continuousOn_jointBottcher
import Submission.Work.NAKANE.BottcherFar.bottcher_comm_pMap_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Elementary facts about `farRadius` -/

theorem farRadius_mono : Monotone farRadius := by
  intro C C' h
  unfold farRadius
  have h1 : (2 : ℝ) ≤ max 2 (1 + C) := le_max_left _ _
  have h2 : max 2 (1 + C) ≤ max 2 (1 + C') := max_le_max le_rfl (by linarith)
  nlinarith

theorem escapeRadius_lt_farRadius (c : ℂ) : Work.Bottcher.escapeRadius c < farRadius ‖c‖ := by
  set M : ℝ := max 2 (1 + ‖c‖) with hM
  have h1 : (1 : ℝ) ≤ M := le_trans (by norm_num) (le_max_left 2 (1 + ‖c‖))
  have h2 : (1 : ℝ) + ‖c‖ ≤ M := le_max_right 2 (1 + ‖c‖)
  have h3 : M ≤ M ^ 2 := by nlinarith
  unfold farRadius Work.Bottcher.escapeRadius
  rw [← hM]
  nlinarith

theorem escapeRadius_lt_of_farRadius_lt {C : ℝ} {c z : ℂ} (hc : ‖c‖ ≤ C)
    (hz : farRadius C < ‖z‖) : Work.Bottcher.escapeRadius c < ‖z‖ :=
  lt_of_le_of_lt (escapeRadius_lt_farRadius c).le (lt_of_le_of_lt (farRadius_mono hc) hz)

/-- Ball membership in the norm form. -/
theorem mem_ball_norm {x y : ℂ} {r : ℝ} : y ∈ Metric.ball x r ↔ ‖y - x‖ < r := by
  rw [Metric.mem_ball, dist_eq_norm]

/-- Membership in `critDomain c` from the far radius. -/
theorem mem_critDomain_of_farRadius_lt' {C : ℝ} {c z : ℂ} (hc : ‖c‖ ≤ C)
    (hz : farRadius C < ‖z‖) : z ∈ Work.ParamRays.critDomain c :=
  Work.NAKANE.BottcherFar.mem_critDomain_of_farRadius_lt
    (lt_of_le_of_lt (farRadius_mono hc) hz)

/-- The far-region identity, uniformly in a parameter block. -/
theorem jointVarphi_eq_jointBottcher_of_far' {C : ℝ} {c z : ℂ} (hc : ‖c‖ ≤ C)
    (hz : farRadius C < ‖z‖) : jointVarphi (c, z) = jointBottcher (c, z) :=
  Work.NAKANE.BottcherFar.jointVarphi_eq_jointBottcher_of_far
    (lt_of_le_of_lt (farRadius_mono hc) hz)

/-- The iterated functional equation of the canonical Böttcher coordinate. -/
theorem varphiCrit_functional_iterate {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) (n : ℕ) :
    (Work.Bottcher.varphiCrit c z) ^ (4 ^ n)
      = Work.Bottcher.varphiCrit c ((Work.Bottcher.pMap c)^[n] z) := by
  have h := (Work.Bottcher.isCritBottcher_varphiCrit c).functional_iterate hz n
  rw [show (Work.Bottcher.pMap c)^[n] z = (Tantibar c)^[2 * n] z from Work.Bottcher.pMap_iterate c z n]
  exact h.symm

/-! ## The auxiliary function `W` and its continuity on far blocks -/

/-- `W N (c,z) = bottcher c ((pMap c)^[N] z)`: the explicit, jointly continuous function whose
`4^N`-th root is the critical Böttcher coordinate `φ_c(z)` (in the far regime). -/
def Witer (N : ℕ) (p : ℂ × ℂ) : ℂ :=
  Work.Bottcher.bottcher p.1 ((Work.Bottcher.pMap p.1)^[N] p.2)

theorem continuous_joint_pMap_iterate (n : ℕ) :
    Continuous (fun p : ℂ × ℂ => (Work.Bottcher.pMap p.1)^[n] p.2) := by
  induction n with
  | zero => simpa using continuous_snd
  | succ n ih =>
    have h1 : Continuous fun p : ℂ × ℂ => Work.Bottcher.pMap p.1 p.2 := by
      unfold Work.Bottcher.pMap
      fun_prop
    have hG : Continuous fun p : ℂ × ℂ => (p.1, (Work.Bottcher.pMap p.1)^[n] p.2) :=
      continuous_fst.prodMk ih
    have h2 := h1.comp hG
    have h3 : (fun p : ℂ × ℂ => (Work.Bottcher.pMap p.1)^[n + 1] p.2)
        = fun p : ℂ × ℂ => Work.Bottcher.pMap p.1 ((Work.Bottcher.pMap p.1)^[n] p.2) := by
      funext p
      rw [Function.iterate_succ_apply']
    rw [h3]
    exact h2

theorem continuousOn_Witer_far (N : ℕ) : ContinuousOn (Witer N)
    {p : ℂ × ℂ | Work.Bottcher.escapeRadius p.1 < ‖(Work.Bottcher.pMap p.1)^[N] p.2‖} := by
  have hF : Continuous (fun p : ℂ × ℂ => (p.1, (Work.Bottcher.pMap p.1)^[N] p.2)) :=
    continuous_fst.prodMk (continuous_joint_pMap_iterate N)
  refine (Work.NAKANE.BottcherFar.continuousOn_jointBottcher.comp hF.continuousOn ?_)
  intro p hp
  exact hp

/-! ## The local formula -/

/-- **The local joint formula.**  At every point `(c₀,z₀)` of `jointDomain` there are open
neighbourhoods `U ∋ c₀`, `V ∋ z₀` and a *jointly continuous* function `Ψ` on `U ×ˢ V` with
`Ψ (c,z) = φ_c(z)` on `U ×ˢ V`. -/
theorem exists_local_joint_formula {c₀ z₀ : ℂ} (hz₀ : z₀ ∈ Work.ParamRays.critDomain c₀) :
    ∃ U V : Set ℂ, IsOpen U ∧ c₀ ∈ U ∧ IsOpen V ∧ z₀ ∈ V ∧
      ∃ Ψ : ℂ × ℂ → ℂ, ContinuousOn Ψ (U ×ˢ V) ∧ ∀ p ∈ U ×ˢ V, jointVarphi p = Ψ p := by
  classical
  -- ## Step 1: the parameter bound `C`, the path to a far point, and a margin around it
  set C : ℝ := ‖c₀‖ + 1 with hCdef
  have hCc₀ : ‖c₀‖ ≤ C := by rw [hCdef]; linarith
  obtain ⟨z₁, hz₁far, hz₁crit, γ, hγ0, hγ1, hγmem⟩ :=
    Work.NAKANE.Topological.exists_path_to_far hz₀ (farRadius C + 1)
  have hpath_cpt : IsCompact (γ '' Set.univ) := isCompact_univ.image γ.continuous
  obtain ⟨η, hηpos, hηsub⟩ := hpath_cpt.exists_cthickening_subset_open
    (Work.ParamRays.isOpen_critDomain c₀) (by rintro z ⟨t, -, rfl⟩; exact hγmem t)
  have hthick : ∀ z : ℂ, (∃ t, ‖z - γ t‖ < η) → z ∈ Work.ParamRays.critDomain c₀ := by
    rintro z ⟨t, ht⟩
    exact hηsub (Metric.mem_cthickening_of_dist_le z (γ t) η (γ '' Set.univ)
      ⟨t, Set.mem_univ t, rfl⟩ (by rw [dist_eq_norm]; exact ht.le))
  -- ## Step 2: the chain of balls along the path
  obtain ⟨m, ctr, rad, hradpos, hradle, hctrpath, hctr0, hctrm, hballsub, hoverlap⟩ :=
    Work.NAKANE.Topological.ballChain_exists (Work.ParamRays.isOpen_critDomain c₀) hγmem hηpos hthick
  have hz₁_eq : z₁ = ctr m := by rw [← hγ1, ← hctrm]
  -- ## Step 3: the compact tube, its critical-domain membership, the escape gap and the far iterate
  set tube : Set ℂ := ⋃ i ∈ Finset.range (m + 1), Metric.closedBall (ctr i) (rad i) with htubedef
  have htube_cpt : IsCompact tube := by
    rw [htubedef]
    refine (Finset.finite_toSet (Finset.range (m + 1))).isCompact_biUnion ?_
    intro i _
    exact isCompact_closedBall (ctr i) (rad i)
  have htube_sub : tube ⊆ Work.ParamRays.critDomain c₀ := by
    intro z hz
    simp only [htubedef, Set.mem_iUnion, Finset.mem_range] at hz
    obtain ⟨i, hi, hzi⟩ := hz
    obtain ⟨t, ht⟩ := hctrpath i (Nat.lt_succ_iff.mp hi)
    have hzi' : dist z (ctr i) ≤ rad i := hzi
    have hzi'' : ‖z - ctr i‖ ≤ rad i := by simpa only [dist_eq_norm] using hzi'
    refine hthick z ⟨t, ?_⟩
    rw [← ht]
    have h4 : rad i ≤ η / 4 := hradle i (Nat.lt_succ_iff.mp hi)
    linarith [hzi'', h4, hηpos]
  obtain ⟨ε₀, hε₀pos, s, hspos, hgap⟩ :=
    Work.NAKANE.BottcherJoint.exists_gap_of_isCompact htube_cpt htube_sub
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z ∈ tube, ‖z‖ ≤ B := by
    obtain ⟨B, hB⟩ := htube_cpt.isBounded.subset_closedBall (0 : ℂ)
    exact ⟨B, fun z hz => by
      have := hB hz
      rwa [Metric.mem_closedBall, dist_zero_right] at this⟩
  obtain ⟨N, hN⟩ := Work.NAKANE.BottcherJoint.exists_far_iterate (C := C) (B := B) hspos
  -- ## Step 4: the parameter ball
  set ε : ℝ := min ε₀ 1 with hεdef
  have hεpos : 0 < ε := lt_min hε₀pos one_pos
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hεball : ∀ c : ℂ, ‖c - c₀‖ < ε → ‖c‖ ≤ C := by
    intro c hc
    have h1 : ‖c‖ ≤ ‖c₀‖ + ‖c - c₀‖ := by
      calc ‖c‖ = ‖(c - c₀) + c₀‖ := by ring_nf
        _ ≤ ‖c - c₀‖ + ‖c₀‖ := norm_add_le _ _
        _ = ‖c₀‖ + ‖c - c₀‖ := by ring
    have hε1 : ε ≤ 1 := min_le_right _ _
    rw [hCdef]; linarith
  have hcrit : ∀ c z : ℂ, ‖c - c₀‖ < ε → z ∈ tube → z ∈ Work.ParamRays.critDomain c := by
    intro c z hc hz
    have h1 := hgap c (lt_of_lt_of_le hc hεε₀) z hz
    have h2 : Work.ParamRays.paramPotential c < Work.ParamRays.paramPotential c + s :=
      lt_add_of_pos_right _ hspos
    rw [Work.ParamRays.mem_critDomain]
    linarith
  have hfarN : ∀ c z : ℂ, ‖c - c₀‖ < ε → z ∈ tube →
      farRadius C < ‖(Work.Bottcher.pMap c)^[N] z‖ := by
    intro c z hc hz
    exact hN c z (hεball c hc) (hB z hz) (hgap c (lt_of_lt_of_le hc hεε₀) z hz)
  have htube_of_ball : ∀ i ≤ m, Metric.ball (ctr i) (rad i) ⊆ tube := by
    intro i hi z hz
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le hi),
      Metric.ball_subset_closedBall hz⟩⟩
  -- ## Step 5: `Witer` agrees with the `4^N`-th power of `φ`
  have hW_varphi : ∀ c z : ℂ, ‖c - c₀‖ < ε → z ∈ tube →
      Witer N (c, z) = (Work.Bottcher.varphiCrit c z) ^ (4 ^ N) := by
    intro c z hc hz
    have hfar := hfarN c z hc hz
    have hcw : ‖c‖ ≤ C := hεball c hc
    have h1 : Work.Bottcher.varphiCrit c ((Work.Bottcher.pMap c)^[N] z)
        = Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[N] z) :=
      jointVarphi_eq_jointBottcher_of_far' hcw hfar
    have h2 : (Work.Bottcher.varphiCrit c z) ^ (4 ^ N)
        = Work.Bottcher.varphiCrit c ((Work.Bottcher.pMap c)^[N] z) :=
      varphiCrit_functional_iterate (hcrit c z hc hz) N
    rw [h2, h1]
    rfl
  have hWiter_ne : ∀ c z : ℂ, ‖c - c₀‖ < ε → z ∈ tube → Witer N (c, z) ≠ 0 := by
    intro c z hc hz
    have h1 := escapeRadius_lt_of_farRadius_lt (hεball c hc) (hfarN c z hc hz)
    have h2 := Work.Bottcher.Core.norm_bottcher_eq_exp_green_of_escapeRadius_le c h1.le
    intro hzero
    have h3 : Work.Bottcher.bottcher c ((Work.Bottcher.pMap c)^[N] z) = 0 := hzero
    rw [h3, norm_zero] at h2
    exact absurd h2.symm (Real.exp_ne_zero _)
  -- ## Step 6: the roots `σ i` of `Witer N` on the balls
  have hroot : ∀ i : ℕ, i ≤ m → ∃ σ : ℂ × ℂ → ℂ,
      ContinuousOn σ (Metric.ball c₀ ε ×ˢ Metric.ball (ctr i) (rad i)) ∧
      ∀ c : ℂ, ‖c - c₀‖ < ε → ∀ z ∈ Metric.ball (ctr i) (rad i),
        σ (c, z) ^ (4 ^ N) = Witer N (c, z) := by
    intro i hi
    have hUo : IsOpen (Metric.ball c₀ ε ×ˢ Metric.ball (ctr i) (rad i)) :=
      Metric.isOpen_ball.prod Metric.isOpen_ball
    have hUc : Convex ℝ (Metric.ball c₀ ε ×ˢ Metric.ball (ctr i) (rad i)) :=
      Convex.prod (convex_ball c₀ ε) (convex_ball (ctr i) (rad i))
    have hUne : (Metric.ball c₀ ε ×ˢ Metric.ball (ctr i) (rad i)).Nonempty :=
      ⟨(c₀, ctr i), Metric.mem_ball_self hεpos, Metric.mem_ball_self (hradpos i hi)⟩
    have hsub : (Metric.ball c₀ ε ×ˢ Metric.ball (ctr i) (rad i))
        ⊆ {p : ℂ × ℂ | Work.Bottcher.escapeRadius p.1 < ‖(Work.Bottcher.pMap p.1)^[N] p.2‖} := by
      rintro p ⟨hp1, hp2⟩
      have hp1' : ‖p.1 - c₀‖ < ε := mem_ball_norm.mp hp1
      exact escapeRadius_lt_of_farRadius_lt (hεball p.1 hp1')
        (hfarN p.1 p.2 hp1' (htube_of_ball i hi hp2))
    have hWc : ContinuousOn (Witer N) (Metric.ball c₀ ε ×ˢ Metric.ball (ctr i) (rad i)) :=
      (continuousOn_Witer_far N).mono hsub
    have hWne : ∀ p ∈ (Metric.ball c₀ ε ×ˢ Metric.ball (ctr i) (rad i)), Witer N p ≠ 0 :=
      fun p hp => hWiter_ne p.1 p.2 (mem_ball_norm.mp hp.1) (htube_of_ball i hi hp.2)
    obtain ⟨σ, hσc, hσp⟩ := Work.NAKANE.BottcherJoint.exists_root_of_continuousOn
      hUo hUc hUne hWc hWne (m := 4 ^ N) (by positivity)
    exact ⟨σ, hσc, fun c hc z hz => hσp (c, z)⟩
  let σ : ℕ → ℂ × ℂ → ℂ := fun i =>
    if hi : i ≤ m then Classical.choose (hroot i hi) else fun _ => 1
  have hσ_cont : ∀ i (hi : i ≤ m),
      ContinuousOn (σ i) (Metric.ball c₀ ε ×ˢ Metric.ball (ctr i) (rad i)) := by
    intro i hi
    rw [show σ i = Classical.choose (hroot i hi) from dif_pos hi]
    exact (Classical.choose_spec (hroot i hi)).1
  have hσ_pow : ∀ i (hi : i ≤ m) (c : ℂ), ‖c - c₀‖ < ε →
      ∀ z ∈ Metric.ball (ctr i) (rad i), (σ i) (c, z) ^ (4 ^ N) = Witer N (c, z) := by
    intro i hi c hc z hz
    rw [show σ i = Classical.choose (hroot i hi) from dif_pos hi]
    exact (Classical.choose_spec (hroot i hi)).2 c hc z hz
  have hσ_ne : ∀ i (hi : i ≤ m) (c : ℂ), ‖c - c₀‖ < ε →
      ∀ z ∈ Metric.ball (ctr i) (rad i), (σ i) (c, z) ≠ 0 := by
    intro i hi c hc z hz h0
    have h1 := hσ_pow i hi c hc z hz
    rw [h0, zero_pow (pow_ne_zero N (by norm_num))] at h1
    exact hWiter_ne c z hc (htube_of_ball i hi hz) h1.symm


  -- ## Step 7: the class `φ_c z / σ_i(c,z)` is constant on each ball
  have hclass : ∀ i (hi : i ≤ m) (c : ℂ), ‖c - c₀‖ < ε → ∀ z ∈ Metric.ball (ctr i) (rad i),
      Work.Bottcher.varphiCrit c z / (σ i) (c, z)
        = Work.Bottcher.varphiCrit c (ctr i) / (σ i) (c, ctr i) := by
    intro i hi c hc z hz
    refine Work.NAKANE.Topological.eq_of_continuousOn_pow_eq_one (m := 4 ^ N)
      (f := fun w : ℂ => Work.Bottcher.varphiCrit c w / (σ i) (c, w))
      (convex_ball (ctr i) (rad i)).isPreconnected
      ?_ (pow_pos (by norm_num) N) ?_ hz (Metric.mem_ball_self (hradpos i hi))
    · have hcont1 : ContinuousOn (fun w : ℂ => Work.Bottcher.varphiCrit c w)
          (Metric.ball (ctr i) (rad i)) :=
        (Work.Bottcher.varphiCrit_continuousOn c).mono fun w hw => hcrit c w hc (htube_of_ball i hi hw)
      have hcont2 : ContinuousOn (fun w : ℂ => (σ i) (c, w)) (Metric.ball (ctr i) (rad i)) :=
        (hσ_cont i hi).comp (continuous_const.prodMk continuous_id).continuousOn
          fun w hw => ⟨mem_ball_norm.mpr hc, hw⟩
      exact hcont1.div hcont2 fun w hw => hσ_ne i hi c hc w hw
    · intro w hw
      rw [div_pow, hσ_pow i hi c hc w hw, ← hW_varphi c w hc (htube_of_ball i hi hw)]
      exact div_self (hWiter_ne c w hc (htube_of_ball i hi hw))

  -- ## Step 8: on the overlaps consecutive roots differ by a *constant*
  have hcompat : ∀ i : ℕ, ∃ lam : ℂ, lam ^ (4 ^ N) = 1 ∧
      (i < m → ∀ c : ℂ, ‖c - c₀‖ < ε →
        ∀ y ∈ Metric.ball (ctr i) (rad i) ∩ Metric.ball (ctr (i + 1)) (rad (i + 1)),
          (σ i) (c, y) = lam * (σ (i + 1)) (c, y)) := by
    intro i
    by_cases hi : i < m
    · obtain ⟨y₀, hy₀⟩ := hoverlap i hi
      have hy₀i : y₀ ∈ Metric.ball (ctr i) (rad i) := hy₀.1
      have hy₀i' : y₀ ∈ Metric.ball (ctr (i + 1)) (rad (i + 1)) := hy₀.2
      have hc₀' : ‖c₀ - c₀‖ < ε := by rw [sub_self, norm_zero]; exact hεpos
      have hWne₀ : Witer N (c₀, y₀) ≠ 0 :=
        hWiter_ne c₀ y₀ hc₀' (htube_of_ball i hi.le hy₀i)
      refine ⟨(σ i) (c₀, y₀) / (σ (i + 1)) (c₀, y₀), ?_, fun _ => ?_⟩
      · rw [div_pow, hσ_pow i hi.le c₀ hc₀' y₀ hy₀i,
          hσ_pow (i + 1) (Nat.succ_le_of_lt hi) c₀ hc₀' y₀ hy₀i']
        exact div_self hWne₀
      · intro c hc y hy
        have hcont : ContinuousOn (fun p : ℂ × ℂ => (σ i) p / (σ (i + 1)) p)
            (Metric.ball c₀ ε ×ˢ (Metric.ball (ctr i) (rad i) ∩ Metric.ball (ctr (i + 1)) (rad (i + 1)))) := by
          refine ContinuousOn.div ((hσ_cont i hi.le).mono ?_)
            ((hσ_cont (i + 1) (Nat.succ_le_of_lt hi)).mono ?_) ?_
          · intro p hp; exact ⟨hp.1, hp.2.1⟩
          · intro p hp; exact ⟨hp.1, hp.2.2⟩
          · intro p hp
            exact hσ_ne (i + 1) (Nat.succ_le_of_lt hi) p.1 (mem_ball_norm.mp hp.1) p.2 hp.2.2
        have hpow : ∀ p ∈ (Metric.ball c₀ ε ×ˢ
            (Metric.ball (ctr i) (rad i) ∩ Metric.ball (ctr (i + 1)) (rad (i + 1)))),
            ((σ i) p / (σ (i + 1)) p) ^ (4 ^ N) = 1 := by
          rintro p ⟨hp1, hp2⟩
          have hp1' : ‖p.1 - c₀‖ < ε := mem_ball_norm.mp hp1
          rw [div_pow, hσ_pow i hi.le p.1 hp1' p.2 hp2.1,
            hσ_pow (i + 1) (Nat.succ_le_of_lt hi) p.1 hp1' p.2 hp2.2]
          exact div_self (hWiter_ne p.1 p.2 hp1' (htube_of_ball i hi.le hp2.1))
        have hpre : IsPreconnected (Metric.ball c₀ ε ×ˢ
            (Metric.ball (ctr i) (rad i) ∩ Metric.ball (ctr (i + 1)) (rad (i + 1)))) :=
          (Convex.prod (convex_ball c₀ ε)
            ((convex_ball (ctr i) (rad i)).inter (convex_ball (ctr (i + 1)) (rad (i + 1))))).isPreconnected
        have hconst := Work.NAKANE.Topological.eq_of_continuousOn_pow_eq_one hpre hcont (pow_pos (by norm_num) N) hpow
          (show (c₀, y₀) ∈ Metric.ball c₀ ε ×ˢ
            (Metric.ball (ctr i) (rad i) ∩ Metric.ball (ctr (i + 1)) (rad (i + 1))) from
            ⟨Metric.mem_ball_self hεpos, hy₀⟩)
          (show (c, y) ∈ Metric.ball c₀ ε ×ˢ
            (Metric.ball (ctr i) (rad i) ∩ Metric.ball (ctr (i + 1)) (rad (i + 1))) from
            ⟨mem_ball_norm.mpr hc, hy⟩)
        have hratio : (σ i) (c, y) / (σ (i + 1)) (c, y)
            = (σ i) (c₀, y₀) / (σ (i + 1)) (c₀, y₀) := hconst.symm
        rw [div_eq_iff (hσ_ne (i + 1) (Nat.succ_le_of_lt hi) c hc y hy.2)] at hratio
        exact hratio
    · exact ⟨1, one_pow _, fun h => absurd h hi⟩
  -- ## Step 9: `χ_0` is a constant multiple of `χ_m`
  let lam : ℕ → ℂ := fun i => Classical.choose (hcompat i)
  have hlam_pow : ∀ i : ℕ, (lam i) ^ (4 ^ N) = 1 :=
    fun i => (Classical.choose_spec (hcompat i)).1
  have hlam_spec : ∀ i (hi : i < m) (c : ℂ), ‖c - c₀‖ < ε →
      ∀ y ∈ Metric.ball (ctr i) (rad i) ∩ Metric.ball (ctr (i + 1)) (rad (i + 1)),
        (σ i) (c, y) = lam i * (σ (i + 1)) (c, y) :=
    fun i hi c hc y hy => (Classical.choose_spec (hcompat i)).2 hi c hc y hy
  have hstep : ∀ i (hi : i < m) (c : ℂ), ‖c - c₀‖ < ε →
      Work.Bottcher.varphiCrit c (ctr i) / (σ i) (c, ctr i)
        = (lam i)⁻¹ * (Work.Bottcher.varphiCrit c (ctr (i + 1))
            / (σ (i + 1)) (c, ctr (i + 1))) := by
    intro i hi c hc
    obtain ⟨y, hy⟩ := hoverlap i hi
    have hyi : y ∈ Metric.ball (ctr i) (rad i) := hy.1
    have hyi' : y ∈ Metric.ball (ctr (i + 1)) (rad (i + 1)) := hy.2
    have h1 := hclass i hi.le c hc y hyi
    have h2 := hclass (i + 1) (Nat.succ_le_of_lt hi) c hc y hyi'
    have h3 := hlam_spec i hi c hc y hy
    have hne : lam i ≠ 0 := by
      intro h0
      have h := hlam_pow i
      rw [h0, zero_pow (pow_ne_zero N (by norm_num))] at h
      exact one_ne_zero h.symm
    have hne2 : (σ (i + 1)) (c, y) ≠ 0 :=
      hσ_ne (i + 1) (Nat.succ_le_of_lt hi) c hc y hyi'
    rw [← h1, ← h2, h3]
    field_simp
  have hchain : ∃ A : ℂ, A ^ (4 ^ N) = 1 ∧ ∀ c : ℂ, ‖c - c₀‖ < ε →
      Work.Bottcher.varphiCrit c (ctr 0) / (σ 0) (c, ctr 0)
        = A * (Work.Bottcher.varphiCrit c (ctr m) / (σ m) (c, ctr m)) := by
    have hind : ∀ k : ℕ, k ≤ m → ∃ A : ℂ, A ^ (4 ^ N) = 1 ∧ ∀ c : ℂ, ‖c - c₀‖ < ε →
        Work.Bottcher.varphiCrit c (ctr (m - k)) / (σ (m - k)) (c, ctr (m - k))
          = A * (Work.Bottcher.varphiCrit c (ctr m) / (σ m) (c, ctr m)) := by
      intro k
      induction k with
      | zero =>
        intro _
        exact ⟨1, one_pow _, fun c hc => by rw [Nat.sub_zero, one_mul]⟩
      | succ k ih =>
        intro hk
        have hk' : k ≤ m := le_trans (Nat.le_succ k) hk
        obtain ⟨A, hA, hAc⟩ := ih hk'
        have hlt : m - (k + 1) < m := by omega
        have hidx : m - (k + 1) + 1 = m - k := by omega
        refine ⟨A * (lam (m - (k + 1)))⁻¹, ?_, ?_⟩
        · rw [mul_pow, hA, inv_pow, hlam_pow (m - (k + 1))]
          simp
        · intro c hc
          rw [hstep (m - (k + 1)) hlt c hc, hidx, hAc c hc]
          ring
    obtain ⟨A, hA, hAc⟩ := hind m le_rfl
    exact ⟨A, hA, fun c hc => by simpa using hAc c hc⟩
  -- ## Step 10: `χ_m` is continuous in `c`
  have hfar_ctr : ∀ c : ℂ, c ∈ Metric.ball c₀ ε → Work.Bottcher.escapeRadius c < ‖ctr m‖ := by
    intro c hc
    have h1 : ‖c - c₀‖ < ε := mem_ball_norm.mp hc
    have h2 : ‖ctr m‖ = ‖z₁‖ := by rw [hctrm, hγ1]
    rw [h2]
    exact escapeRadius_lt_of_farRadius_lt (hεball c h1) (by linarith [hz₁far])
  have hχm_cont : ContinuousOn
      (fun c : ℂ => Work.Bottcher.bottcher c (ctr m) / (σ m) (c, ctr m)) (Metric.ball c₀ ε) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · refine (Work.NAKANE.BottcherFar.continuousOn_jointBottcher.comp
        (continuous_id.prodMk continuous_const).continuousOn ?_)
      intro c hc
      exact hfar_ctr c hc
    · refine (hσ_cont m le_rfl).comp (continuous_id.prodMk continuous_const).continuousOn ?_
      intro c hc
      exact ⟨hc, Metric.mem_ball_self (hradpos m le_rfl)⟩
    · intro c hc
      exact hσ_ne m le_rfl c (mem_ball_norm.mp hc) (ctr m) (Metric.mem_ball_self (hradpos m le_rfl))
  have hχ_cont : ContinuousOn
      (fun c : ℂ => Work.Bottcher.varphiCrit c (ctr m) / (σ m) (c, ctr m)) (Metric.ball c₀ ε) := by
    refine hχm_cont.congr ?_
    intro c hc
    have h1 : ‖c - c₀‖ < ε := mem_ball_norm.mp hc
    have h2 : ‖ctr m‖ = ‖z₁‖ := by rw [hctrm, hγ1]
    have h3 : Work.NAKANE.farRadius C < ‖ctr m‖ := by
      rw [h2]
      linarith [hz₁far]
    show Work.Bottcher.varphiCrit c (ctr m) / (σ m) (c, ctr m)
      = Work.Bottcher.bottcher c (ctr m) / (σ m) (c, ctr m)
    rw [show Work.Bottcher.varphiCrit c (ctr m) = Work.Bottcher.bottcher c (ctr m) from
      jointVarphi_eq_jointBottcher_of_far' (hεball c h1) h3]
  -- ## Step 11: `χ_0` is constant in `c`
  have hχ0_const : ∀ c : ℂ, c ∈ Metric.ball c₀ ε →
      Work.Bottcher.varphiCrit c (ctr 0) / (σ 0) (c, ctr 0)
        = Work.Bottcher.varphiCrit c₀ (ctr 0) / (σ 0) (c₀, ctr 0) := by
    intro c hc
    obtain ⟨A, hA, hAc⟩ := hchain
    have hc' : ‖c - c₀‖ < ε := mem_ball_norm.mp hc
    have hc₀' : ‖c₀ - c₀‖ < ε := by rw [sub_self, norm_zero]; exact hεpos
    have hpowm : ∀ c' ∈ Metric.ball c₀ ε,
        (A * (Work.Bottcher.varphiCrit c' (ctr m) / (σ m) (c', ctr m))) ^ (4 ^ N) = 1 := by
      intro c' hc''
      have hc''' : ‖c' - c₀‖ < ε := mem_ball_norm.mp hc''
      have hball : ctr m ∈ Metric.ball (ctr m) (rad m) := Metric.mem_ball_self (hradpos m le_rfl)
      have h1 : (Work.Bottcher.varphiCrit c' (ctr m) / (σ m) (c', ctr m)) ^ (4 ^ N) = 1 := by
        rw [div_pow, hσ_pow m le_rfl c' hc''' (ctr m) hball,
          ← hW_varphi c' (ctr m) hc''' (htube_of_ball m le_rfl hball)]
        exact div_self (hWiter_ne c' (ctr m) hc''' (htube_of_ball m le_rfl hball))
      rw [mul_pow, hA, h1, mul_one]
    have hc₀'' : c₀ ∈ Metric.ball c₀ ε := Metric.mem_ball_self hεpos
    have hconstm := Work.NAKANE.Topological.eq_of_continuousOn_pow_eq_one (m := 4 ^ N)
      (f := fun c' : ℂ => A * (Work.Bottcher.varphiCrit c' (ctr m) / (σ m) (c', ctr m)))
      (convex_ball c₀ ε).isPreconnected (hχ_cont.const_mul A) (pow_pos (by norm_num) N) hpowm hc hc₀''
    rw [hAc c hc', hconstm, ← hAc c₀ hc₀']
  -- ## Step 12: the conclusion
  have hctr0_eq : ctr 0 = z₀ := by rw [hctr0, hγ0]
  refine ⟨Metric.ball c₀ ε, Metric.ball (ctr 0) (rad 0), Metric.isOpen_ball, Metric.mem_ball_self hεpos,
    Metric.isOpen_ball, hctr0_eq ▸ Metric.mem_ball_self (hradpos 0 (Nat.zero_le m)), ?_⟩
  refine ⟨fun p => (σ 0) p * (Work.Bottcher.varphiCrit c₀ (ctr 0) / (σ 0) (c₀, ctr 0)), ?_, ?_⟩
  · exact ContinuousOn.mul ((hσ_cont 0 (Nat.zero_le m)).mono fun p hp => hp) continuousOn_const
  · rintro ⟨c, z⟩ ⟨hc, hz⟩
    have hc' : ‖c - c₀‖ < ε := mem_ball_norm.mp hc
    have h1 := hclass 0 (Nat.zero_le m) c hc' z hz
    have h2 := hχ0_const c hc
    have hne : (σ 0) (c, z) ≠ 0 := hσ_ne 0 (Nat.zero_le m) c hc' z hz
    show jointVarphi (c, z) = (σ 0) (c, z) * (Work.Bottcher.varphiCrit c₀ (ctr 0) / (σ 0) (c₀, ctr 0))
    rw [jointVarphi_apply]
    calc Work.Bottcher.varphiCrit c z
        = (σ 0) (c, z) * (Work.Bottcher.varphiCrit c z / (σ 0) (c, z)) := by field_simp
      _ = (σ 0) (c, z) * (Work.Bottcher.varphiCrit c (ctr 0) / (σ 0) (c, ctr 0)) := by rw [h1]
      _ = (σ 0) (c, z) * (Work.Bottcher.varphiCrit c₀ (ctr 0) / (σ 0) (c₀, ctr 0)) := by rw [h2]

/-! ## The joint continuity of the critical Böttcher coordinate -/

/-- `jointDomain` is open. -/
theorem isOpen_jointDomain : IsOpen jointDomain := by
  rw [show jointDomain = {p : ℂ × ℂ |
    Work.ParamRays.paramPotential p.1 < Work.ParamRays.greenFun p.1 p.2} from rfl]
  exact isOpen_lt (continuous_paramPotential.comp continuous_fst)
    (continuous_greenFun.comp (continuous_fst.prodMk continuous_snd))

/-- **Joint continuity of the critical Böttcher coordinate**, pointwise form. -/
theorem continuousAt_jointVarphi {c₀ z₀ : ℂ} (hz₀ : z₀ ∈ Work.ParamRays.critDomain c₀) :
    ContinuousAt jointVarphi (c₀, z₀) := by
  obtain ⟨U, V, hUo, hc₀U, hVo, hz₀V, Ψ, hΨc, hΨeq⟩ := exists_local_joint_formula hz₀
  have hopen : IsOpen (U ×ˢ V) := hUo.prod hVo
  have hmem : (c₀, z₀) ∈ U ×ˢ V := ⟨hc₀U, hz₀V⟩
  have h1 : ContinuousAt Ψ (c₀, z₀) := hΨc.continuousAt (hopen.mem_nhds hmem)
  refine h1.congr ?_
  filter_upwards [hopen.mem_nhds hmem] with p hp
  exact (hΨeq p hp).symm

/-- **The critical Böttcher coordinate is jointly continuous on `jointDomain`.** -/
theorem continuousOn_jointVarphi : ContinuousOn jointVarphi jointDomain :=
  fun p hp => (continuousAt_jointVarphi hp).continuousWithinAt

/-- **Joint continuity for an arbitrary family of critical Böttcher coordinates** (by uniqueness
on `critDomain`). -/
theorem continuousOn_jointVarphi_of_isCritBottcher {φ : ℂ → ℂ → ℂ}
    (hφ : ∀ c : ℂ, Work.ParamRays.IsCritBottcher c (φ c)) :
    ContinuousOn (fun p : ℂ × ℂ => φ p.1 p.2) jointDomain := by
  refine continuousOn_jointVarphi.congr ?_
  intro p hp
  exact (Work.Bottcher.varphiCrit_unique (hφ p.1) hp).symm

/-- **The critical Böttcher coordinate is continuous along the diagonal `c ↦ φ_c(c)`**, outside
the mandelbar (where `c ∈ critDomain c`). -/
theorem continuousOn_varphiCrit_self :
    ContinuousOn (fun c : ℂ => Work.Bottcher.varphiCrit c c) {c : ℂ | c ∉ Mb} := by
  have h := ContinuousOn.comp (s := {c : ℂ | c ∉ Mb}) (t := jointDomain)
    (g := jointVarphi) (f := fun c : ℂ => (c, c))
    continuousOn_jointVarphi (continuous_id.prodMk continuous_id).continuousOn ?_
  · exact h
  · intro c hc
    exact Work.ParamRays.self_mem_critDomain hc

end Work.NAKANE
