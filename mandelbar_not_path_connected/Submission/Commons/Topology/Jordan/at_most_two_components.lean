import Mathlib
import Submission.Commons.Topology.Brouwer.brouwer_fixed_point_closedBall
import Submission.Commons.Topology.Connected.frontier_component_compl_range
import Submission.Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds
import Submission.Commons.Topology.Connected.isPreconnected_compl_closedBall
import Submission.Commons.Topology.Jordan.at_most_one_bounded_component

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1600000

open Set Metric
open scoped Topology

namespace Commons.Topology.Jordan

/-! ## A Brouwer-based obstruction for regions bounded by an arc -/

/-- **Brouwer obstruction.**  An open connected bounded region `C` whose (topological) frontier
is contained in the image of an arc, and which is disjoint from that arc, cannot exist.

This is proved exactly as in `frontier_component_compl_range`: the arc admits a retraction
`r` of the plane; the self-map `G` of a large disc built from `r` has a Brouwer fixed point
which forces an impossible vector equation. -/
lemma no_bounded_arc_boundary (β : C(Commons.Topology.Connected.UI, ℂ))
    (hβ : Function.Injective β)
    {C : Set ℂ} (hCop : IsOpen C) (hCne : C.Nonempty) (hCbdd : Bornology.IsBounded C)
    (hCpre : IsPreconnected C) (hsub : frontier C ⊆ Set.range β)
    (hdisj : Disjoint C (Set.range β)) : False := by
  classical
  obtain ⟨r, hrβ, hrrange⟩ := Commons.Topology.Connected.exists_retraction_of_arc hβ
  obtain ⟨c0, hc0⟩ := hCne
  have hc0not : c0 ∉ Set.range β := fun h => hdisj.le_bot ⟨hc0, h⟩
  have hcompactβ : IsCompact (Set.range β) := isCompact_range β.continuous
  obtain ⟨R1, hR1⟩ := (Metric.isBounded_iff_subset_closedBall c0).mp hCbdd.closure
  obtain ⟨R2, hR2⟩ := (Metric.isBounded_iff_subset_closedBall c0).mp hcompactβ.isBounded
  have hR1nonneg : 0 ≤ R1 := by
    have h1 := hR1 (subset_closure hc0)
    rw [Metric.mem_closedBall, dist_self] at h1
    exact h1
  set R : ℝ := max R1 R2 + 1 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; have := le_max_left R1 R2; linarith
  have hcl_ball : closure C ⊆ Metric.ball c0 R := by
    intro z hz
    have h1 := hR1 hz
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_ball]
    calc dist z c0 ≤ R1 := h1
      _ < R := by rw [hRdef]; have := le_max_left R1 R2; linarith
  have hβ_ball : Set.range β ⊆ Metric.closedBall c0 R := by
    intro z hz
    have h1 := hR2 hz
    rw [Metric.mem_closedBall] at h1
    rw [Metric.mem_closedBall]
    calc dist z c0 ≤ R2 := h1
      _ ≤ R := by rw [hRdef]; have := le_max_right R1 R2; linarith
  set D : Set ℂ := Metric.closedBall c0 R with hDdef
  have hr_on : ∀ a ∈ Set.range β, r a = a := by
    rintro a ⟨t, rfl⟩
    exact hrβ t
  have hcontpiece : Continuous (fun z : ℂ => if z ∈ closure C then r z else z) := by
    apply continuous_if
    · intro a ha
      exact hr_on a (hsub (frontier_closure_subset ha))
    · exact r.continuous.continuousOn
    · exact continuous_id.continuousOn
  set fp : C(ℂ, ℂ) := ⟨fun z => if z ∈ closure C then r z else z, hcontpiece⟩ with hfpdef
  set fD : C(D, ℂ) := fp.restrict D with hfDdef
  have hneD : ∀ z : D, fD z ≠ c0 := by
    intro z
    have hzval : fD z = (if z.1 ∈ closure C then r z.1 else z.1) := by
      rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
    rw [hzval]
    by_cases hzC : z.1 ∈ closure C
    · rw [if_pos hzC]
      intro heq
      have : c0 ∈ Set.range ⇑r := ⟨z.1, heq⟩
      exact hc0not (hrrange this)
    · rw [if_neg hzC]
      intro heq
      exact hzC (heq ▸ subset_closure hc0)
  have hinD : ∀ z : D, fD z ∈ D := by
    intro z
    have hzval : fD z = (if z.1 ∈ closure C then r z.1 else z.1) := by
      rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
    rw [hzval]
    by_cases hzC : z.1 ∈ closure C
    · rw [if_pos hzC]
      exact hβ_ball (hrrange ⟨z.1, rfl⟩)
    · rw [if_neg hzC]
      exact z.2
  have hnormne : ∀ z : D, ‖fD z - c0‖ ≠ 0 := fun z =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hneD z))
  set w : D → ℂ := fun z => c0 + (R / ‖fD z - c0‖) • (fD z - c0) with hwdef
  have hwcont : Continuous w := by
    have hnorm : Continuous fun z : D => ‖fD z - c0‖ := (fD.continuous.sub continuous_const).norm
    exact continuous_const.add ((continuous_const.div hnorm hnormne).smul
      (fD.continuous.sub continuous_const))
  have hw_sphere : ∀ z : D, ‖w z - c0‖ = R := by
    intro z
    have heq : w z - c0 = (R / ‖fD z - c0‖) • (fD z - c0) := by rw [hwdef]; ring
    rw [heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hRpos.le (norm_nonneg _))]
    rw [div_mul_cancel₀ _ (hnormne z)]
  have hGmem : ∀ z : D, (2 * c0 - w z) ∈ D := fun z => by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h2 : (2 * c0 - w z) - c0 = -(w z - c0) := by ring
    rw [h2, norm_neg, hw_sphere z]
  set G : C(D, D) := ⟨fun z => ⟨2 * c0 - w z, hGmem z⟩,
    Continuous.subtype_mk (continuous_const.sub hwcont) hGmem⟩ with hGdef
  obtain ⟨z, hzfix⟩ := Commons.Topology.Brouwer.brouwer_fixed_point_closedBall c0 hRpos G
  have hz1 : 2 * c0 - w z = z.1 := Subtype.ext_iff.mp hzfix
  have hwz : w z = 2 * c0 - z.1 := by rw [← hz1]; ring
  have hspz : ‖z.1 - c0‖ = R := by
    have := hw_sphere z
    rw [hwz] at this
    rw [show (2 * c0 - z.1) - c0 = -(z.1 - c0) from by ring, norm_neg] at this
    exact this
  have hz1notC : z.1 ∉ closure C := by
    intro hzc
    have h1 := hcl_ball hzc
    rw [Metric.mem_ball, dist_eq_norm, hspz] at h1
    linarith
  have hz_fd : fD z = z.1 := by
    have hzval : fD z = (if z.1 ∈ closure C then r z.1 else z.1) := by
      rw [hfDdef, ContinuousMap.restrict_apply, hfpdef]; rfl
    rw [hzval, if_neg hz1notC]
  have hdir : (R / ‖z.1 - c0‖) • (z.1 - c0) = -(z.1 - c0) := by
    have hwdef' : w z = c0 + (R / ‖fD z - c0‖) • (fD z - c0) := rfl
    have hone : (R / ‖fD z - c0‖) • (fD z - c0) = -(z.1 - c0) := by
      have h1 : c0 + (R / ‖fD z - c0‖) • (fD z - c0) = 2 * c0 - z.1 := by
        rw [← hwdef']; exact hwz
      have h2 : (R / ‖fD z - c0‖) • (fD z - c0) = (2 * c0 - z.1) - c0 := by
        linear_combination h1
      rw [h2]; ring
    rw [hz_fd, hspz, div_self (ne_of_gt hRpos), one_smul] at hone
    rw [hspz, div_self (ne_of_gt hRpos), one_smul]
    exact hone
  exact Commons.Topology.Connected.smul_sub_eq_neg_false hRpos hspz hdir

/-! ## Connectedness of the complement of an arc -/

/-! ## Assembly -/

variable (γ : C(Circle, ℂ))


lemma isOpen_compl_range : IsOpen (Set.range γ)ᶜ :=
  (isCompact_range γ.continuous).isClosed.isOpen_compl

lemma not_isBounded_gt_norm (R : ℝ) : ¬ Bornology.IsBounded {z : ℂ | R < ‖z‖} := by
  intro hb
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp hb
  have hmem : (((|R| + |r| + 1 : ℝ)) : ℂ) ∈ {z : ℂ | R < ‖z‖} := by
    rw [Set.mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ |R| + |r| + 1)]
    linarith [le_abs_self R, abs_nonneg r]
  have h1 := hr hmem
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ |R| + |r| + 1)] at h1
  linarith [le_abs_self r, abs_nonneg R]

lemma joinedIn_of_mem_cc (hγ : Function.Injective γ)
    {c x : ℂ} (hc : c ∈ connectedComponentIn (Set.range γ)ᶜ x) (hx : x ∈ (Set.range γ)ᶜ) :
    JoinedIn (Set.range γ)ᶜ c x := by
  have hF : IsOpen (Set.range γ)ᶜ := isOpen_compl_range γ
  have hcc_open : IsOpen (connectedComponentIn (Set.range γ)ᶜ x) := hF.connectedComponentIn
  have hpath : IsPathConnected (connectedComponentIn (Set.range γ)ᶜ x) := by
    refine Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds
      ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩ ?_
    intro w hw
    obtain ⟨r, hr, hwr⟩ := Metric.isOpen_iff.mp hcc_open w hw
    exact ⟨Metric.ball w r, Metric.isOpen_ball, mem_ball_self hr, Metric.isPathConnected_ball hr, hwr⟩
  exact (isPathConnected_iff.mp hpath).2 c hc x (mem_connectedComponentIn hx) |>.mono
    (connectedComponentIn_subset _ _)


lemma exists_subset_closedBall : ∃ R : ℝ, Set.range γ ⊆ Metric.closedBall 0 R := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp
    (isCompact_range γ.continuous).isBounded
  exact ⟨R, hR⟩

lemma exists_mem_compl_gt (M : ℝ) : ∃ x ∈ (Set.range γ)ᶜ, M < ‖x - 0‖ := by
  obtain ⟨R, hR⟩ := exists_subset_closedBall γ
  refine ⟨((( |M| + |R| + 1 : ℝ)) : ℂ), ?_, ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
    intro t ht
    have h1 : ‖γ t‖ ≤ R := by
      have := hR ⟨t, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    have h2 : ‖(((|M| + |R| + 1 : ℝ)) : ℂ)‖ = |M| + |R| + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ |M| + |R| + 1)]
    rw [ht, h2] at h1
    linarith [le_abs_self R, abs_nonneg M]
  · rw [sub_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ |M| + |R| + 1)]
    linarith [le_abs_self M, abs_nonneg R]

lemma cc_eq_of_unbounded (hγ : Function.Injective γ)
    {a b : ℂ} (ha : a ∈ (Set.range γ)ᶜ) (hb : b ∈ (Set.range γ)ᶜ)
    (hna : ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ a))
    (hnb : ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ b)) :
    connectedComponentIn (Set.range γ)ᶜ a = connectedComponentIn (Set.range γ)ᶜ b := by
  obtain ⟨R, hR⟩ := exists_subset_closedBall γ
  have hsub : {z : ℂ | R < ‖z - 0‖} ⊆ (Set.range γ)ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
    intro t ht
    have h1 : ‖γ t‖ ≤ R := by
      have := hR ⟨t, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    rw [ht] at h1
    have h2 : R < ‖z‖ := by simpa [sub_zero] using hz
    linarith
  have hpre : IsPreconnected {z : ℂ | R < ‖z - 0‖} :=
    Commons.Topology.Connected.isPreconnected_compl_closedBall 0 R
  have hmem : ∀ {c : ℂ}, c ∈ (Set.range γ)ᶜ →
      ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ c) →
      {z : ℂ | R < ‖z - 0‖} ⊆ connectedComponentIn (Set.range γ)ᶜ c := by
    intro c hc hnc
    have hex : ∃ p ∈ connectedComponentIn (Set.range γ)ᶜ c, R < ‖p - 0‖ := by
      by_contra h
      push Not at h
      apply hnc
      rw [Metric.isBounded_iff_subset_closedBall (0:ℂ)]
      exact ⟨R, fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right]
        simpa using h z hz⟩
    obtain ⟨p, hp, hpn⟩ := hex
    have h1 : {z : ℂ | R < ‖z - 0‖} ⊆ connectedComponentIn (Set.range γ)ᶜ p :=
      hpre.subset_connectedComponentIn (by simpa [sub_zero] using hpn) hsub
    have h2 : connectedComponentIn (Set.range γ)ᶜ p = connectedComponentIn (Set.range γ)ᶜ c :=
      (connectedComponentIn_eq hp).symm
    rwa [h2] at h1
  obtain ⟨q, hq : R < ‖q - 0‖⟩ : ∃ q : ℂ, R < ‖q - 0‖ :=
    ⟨((|R| + 1 : ℝ) : ℂ), by
      rw [sub_zero, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ |R| + 1)]
      linarith [le_abs_self R]⟩
  exact (connectedComponentIn_eq (hmem ha hna hq)).trans
    (connectedComponentIn_eq (hmem hb hnb hq)).symm

/-- Assembly: the "at most one bounded component" statement plus disconnectedness of the
complement yield the two-point conclusion. -/
lemma assembly (hγ : Function.Injective γ)
    (hpre : ¬ IsPreconnected (Set.range γ)ᶜ)
    (hCrux : ∀ x ∈ (Set.range γ)ᶜ, ∀ y ∈ (Set.range γ)ᶜ,
      Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ x) →
      Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ y) →
      connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ y) :
    ∃ x ∈ (Set.range γ)ᶜ, ∃ y ∈ (Set.range γ)ᶜ,
      ∀ z ∈ (Set.range γ)ᶜ, JoinedIn (Set.range γ)ᶜ z x ∨ JoinedIn (Set.range γ)ᶜ z y := by
  obtain ⟨R, hR⟩ := exists_subset_closedBall γ
  have hsub : {z : ℂ | R < ‖z - 0‖} ⊆ (Set.range γ)ᶜ := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
    intro t ht
    have h1 : ‖γ t‖ ≤ R := by
      have := hR ⟨t, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    rw [ht] at h1
    have h2 : R < ‖z‖ := by simpa [sub_zero] using hz
    linarith
  have hpre' : IsPreconnected {z : ℂ | R < ‖z - 0‖} :=
    Commons.Topology.Connected.isPreconnected_compl_closedBall 0 R
  obtain ⟨x, hx, hxn⟩ := exists_mem_compl_gt γ R
  have hxR : R < ‖x - 0‖ := hxn
  have hxcc : {z : ℂ | R < ‖z - 0‖} ⊆ connectedComponentIn (Set.range γ)ᶜ x :=
    hpre'.subset_connectedComponentIn hxR hsub
  have hxunb : ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ x) := fun hb =>
    not_isBounded_gt_norm R (hb.subset (fun z hz => hxcc (by simpa using hz)))
  have hy_exists : ∃ y ∈ (Set.range γ)ᶜ, y ∉ connectedComponentIn (Set.range γ)ᶜ x := by
    by_contra h
    push Not at h
    apply hpre
    rw [show (Set.range γ)ᶜ = connectedComponentIn (Set.range γ)ᶜ x from
      Set.Subset.antisymm (fun z hz => h z hz) (connectedComponentIn_subset _ _)]
    exact isPreconnected_connectedComponentIn
  obtain ⟨y, hy, hyx⟩ := hy_exists
  have hybdd : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ y) := by
    by_contra hc
    exact hyx ((cc_eq_of_unbounded γ hγ hx hy hxunb hc).symm ▸ mem_connectedComponentIn hy)
  refine ⟨x, hx, y, hy, ?_⟩
  intro z hz
  by_cases hzbd : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)
  · right
    have heq := hCrux z hz y hy hzbd hybdd
    exact joinedIn_of_mem_cc γ hγ (heq ▸ mem_connectedComponentIn hz) hy
  · left
    have heq := cc_eq_of_unbounded γ hγ hz hx hzbd hxunb
    exact joinedIn_of_mem_cc γ hγ (heq ▸ mem_connectedComponentIn hz) hx

/-! ## The requested lemma -/

/-- In the normalized setting for a Jordan curve `γ` whose complement is disconnected, the
complement has at most two connected components: every point of the complement can be joined,
inside the complement, to one of two fixed points. -/
theorem at_most_two_components (γ : C(Circle, ℂ)) (hγ : Function.Injective γ)
    (hE : ∀ t : Circle, (γ t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (γ t).im ∈ Set.Icc (-2:ℝ) 2)
    (hbd : ∀ t : Circle, (γ t).re = 1 ∨ (γ t).re = -1 ∨ (γ t).im = 2 ∨ (γ t).im = -2 →
      γ t = 1 ∨ γ t = -1)
    (h1 : (1:ℂ) ∈ Set.range γ) (hm1 : (-1:ℂ) ∈ Set.range γ)
    (hpre : ¬ IsPreconnected (Set.range γ)ᶜ) :
    ∃ x ∈ (Set.range γ)ᶜ, ∃ y ∈ (Set.range γ)ᶜ,
      ∀ z ∈ (Set.range γ)ᶜ, JoinedIn (Set.range γ)ᶜ z x ∨ JoinedIn (Set.range γ)ᶜ z y :=
  assembly γ hγ hpre fun x hx y hy hb1 hb2 =>
    Commons.Topology.Jordan.at_most_one_bounded_component γ hγ hx hy hb1 hb2

end Commons.Topology.Jordan
