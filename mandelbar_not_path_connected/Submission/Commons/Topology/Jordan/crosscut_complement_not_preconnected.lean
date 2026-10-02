import Mathlib
import Submission.Commons.Topology.Jordan.plane_separation
import Submission.Commons.Topology.Connected.frontier_component_compl_range
import Submission.Commons.Topology.Jordan.exists_injective_circle_map_of_two_arcs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Commons.Topology.Jordan

noncomputable section

/-- The parametrisation `u ↦ c + r * u` of the sphere of radius `r` about `c`. -/
private def sph (c : ℂ) (r : ℝ) : C(Circle, ℂ) := ⟨fun u => c + r * (u : ℂ), by fun_prop⟩

private lemma sph_apply (c : ℂ) (r : ℝ) (u : Circle) : sph c r u = c + r * (u : ℂ) := rfl

private lemma sph_mem_sphere (c : ℂ) (r : ℝ) (hr : 0 < r) (u : Circle) :
    sph c r u ∈ Metric.sphere c r := by
  rw [Metric.mem_sphere, dist_eq_norm, sph_apply, add_sub_cancel_left, norm_mul,
    Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

private lemma sph_range (c : ℂ) (r : ℝ) (hr : 0 < r) :
    Set.range (sph c r) = Metric.sphere c r := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, rfl⟩; exact sph_mem_sphere c r hr u
  · intro z hz
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    refine ⟨⟨(z - c) / (r : ℂ), ?_⟩, ?_⟩
    · refine mem_sphere_zero_iff_norm.mpr ?_
      rw [norm_div, Complex.norm_real, hz, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
    · show c + r * ((z - c) / (r : ℂ)) = z
      rw [← mul_div_assoc, mul_div_cancel_left₀ (z - c) hr0]; ring

private lemma sph_injective (c : ℂ) (r : ℝ) (hr : 0 < r) : Function.Injective (sph c r) := by
  intro u v huv
  rw [sph_apply, sph_apply] at huv
  have h : ((u:ℂ)) = (v:ℂ) := by
    have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact mul_left_cancel₀ hr0 (by simpa using huv)
  exact Subtype.ext h

/-- The boundary arc of the sphere joining `sph c r u` to `sph c r v`. -/
private def bdryArc (c : ℂ) (r : ℝ) (u v : Circle) : C(Set.Icc (0:ℝ) 1, ℂ) :=
  ⟨fun t => sph c r (Circle.path u v t), (sph c r).continuous.comp (Circle.path u v).continuous⟩

private lemma bdryArc_zero (c : ℂ) (r : ℝ) (u v : Circle) :
    bdryArc c r u v 0 = sph c r u := by
  show sph c r (Circle.path u v 0) = sph c r u
  rw [(Circle.path u v).source]

private lemma bdryArc_one (c : ℂ) (r : ℝ) (u v : Circle) :
    bdryArc c r u v 1 = sph c r v := by
  show sph c r (Circle.path u v 1) = sph c r v
  rw [(Circle.path u v).target]

private lemma bdryArc_inj (c : ℂ) (r : ℝ) (hr : 0 < r) {u v : Circle} (huv : u ≠ v) :
    Function.Injective (bdryArc c r u v) := by
  intro a b hab
  exact Circle.path_injective_of_ne huv (sph_injective c r hr hab)

private lemma bdryArc_mem_sphere (c : ℂ) (r : ℝ) (hr : 0 < r) (u v : Circle)
    (t : Set.Icc (0:ℝ) 1) : bdryArc c r u v t ∈ Metric.sphere c r :=
  sph_mem_sphere c r hr _


/-- A crosscut of a disc separates it: if `β` is an injective arc with endpoints on the sphere of a
ball and interior inside the ball, then the ball with the arc removed is not connected. -/
theorem crosscut_complement_not_preconnected (c : ℂ) {r : ℝ} (hr : 0 < r)
    (β : C(Set.Icc (0:ℝ) 1, ℂ)) (hβ : Function.Injective β)
    (h0 : β 0 ∈ Metric.sphere c r) (h1 : β 1 ∈ Metric.sphere c r)
    (hinterior : ∀ t : Set.Icc (0:ℝ) 1, β t ≠ β 0 → β t ≠ β 1 → β t ∈ Metric.ball c r) :
    ¬ IsPreconnected (Metric.ball c r \ Set.range β) := by
  classical
  -- the two endpoints are distinct
  have hne : β 0 ≠ β 1 := by
    intro h
    have h01 : (0 : Set.Icc (0:ℝ) 1) = 1 := hβ h
    exact absurd (congrArg Subtype.val h01) (by norm_num)
  -- a point of the arc lying on the sphere must be an endpoint
  have hinS : ∀ t : Set.Icc (0:ℝ) 1, β t ∈ Metric.sphere c r → β t = β 0 ∨ β t = β 1 := by
    intro t ht
    by_cases h0t : t = 0
    · exact Or.inl (by rw [h0t])
    · by_cases h1t : t = 1
      · exact Or.inr (by rw [h1t])
      · exfalso
        have hb := hinterior t (fun hh => h0t (hβ hh)) (fun hh => h1t (hβ hh))
        rw [Metric.mem_sphere, dist_eq_norm] at ht
        rw [Metric.mem_ball, dist_eq_norm] at hb
        linarith
  -- parametrise the endpoints on the sphere
  obtain ⟨u, hu⟩ : ∃ u : Circle, sph c r u = β 0 := by
    have : β 0 ∈ Set.range (sph c r) := by rw [sph_range c r hr]; exact h0
    exact this
  obtain ⟨v, hv⟩ : ∃ v : Circle, sph c r v = β 1 := by
    have : β 1 ∈ Set.range (sph c r) := by rw [sph_range c r hr]; exact h1
    exact this
  have huv : u ≠ v := by intro h; exact hne (by rw [← hu, ← hv, h])
  -- the closing boundary arc
  have hQinj : Function.Injective (bdryArc c r u v) := bdryArc_inj c r hr huv
  have hdisj : ∀ s t : Set.Icc (0:ℝ) 1, β s = bdryArc c r u v t → s = 0 ∨ s = 1 := by
    intro s t hst
    have hsp : β s ∈ Metric.sphere c r := by
      rw [hst]; exact bdryArc_mem_sphere c r hr u v t
    rcases hinS s hsp with hh | hh
    · exact Or.inl (hβ hh)
    · exact Or.inr (hβ hh)
  obtain ⟨γ, hγinj, hγrange⟩ :=
    exists_injective_circle_map_of_two_arcs β (bdryArc c r u v) hβ hQinj
      ((bdryArc_zero c r u v).trans hu).symm
      ((bdryArc_one c r u v).trans hv).symm hne hdisj
  -- the boundary arc lies on the sphere, hence outside the ball
  have hQsphere : Set.range (bdryArc c r u v) ⊆ Metric.sphere c r := by
    rintro _ ⟨t, rfl⟩; exact bdryArc_mem_sphere c r hr u v t
  have hball_sphere : Disjoint (Metric.ball c r) (Metric.sphere c r) := by
    rw [Set.disjoint_left]
    intro z hzb hzs
    rw [Metric.mem_ball, dist_eq_norm] at hzb
    rw [Metric.mem_sphere, dist_eq_norm] at hzs
    linarith
  -- the part of the Jordan curve inside the ball is exactly the crosscut
  have hInterEq : Set.range γ ∩ Metric.ball c r = Set.range β ∩ Metric.ball c r := by
    rw [hγrange]
    ext z
    constructor
    · rintro ⟨hz | hz, hzb⟩
      · exact ⟨hz, hzb⟩
      · exact absurd (hQsphere hz) (Set.disjoint_left.mp hball_sphere hzb)
    · rintro ⟨hz, hzb⟩
      exact ⟨Or.inl hz, hzb⟩
  have hDiff : Metric.ball c r \ Set.range γ = Metric.ball c r \ Set.range β := by
    have h1 : Metric.ball c r \ Set.range γ
        = Metric.ball c r \ (Set.range γ ∩ Metric.ball c r) := by
      ext z; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
    have h2 : Metric.ball c r \ Set.range β
        = Metric.ball c r \ (Set.range β ∩ Metric.ball c r) := by
      ext z; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
    rw [h1, h2, hInterEq]
  -- Jordan separation for γ
  obtain ⟨U, V, hUo, hVo, hUc, hVc, hUVdisj, _hUb, _hVb, hUVeq⟩ :=
    Commons.Topology.Jordan.plane_separation γ hγinj
  have hUsub : U ⊆ (Set.range γ)ᶜ := by rw [← hUVeq]; exact Set.subset_union_left
  have hVsub : V ⊆ (Set.range γ)ᶜ := by rw [← hUVeq]; exact Set.subset_union_right
  -- the complement of γ is not preconnected
  have hnotpre : ¬ IsPreconnected (Set.range γ)ᶜ := by
    intro hpre
    rcases hpre.subset_or_subset hUo hVo hUVdisj (le_of_eq hUVeq.symm) with h1 | h2
    · obtain ⟨y, hy⟩ := hVc.nonempty
      exact (Set.disjoint_left.mp hUVdisj) (h1 (hVsub hy)) hy
    · obtain ⟨y, hy⟩ := hUc.nonempty
      exact (Set.disjoint_left.mp hUVdisj) hy (h2 (hUsub hy))
  -- identify `U` and `V` with connected components and compute their frontiers
  obtain ⟨xU, hxU⟩ := hUc.nonempty
  obtain ⟨xV, hxV⟩ := hVc.nonempty
  have hxUγ : xU ∈ (Set.range γ)ᶜ := hUsub hxU
  have hxVγ : xV ∈ (Set.range γ)ᶜ := hVsub hxV
  have hcompU : connectedComponentIn (Set.range γ)ᶜ xU = U := by
    refine Set.Subset.antisymm ?_ ?_
    · rcases (isPreconnected_connectedComponentIn (F := (Set.range γ)ᶜ) (x := xU)).subset_or_subset
        hUo hVo hUVdisj (by rw [← hUVeq]; exact connectedComponentIn_subset _ _) with hsub | hsub
      · exact hsub
      · exact absurd (hsub (mem_connectedComponentIn hxUγ))
          ((Set.disjoint_left.mp hUVdisj) hxU)
    · exact hUc.isPreconnected.subset_connectedComponentIn hxU hUsub
  have hcompV : connectedComponentIn (Set.range γ)ᶜ xV = V := by
    refine Set.Subset.antisymm ?_ ?_
    · rcases (isPreconnected_connectedComponentIn (F := (Set.range γ)ᶜ) (x := xV)).subset_or_subset
        hUo hVo hUVdisj (by rw [← hUVeq]; exact connectedComponentIn_subset _ _) with hsub | hsub
      · exact absurd (hsub (mem_connectedComponentIn hxVγ))
          (Set.disjoint_right.mp hUVdisj hxV)
      · exact hsub
    · exact hVc.isPreconnected.subset_connectedComponentIn hxV hVsub
  have hfrontU : frontier U = Set.range γ := by
    have h := Commons.Topology.Connected.frontier_component_compl_range γ hγinj hnotpre xU hxUγ
    rwa [hcompU] at h
  have hfrontV : frontier V = Set.range γ := by
    have h := Commons.Topology.Connected.frontier_component_compl_range γ hγinj hnotpre xV hxVγ
    rwa [hcompV] at h
  -- an interior point of the crosscut, lying in the open ball
  set p : ℂ := β ⟨(1/2 : ℝ), by norm_num⟩ with hpdef
  have hp_ball : p ∈ Metric.ball c r := by
    rw [hpdef]
    refine hinterior ⟨1/2, by norm_num⟩ ?_ ?_
    · intro hh; exact absurd (congrArg Subtype.val (hβ hh)) (by norm_num)
    · intro hh; exact absurd (congrArg Subtype.val (hβ hh)) (by norm_num)
  have hp_γ : p ∈ Set.range γ := by
    rw [hγrange]
    exact Or.inl ⟨⟨1/2, by norm_num⟩, hpdef.symm⟩
  have hp_clU : p ∈ closure U :=
    frontier_subset_closure (by rw [hfrontU]; exact hp_γ)
  have hp_clV : p ∈ closure V :=
    frontier_subset_closure (by rw [hfrontV]; exact hp_γ)
  -- each side of the arc meets the ball
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp Metric.isOpen_ball p hp_ball
  obtain ⟨b1, hb1U, hb1dist⟩ := Metric.mem_closure_iff.mp hp_clU ε hεpos
  obtain ⟨b2, hb2V, hb2dist⟩ := Metric.mem_closure_iff.mp hp_clV ε hεpos
  have hb1S : b1 ∈ Metric.ball c r \ Set.range γ :=
    ⟨hεsub (Metric.mem_ball.mpr (by rw [dist_comm]; exact hb1dist)), hUsub hb1U⟩
  have hb2S : b2 ∈ Metric.ball c r \ Set.range γ :=
    ⟨hεsub (Metric.mem_ball.mpr (by rw [dist_comm]; exact hb2dist)), hVsub hb2V⟩
  have hSneU : ((Metric.ball c r \ Set.range γ) ∩ U).Nonempty := ⟨b1, hb1S, hb1U⟩
  have hSneV : ((Metric.ball c r \ Set.range γ) ∩ V).Nonempty := ⟨b2, hb2S, hb2V⟩
  intro hpre
  have hSU_V : Metric.ball c r \ Set.range β ⊆ U ∪ V := by
    rw [← hDiff, hUVeq]
    intro z hz; exact hz.2
  have hinter_empty : (Metric.ball c r \ Set.range β) ∩ (U ∩ V) = ∅ := by
    rw [Set.disjoint_iff_inter_eq_empty.mp hUVdisj, Set.inter_empty]
  rcases (isPreconnected_iff_subset_of_disjoint.mp hpre) U V hUo hVo hSU_V hinter_empty
    with h1 | h2
  · obtain ⟨b, hbS, hbV⟩ := hSneV
    exact (Set.disjoint_left.mp hUVdisj) (h1 (by rw [← hDiff]; exact hbS)) hbV
  · obtain ⟨b, hbS, hbU⟩ := hSneU
    exact (Set.disjoint_left.mp hUVdisj) hbU (h2 (by rw [← hDiff]; exact hbS))

end

end Commons.Topology.Jordan
