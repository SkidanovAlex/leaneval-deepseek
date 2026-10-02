import Mathlib
import Submission.Commons.Topology.Jordan.normalized_no_two_bounded_components
import Submission.Commons.Topology.Metric.isBounded_image_similarity
import Submission.Commons.Topology.Connected.isPreconnected_compl_closedBall

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Commons.Topology.Jordan

open Set Metric
open scoped Topology

noncomputable section

/-! ### Normalization and transfer lemmas for a Jordan curve

Kept in a topic sub-namespace so the names do not clash with the identical lemmas
used by other commons modules. -/

namespace AMOBC

/-! ## Normalization of a Jordan curve -/

lemma exists_max_dist (γ : C(Circle, ℂ)) :
    ∃ s t : Circle, ∀ x y : Circle, ‖γ x - γ y‖ ≤ ‖γ s - γ t‖ := by
  have hcont : Continuous fun p : Circle × Circle => ‖γ p.1 - γ p.2‖ := by fun_prop
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn
    (⟨(1, 1), mem_univ _⟩ : (Set.univ : Set (Circle × Circle)).Nonempty) hcont.continuousOn
  exact ⟨p.1, p.2, fun x y => hp (mem_univ (x, y))⟩

noncomputable def sim (d c z : ℂ) : ℂ := (2 / d) * (z - c)
noncomputable def invSim (d c w : ℂ) : ℂ := (d / 2) * w + c

lemma sim_invSim {d c : ℂ} (hd : d ≠ 0) (w : ℂ) : sim d c (invSim d c w) = w := by
  unfold sim invSim; field_simp; ring

lemma invSim_sim {d c : ℂ} (hd : d ≠ 0) (z : ℂ) : invSim d c (sim d c z) = z := by
  unfold sim invSim; field_simp; ring

lemma sim_injective {d c : ℂ} (hd : d ≠ 0) : Function.Injective (sim d c) := by
  intro z w hzw
  have h := congrArg (invSim d c) hzw
  rw [invSim_sim hd z, invSim_sim hd w] at h
  exact h

lemma sim_surjective {d c : ℂ} (hd : d ≠ 0) : Function.Surjective (sim d c) :=
  fun w => ⟨invSim d c w, sim_invSim hd w⟩

lemma continuous_sim (d c : ℂ) : Continuous (sim d c) := by unfold sim; fun_prop
lemma continuous_invSim (d c : ℂ) : Continuous (invSim d c) := by unfold invSim; fun_prop

lemma sim_add {d c : ℂ} (hd : d ≠ 0) (z w : ℂ) :
    sim d c z - sim d c w = (2 / d) * (z - w) := by unfold sim; ring

lemma norm_sim_sub {d c : ℂ} (hd : d ≠ 0) (z w : ℂ) :
    ‖sim d c z - sim d c w‖ = 2 / ‖d‖ * ‖z - w‖ := by
  rw [sim_add hd, norm_mul, norm_div, Complex.norm_ofNat]

noncomputable def normalizedCurve (γ : C(Circle, ℂ)) (s t : Circle) : C(Circle, ℂ) :=
  ⟨fun z => sim (γ t - γ s) ((γ s + γ t) / 2) (γ z), by unfold sim; fun_prop⟩

@[simp] lemma normalizedCurve_apply (γ : C(Circle, ℂ)) (s t z : Circle) :
    normalizedCurve γ s t z = sim (γ t - γ s) ((γ s + γ t) / 2) (γ z) := rfl

lemma normalizedCurve_apply_s {γ : C(Circle, ℂ)} {s t : Circle} (hd : γ t ≠ γ s) :
    normalizedCurve γ s t s = -1 := by
  simp only [normalizedCurve_apply]
  have hne : γ t - γ s ≠ 0 := sub_ne_zero.mpr hd
  unfold sim; field_simp; ring

lemma normalizedCurve_apply_t {γ : C(Circle, ℂ)} {s t : Circle} (hd : γ t ≠ γ s) :
    normalizedCurve γ s t t = 1 := by
  simp only [normalizedCurve_apply]
  have hne : γ t - γ s ≠ 0 := sub_ne_zero.mpr hd
  unfold sim; field_simp; ring

lemma normalizedCurve_injective {γ : C(Circle, ℂ)} (hγ : Function.Injective γ)
    {s t : Circle} (hd : γ t ≠ γ s) : Function.Injective (normalizedCurve γ s t) := by
  intro x y hxy
  have hne : γ t - γ s ≠ 0 := sub_ne_zero.mpr hd
  have h1 : sim (γ t - γ s) ((γ s + γ t) / 2) (γ x)
      = sim (γ t - γ s) ((γ s + γ t) / 2) (γ y) := hxy
  exact hγ (sim_injective hne h1)

lemma normalizedCurve_diam {γ : C(Circle, ℂ)} {s t : Circle} (hd : γ t ≠ γ s)
    (hdiam : ∀ x y : Circle, ‖γ x - γ y‖ ≤ ‖γ s - γ t‖) (x y : Circle) :
    ‖normalizedCurve γ s t x - normalizedCurve γ s t y‖ ≤ 2 := by
  have hne : γ t - γ s ≠ 0 := sub_ne_zero.mpr hd
  rw [normalizedCurve_apply, normalizedCurve_apply, norm_sim_sub hne]
  have hnorm : ‖γ t - γ s‖ = ‖γ s - γ t‖ := by rw [norm_sub_rev]
  rw [hnorm]
  have hpos : 0 < ‖γ s - γ t‖ := by rw [← hnorm]; exact norm_pos_iff.mpr hne
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  have := hdiam x y
  linarith

/-- The normalized curve lies in the rectangle `[-1,1] × [-2,2]`. -/
lemma range_subset_Erect_set (γ : C(Circle, ℂ))
    (hdiam : ∀ x y : Circle, ‖γ x - γ y‖ ≤ 2)
    (hneg : ∃ u : Circle, γ u = -1) (hpos : ∃ u : Circle, γ u = 1) :
    ∀ t : Circle, (γ t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (γ t).im ∈ Set.Icc (-2:ℝ) 2 := by
  intro t
  obtain ⟨u, hu⟩ := hneg
  obtain ⟨v, hv⟩ := hpos
  have hA : ‖γ t + 1‖ ≤ 2 := by
    have h := hdiam t u; rw [hu] at h; simpa using h
  have hB : ‖γ t - 1‖ ≤ 2 := by
    have h := hdiam t v; rwa [hv] at h
  have hAre : |(γ t + 1).re| ≤ 2 := le_trans (Complex.abs_re_le_norm _) hA
  have hBre : |(γ t - 1).re| ≤ 2 := le_trans (Complex.abs_re_le_norm _) hB
  have hAim : |(γ t + 1).im| ≤ 2 := le_trans (Complex.abs_im_le_norm _) hA
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    sub_zero] at hAre hBre hAim
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linarith [(abs_le.mp hBre).1]
  · linarith [(abs_le.mp hAre).2]
  · linarith [(abs_le.mp hAim).1]
  · linarith [(abs_le.mp hAim).2]

/-- In the normalized setting, the curve meets the boundary of the rectangle only in `±1`. -/
lemma eq_pm_one_of_boundary (γ : C(Circle, ℂ))
    (hdiam : ∀ x y : Circle, ‖γ x - γ y‖ ≤ 2)
    (hneg : ∃ u : Circle, γ u = -1) (hpos : ∃ u : Circle, γ u = 1)
    {t : Circle}
    (hb : (γ t).re = 1 ∨ (γ t).re = -1 ∨ (γ t).im = 2 ∨ (γ t).im = -2) :
    γ t = 1 ∨ γ t = -1 := by
  obtain ⟨u, hu⟩ := hneg
  obtain ⟨v, hv⟩ := hpos
  have hA : ‖γ t + 1‖ ≤ 2 := by
    have h := hdiam t u; rw [hu] at h; simpa using h
  have hB : ‖γ t - 1‖ ≤ 2 := by
    have h := hdiam t v; rwa [hv] at h
  have hA2 : ‖γ t + 1‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (γ t + 1)]
  have hB2 : ‖γ t - 1‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (γ t - 1)]
  have hAsq : ‖γ t + 1‖ ^ 2 = ((γ t).re + 1) ^ 2 + (γ t).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have hBsq : ‖γ t - 1‖ ^ 2 = ((γ t).re - 1) ^ 2 + (γ t).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [hAsq] at hA2
  rw [hBsq] at hB2
  rcases hb with hb | hb | hb | hb
  · left
    have him : (γ t).im = 0 := by nlinarith [sq_nonneg (γ t).im]
    apply Complex.ext
    · simpa using hb
    · simpa using him
  · right
    have him : (γ t).im = 0 := by nlinarith [sq_nonneg (γ t).im]
    apply Complex.ext
    · simpa using hb
    · simpa using him
  · exfalso
    rw [hb] at hA2 hB2
    have hre : (γ t).re = -1 := by nlinarith [sq_nonneg ((γ t).re + 1)]
    nlinarith [sq_nonneg ((γ t).re - 1)]
  · exfalso
    rw [hb] at hA2 hB2
    have hre : (γ t).re = -1 := by nlinarith [sq_nonneg ((γ t).re + 1)]
    nlinarith [sq_nonneg ((γ t).re - 1)]

/-- Image of a connected component under a bijection (with explicit inverse). -/
lemma image_connectedComponentIn_of_inv {f g : ℂ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ z, g (f z) = z) (hgf : ∀ w, f (g w) = w) (A : Set ℂ) (x : ℂ) :
    f '' connectedComponentIn A x = connectedComponentIn (f '' A) (f x) := by
  have hfinj : Function.Injective f := fun a b h => by rw [← hfg a, ← hfg b, h]
  by_cases hx : x ∈ A
  · apply Subset.antisymm
    · exact hf.continuousOn.image_connectedComponentIn_subset hx
    · intro z hz
      have hfx : f x ∈ f '' A := ⟨x, hx, rfl⟩
      have h2 : g '' connectedComponentIn (f '' A) (f x) ⊆
          connectedComponentIn (g '' (f '' A)) (g (f x)) :=
        hg.continuousOn.image_connectedComponentIn_subset hfx
      have h3 : g '' (f '' A) = A := by
        rw [← Set.image_comp]
        have : g ∘ f = id := funext hfg
        rw [this, Set.image_id]
      rw [h3, hfg x] at h2
      have hgz : g z ∈ connectedComponentIn A x := h2 ⟨z, hz, rfl⟩
      exact ⟨g z, hgz, hgf z⟩
  · rw [connectedComponentIn_eq_empty hx, Set.image_empty]
    have hfx : f x ∉ f '' A := fun h => by obtain ⟨w, hw, hwz⟩ := h; exact hx (by rwa [hfinj hwz] at hw)
    rw [connectedComponentIn_eq_empty hfx]

/-- `sim d c` maps `(range γ)ᶜ` onto `(range (normalizedCurve γ s t))ᶜ`. -/
lemma sim_image_compl (γ : C(Circle, ℂ)) (s t : Circle) (hne' : γ t ≠ γ s) :
    sim (γ t - γ s) ((γ s + γ t) / 2) '' (Set.range γ)ᶜ
      = (Set.range (normalizedCurve γ s t))ᶜ := by
  have hne : γ t - γ s ≠ 0 := sub_ne_zero.mpr hne'
  have h1 : sim (γ t - γ s) ((γ s + γ t) / 2) '' Set.range γ
      = Set.range (normalizedCurve γ s t) := by
    ext z; constructor
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, by simp [normalizedCurve_apply]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨γ u, ⟨u, rfl⟩, by simp [normalizedCurve_apply]⟩
  rw [← h1]
  exact Set.image_compl_eq (s := Set.range γ) ⟨sim_injective hne, sim_surjective hne⟩

lemma sim_eq_affine (d c : ℂ) : sim d c = fun z => (2 / d) * z + (-(2 / d) * c) := by
  funext z; unfold sim; ring

lemma isBounded_image_sim_iff {d c : ℂ} (hd : d ≠ 0) (S : Set ℂ) :
    Bornology.IsBounded (sim d c '' S) ↔ Bornology.IsBounded S := by
  rw [sim_eq_affine]
  exact _root_.Commons.Topology.Metric.isBounded_image_similarity (by simp [hd]) S


end AMOBC

open AMOBC

/-! ### At most one bounded component -/

theorem at_most_one_bounded_component (γ : C(Circle, ℂ)) (hγ : Function.Injective γ)
    {x y : ℂ} (hx : x ∈ (Set.range γ)ᶜ) (hy : y ∈ (Set.range γ)ᶜ)
    (hxb : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ x))
    (hyb : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ y)) :
    connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ y := by
  by_cases hpre : IsPreconnected (Set.range γ)ᶜ
  · have hx' : (Set.range γ)ᶜ ⊆ connectedComponentIn (Set.range γ)ᶜ x :=
      hpre.subset_connectedComponentIn hx (subset_refl _)
    have hy' : (Set.range γ)ᶜ ⊆ connectedComponentIn (Set.range γ)ᶜ y :=
      hpre.subset_connectedComponentIn hy (subset_refl _)
    have e1 : connectedComponentIn (Set.range γ)ᶜ x = (Set.range γ)ᶜ :=
      Set.Subset.antisymm (connectedComponentIn_subset _ _) hx'
    have e2 : connectedComponentIn (Set.range γ)ᶜ y = (Set.range γ)ᶜ :=
      Set.Subset.antisymm (connectedComponentIn_subset _ _) hy'
    rw [e1, e2]
  · obtain ⟨s, t, hmax⟩ := exists_max_dist γ
    have hst : s ≠ t := by
      intro hst
      apply hpre
      have hconst : Set.range γ = {γ s} := by
        ext z; constructor
        · rintro ⟨u, rfl⟩
          have h := hmax u s
          rw [← hst, sub_self, norm_zero] at h
          have h2 : γ u = γ s := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
          rw [h2]; rfl
        · rintro ⟨rfl⟩; exact ⟨s, rfl⟩
      rw [hconst]
      have hset : ({γ s} : Set ℂ)ᶜ = {z : ℂ | (0:ℝ) < ‖z - γ s‖} := by
        ext z
        rw [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_setOf_eq, norm_pos_iff, sub_ne_zero]
      rw [hset]
      exact Commons.Topology.Connected.isPreconnected_compl_closedBall (γ s) 0
    have hd : γ t ≠ γ s := fun h => hst (hγ h).symm
    have hdne : γ t - γ s ≠ 0 := sub_ne_zero.mpr hd
    have hγ'inj : Function.Injective (normalizedCurve γ s t) := normalizedCurve_injective hγ hd
    have hdiam : ∀ a b : Circle, ‖normalizedCurve γ s t a - normalizedCurve γ s t b‖ ≤ 2 :=
      normalizedCurve_diam hd hmax
    have hneg : ∃ u : Circle, normalizedCurve γ s t u = -1 := ⟨s, normalizedCurve_apply_s hd⟩
    have hpos : ∃ u : Circle, normalizedCurve γ s t u = 1 := ⟨t, normalizedCurve_apply_t hd⟩
    have hE : ∀ u : Circle, (normalizedCurve γ s t u).re ∈ Set.Icc (-1:ℝ) 1 ∧
        (normalizedCurve γ s t u).im ∈ Set.Icc (-2:ℝ) 2 :=
      range_subset_Erect_set _ hdiam hneg hpos
    have hbd : ∀ u : Circle, (normalizedCurve γ s t u).re = 1 ∨
        (normalizedCurve γ s t u).re = -1 ∨ (normalizedCurve γ s t u).im = 2 ∨
        (normalizedCurve γ s t u).im = -2 →
        normalizedCurve γ s t u = 1 ∨ normalizedCurve γ s t u = -1 := fun u hb =>
      eq_pm_one_of_boundary _ hdiam hneg hpos hb
    have h1' : (1:ℂ) ∈ Set.range (normalizedCurve γ s t) := ⟨t, normalizedCurve_apply_t hd⟩
    have hm1' : (-1:ℂ) ∈ Set.range (normalizedCurve γ s t) := ⟨s, normalizedCurve_apply_s hd⟩
    have hsimx : sim (γ t - γ s) ((γ s + γ t) / 2) x ∈ (Set.range (normalizedCurve γ s t))ᶜ := by
      rw [← sim_image_compl γ s t hd]; exact ⟨x, hx, rfl⟩
    have hsimy : sim (γ t - γ s) ((γ s + γ t) / 2) y ∈ (Set.range (normalizedCurve γ s t))ᶜ := by
      rw [← sim_image_compl γ s t hd]; exact ⟨y, hy, rfl⟩
    have hccx : connectedComponentIn (Set.range (normalizedCurve γ s t))ᶜ
          (sim (γ t - γ s) ((γ s + γ t) / 2) x)
        = sim (γ t - γ s) ((γ s + γ t) / 2) '' connectedComponentIn (Set.range γ)ᶜ x := by
      rw [← sim_image_compl γ s t hd]
      exact (image_connectedComponentIn_of_inv
        (f := sim (γ t - γ s) ((γ s + γ t) / 2))
        (g := invSim (γ t - γ s) ((γ s + γ t) / 2))
        (continuous_sim _ _) (continuous_invSim _ _)
        (fun z => invSim_sim hdne z) (fun w => sim_invSim hdne w) (Set.range γ)ᶜ x).symm
    have hccy : connectedComponentIn (Set.range (normalizedCurve γ s t))ᶜ
          (sim (γ t - γ s) ((γ s + γ t) / 2) y)
        = sim (γ t - γ s) ((γ s + γ t) / 2) '' connectedComponentIn (Set.range γ)ᶜ y := by
      rw [← sim_image_compl γ s t hd]
      exact (image_connectedComponentIn_of_inv
        (f := sim (γ t - γ s) ((γ s + γ t) / 2))
        (g := invSim (γ t - γ s) ((γ s + γ t) / 2))
        (continuous_sim _ _) (continuous_invSim _ _)
        (fun z => invSim_sim hdne z) (fun w => sim_invSim hdne w) (Set.range γ)ᶜ y).symm
    have hxb' : Bornology.IsBounded (connectedComponentIn (Set.range (normalizedCurve γ s t))ᶜ
        (sim (γ t - γ s) ((γ s + γ t) / 2) x)) := by
      rw [hccx]; exact (isBounded_image_sim_iff hdne _).mpr hxb
    have hyb' : Bornology.IsBounded (connectedComponentIn (Set.range (normalizedCurve γ s t))ᶜ
        (sim (γ t - γ s) ((γ s + γ t) / 2) y)) := by
      rw [hccy]; exact (isBounded_image_sim_iff hdne _).mpr hyb
    have heq := normalized_no_two_bounded_components (normalizedCurve γ s t) hγ'inj hE hbd h1' hm1'
      (sim (γ t - γ s) ((γ s + γ t) / 2) x) hsimx hxb'
      (sim (γ t - γ s) ((γ s + γ t) / 2) y) hsimy hyb'
    rw [hccx, hccy] at heq
    exact Set.image_injective.mpr (sim_injective hdne) heq


end
end Commons.Topology.Jordan
