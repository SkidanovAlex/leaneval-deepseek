import Mathlib
import Submission.Commons.Topology.Jordan.crossing_lemma_rect
import Submission.Commons.Topology.Jordan.bounded_component_exists
import Submission.Commons.Topology.Jordan.at_most_two_components

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Set Metric Filter
open scoped Topology

namespace Commons.Topology.Jordan

/-! ## The crossing lemma

The crossing lemma (Maehara's Lemma 2, the plane form of the two-dimensional Brouwer fixed
point theorem) is available in the shared commons as
`Commons.Topology.Jordan.crossing_lemma_rect`. -/

/-! ## Normalization of a Jordan curve -/

/-- The diameter of the image of `γ : C(Circle, ℂ)` is attained. -/
lemma exists_max_dist (γ : C(Circle, ℂ)) :
    ∃ s t : Circle, ∀ x y : Circle, ‖γ x - γ y‖ ≤ ‖γ s - γ t‖ := by
  have hcont : Continuous fun p : Circle × Circle => ‖γ p.1 - γ p.2‖ := by fun_prop
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn
    (⟨(1, 1), mem_univ _⟩ : (Set.univ : Set (Circle × Circle)).Nonempty) hcont.continuousOn
  exact ⟨p.1, p.2, fun x y => hp (mem_univ (x, y))⟩

/-- The direct similarity `z ↦ (2/d) (z - c)`. -/
noncomputable def sim (d c z : ℂ) : ℂ := (2 / d) * (z - c)

/-- The inverse of `sim d c`. -/
noncomputable def invSim (d c w : ℂ) : ℂ := (d / 2) * w + c

lemma sim_invSim {d c : ℂ} (hd : d ≠ 0) (w : ℂ) : sim d c (invSim d c w) = w := by
  unfold sim invSim
  field_simp
  ring

lemma invSim_sim {d c : ℂ} (hd : d ≠ 0) (z : ℂ) : invSim d c (sim d c z) = z := by
  unfold sim invSim
  field_simp
  ring

lemma sim_injective {d c : ℂ} (hd : d ≠ 0) : Function.Injective (sim d c) := by
  intro z w hzw
  have h := congrArg (invSim d c) hzw
  rw [invSim_sim hd z, invSim_sim hd w] at h
  exact h

lemma sim_add {d c : ℂ} (hd : d ≠ 0) (z w : ℂ) :
    sim d c z - sim d c w = (2 / d) * (z - w) := by
  unfold sim; ring

lemma norm_sim_sub {d c : ℂ} (hd : d ≠ 0) (z w : ℂ) :
    ‖sim d c z - sim d c w‖ = 2 / ‖d‖ * ‖z - w‖ := by
  rw [sim_add hd, norm_mul, norm_div, Complex.norm_ofNat]

/-- The curve normalized so that the diameter points `s`, `t` are sent to `-1` and `1`. -/
noncomputable def normalizedCurve (γ : C(Circle, ℂ)) (s t : Circle) : C(Circle, ℂ) :=
  ⟨fun z => sim (γ t - γ s) ((γ s + γ t) / 2) (γ z), by unfold sim; fun_prop⟩

@[simp] lemma normalizedCurve_apply (γ : C(Circle, ℂ)) (s t z : Circle) :
    normalizedCurve γ s t z = sim (γ t - γ s) ((γ s + γ t) / 2) (γ z) := rfl

lemma normalizedCurve_apply_s {γ : C(Circle, ℂ)} {s t : Circle} (hd : γ t ≠ γ s) :
    normalizedCurve γ s t s = -1 := by
  simp only [normalizedCurve_apply]
  have hne : γ t - γ s ≠ 0 := sub_ne_zero.mpr hd
  unfold sim
  field_simp
  ring

lemma normalizedCurve_apply_t {γ : C(Circle, ℂ)} {s t : Circle} (hd : γ t ≠ γ s) :
    normalizedCurve γ s t t = 1 := by
  simp only [normalizedCurve_apply]
  have hne : γ t - γ s ≠ 0 := sub_ne_zero.mpr hd
  unfold sim
  field_simp
  ring

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
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im]
    at hAre hBre hAim
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


/-! ## Assembly: two halves of the Jordan theorem give the separation statement -/

lemma mem_connectedComponentIn_of_joinedIn {F : Set ℂ} {x z : ℂ} (h : JoinedIn F z x) :
    z ∈ connectedComponentIn F x := by
  have hsub : Set.range h.somePath ⊆ F := by
    rintro _ ⟨t, rfl⟩
    exact h.somePath_mem t
  have hpre : IsPreconnected (Set.range h.somePath) := isPreconnected_range h.somePath.continuous
  have hx : x ∈ Set.range h.somePath := ⟨1, h.somePath.target⟩
  exact hpre.subset_connectedComponentIn hx hsub ⟨0, h.somePath.source⟩

/-- The complement of the range of `γ` is unbounded. -/
lemma compl_range_ge (γ : C(Circle, ℂ)) (R : ℝ) :
    ∃ z ∈ (Set.range γ)ᶜ, R < ‖z‖ := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp
    (isCompact_range γ.continuous).isBounded
  set z : ℂ := ((max R C + 1 : ℝ) : ℂ) with hz
  have hznorm : max R C + 1 ≤ ‖z‖ := by
    rw [hz, Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  have hmaxC : C < max R C + 1 := by have := le_max_right R C; linarith
  have hmaxR : R < max R C + 1 := by have := le_max_left R C; linarith
  refine ⟨z, ?_, by linarith⟩
  simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
  intro t ht
  have h1 : ‖γ t‖ ≤ C := by
    have := hC ⟨t, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  rw [ht] at h1
  linarith

lemma not_isBounded_compl_range (γ : C(Circle, ℂ)) : ¬ Bornology.IsBounded (Set.range γ)ᶜ := by
  intro hb
  obtain ⟨C', hC'⟩ := isBounded_iff_forall_norm_le.mp hb
  obtain ⟨z, hz, hzbig⟩ := compl_range_ge γ C'
  exact absurd (hC' z hz) (not_le.mpr hzbig)

/-- From "there is a bounded component of the complement" and "the complement has at most two
components" the full separation statement follows. -/
theorem separation_of_halves (γ : C(Circle, ℂ))
    (hA : ∃ z ∈ (Set.range γ)ᶜ, Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z))
    (hB : ∃ x ∈ (Set.range γ)ᶜ, ∃ y ∈ (Set.range γ)ᶜ,
      ∀ z ∈ (Set.range γ)ᶜ, JoinedIn (Set.range γ)ᶜ z x ∨ JoinedIn (Set.range γ)ᶜ z y) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ U ∪ V = (Set.range γ)ᶜ := by
  classical
  set K := Set.range γ with hK
  have hKcopen : IsOpen Kᶜ := (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hunb : ¬ Bornology.IsBounded Kᶜ := hK ▸ not_isBounded_compl_range γ
  obtain ⟨z₀, hz₀, hbdd⟩ := hA
  -- the component of z₀ is closed in Kᶜ
  have hcl : Kᶜ ∩ closure (connectedComponentIn Kᶜ z₀) ⊆ connectedComponentIn Kᶜ z₀ := by
    intro w hw
    obtain ⟨hwK, hwcl⟩ := hw
    obtain ⟨u, hu⟩ := _root_.mem_closure_iff.1 hwcl (connectedComponentIn Kᶜ w)
      (hKcopen.connectedComponentIn) (mem_connectedComponentIn hwK)
    obtain ⟨hu1, hu2⟩ := hu
    have h1 : connectedComponentIn Kᶜ z₀ = connectedComponentIn Kᶜ u :=
      connectedComponentIn_eq hu2
    have h2 : connectedComponentIn Kᶜ w = connectedComponentIn Kᶜ u :=
      connectedComponentIn_eq hu1
    rw [h1, ← h2]
    exact mem_connectedComponentIn hwK
  -- hence Kᶜ is not preconnected
  have hpre : ¬ IsPreconnected Kᶜ := by
    intro hcon
    have hsub : Kᶜ ⊆ connectedComponentIn Kᶜ z₀ ∪ (closure (connectedComponentIn Kᶜ z₀))ᶜ := by
      intro w hw
      by_cases hw' : w ∈ connectedComponentIn Kᶜ z₀
      · exact Or.inl hw'
      · refine Or.inr ?_
        simp only [Set.mem_compl_iff]
        intro hwcl
        exact hw' (hcl (Set.mem_inter hw hwcl))
    rcases hcon.subset_or_subset (hKcopen.connectedComponentIn) (isClosed_closure.isOpen_compl)
      ((disjoint_compl_right (a := closure (connectedComponentIn Kᶜ z₀))).mono_left subset_closure)
      hsub with h | h
    · -- Kᶜ is a bounded component, impossible
      have : Kᶜ = connectedComponentIn Kᶜ z₀ :=
        Subset.antisymm h (connectedComponentIn_subset Kᶜ z₀)
      exact hunb (this ▸ hbdd)
    · -- z₀ ∈ Kᶜ but Kᶜ avoids the closure of its component: impossible
      exact (h hz₀) (subset_closure (mem_connectedComponentIn hz₀))
  obtain ⟨x, hx, y, hy, hxy⟩ := hB
  -- every component is the component of x or of y
  have hcover : Kᶜ = connectedComponentIn Kᶜ x ∪ connectedComponentIn Kᶜ y := by
    refine Subset.antisymm ?_ (Set.union_subset (connectedComponentIn_subset _ _)
      (connectedComponentIn_subset _ _))
    intro z hz
    rcases hxy z hz with h | h
    · exact Or.inl (mem_connectedComponentIn_of_joinedIn h)
    · exact Or.inr (mem_connectedComponentIn_of_joinedIn h)
  have hne : connectedComponentIn Kᶜ x ≠ connectedComponentIn Kᶜ y := by
    intro heq
    apply hpre
    rw [hcover, heq, Set.union_self]
    exact isPreconnected_connectedComponentIn
  have hle : connectedComponentIn Kᶜ z₀ ⊆ connectedComponentIn Kᶜ x ∪ connectedComponentIn Kᶜ y :=
    hcover ▸ connectedComponentIn_subset Kᶜ z₀
  rcases hle (mem_connectedComponentIn hz₀) with hmem | hmem
  · -- the component of `z₀` is the component of `x`
    have hUb : Bornology.IsBounded (connectedComponentIn Kᶜ x) :=
      hbdd.subset (fun w hw => (connectedComponentIn_eq hmem) ▸ hw)
    have hdisj : Disjoint (connectedComponentIn Kᶜ x) (connectedComponentIn Kᶜ y) := by
      rw [Set.disjoint_left]
      intro w hw hw'
      have h1 : connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ w :=
        connectedComponentIn_eq (F := Kᶜ) (x := x) (y := w) hw
      have h2 : connectedComponentIn Kᶜ y = connectedComponentIn Kᶜ w :=
        connectedComponentIn_eq (F := Kᶜ) (x := y) (y := w) hw'
      exact hne (h1.trans h2.symm)
    refine ⟨connectedComponentIn Kᶜ x, connectedComponentIn Kᶜ y, hKcopen.connectedComponentIn,
      hKcopen.connectedComponentIn,
      ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩,
      ⟨⟨y, mem_connectedComponentIn hy⟩, isPreconnected_connectedComponentIn⟩,
      hdisj, hUb, ?_, hcover.symm⟩
    intro hVb
    exact hunb (hcover ▸ hUb.union hVb)
  · -- the component of `z₀` is the component of `y`
    have hVb : Bornology.IsBounded (connectedComponentIn Kᶜ y) :=
      hbdd.subset (fun w hw => (connectedComponentIn_eq hmem) ▸ hw)
    have hdisj : Disjoint (connectedComponentIn Kᶜ y) (connectedComponentIn Kᶜ x) := by
      rw [Set.disjoint_left]
      intro w hw hw'
      have h1 : connectedComponentIn Kᶜ y = connectedComponentIn Kᶜ w :=
        connectedComponentIn_eq (F := Kᶜ) (x := y) (y := w) hw
      have h2 : connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ w :=
        connectedComponentIn_eq (F := Kᶜ) (x := x) (y := w) hw'
      exact hne (h1.trans h2.symm).symm
    refine ⟨connectedComponentIn Kᶜ y, connectedComponentIn Kᶜ x, hKcopen.connectedComponentIn,
      hKcopen.connectedComponentIn,
      ⟨⟨y, mem_connectedComponentIn hy⟩, isPreconnected_connectedComponentIn⟩,
      ⟨⟨x, mem_connectedComponentIn hx⟩, isPreconnected_connectedComponentIn⟩,
      hdisj, hVb, ?_, (Set.union_comm _ _).trans hcover.symm⟩
    intro hUbb
    exact hunb (hcover ▸ hUbb.union hVb)


/-- If some component of `(range γ)ᶜ` is bounded then `(range γ)ᶜ` is not preconnected. -/
theorem not_preconnected_of_bounded_component (γ : C(Circle, ℂ))
    (hA : ∃ z ∈ (Set.range γ)ᶜ, Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z)) :
    ¬ IsPreconnected (Set.range γ)ᶜ := by
  classical
  set K := Set.range γ with hK
  have hKcopen : IsOpen Kᶜ := (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hunb : ¬ Bornology.IsBounded Kᶜ := hK ▸ not_isBounded_compl_range γ
  obtain ⟨z₀, hz₀, hbdd⟩ := hA
  intro hcon
  have hcl : Kᶜ ∩ closure (connectedComponentIn Kᶜ z₀) ⊆ connectedComponentIn Kᶜ z₀ := by
    intro w hw
    obtain ⟨hwK, hwcl⟩ := hw
    obtain ⟨u, hu⟩ := _root_.mem_closure_iff.1 hwcl (connectedComponentIn Kᶜ w)
      (hKcopen.connectedComponentIn) (mem_connectedComponentIn hwK)
    obtain ⟨hu1, hu2⟩ := hu
    have h1 : connectedComponentIn Kᶜ z₀ = connectedComponentIn Kᶜ u :=
      connectedComponentIn_eq hu2
    have h2 : connectedComponentIn Kᶜ w = connectedComponentIn Kᶜ u :=
      connectedComponentIn_eq hu1
    rw [h1, ← h2]
    exact mem_connectedComponentIn hwK
  have hsub : Kᶜ ⊆ connectedComponentIn Kᶜ z₀ ∪ (closure (connectedComponentIn Kᶜ z₀))ᶜ := by
    intro w hw
    by_cases hw' : w ∈ connectedComponentIn Kᶜ z₀
    · exact Or.inl hw'
    · refine Or.inr ?_
      simp only [Set.mem_compl_iff]
      intro hwcl
      exact hw' (hcl (Set.mem_inter hw hwcl))
  rcases hcon.subset_or_subset (hKcopen.connectedComponentIn) (isClosed_closure.isOpen_compl)
    ((disjoint_compl_right (a := closure (connectedComponentIn Kᶜ z₀))).mono_left subset_closure)
    hsub with h | h
  · have : Kᶜ = connectedComponentIn Kᶜ z₀ :=
      Subset.antisymm h (connectedComponentIn_subset Kᶜ z₀)
    exact hunb (this ▸ hbdd)
  · exact (h hz₀) (subset_closure (mem_connectedComponentIn hz₀))

/-! ## Transport of the separation statement along a direct similarity -/

lemma mem_invSim_image_iff {d c : ℂ} (hd : d ≠ 0) {U : Set ℂ} {x : ℂ} :
    x ∈ invSim d c '' U ↔ sim d c x ∈ U := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rwa [sim_invSim hd]
  · intro hx
    exact ⟨sim d c x, hx, invSim_sim hd x⟩

lemma invSim_image_compl {d c : ℂ} (hd : d ≠ 0) (S : Set ℂ) :
    invSim d c '' (sim d c '' S)ᶜ = Sᶜ := by
  ext x
  rw [mem_invSim_image_iff hd]
  constructor
  · intro hx hmem
    exact hx ⟨x, hmem, rfl⟩
  · rintro hx ⟨y, hy, hyx⟩
    exact hx (sim_injective hd hyx ▸ hy)

lemma continuous_sim (d c : ℂ) : Continuous (sim d c) := by unfold sim; fun_prop

lemma continuous_invSim (d c : ℂ) : Continuous (invSim d c) := by unfold invSim; fun_prop

lemma norm_invSim_le (d c : ℂ) (w : ℂ) : ‖invSim d c w‖ ≤ ‖d / 2‖ * ‖w‖ + ‖c‖ := by
  calc ‖invSim d c w‖ = ‖d / 2 * w + c‖ := by rw [invSim]
    _ ≤ ‖d / 2 * w‖ + ‖c‖ := norm_add_le _ _
    _ = ‖d / 2‖ * ‖w‖ + ‖c‖ := by rw [norm_mul]

lemma isBounded_invSim_image {d c : ℂ} (hd : d ≠ 0) {U : Set ℂ} :
    Bornology.IsBounded (invSim d c '' U) ↔ Bornology.IsBounded U := by
  constructor
  · intro hb
    obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hb
    have hd2 : 0 < ‖d / 2‖ := by
      rw [norm_div, Complex.norm_ofNat]
      exact div_pos (norm_pos_iff.mpr hd) (by norm_num)
    refine isBounded_iff_forall_norm_le.mpr ⟨(K + ‖c‖) / ‖d / 2‖, fun u hu => ?_⟩
    have h1 : ‖invSim d c u‖ ≤ K := hK (invSim d c u) ⟨u, hu, rfl⟩
    have h3 : ‖d / 2 * u‖ ≤ ‖invSim d c u‖ + ‖c‖ := by
      have h := norm_sub_le (invSim d c u) c
      rw [show invSim d c u - c = d / 2 * u from by rw [invSim]; ring] at h
      exact h
    have h4 : ‖d / 2‖ * ‖u‖ ≤ K + ‖c‖ := by
      rw [norm_mul] at h3
      linarith
    rw [le_div_iff₀ hd2]
    linarith
  · intro hb
    obtain ⟨K, hK⟩ := isBounded_iff_forall_norm_le.mp hb
    refine isBounded_iff_forall_norm_le.mpr ⟨‖d / 2‖ * K + ‖c‖, fun w hw => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hw
    calc ‖invSim d c u‖ ≤ ‖d / 2‖ * ‖u‖ + ‖c‖ := norm_invSim_le _ _ _
      _ ≤ ‖d / 2‖ * K + ‖c‖ := by
          have h5 : ‖u‖ * ‖d / 2‖ ≤ K * ‖d / 2‖ :=
            mul_le_mul_of_nonneg_right (hK u hu) (norm_nonneg _)
          nlinarith [norm_nonneg (d / 2), norm_nonneg c]

/-- **Transport**: if the separation statement holds for a direct similarity image of `γ`, it
holds for `γ`. -/
theorem separation_of_similarity (γ : C(Circle, ℂ)) (s t : Circle) (hd : γ t ≠ γ s)
    (hgoal : ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      U ∪ V = (Set.range (normalizedCurve γ s t))ᶜ) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      U ∪ V = (Set.range γ)ᶜ := by
  obtain ⟨U', V', hUo, hVo, hUc, hVc, hUV, hUb, hVb, hUeq⟩ := hgoal
  set d := γ t - γ s with hddef
  set c := (γ s + γ t) / 2 with hcdef
  have hd' : d ≠ 0 := sub_ne_zero.mpr hd
  have hsurj : Set.range (normalizedCurve γ s t) = sim d c '' Set.range γ := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨γ u, ⟨u, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, by simp [normalizedCurve_apply, hddef, hcdef]⟩
  refine ⟨invSim d c '' U', invSim d c '' V', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show invSim d c '' U' = sim d c ⁻¹' U' from Set.ext fun x => mem_invSim_image_iff hd']
    exact hUo.preimage (continuous_sim d c)
  · rw [show invSim d c '' V' = sim d c ⁻¹' V' from Set.ext fun x => mem_invSim_image_iff hd']
    exact hVo.preimage (continuous_sim d c)
  · exact hUc.image (invSim d c) (continuous_invSim d c).continuousOn
  · exact hVc.image (invSim d c) (continuous_invSim d c).continuousOn
  · rw [Set.disjoint_left]
    intro x hx hx'
    rw [mem_invSim_image_iff hd'] at hx hx'
    exact (Set.disjoint_left.1 hUV hx) hx'
  · exact (isBounded_invSim_image hd').mpr hUb
  · intro hb
    exact hVb ((isBounded_invSim_image hd').mp hb)
  · rw [← Set.image_union, hUeq, hsurj, invSim_image_compl hd']


/-! ## The normalized hypotheses, and the final assembly -/

/-- Two distinct points on the circle. -/
lemma circle_exp_one_ne_exp_zero : (Circle.exp 1 : Circle) ≠ Circle.exp 0 := by
  intro h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  have h2 : (m : ℝ) * (2 * Real.pi) = 1 := by linarith [hm]
  rcases eq_or_ne m 0 with hm0 | hm0
  · subst hm0; norm_num at h2
  · have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have := Int.one_le_abs hm0
      exact_mod_cast this
    have h3 : |(m : ℝ) * (2 * Real.pi)| = 1 := by rw [h2]; norm_num
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h3
    nlinarith [Real.pi_gt_three, abs_nonneg (m : ℝ), h1, h3]

/-- **The final assembly**: from the two halves of the Jordan theorem (existence of a bounded
component, and at most two components) in the normalized setting, the separation statement
follows for every Jordan curve. -/
theorem plane_separation_of_halves
    (hA : ∀ γ : C(Circle, ℂ), Function.Injective γ →
      (∀ t : Circle, (γ t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (γ t).im ∈ Set.Icc (-2:ℝ) 2) →
      (∀ t : Circle, (γ t).re = 1 ∨ (γ t).re = -1 ∨ (γ t).im = 2 ∨ (γ t).im = -2 →
        γ t = 1 ∨ γ t = -1) →
      (1:ℂ) ∈ Set.range γ → (-1:ℂ) ∈ Set.range γ →
      ∃ z ∈ (Set.range γ)ᶜ, Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ z))
    (hB : ∀ γ : C(Circle, ℂ), Function.Injective γ →
      (∀ t : Circle, (γ t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (γ t).im ∈ Set.Icc (-2:ℝ) 2) →
      (∀ t : Circle, (γ t).re = 1 ∨ (γ t).re = -1 ∨ (γ t).im = 2 ∨ (γ t).im = -2 →
        γ t = 1 ∨ γ t = -1) →
      (1:ℂ) ∈ Set.range γ → (-1:ℂ) ∈ Set.range γ →
      ¬ IsPreconnected (Set.range γ)ᶜ →
      ∃ x ∈ (Set.range γ)ᶜ, ∃ y ∈ (Set.range γ)ᶜ,
        ∀ z ∈ (Set.range γ)ᶜ, JoinedIn (Set.range γ)ᶜ z x ∨ JoinedIn (Set.range γ)ᶜ z y) :
    ∀ γ : C(Circle, ℂ), Function.Injective γ →
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ U ∪ V = (Set.range γ)ᶜ := by
  intro γ hγ
  obtain ⟨s, t, hmax⟩ := exists_max_dist γ
  have hst : s ≠ t := by
    intro hst
    have hconst : ∀ x y : Circle, x = y := by
      intro x y
      have h := hmax x y
      rw [hst, sub_self, norm_zero] at h
      exact hγ (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _))))
    exact absurd (hconst (Circle.exp 1) (Circle.exp 0)) circle_exp_one_ne_exp_zero
  have hne : γ t ≠ γ s := fun h => hst (hγ h).symm
  set γ' := normalizedCurve γ s t with hγ'def
  have hγ'inj : Function.Injective γ' := normalizedCurve_injective hγ hne
  have hdiam : ∀ x y : Circle, ‖γ' x - γ' y‖ ≤ 2 := normalizedCurve_diam hne hmax
  have hneg' : ∃ u : Circle, γ' u = -1 := ⟨s, normalizedCurve_apply_s hne⟩
  have hpos' : ∃ u : Circle, γ' u = 1 := ⟨t, normalizedCurve_apply_t hne⟩
  have hE : ∀ u : Circle, (γ' u).re ∈ Set.Icc (-1:ℝ) 1 ∧ (γ' u).im ∈ Set.Icc (-2:ℝ) 2 :=
    range_subset_Erect_set γ' hdiam hneg' hpos'
  have hbd : ∀ u : Circle,
      (γ' u).re = 1 ∨ (γ' u).re = -1 ∨ (γ' u).im = 2 ∨ (γ' u).im = -2 →
      γ' u = 1 ∨ γ' u = -1 := fun u hb => eq_pm_one_of_boundary γ' hdiam hneg' hpos' hb
  have h1' : (1:ℂ) ∈ Set.range γ' := ⟨t, normalizedCurve_apply_t hne⟩
  have hm1' : (-1:ℂ) ∈ Set.range γ' := ⟨s, normalizedCurve_apply_s hne⟩
  have hAc := hA γ' hγ'inj hE hbd h1' hm1'
  have hpre : ¬ IsPreconnected (Set.range γ')ᶜ := not_preconnected_of_bounded_component γ' hAc
  have hBc := hB γ' hγ'inj hE hbd h1' hm1' hpre
  exact separation_of_similarity γ s t hne (separation_of_halves γ' hAc hBc)


/-- **Pannwitz–Kuperberg / Jordan**: the complement of the image of an injective curve
`Circle → ℂ` has exactly two connected components, one bounded and one unbounded. -/
theorem plane_separation (γ : C(Circle, ℂ)) (hγ : Function.Injective γ) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ U ∪ V = (Set.range γ)ᶜ := by
  -- The two halves of the Jordan theorem (existence of a bounded component, and at most two
  -- components) in the normalized setting are supplied by the shared commons:
  -- `Commons.Topology.Jordan.bounded_component_exists` and
  -- `Commons.Topology.Jordan.at_most_two_components`.
  exact plane_separation_of_halves
    (fun γ hγ hE hbd h1 hm1 => bounded_component_exists γ hγ hE hbd h1 hm1)
    (fun γ hγ hE hbd h1 hm1 hpre => at_most_two_components γ hγ hE hbd h1 hm1 hpre) γ hγ

end Commons.Topology.Jordan
