import Mathlib
import Submission.Commons.Topology.Jordan.bounded_component_exists
import Submission.Commons.Topology.Connected.frontier_component_compl_range
import Submission.Commons.Topology.Jordan.crosscut_complement_at_most_two
import Submission.Commons.Topology.Jordan.arc_complement_no_bounded_component
import Submission.Commons.Topology.Jordan.crossing_lemma_rect
import Submission.Commons.Topology.Jordan.two_arcs_through
import Submission.Commons.Topology.Jordan.compl_compact_unique_unbounded
import Submission.Commons.Topology.Path.range_trans
import Submission.Commons.Topology.Path.range_symm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Commons.Topology.Jordan

open Set Metric Filter
open scoped Topology
open unitInterval

noncomputable section

/-! ## Local auxiliary lemmas -/

/-- The range of the straight segment path is preconnected. -/
private lemma nnb_preconnected_range_segPath (z w : ℂ) :
    IsPreconnected (Set.range (segPath z w)) := by
  have hcont : Continuous (fun t : ℝ => (1 - t) * z + t * w) := by fun_prop
  have himg : Set.range (segPath z w) =
      (fun t : ℝ => (1 - t) * z + t * w) '' Set.Icc (0:ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(t:ℝ), ⟨t.2.1, t.2.2⟩, by simp [segPath_apply]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, by simp [segPath_apply]⟩
  rw [himg]
  exact isPreconnected_Icc.image _ hcont.continuousOn

/-- If the whole straight segment between `z` and `w` lies in `Kᶜ` then `z` and `w` lie in
the same connected component of `Kᶜ`. -/
private lemma nnb_cc_eq_of_segPath_mem {K : Set ℂ} {z w : ℂ}
    (h : ∀ u : I, segPath z w u ∈ Kᶜ) :
    connectedComponentIn Kᶜ z = connectedComponentIn Kᶜ w := by
  have hsub : Set.range (segPath z w) ⊆ Kᶜ := by rintro _ ⟨u, rfl⟩; exact h u
  have hz : z ∈ Set.range (segPath z w) := ⟨0, by simp [segPath_apply]⟩
  have hw : w ∈ Set.range (segPath z w) := ⟨1, by simp [segPath_apply]⟩
  have h1 : Set.range (segPath z w) ⊆ connectedComponentIn Kᶜ z :=
    (nnb_preconnected_range_segPath z w).subset_connectedComponentIn hz hsub
  exact connectedComponentIn_eq (h1 hw)

/-- A strict convex combination is below a bound that is above both endpoints. -/
private lemma nnb_comb_lt {a b x t : ℝ} (ha : a < x) (hb : b < x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * a + t * b < x := by
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · subst h1; simpa using hb
  · have h1' : 0 < 1 - t := by linarith
    have hprod : 0 < (1 - t) * (x - a) := mul_pos h1' (by linarith)
    have hprod2 : 0 ≤ t * (x - b) := mul_nonneg ht0 (by linarith)
    nlinarith [hprod, hprod2]

/-- A strict convex combination is above a bound that is below both endpoints. -/
private lemma nnb_lt_comb {a b x t : ℝ} (ha : x < a) (hb : x < b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x < (1 - t) * a + t * b := by
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · subst h1; simpa using hb
  · have h1' : 0 < 1 - t := by linarith
    have hprod : 0 < (1 - t) * (a - x) := mul_pos h1' (by linarith)
    have hprod2 : 0 ≤ t * (b - x) := mul_nonneg ht0 (by linarith)
    nlinarith [hprod, hprod2]

/-- Half planes of `ℂ` are unbounded (four variants). -/
private lemma nnb_not_isBounded_re_lt (a : ℝ) :
    ¬ Bornology.IsBounded {z : ℂ | z.re < a} := by
  intro hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  set M : ℝ := |C| + |a| + 1 with hM
  have hMpos : 0 < M := by rw [hM]; linarith [abs_nonneg C, abs_nonneg a]
  have hz : (((a - M : ℝ)) : ℂ) ∈ {z : ℂ | z.re < a} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]
    linarith
  have h2 := hC _ hz
  have hMa : 0 ≤ M - a := by rw [hM]; linarith [abs_nonneg C, abs_nonneg a, le_abs_self a]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg hMa, hM] at h2
  linarith [le_abs_self C, le_abs_self a, abs_nonneg a]

private lemma nnb_not_isBounded_re_gt (a : ℝ) :
    ¬ Bornology.IsBounded {z : ℂ | a < z.re} := by
  intro hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  set M : ℝ := |C| + |a| + 1 with hM
  have hMpos : 0 < M := by rw [hM]; linarith [abs_nonneg C, abs_nonneg a]
  have hz : (((a + M : ℝ)) : ℂ) ∈ {z : ℂ | a < z.re} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]
    linarith
  have h2 := hC _ hz
  have haM : 0 ≤ a + M := by rw [hM]; linarith [abs_nonneg C, abs_nonneg a, neg_abs_le a]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg haM, hM] at h2
  linarith [le_abs_self C, neg_abs_le a, abs_nonneg a]

private lemma nnb_not_isBounded_im_lt (a : ℝ) :
    ¬ Bornology.IsBounded {z : ℂ | z.im < a} := by
  intro hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  set M : ℝ := |C| + |a| + 1 with hM
  have hMpos : 0 < M := by rw [hM]; linarith [abs_nonneg C, abs_nonneg a]
  have hz : (((a - M : ℝ)) * Complex.I) ∈ {z : ℂ | z.im < a} := by
    simp only [Set.mem_setOf_eq, Complex.mul_I_im, Complex.ofReal_re]
    linarith
  have h2 := hC _ hz
  have hMa : 0 ≤ M - a := by rw [hM]; linarith [abs_nonneg C, abs_nonneg a, le_abs_self a]
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
    abs_of_nonneg hMa, hM] at h2
  linarith [le_abs_self C, le_abs_self a, abs_nonneg a]

private lemma nnb_not_isBounded_im_gt (a : ℝ) :
    ¬ Bornology.IsBounded {z : ℂ | a < z.im} := by
  intro hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  set M : ℝ := |C| + |a| + 1 with hM
  have hMpos : 0 < M := by rw [hM]; linarith [abs_nonneg C, abs_nonneg a]
  have hz : (((a + M : ℝ)) * Complex.I) ∈ {z : ℂ | a < z.im} := by
    simp only [Set.mem_setOf_eq, Complex.mul_I_im, Complex.ofReal_re]
    linarith
  have h2 := hC _ hz
  have haM : 0 ≤ a + M := by rw [hM]; linarith [abs_nonneg C, abs_nonneg a, neg_abs_le a]
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg haM, hM] at h2
  linarith [le_abs_self C, neg_abs_le a, abs_nonneg a]

/-- Half planes of `ℂ` are preconnected (four variants). -/
private lemma nnb_isPreconnected_re_lt (a : ℝ) : IsPreconnected {z : ℂ | z.re < a} := by
  have h : {z : ℂ | z.re < a} = Complex.re ⁻¹' Set.Iio a := by ext z; simp
  rw [h]
  exact ((convex_Iio a).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)).isPreconnected

private lemma nnb_isPreconnected_re_gt (a : ℝ) : IsPreconnected {z : ℂ | a < z.re} := by
  have h : {z : ℂ | a < z.re} = Complex.re ⁻¹' Set.Ioi a := by ext z; simp
  rw [h]
  exact ((convex_Ioi a).linear_preimage (Complex.reCLM : ℂ →ₗ[ℝ] ℝ)).isPreconnected

private lemma nnb_isPreconnected_im_lt (a : ℝ) : IsPreconnected {z : ℂ | z.im < a} := by
  have h : {z : ℂ | z.im < a} = Complex.im ⁻¹' Set.Iio a := by ext z; simp
  rw [h]
  exact ((convex_Iio a).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)).isPreconnected

private lemma nnb_isPreconnected_im_gt (a : ℝ) : IsPreconnected {z : ℂ | a < z.im} := by
  have h : {z : ℂ | a < z.im} = Complex.im ⁻¹' Set.Ioi a := by ext z; simp
  rw [h]
  exact ((convex_Ioi a).linear_preimage (Complex.imCLM : ℂ →ₗ[ℝ] ℝ)).isPreconnected

/-- Every bounded connected component of the complement of a subset `K ⊆ Rect` is contained
in `Rect`. -/
private theorem nnb_bounded_component_subset_Rect {K : Set ℂ} (hKsub : K ⊆ Rect)
    {y : ℂ} (hyb : Bornology.IsBounded (connectedComponentIn Kᶜ y)) :
    connectedComponentIn Kᶜ y ⊆ Rect := by
  intro z hz
  by_contra hzR
  have hcases : z.re < -1 ∨ 1 < z.re ∨ z.im < -2 ∨ 2 < z.im := by
    by_contra hc
    push Not at hc
    exact hzR ⟨⟨hc.1, hc.2.1⟩, ⟨hc.2.2.1, hc.2.2.2⟩⟩
  have key : ∀ {H : Set ℂ}, IsPreconnected H → H ⊆ Kᶜ → z ∈ H → ¬ Bornology.IsBounded H →
      False := by
    intro H hHpc hHKc hzH hHunb
    have hsub : H ⊆ connectedComponentIn Kᶜ y := by
      rw [connectedComponentIn_eq hz]
      exact hHpc.subset_connectedComponentIn hzH hHKc
    exact hHunb (hyb.subset hsub)
  rcases hcases with hc | hc | hc | hc
  · refine key (H := {w : ℂ | w.re < -1}) (nnb_isPreconnected_re_lt (-1)) ?_ hc
      (nnb_not_isBounded_re_lt (-1))
    intro w hw
    rw [Set.mem_compl_iff]
    intro hwK
    have hw' : w.re < -1 := hw
    linarith [(hKsub hwK).1.1]
  · refine key (H := {w : ℂ | 1 < w.re}) (nnb_isPreconnected_re_gt 1) ?_ hc
      (nnb_not_isBounded_re_gt 1)
    intro w hw
    rw [Set.mem_compl_iff]
    intro hwK
    have hw' : 1 < w.re := hw
    linarith [(hKsub hwK).1.2]
  · refine key (H := {w : ℂ | w.im < -2}) (nnb_isPreconnected_im_lt (-2)) ?_ hc
      (nnb_not_isBounded_im_lt (-2))
    intro w hw
    rw [Set.mem_compl_iff]
    intro hwK
    have hw' : w.im < -2 := hw
    linarith [(hKsub hwK).2.1]
  · refine key (H := {w : ℂ | 2 < w.im}) (nnb_isPreconnected_im_gt 2) ?_ hc
      (nnb_not_isBounded_im_gt 2)
    intro w hw
    rw [Set.mem_compl_iff]
    intro hwK
    have hw' : 2 < w.im := hw
    linarith [(hKsub hwK).2.2]

/-- **A connected set cannot meet both sides of a top-to-bottom barrier.**

`Rect = [-1,1] × [-2,2]` has bottom-middle point `Spt` and top-middle point `Npt`.  If `W`
is a nonempty open preconnected subset of `Rect` whose closure contains both `1` and `-1`,
then there is no path `β` from `Spt` to `Npt` inside `Rect` avoiding `W` and the two points
`±1`. -/
private theorem nnb_no_component_across_barrier {W : Set ℂ} (hWopen : IsOpen W)
    (hWpc : IsPreconnected W) (hWne : W.Nonempty) (hWsub : W ⊆ Rect)
    (h1cl : (1:ℂ) ∈ closure W) (hm1cl : (-1:ℂ) ∈ closure W)
    (β : Path Spt Npt) (hβrect : ∀ t : I, β t ∈ Rect)
    (hβW : ∀ t : I, β t ∉ W) (hβ1 : ∀ t : I, β t ≠ 1) (hβm1 : ∀ t : I, β t ≠ -1) : False := by
  have hβcpt : IsCompact (Set.range β) := isCompact_range β.continuous
  have h1not : (1:ℂ) ∉ Set.range β := by rintro ⟨t, ht⟩; exact hβ1 t ht
  have hm1not : (-1:ℂ) ∉ Set.range β := by rintro ⟨t, ht⟩; exact hβm1 t ht
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := Metric.mem_nhds_iff.mp (hβcpt.isClosed.isOpen_compl.mem_nhds h1not)
  obtain ⟨ε₂, hε₂pos, hε₂sub⟩ := Metric.mem_nhds_iff.mp (hβcpt.isClosed.isOpen_compl.mem_nhds hm1not)
  set ε : ℝ := min ε₁ ε₂ with hεdef
  have hεpos : 0 < ε := lt_min hε₁pos hε₂pos
  have hball1 : Metric.ball (1:ℂ) ε ⊆ (Set.range β)ᶜ := fun z hz =>
    hε₁sub (Metric.ball_subset_ball (min_le_left _ _) hz)
  have hballm1 : Metric.ball (-1:ℂ) ε ⊆ (Set.range β)ᶜ := fun z hz =>
    hε₂sub (Metric.ball_subset_ball (min_le_right _ _) hz)
  obtain ⟨b₁, hb₁W, hb₁dist⟩ := Metric.mem_closure_iff.mp h1cl ε hεpos
  obtain ⟨a₁, ha₁W, ha₁dist⟩ := Metric.mem_closure_iff.mp hm1cl ε hεpos
  have ha₁ball : a₁ ∈ Metric.ball (-1:ℂ) ε := by rw [Metric.mem_ball, dist_comm]; exact ha₁dist
  have hb₁ball : b₁ ∈ Metric.ball (1:ℂ) ε := by rw [Metric.mem_ball, dist_comm]; exact hb₁dist
  have hWpc' : IsPathConnected W := (hWopen.isConnected_iff_isPathConnected).mp ⟨hWne, hWpc⟩
  obtain ⟨τ, hτ⟩ := hWpc'.joinedIn a₁ ha₁W b₁ hb₁W
  have hτKc : Set.range τ ⊆ (Set.range β)ᶜ := by
    rintro z ⟨t, rfl⟩ hzβ
    obtain ⟨s, hs⟩ := hzβ
    exact hβW s (hs ▸ hτ t)
  let η : Path (((-1:ℝ)) : ℂ) (((1:ℝ)) : ℂ) :=
    ((segPath (-1:ℂ) a₁).trans (τ.trans (segPath b₁ (1:ℂ)))).cast
      (by norm_num) (by norm_num)
  have hηcoe : ∀ t : I, η t = (segPath (-1:ℂ) a₁).trans (τ.trans (segPath b₁ (1:ℂ))) t := by
    intro t; rw [Path.cast_apply]
  have hηrange : Set.range η ⊆ Rect := by
    rintro z ⟨t, rfl⟩
    rw [hηcoe t]
    have hmem : (segPath (-1:ℂ) a₁).trans (τ.trans (segPath b₁ (1:ℂ))) t ∈
        Set.range ((segPath (-1:ℂ) a₁).trans (τ.trans (segPath b₁ (1:ℂ)))) := ⟨t, rfl⟩
    rw [Path.trans_range, Path.trans_range] at hmem
    rcases hmem with h | h | h
    · rcases h with ⟨u, hu⟩
      rw [← hu]
      exact segPath_mem_Rect (by norm_num [Rect]) (hWsub ha₁W) u
    · rcases h with ⟨u, hu⟩
      rw [← hu]
      exact hWsub (hτ u)
    · rcases h with ⟨u, hu⟩
      rw [← hu]
      exact segPath_mem_Rect (hWsub hb₁W) (by norm_num [Rect]) u
  have hηβ : Set.range η ⊆ (Set.range β)ᶜ := by
    rintro z ⟨t, rfl⟩
    rw [hηcoe t]
    have hmem : (segPath (-1:ℂ) a₁).trans (τ.trans (segPath b₁ (1:ℂ))) t ∈
        Set.range ((segPath (-1:ℂ) a₁).trans (τ.trans (segPath b₁ (1:ℂ)))) := ⟨t, rfl⟩
    rw [Path.trans_range, Path.trans_range] at hmem
    rcases hmem with h | h | h
    · rcases h with ⟨u, hu⟩
      rw [← hu]
      have hsub : segPath (-1:ℂ) a₁ u - (-1:ℂ) = ((u:ℝ) * (a₁ - (-1:ℂ))) := by
        rw [segPath_apply]; ring
      rw [Set.mem_compl_iff]
      apply hballm1
      rw [Metric.mem_ball, dist_eq_norm, hsub, norm_mul]
      have h1 : ‖((u:ℝ) : ℂ)‖ = (u:ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg u.2.1]
      rw [h1]
      calc (u:ℝ) * ‖a₁ - (-1:ℂ)‖ ≤ 1 * ‖a₁ - (-1:ℂ)‖ :=
            mul_le_mul_of_nonneg_right u.2.2 (norm_nonneg _)
        _ = ‖a₁ - (-1:ℂ)‖ := one_mul _
        _ = dist a₁ (-1:ℂ) := (dist_eq_norm _ _).symm
        _ = dist (-1:ℂ) a₁ := dist_comm _ _
        _ < ε := ha₁dist
    · rcases h with ⟨u, hu⟩
      rw [← hu]; exact hτKc ⟨u, rfl⟩
    · rcases h with ⟨u, hu⟩
      rw [← hu]
      have hsub : segPath b₁ (1:ℂ) u - (1:ℂ) = ((1 - (u:ℝ)) * (b₁ - (1:ℂ))) := by
        rw [segPath_apply]; ring
      rw [Set.mem_compl_iff]
      apply hball1
      rw [Metric.mem_ball, dist_eq_norm, hsub, norm_mul]
      have h1 : ‖(1:ℂ) - ((u:ℝ):ℂ)‖ = 1 - (u:ℝ) := by
        rw [show (1:ℂ) - ((u:ℝ):ℂ) = (((1 - (u:ℝ)) : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [u.2.2])]
      rw [h1]
      calc (1 - (u:ℝ)) * ‖b₁ - (1:ℂ)‖ ≤ 1 * ‖b₁ - (1:ℂ)‖ :=
            mul_le_mul_of_nonneg_right (by linarith [u.2.1]) (norm_nonneg _)
        _ = ‖b₁ - (1:ℂ)‖ := one_mul _
        _ = dist b₁ (1:ℂ) := (dist_eq_norm _ _).symm
        _ = dist (1:ℂ) b₁ := dist_comm _ _
        _ < ε := hb₁dist
  have hh : ∀ t : I, (η t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (η t).im ∈ Set.Icc (-2:ℝ) 2 :=
    fun t => hηrange ⟨t, rfl⟩
  have hv : ∀ t : I, (β t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (β t).im ∈ Set.Icc (-2:ℝ) 2 :=
    fun t => hβrect t
  obtain ⟨s, t, hst⟩ := Commons.Topology.Crossing.crossing_lemma_rect_path (a := -1) (b := 1)
    (c := -2) (d := 2) (by norm_num) (by norm_num) η β hh hv
  exact hηβ ⟨s, rfl⟩ ⟨t, hst.symm⟩
theorem normalized_no_two_bounded_components (γ : C(Circle, ℂ)) (hγ : Function.Injective γ)
    (hE : ∀ t : Circle, (γ t).re ∈ Set.Icc (-1:ℝ) 1 ∧ (γ t).im ∈ Set.Icc (-2:ℝ) 2)
    (hbd : ∀ t : Circle, (γ t).re = 1 ∨ (γ t).re = -1 ∨ (γ t).im = 2 ∨ (γ t).im = -2 →
      γ t = 1 ∨ γ t = -1)
    (h1 : (1:ℂ) ∈ Set.range γ) (hm1 : (-1:ℂ) ∈ Set.range γ) :
    ∀ x ∈ (Set.range γ)ᶜ, Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ x) →
    ∀ y ∈ (Set.range γ)ᶜ, Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ y) →
      connectedComponentIn (Set.range γ)ᶜ x = connectedComponentIn (Set.range γ)ᶜ y := by
  classical
  have hKsub : Set.range γ ⊆ Rect := fun z hz => by
    rcases hz with ⟨t, rfl⟩; exact ⟨(hE t).1, (hE t).2⟩
  have hKBd : ∀ z ∈ Set.range γ, z ∈ RectBd → z = 1 ∨ z = -1 := by
    rintro z ⟨t, rfl⟩ hz; exact hbd t hz
  have hKcompact : IsCompact (Set.range γ) := isCompact_range γ.continuous
  have hKc_open : IsOpen (Set.range γ)ᶜ := hKcompact.isClosed.isOpen_compl
  have hKc_unbounded : ¬ Bornology.IsBounded ((Set.range γ)ᶜ : Set ℂ) := by
    intro hb
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0:ℂ)).mp hKcompact.isBounded
    set M : ℝ := |C| + |R| + 1 with hM
    have hMpos : 0 < M := by rw [hM]; positivity
    have hzKc : ((M:ℝ):ℂ) ∈ (Set.range γ)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hzK
      have h1' : ‖((M:ℝ):ℂ)‖ ≤ R := by
        have := hR hzK
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos] at h1'
      rw [hM] at h1'
      linarith [le_abs_self R, le_abs_self C, abs_nonneg R, abs_nonneg C]
    have h2 := hC _ hzKc
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos, hM] at h2
    linarith [le_abs_self C, le_abs_self R, abs_nonneg C, abs_nonneg R]
  have hre0 : ∃ t : Circle, (γ t).re = 0 := by
    obtain ⟨t₁, ht₁⟩ := hm1
    obtain ⟨t₂, ht₂⟩ := h1
    obtain ⟨t, -, ht⟩ :=
      (PreconnectedSpace.isPreconnected_univ (α := Circle)).intermediate_value₂
        (show t₁ ∈ (univ : Set Circle) from trivial)
        (show t₂ ∈ (univ : Set Circle) from trivial)
        (f := fun t : Circle => (γ t).re) (g := fun _ : Circle => (0:ℝ))
        (by fun_prop) continuousOn_const (by rw [ht₁]; norm_num) (by rw [ht₂]; norm_num)
    exact ⟨t, ht⟩
  have hne : (Set.range γ ∩ VSeg).Nonempty := by
    obtain ⟨t, ht⟩ := hre0
    exact ⟨γ t, ⟨⟨t, rfl⟩, ⟨ht, (hE t).2⟩⟩⟩
  have hcomp : IsCompact (Set.range γ ∩ VSeg) :=
    (isCompact_range γ.continuous).inter_right VSeg_closed
  obtain ⟨l, hl, hlmax⟩ := hcomp.exists_isMaxOn hne Complex.continuous_im.continuousOn
  have hlK : l ∈ Set.range γ := hl.1
  have hlV : l ∈ VSeg := hl.2
  have hl_re : l.re = 0 := hlV.1
  have hl_ne1 : l ≠ 1 := by intro h; have := hlV.1; rw [h] at this; norm_num at this
  have hl_nem1 : l ≠ -1 := by intro h; have := hlV.1; rw [h] at this; norm_num at this
  obtain ⟨P, Q, hPQrange, hPQinter, hPinj, hQinj, hlP⟩ :=
    Commons.Topology.Jordan.two_arcs_through γ hγ l hlK hl_ne1 hl_nem1 h1 hm1
  have hPsubK : Set.range P ⊆ Set.range γ := by rw [← hPQrange]; exact Set.subset_union_left
  have hQsubK : Set.range Q ⊆ Set.range γ := by rw [← hPQrange]; exact Set.subset_union_right
  have hPrect : ∀ t, P t ∈ Rect := fun t => hKsub (hPsubK ⟨t, rfl⟩)
  have hQrect : ∀ t, Q t ∈ Rect := fun t => hKsub (hQsubK ⟨t, rfl⟩)
  have hSPne : (Set.range P ∩ VSeg).Nonempty := ⟨l, hlP, hlV⟩
  have hSPcomp : IsCompact (Set.range P ∩ VSeg) :=
    (isCompact_range P.continuous).inter_right VSeg_closed
  obtain ⟨m, hm, hmmin⟩ := hSPcomp.exists_isMinOn hSPne Complex.continuous_im.continuousOn
  have hmP : m ∈ Set.range P := hm.1
  have hmV : m ∈ VSeg := hm.2
  have hm_re : m.re = 0 := hmV.1
  have hm_ne1 : m ≠ 1 := by intro h; have := hmV.1; rw [h] at this; norm_num at this
  have hm_nem1 : m ≠ -1 := by intro h; have := hmV.1; rw [h] at this; norm_num at this
  obtain ⟨al, hal⟩ : ∃ al : I, P al = l := by exact hlP
  obtain ⟨am, ham⟩ : ∃ am : I, P am = m := by exact hmP
  have hal0 : (al:ℝ) ≠ 0 := by
    intro h0
    have hal' : al = 0 := Subtype.ext h0
    rw [hal', Path.source] at hal
    exact hl_nem1 hal.symm
  have hal1 : (al:ℝ) ≠ 1 := by
    intro h0
    have hal' : al = 1 := Subtype.ext h0
    rw [hal', Path.target] at hal
    exact hl_ne1 hal.symm
  have ham0 : (am:ℝ) ≠ 0 := by
    intro h0
    have ham' : am = 0 := Subtype.ext h0
    rw [ham', Path.source] at ham
    exact hm_nem1 ham.symm
  have ham1 : (am:ℝ) ≠ 1 := by
    intro h0
    have ham' : am = 1 := Subtype.ext h0
    rw [ham', Path.target] at ham
    exact hm_ne1 ham.symm
  let arc : Path m l := (P.subpath am al).cast ham.symm hal.symm
  have harc_coe : ∀ u : I, arc u = P.subpath am al u := by
    intro u
    simp only [arc, Path.cast_coe]
  have harc_range : Set.range arc ⊆ Set.range P := by
    rintro z ⟨u, rfl⟩
    refine ⟨Icc.convexComb am al u, ?_⟩
    rw [harc_coe u]
    rfl
  have harc_ne : ∀ u, arc u ≠ 1 ∧ arc u ≠ -1 := by
    intro u
    rw [harc_coe u]
    exact subpath_ne_pm_one hPinj ham0 ham1 hal0 hal1 u
  let v6 : Path Spt Npt := (segPath Spt m).trans (arc.trans (segPath l Npt))
  have hSpt_re : Spt.re = 0 := by norm_num [Spt]
  have hNpt_re : Npt.re = 0 := by norm_num [Npt]
  have hSpt_im : Spt.im = -2 := by norm_num [Spt]
  have hNpt_im : Npt.im = 2 := by norm_num [Npt]
  have hseg_Sm : Set.range (segPath Spt m) ⊆ Rect := by
    rintro z ⟨u, rfl⟩
    exact segPath_mem_Rect Spt_mem_Rect (VSeg_subset_Rect hmV) u
  have harc_rect : Set.range arc ⊆ Rect := fun z hz => hKsub (hPsubK (harc_range hz))
  have hseg_lN : Set.range (segPath l Npt) ⊆ Rect := by
    rintro z ⟨u, rfl⟩
    exact segPath_mem_Rect (VSeg_subset_Rect hlV) Npt_mem_Rect u
  have hv6range : Set.range v6 ⊆ Rect := by
    intro z hz
    have hz' : z ∈ Set.range (segPath Spt m) ∪ (Set.range arc ∪ Set.range (segPath l Npt)) := by
      simpa [v6, Path.trans_range] using hz
    rcases hz' with h | h | h
    · exact hseg_Sm h
    · exact harc_rect h
    · exact hseg_lN h
  obtain ⟨s0, t0, hst0⟩ := cross_exists Q v6 hQrect (fun t => hv6range ⟨t, rfl⟩)
  have harc_Q : ∀ z, z ∈ Set.range arc → z ∈ Set.range Q → False := by
    rintro z ⟨u, rfl⟩ hzQ
    have h1 := (harc_ne u).1
    have h2 := (harc_ne u).2
    have hzP : arc u ∈ Set.range P := harc_range ⟨u, rfl⟩
    have hmem : arc u ∈ Set.range P ∩ Set.range Q := ⟨hzP, hzQ⟩
    rw [hPQinter] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact h1 h
    · exact h2 h
  have hseg_Q : ∀ z, z ∈ Set.range (segPath l Npt) → z ∈ Set.range Q → False := by
    rintro z ⟨u, rfl⟩ hzQ
    have hzV : segPath l Npt u ∈ VSeg := segPath_mem_VSeg hlV Npt_mem_VSeg u
    have hzK : segPath l Npt u ∈ Set.range γ := hQsubK hzQ
    have hle : (segPath l Npt u).im ≤ l.im := isMaxOn_iff.mp hlmax _ ⟨hzK, hzV⟩
    have hge : l.im ≤ (segPath l Npt u).im := by
      rw [segPath_im, hNpt_im]
      have hlim2 : l.im ≤ 2 := hlV.2.2
      have := mul_nonneg u.2.1 (by linarith : (0:ℝ) ≤ 2 - l.im); linarith
    have heq_im : (segPath l Npt u).im = l.im := le_antisymm hle hge
    have heq : segPath l Npt u = l := Complex.ext (by rw [hzV.1, hl_re]) heq_im
    have hlQ : l ∈ Set.range Q := heq ▸ hzQ
    have hmem : l ∈ Set.range P ∩ Set.range Q := ⟨hlP, hlQ⟩
    rw [hPQinter] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hl_ne1 h
    · exact hl_nem1 h
  have hQmseg : (Set.range Q ∩ Set.range (segPath Spt m)).Nonempty := by
    have hmem : Q s0 ∈ Set.range v6 := ⟨t0, hst0.symm⟩
    have hmem' : Q s0 ∈ Set.range (segPath Spt m) ∪ (Set.range arc ∪ Set.range (segPath l Npt)) := by
      simpa [v6, Path.trans_range] using hmem
    rcases hmem' with h | h | h
    · exact ⟨Q s0, ⟨⟨s0, rfl⟩, h⟩⟩
    · exact absurd (harc_Q (Q s0) h ⟨s0, rfl⟩) (fun hh => hh)
    · exact absurd (hseg_Q (Q s0) h ⟨s0, rfl⟩) (fun hh => hh)
  have hQcompact : IsCompact (Set.range Q) := isCompact_range Q.continuous
  have hsegcompact : IsCompact (Set.range (segPath Spt m)) :=
    isCompact_range (segPath Spt m).continuous
  obtain ⟨p, hp, hpmax⟩ := (hQcompact.inter hsegcompact).exists_isMaxOn hQmseg
    Complex.continuous_im.continuousOn
  have hpQ : p ∈ Set.range Q := hp.1
  have hpS : p ∈ Set.range (segPath Spt m) := hp.2
  have hpV : p ∈ VSeg := by
    obtain ⟨u, rfl⟩ := hpS
    refine ⟨segPath_re_eq_zero hSpt_re hm_re u, ?_⟩
    rw [segPath_im, hSpt_im]
    constructor <;> nlinarith [hmV.2.1, hmV.2.2, u.2.1, u.2.2]
  have hp_im_le : p.im ≤ m.im := by
    obtain ⟨u, rfl⟩ := hpS
    rw [segPath_im, hSpt_im]
    nlinarith [hmV.2.1, u.2.1, u.2.2]
  have hp_ne_m : p ≠ m := by
    intro hpm
    have hmQ : m ∈ Set.range Q := hpm ▸ hpQ
    have hmem : m ∈ Set.range P ∩ Set.range Q := ⟨hmP, hmQ⟩
    rw [hPQinter] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact hm_ne1 h
    · exact hm_nem1 h
  have hp_im_lt : p.im < m.im := by
    refine lt_of_le_of_ne hp_im_le (fun h => hp_ne_m ?_)
    exact Complex.ext (by rw [hpV.1, hm_re]) h
  let z0 : ℂ := (m + p) / 2
  have hz0_re : z0.re = 0 := by
    simp only [z0, Complex.add_re, Complex.div_ofNat_re]
    rw [hm_re, hpV.1]; ring
  have hz0_im : z0.im = (m.im + p.im) / 2 := by
    simp only [z0, Complex.add_im, Complex.div_ofNat_im]
  have hz0_lt_m : z0.im < m.im := by rw [hz0_im]; linarith [hp_im_lt]
  have hz0_gt_p : p.im < z0.im := by rw [hz0_im]; linarith [hp_im_lt]
  have hm_im_gt : (-2:ℝ) < m.im := by
    refine lt_of_le_of_ne hmV.2.1 (fun h => ?_)
    have hmBd : m ∈ RectBd := Or.inr (Or.inr (Or.inr h.symm))
    rcases hKBd m (hPsubK hmP) hmBd with h1 | h1
    · exact hm_ne1 h1
    · exact hm_nem1 h1
  have hz0_im_lo : (-2:ℝ) < z0.im := by rw [hz0_im]; linarith [hm_im_gt, hpV.2.1]
  have hz0_im_hi : z0.im < 2 := by rw [hz0_im]; linarith [hp_im_lt, hp_im_le, hmV.2.2]
  have hz0_int : z0 ∈ interior Rect :=
    Rect_open_inside ⟨⟨by rw [hz0_re]; norm_num, by rw [hz0_re]; norm_num⟩,
      ⟨hz0_im_lo, hz0_im_hi⟩⟩
  have hzS : z0 ∈ Set.range (segPath Spt m) := by
    obtain ⟨up, hup⟩ := hpS
    refine ⟨⟨(1 + (up:ℝ)) / 2, ⟨by linarith [up.2.1], by linarith [up.2.2]⟩⟩, ?_⟩
    have hup' : p = (1 - (up:ℝ)) * Spt + (up:ℝ) * m := by rw [← hup, segPath_apply]
    rw [segPath_apply]
    simp only [z0]
    rw [hup']
    push_cast
    ring
  have hz0_notK : z0 ∉ Set.range γ := by
    intro hz
    have hzV : z0 ∈ VSeg := ⟨hz0_re, ⟨le_of_lt hz0_im_lo, le_of_lt hz0_im_hi⟩⟩
    have hz2 : z0 ∈ Set.range P ∪ Set.range Q := by rw [hPQrange]; exact hz
    rcases hz2 with hzP | hzQ
    · have hle := isMinOn_iff.mp hmmin z0 ⟨hzP, hzV⟩
      linarith [hz0_lt_m]
    · have hle := isMaxOn_iff.mp hpmax z0 ⟨hzQ, hzS⟩
      linarith [hz0_gt_p]
  -- ## the part of the segment between `p` and `m` is disjoint from the curve
  have hpm_free : ∀ w : ℂ, w.re = 0 → p.im < w.im → w.im < m.im → w ∉ Set.range γ := by
    intro w hwr hw1 hw2 hwK
    have hwV : w ∈ VSeg := ⟨hwr, ⟨by linarith [hpV.2.1, hw1], by linarith [hw2, hmV.2.2]⟩⟩
    have hw2' : w ∈ Set.range P ∪ Set.range Q := by rw [hPQrange]; exact hwK
    rcases hw2' with hwP | hwQ
    · exact absurd (isMinOn_iff.mp hmmin w ⟨hwP, hwV⟩) (not_le.mpr hw2)
    · have hm2 : (0:ℝ) < m.im + 2 := by linarith [hm_im_gt]
      have hwseg : w ∈ Set.range (segPath Spt m) := by
        refine ⟨⟨(w.im + 2) / (m.im + 2), ⟨div_nonneg (by linarith [hwV.2.1]) hm2.le,
          by rw [div_le_one hm2]; linarith [hw2.le]⟩⟩, ?_⟩
        apply Complex.ext
        · rw [segPath_re_eq_zero hSpt_re hm_re, hwr]
        · rw [segPath_im, hSpt_im]
          field_simp
          ring
      exact absurd (isMaxOn_iff.mp hpmax w ⟨hwQ, hwseg⟩) (not_le.mpr hw1)
  -- ## the bottom point `q` of `Q` on the vertical segment
  have hQseg_ne : (Set.range Q ∩ VSeg).Nonempty := by
    have hf : ContinuousOn (fun t : I => (Q t).re) (Set.univ : Set I) :=
      (Complex.continuous_re.comp Q.continuous).continuousOn
    obtain ⟨t, -, ht⟩ := (PreconnectedSpace.isPreconnected_univ (α := I)).intermediate_value₂
      (show (0:I) ∈ (univ : Set I) from trivial) (show (1:I) ∈ (univ : Set I) from trivial)
      (f := fun t : I => (Q t).re) (g := fun _ : I => (0:ℝ))
      hf continuousOn_const (by rw [Path.source]; norm_num) (by rw [Path.target]; norm_num)
    exact ⟨Q t, ⟨⟨t, rfl⟩, ⟨ht, (hQrect t).2⟩⟩⟩
  obtain ⟨q, hq, hqmin⟩ :=
    (hQcompact.inter_right VSeg_closed).exists_isMinOn hQseg_ne Complex.continuous_im.continuousOn
  have hqQ : q ∈ Set.range Q := hq.1
  have hqV : q ∈ VSeg := hq.2
  have hq_re : q.re = 0 := hqV.1
  have hq_ne1 : q ≠ 1 := by intro h; have := hqV.1; rw [h] at this; norm_num at this
  have hq_nem1 : q ≠ -1 := by intro h; have := hqV.1; rw [h] at this; norm_num at this
  have hq_im_gt : (-2:ℝ) < q.im := by
    refine lt_of_le_of_ne hqV.2.1 (fun h => ?_)
    have hqBd : q ∈ RectBd := Or.inr (Or.inr (Or.inr h.symm))
    rcases hKBd q (hQsubK hqQ) hqBd with h1 | h1
    · exact hq_ne1 h1
    · exact hq_nem1 h1
  have hqK : q ∈ Set.range γ := hQsubK hqQ
  have hpK : p ∈ Set.range γ := hQsubK hpQ
  have hq_le_p : q.im ≤ p.im := isMinOn_iff.mp hqmin p ⟨hpQ, hpV⟩
  have hq_lt_m : q.im < m.im := lt_of_le_of_lt hq_le_p hp_im_lt
  -- ## the ray of the vertical segment below `q` lies in the unbounded component
  have hS1_Kc : ∀ w : ℂ, w.re = 0 → w.im < q.im → w ∉ Set.range γ := by
    intro w hwr hwi hwK
    have hwV : w ∈ VSeg := ⟨hwr, ⟨(hKsub hwK).2.1, (hKsub hwK).2.2⟩⟩
    have hw2' : w ∈ Set.range P ∪ Set.range Q := by rw [hPQrange]; exact hwK
    rcases hw2' with hwP | hwQ
    · exact absurd (isMinOn_iff.mp hmmin w ⟨hwP, hwV⟩) (not_le.mpr (lt_trans hwi hq_lt_m))
    · exact absurd (isMinOn_iff.mp hqmin w ⟨hwQ, hwV⟩) (not_le.mpr hwi)
  have hS1cc : {z : ℂ | z.re = 0 ∧ z.im < q.im} ⊆ connectedComponentIn (Set.range γ)ᶜ Spt := by
    intro z hz
    have hseg : ∀ u : I, segPath Spt z u ∈ (Set.range γ)ᶜ := by
      intro u
      rw [Set.mem_compl_iff]
      refine hS1_Kc _ (segPath_re_eq_zero hSpt_re hz.1 u) ?_
      rw [segPath_im, hSpt_im]
      exact nnb_comb_lt hq_im_gt hz.2 u.2.1 u.2.2
    rw [nnb_cc_eq_of_segPath_mem hseg]
    exact mem_connectedComponentIn (by rw [Set.mem_compl_iff]; exact hS1_Kc z hz.1 hz.2)
  have hS1unb : ¬ Bornology.IsBounded {z : ℂ | z.re = 0 ∧ z.im < q.im} := by
    intro hb
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
    set M : ℝ := q.im - (|C| + |q.im| + 1) with hM
    have hz : (((M:ℝ)) * Complex.I) ∈ {z : ℂ | z.re = 0 ∧ z.im < q.im} := by
      constructor
      · simp
      · simp only [Complex.mul_I_im, Complex.ofReal_re]
        rw [hM]; linarith [abs_nonneg C, abs_nonneg q.im]
    have h2 := hC _ hz
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h2
    have hMnonpos : M ≤ 0 := by
      rw [hM]; linarith [le_abs_self q.im, abs_nonneg C, abs_nonneg q.im]
    rw [abs_of_nonpos hMnonpos, hM] at h2
    linarith [le_abs_self C, le_abs_self q.im, abs_nonneg C]
  have hccSpt_unbounded : ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ Spt) :=
    fun hb => hS1unb (hb.subset hS1cc)
  -- ## the ray of the vertical segment above `l` lies in the unbounded component
  have hl_im_lt_2 : l.im < 2 := by
    refine lt_of_le_of_ne hlV.2.2 (fun h => ?_)
    have hlBd : l ∈ RectBd := Or.inr (Or.inr (Or.inl h))
    rcases hKBd l hlK hlBd with h1 | h1
    · exact hl_ne1 h1
    · exact hl_nem1 h1
  have hS2_Kc : ∀ w : ℂ, w.re = 0 → l.im < w.im → w ∉ Set.range γ := by
    intro w hwr hwi hwK
    have hwV : w ∈ VSeg := ⟨hwr, ⟨(hKsub hwK).2.1, (hKsub hwK).2.2⟩⟩
    exact absurd (isMaxOn_iff.mp hlmax w ⟨hwK, hwV⟩) (not_le.mpr hwi)
  have hS2cc : {z : ℂ | z.re = 0 ∧ l.im < z.im} ⊆ connectedComponentIn (Set.range γ)ᶜ Npt := by
    intro z hz
    have hseg : ∀ u : I, segPath z Npt u ∈ (Set.range γ)ᶜ := by
      intro u
      rw [Set.mem_compl_iff]
      refine hS2_Kc _ (segPath_re_eq_zero hz.1 hNpt_re u) ?_
      rw [segPath_im, hNpt_im]
      exact nnb_lt_comb hz.2 hl_im_lt_2 u.2.1 u.2.2
    rw [← nnb_cc_eq_of_segPath_mem hseg]
    exact mem_connectedComponentIn (by rw [Set.mem_compl_iff]; exact hS2_Kc z hz.1 hz.2)
  have hS2unb : ¬ Bornology.IsBounded {z : ℂ | z.re = 0 ∧ l.im < z.im} := by
    intro hb
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
    set M : ℝ := l.im + (|C| + |l.im| + 1) with hM
    have hz : (((M:ℝ)) * Complex.I) ∈ {z : ℂ | z.re = 0 ∧ l.im < z.im} := by
      constructor
      · simp
      · simp only [Complex.mul_I_im, Complex.ofReal_re]
        rw [hM]; linarith [abs_nonneg C, abs_nonneg l.im]
    have h2 := hC _ hz
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h2
    have hMnonneg : 0 ≤ M := by
      rw [hM]; linarith [neg_abs_le l.im, abs_nonneg C, abs_nonneg l.im]
    rw [abs_of_nonneg hMnonneg, hM] at h2
    linarith [le_abs_self C, neg_abs_le l.im, abs_nonneg C]
  have hccNpt_unbounded : ¬ Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ Npt) :=
    fun hb => hS2unb (hb.subset hS2cc)
  -- ## the region strictly between `p` and `m` lies in the component of `z0`
  have hS3cc : {z : ℂ | z.re = 0 ∧ p.im < z.im ∧ z.im < m.im} ⊆
      connectedComponentIn (Set.range γ)ᶜ z0 := by
    intro z hz
    have hseg : ∀ u : I, segPath z0 z u ∈ (Set.range γ)ᶜ := by
      intro u
      rw [Set.mem_compl_iff]
      refine hpm_free _ (segPath_re_eq_zero hz0_re hz.1 u) ?_ ?_
      · rw [segPath_im]; exact nnb_lt_comb hz0_gt_p hz.2.1 u.2.1 u.2.2
      · rw [segPath_im]; exact nnb_comb_lt hz0_lt_m hz.2.2 u.2.1 u.2.2
    rw [nnb_cc_eq_of_segPath_mem hseg]
    exact mem_connectedComponentIn (by rw [Set.mem_compl_iff]; exact hpm_free z hz.1 hz.2.1 hz.2.2)
  -- ## the barrier path
  have hp_ne1 : p ≠ 1 := by intro h; have := hpV.1; rw [h] at this; norm_num at this
  have hp_nem1 : p ≠ -1 := by intro h; have := hpV.1; rw [h] at this; norm_num at this
  obtain ⟨tq, htq⟩ : ∃ tq : I, Q tq = q := hqQ
  obtain ⟨tp, htp⟩ : ∃ tp : I, Q tp = p := hpQ
  have htq0 : (tq:ℝ) ≠ 0 := by
    intro h0
    have h' : tq = 0 := Subtype.ext h0
    rw [h', Path.source] at htq
    exact hq_nem1 htq.symm
  have htq1 : (tq:ℝ) ≠ 1 := by
    intro h0
    have h' : tq = 1 := Subtype.ext h0
    rw [h', Path.target] at htq
    exact hq_ne1 htq.symm
  have htp0 : (tp:ℝ) ≠ 0 := by
    intro h0
    have h' : tp = 0 := Subtype.ext h0
    rw [h', Path.source] at htp
    exact hp_nem1 htp.symm
  have htp1 : (tp:ℝ) ≠ 1 := by
    intro h0
    have h' : tp = 1 := Subtype.ext h0
    rw [h', Path.target] at htp
    exact hp_ne1 htp.symm
  let Qsub : Path q p := (Q.subpath tq tp).cast htq.symm htp.symm
  let Psub : Path m l := (P.subpath am al).cast ham.symm hal.symm
  let β : Path Spt Npt :=
    (segPath Spt q).trans (Qsub.trans ((segPath p m).trans (Psub.trans (segPath l Npt))))
  have hmem5 : ∀ z : ℂ, z ∈ Set.range β ↔ z ∈ Set.range (segPath Spt q) ∨ z ∈ Set.range Qsub
      ∨ z ∈ Set.range (segPath p m) ∨ z ∈ Set.range Psub ∨ z ∈ Set.range (segPath l Npt) := by
    intro z
    have h : Set.range β = Set.range (segPath Spt q) ∪ Set.range Qsub ∪ Set.range (segPath p m)
        ∪ Set.range Psub ∪ Set.range (segPath l Npt) := by
      simp only [β, Path.trans_range]
      ext y; simp only [Set.mem_union]; tauto
    rw [h]; simp only [Set.mem_union]; tauto
  have hQsub_range : Set.range Qsub ⊆ Set.range Q := by
    intro z hz
    have h1 : z ∈ Set.range (Q.subpath tq tp) := by simpa [Qsub] using hz
    rw [Path.range_subpath] at h1
    obtain ⟨u, -, hu⟩ := h1
    exact ⟨u, hu⟩
  have hPsub_range : Set.range Psub ⊆ Set.range P := by
    intro z hz
    have h1 : z ∈ Set.range (P.subpath am al) := by simpa [Psub] using hz
    rw [Path.range_subpath] at h1
    obtain ⟨u, -, hu⟩ := h1
    exact ⟨u, hu⟩
  have hQsub_ne : ∀ u : I, Qsub u ≠ 1 ∧ Qsub u ≠ -1 := by
    intro u
    have h := subpath_ne_pm_one hQinj htq0 htq1 htp0 htp1 u
    simpa [Qsub] using h
  have hPsub_ne : ∀ u : I, Psub u ≠ 1 ∧ Psub u ≠ -1 := by
    intro u
    have h := subpath_ne_pm_one hPinj ham0 ham1 hal0 hal1 u
    simpa [Psub] using h
  have hsegSq_rect : Set.range (segPath Spt q) ⊆ Rect := by
    rintro z ⟨u, rfl⟩
    exact segPath_mem_Rect Spt_mem_Rect (VSeg_subset_Rect hqV) u
  have hQsub_rect : Set.range Qsub ⊆ Rect := fun z hz => hKsub (hQsubK (hQsub_range hz))
  have hsegpm_rect : Set.range (segPath p m) ⊆ Rect := by
    rintro z ⟨u, rfl⟩
    exact segPath_mem_Rect (VSeg_subset_Rect hpV) (VSeg_subset_Rect hmV) u
  have hPsub_rect : Set.range Psub ⊆ Rect := fun z hz => hKsub (hPsubK (hPsub_range hz))
  have hsegNpt_rect : Set.range (segPath l Npt) ⊆ Rect := by
    rintro z ⟨u, rfl⟩
    exact segPath_mem_Rect (VSeg_subset_Rect hlV) Npt_mem_Rect u
  have hsegSq_pm : ∀ z ∈ Set.range (segPath Spt q), z ≠ 1 ∧ z ≠ -1 := by
    rintro z ⟨u, rfl⟩
    have h := segPath_re_eq_zero hSpt_re hq_re u
    constructor
    · intro hcon; rw [hcon] at h; norm_num at h
    · intro hcon; rw [hcon] at h; norm_num at h
  have hQsub_pm : ∀ z ∈ Set.range Qsub, z ≠ 1 ∧ z ≠ -1 := by
    rintro z ⟨u, rfl⟩
    exact hQsub_ne u
  have hsegpm_pm : ∀ z ∈ Set.range (segPath p m), z ≠ 1 ∧ z ≠ -1 := by
    rintro z ⟨u, rfl⟩
    have h := segPath_re_eq_zero hpV.1 hm_re u
    constructor
    · intro hcon; rw [hcon] at h; norm_num at h
    · intro hcon; rw [hcon] at h; norm_num at h
  have hPsub_pm : ∀ z ∈ Set.range Psub, z ≠ 1 ∧ z ≠ -1 := by
    rintro z ⟨u, rfl⟩
    exact hPsub_ne u
  have hsegNpt_pm : ∀ z ∈ Set.range (segPath l Npt), z ≠ 1 ∧ z ≠ -1 := by
    rintro z ⟨u, rfl⟩
    have h := segPath_re_eq_zero hlV.1 hNpt_re u
    constructor
    · intro hcon; rw [hcon] at h; norm_num at h
    · intro hcon; rw [hcon] at h; norm_num at h
  have hβrect : ∀ t : I, β t ∈ Rect := by
    intro t
    have ht := (hmem5 (β t)).mp ⟨t, rfl⟩
    rcases ht with h | h | h | h | h
    · exact hsegSq_rect h
    · exact hQsub_rect h
    · exact hsegpm_rect h
    · exact hPsub_rect h
    · exact hsegNpt_rect h
  have hβ1 : ∀ t : I, β t ≠ 1 := by
    intro t hcon
    have ht := (hmem5 (β t)).mp ⟨t, rfl⟩
    rcases ht with h | h | h | h | h
    · exact (hsegSq_pm _ h).1 hcon
    · exact (hQsub_pm _ h).1 hcon
    · exact (hsegpm_pm _ h).1 hcon
    · exact (hPsub_pm _ h).1 hcon
    · exact (hsegNpt_pm _ h).1 hcon
  have hβm1 : ∀ t : I, β t ≠ -1 := by
    intro t hcon
    have ht := (hmem5 (β t)).mp ⟨t, rfl⟩
    rcases ht with h | h | h | h | h
    · exact (hsegSq_pm _ h).2 hcon
    · exact (hQsub_pm _ h).2 hcon
    · exact (hsegpm_pm _ h).2 hcon
    · exact (hPsub_pm _ h).2 hcon
    · exact (hsegNpt_pm _ h).2 hcon
  -- ## the key statement: every bounded component is the component of `z0`
  have key : ∀ y ∈ (Set.range γ)ᶜ, Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ y) →
      connectedComponentIn (Set.range γ)ᶜ y = connectedComponentIn (Set.range γ)ᶜ z0 := by
    intro y hy hyb
    by_contra hne
    have hnotpre : ¬ IsPreconnected (Set.range γ)ᶜ := by
      intro hpre
      have hsub : (Set.range γ)ᶜ ⊆ connectedComponentIn (Set.range γ)ᶜ y :=
        hpre.subset_connectedComponentIn hy (subset_refl _)
      have heq : connectedComponentIn (Set.range γ)ᶜ y = (Set.range γ)ᶜ :=
        Subset.antisymm (connectedComponentIn_subset _ _) hsub
      exact hKc_unbounded (heq ▸ hyb)
    have hfront : frontier (connectedComponentIn (Set.range γ)ᶜ y) = Set.range γ :=
      Commons.Topology.Connected.frontier_component_compl_range γ hγ hnotpre y hy
    have hWopen : IsOpen (connectedComponentIn (Set.range γ)ᶜ y) := hKc_open.connectedComponentIn
    have hWpc : IsPreconnected (connectedComponentIn (Set.range γ)ᶜ y) :=
      isPreconnected_connectedComponentIn
    have hWne : (connectedComponentIn (Set.range γ)ᶜ y).Nonempty :=
      ⟨y, mem_connectedComponentIn hy⟩
    have hWsub : connectedComponentIn (Set.range γ)ᶜ y ⊆ Rect :=
      nnb_bounded_component_subset_Rect hKsub hyb
    have h1cl : (1:ℂ) ∈ closure (connectedComponentIn (Set.range γ)ᶜ y) :=
      frontier_subset_closure (by rw [hfront]; exact h1)
    have hm1cl : (-1:ℂ) ∈ closure (connectedComponentIn (Set.range γ)ᶜ y) :=
      frontier_subset_closure (by rw [hfront]; exact hm1)
    have hsegSq_W : ∀ z ∈ Set.range (segPath Spt q), z ∉ connectedComponentIn (Set.range γ)ᶜ y := by
      rintro z ⟨u, rfl⟩ htW
      have htJ : segPath Spt q u ∉ Set.range γ := connectedComponentIn_subset _ _ htW
      have hzre : (segPath Spt q u).re = 0 := segPath_re_eq_zero hSpt_re hq_re u
      have hzim : (segPath Spt q u).im ≤ q.im := by
        rw [segPath_im, hSpt_im]; nlinarith [hq_im_gt, u.2.1, u.2.2]
      rcases lt_or_eq_of_le hzim with hlt | heq
      · exact hccSpt_unbounded (((connectedComponentIn_eq (hS1cc ⟨hzre, hlt⟩)).trans
          ((connectedComponentIn_eq htW).symm)) ▸ hyb)
      · have hq_eq : segPath Spt q u = q := Complex.ext (by rw [hzre, hq_re]) heq
        rw [hq_eq] at htJ
        exact htJ hqK
    have hQsub_W : ∀ z ∈ Set.range Qsub, z ∉ connectedComponentIn (Set.range γ)ᶜ y := by
      intro z hz htW
      exact (connectedComponentIn_subset _ _ htW) (hQsubK (hQsub_range hz))
    have hsegpm_W : ∀ z ∈ Set.range (segPath p m), z ∉ connectedComponentIn (Set.range γ)ᶜ y := by
      rintro z ⟨u, rfl⟩ htW
      have htJ : segPath p m u ∉ Set.range γ := connectedComponentIn_subset _ _ htW
      have hzre : (segPath p m u).re = 0 := segPath_re_eq_zero hpV.1 hm_re u
      have hz1 : p.im ≤ (segPath p m u).im := by
        rw [segPath_im]; nlinarith [hp_im_lt, u.2.1]
      have hz2 : (segPath p m u).im ≤ m.im := by
        rw [segPath_im]; nlinarith [hp_im_lt, u.2.2]
      rcases lt_or_eq_of_le hz1 with hlt1 | heq1
      · rcases lt_or_eq_of_le hz2 with hlt2 | heq2
        · exact hne ((connectedComponentIn_eq htW).trans
            (connectedComponentIn_eq (hS3cc ⟨hzre, hlt1, hlt2⟩)).symm)
        · have hm_eq : segPath p m u = m := Complex.ext (by rw [hzre, hm_re]) heq2
          rw [hm_eq] at htJ
          exact htJ (hPsubK hmP)
      · have hp_eq : segPath p m u = p := Complex.ext (by rw [hzre, hpV.1]) heq1.symm
        rw [hp_eq] at htJ
        exact htJ hpK
    have hPsub_W : ∀ z ∈ Set.range Psub, z ∉ connectedComponentIn (Set.range γ)ᶜ y := by
      intro z hz htW
      exact (connectedComponentIn_subset _ _ htW) (hPsubK (hPsub_range hz))
    have hsegNpt_W : ∀ z ∈ Set.range (segPath l Npt), z ∉ connectedComponentIn (Set.range γ)ᶜ y := by
      rintro z ⟨u, rfl⟩ htW
      have htJ : segPath l Npt u ∉ Set.range γ := connectedComponentIn_subset _ _ htW
      have hzre : (segPath l Npt u).re = 0 := segPath_re_eq_zero hlV.1 hNpt_re u
      have hzim : l.im ≤ (segPath l Npt u).im := by
        rw [segPath_im, hNpt_im]; nlinarith [hl_im_lt_2, u.2.1]
      rcases lt_or_eq_of_le hzim with hlt | heq
      · exact hccNpt_unbounded (((connectedComponentIn_eq (hS2cc ⟨hzre, hlt⟩)).trans
          ((connectedComponentIn_eq htW).symm)) ▸ hyb)
      · have hl_eq : segPath l Npt u = l := Complex.ext (by rw [hzre, hl_re]) heq.symm
        rw [hl_eq] at htJ
        exact htJ hlK
    have hβW : ∀ t : I, β t ∉ connectedComponentIn (Set.range γ)ᶜ y := by
      intro t
      have ht := (hmem5 (β t)).mp ⟨t, rfl⟩
      rcases ht with h | h | h | h | h
      · exact hsegSq_W _ h
      · exact hQsub_W _ h
      · exact hsegpm_W _ h
      · exact hPsub_W _ h
      · exact hsegNpt_W _ h
    exact nnb_no_component_across_barrier hWopen hWpc hWne hWsub h1cl hm1cl β hβrect hβW hβ1 hβm1
  intro x hx hxb y hy hyb
  rw [key x hx hxb, key y hy hyb]

end

end Commons.Topology.Jordan
