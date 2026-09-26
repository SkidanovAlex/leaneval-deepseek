import Mathlib
import Submission.Work.Topology.PlaneCurve.exists_bounded_component_of_rectSetup
import Submission.Work.Smooth.SphereJordan.jordan_compl_atMostTwo
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic
import Submission.Work.Topology.PlaneCurve.frontier_component_eq_range

/-!
# A continuous simple closed plane curve has at least two complementary components

The companion of `Work.Topology.PlaneCurve.compl_jordan_atMostTwo`, which gives the *at most two*
half: here we prove that a continuous `2π`-periodic curve `γ : ℝ → ℂ` which is injective on one
period has two points off its trace lying in *different* connected components of the complement.

This is the `hatLeast` input of `Work.Smooth.JordanSeparation.nonempty_planeSeparation` (which
turns "at most two" + "at least two" into a `Work.Smooth.Jordan.PlaneSeparation`), and it is the
missing "at least two" half for *merely continuous* (not `C¹`) Jordan curves -- for `C¹` curves the
same statement is `Work.Smooth.JordanSeparation.SimpleCurves.exists_two_components_of_isSimple`,
proved there by the index jump at a regular point.

## Route

No winding number is needed, and hence nothing beyond the axiom-clean part of the workspace:

* `Work.Smooth.SphereJordan.exists_diam_pair` + `toUnitHomeo` is the diameter similarity, which
  carries the trace into the closed rectangle `[-1,1] × [-2,2]` touching `±1` (the normalised
  "rectangle setup" of `Work.Topology.PlaneCurve`);
* shifting the parameter (which does not change the trace) puts `γ 0 = -1`;
* `Work.Topology.PlaneCurve.exists_bounded_component_of_rectSetup` (Maehara's boundedness lemma)
  then provides a point `z₀` off the trace whose complementary component is *bounded*;
* pulling `z₀` back along the similarity gives a point `x` off the trace of `γ` whose component is
  bounded (its image lies in the component of `z₀`), while a point `y` of sufficiently large norm
  has an unbounded component; bounded and unbounded components are different.
-/

open Set

namespace Work.Smooth.SphereJordan


theorem twoComponentsOfSimpleClosed {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) :
    ∃ x y : ℂ, x ∉ Set.range γ ∧ y ∉ Set.range γ ∧
      connectedComponentIn (Set.range γ)ᶜ x ≠ connectedComponentIn (Set.range γ)ᶜ y := by
  -- ## Step 1: the diameter similarity
  obtain ⟨a, ha, b, hb, hab, hmax⟩ := exists_diam_pair hγ hper hinj
  obtain ⟨sa, hsa⟩ := ha
  obtain ⟨sb, hsb⟩ := hb
  set c : ℂ := (a + b) / 2 with hc
  set w : ℂ := (b - a) / 2 with hw
  have hwne : w ≠ 0 := by
    rw [hw]; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hab)) (by norm_num)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set Φ : ℂ ≃ₜ ℂ := toUnitHomeo a b hab with hΦ
  have hΦapp : ∀ z : ℂ, Φ z = (z - c) / w := by
    intro z
    rw [hΦ, toUnitHomeo_apply, hc, hw]
    field_simp
  have hsub : ∀ t : ℝ, (γ t - c) / w ∈ Work.Topology.PlaneCurve.rectR ∨
      (γ t - c) / w = -1 ∨ (γ t - c) / w = 1 := by
    intro t
    obtain ⟨hza, hzb⟩ := hmax (γ t) ⟨t, rfl⟩
    obtain ⟨h1, h2⟩ := toUnit_norm_bounds (z := γ t) hab hzb hza
    obtain ⟨hre, hre1, him⟩ := re_im_data h1 h2
    have key : Φ (γ t) = (γ t - c) / w := hΦapp (γ t)
    rw [key] at hre hre1 him
    rcases lt_trichotomy |((γ t - c) / w).re| 1 with hlt | heq | hgt
    · refine Or.inl ?_
      rw [Work.Topology.PlaneCurve.rectR]
      exact ⟨(abs_lt.mp hlt).1, (abs_lt.mp hlt).2, (abs_lt.mp him).1, (abs_lt.mp him).2⟩
    · rcases hre1 heq with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · exact absurd hgt (not_lt.mpr hre)
  have hm1 : ∃ t : ℝ, (γ t - c) / w = -1 := by
    refine ⟨sa, ?_⟩
    rw [hsa, ← hΦapp]; exact toUnitHomeo_neg_one a b hab
  -- ## Step 2: shift the parameter to start at `-1`
  obtain ⟨s, hs⟩ := hm1
  set γ' : ℝ → ℂ := fun t => Φ (γ (t + s)) with hγ'def
  have hγ' : Continuous γ' :=
    Φ.continuous.comp (hγ.comp (continuous_id.add continuous_const))
  have hper' : Function.Periodic γ' (2 * Real.pi) := by
    intro t
    show Φ (γ (t + 2 * Real.pi + s)) = Φ (γ (t + s))
    rw [show t + 2 * Real.pi + s = (t + s) + 2 * Real.pi by ring, hper]
  have hsub' : ∀ u ∈ Set.range γ', u ∈ Work.Topology.PlaneCurve.rectR ∨ u = -1 ∨ u = 1 := by
    rintro u ⟨t, rfl⟩
    have h : γ' t = (γ (t + s) - c) / w := hΦapp (γ (t + s))
    rw [h]; exact hsub (t + s)
  have hzero' : γ' 0 = -1 := by
    show Φ (γ (0 + s)) = -1
    rw [zero_add, hΦapp]; exact hs
  have hpos' : (1 : ℂ) ∈ Set.range γ' := by
    refine ⟨sb - s, ?_⟩
    show Φ (γ (sb - s + s)) = 1
    rw [sub_add_cancel, hsb, hΦ]; exact toUnitHomeo_one a b hab
  have hinj' : Set.InjOn γ' (Set.Ico 0 (2 * Real.pi)) := by
    intro u hu v hv huv
    have huv' : γ (u + s) = γ (v + s) := Φ.injective huv
    obtain ⟨k, hk⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj huv'
    have h2 : (k : ℝ) * (2 * Real.pi) = (u + s) - (v + s) := by linarith [hk]
    have h3 : |u - v| < 2 * Real.pi := by
      rw [abs_lt]; exact ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
    have hk0 : k = 0 := by
      by_contra hkne
      have h4 : (1 : ℝ) ≤ |(k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hkne
      have h5 : 2 * Real.pi ≤ |(u + s) - (v + s)| := by
        rw [← h2, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        nlinarith [h4, Real.pi_pos]
      rw [show (u + s) - (v + s) = u - v by ring] at h5
      linarith
    rw [hk0] at h2
    simp only [Int.cast_zero, zero_mul] at h2
    linarith
  -- ## Step 3: Maehara's bounded component, in the same picture
  obtain ⟨z₀, hz₀re, hz₀, hbdd⟩ :=
    Work.Topology.PlaneCurve.exists_bounded_component_of_rectSetup hγ' hper' hinj' hsub' hzero' hpos'
  obtain ⟨M, hM⟩ := hbdd.exists_norm_le
  set x : ℂ := z₀ * w + c with hxdef
  have hΦx : Φ x = z₀ := by
    rw [hΦapp]
    show (z₀ * w + c - c) / w = z₀
    rw [add_sub_cancel_right]
    field_simp
  have hphi_range : Φ '' (Set.range γ) = Set.range γ' := by
    ext v; constructor
    · rintro ⟨z, ⟨u, rfl⟩, rfl⟩
      exact ⟨u - s, by rw [hγ'def]; congr 1; ring⟩
    · rintro ⟨t, rfl⟩
      exact ⟨γ (t + s), ⟨t + s, rfl⟩, rfl⟩
  have hcompl : Φ '' (Set.range γ)ᶜ = (Set.range γ')ᶜ := by
    ext v; constructor
    · rintro ⟨y, hy, rfl⟩ hv
      obtain ⟨t, ht⟩ := hv
      have h2 : γ (t + s) = y := by
        apply Φ.injective
        rw [hγ'def] at ht
        exact ht
      exact hy ⟨t + s, h2⟩
    · intro hv
      refine ⟨Φ.symm v, ?_, Φ.apply_symm_apply v⟩
      intro hy
      obtain ⟨t, ht⟩ := hy
      refine hv ⟨t - s, ?_⟩
      show Φ (γ (t - s + s)) = v
      rw [sub_add_cancel, ht, Φ.apply_symm_apply]
  -- a far point
  obtain ⟨R, hR⟩ := (Work.Topology.PlaneCurve.isCompact_range_of_periodic hγ hper).isBounded.exists_norm_le
  set R₁ : ℝ := max (max R 0) (M * ‖w‖ + ‖c‖) with hR₁def
  set y : ℂ := ((R₁ + 1 : ℝ) : ℂ) with hydef
  have hynorm : ‖y‖ = R₁ + 1 := by
    rw [hydef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hyrange : y ∉ Set.range γ := by
    rintro ⟨t, ht⟩
    have h1 : ‖γ t‖ ≤ R := hR _ ⟨t, rfl⟩
    rw [ht, hynorm] at h1
    have h4 : R ≤ R₁ := le_trans (le_max_left R 0) (le_max_left _ _)
    linarith
  have hxrange : x ∉ Set.range γ := by
    intro hx
    have h1 : Φ x ∈ Φ '' (Set.range γ) := ⟨x, hx, rfl⟩
    rw [hphi_range, hΦx] at h1
    exact hz₀ h1
  -- ## Step 4: the two components differ
  refine ⟨x, y, hxrange, hyrange, ?_⟩
  intro heq
  have hCy : connectedComponentIn (Set.range γ)ᶜ y ⊆ (Set.range γ)ᶜ :=
    connectedComponentIn_subset _ _
  have hpre : IsPreconnected (Φ '' connectedComponentIn (Set.range γ)ᶜ y) :=
    isPreconnected_connectedComponentIn.image Φ Φ.continuous.continuousOn
  have hsub : Φ '' connectedComponentIn (Set.range γ)ᶜ y ⊆ (Set.range γ')ᶜ := by
    rw [← hcompl]; exact Set.image_mono hCy
  have hxmem : x ∈ connectedComponentIn (Set.range γ)ᶜ y := by
    rw [← heq]; exact mem_connectedComponentIn hxrange
  have hz₀mem : z₀ ∈ Φ '' connectedComponentIn (Set.range γ)ᶜ y := ⟨x, hxmem, hΦx⟩
  have hymem : Φ y ∈ Φ '' connectedComponentIn (Set.range γ)ᶜ y :=
    ⟨y, mem_connectedComponentIn hyrange, rfl⟩
  have hmem : Φ y ∈ connectedComponentIn (Set.range γ')ᶜ z₀ :=
    hpre.subset_connectedComponentIn hz₀mem hsub hymem
  have h2 : ‖y - c‖ ≤ M * ‖w‖ := by
    have h3 := hM _ hmem
    rw [hΦapp, norm_div, div_le_iff₀ (norm_pos_iff.mpr hwne)] at h3
    exact h3
  have h1 : ‖y‖ ≤ M * ‖w‖ + ‖c‖ := by
    calc ‖y‖ = ‖(y - c) + c‖ := by ring_nf
      _ ≤ ‖y - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ M * ‖w‖ + ‖c‖ := by linarith
  rw [hynorm] at h1
  have h4 : M * ‖w‖ + ‖c‖ ≤ R₁ := le_max_right _ _
  linarith

end Work.Smooth.SphereJordan
