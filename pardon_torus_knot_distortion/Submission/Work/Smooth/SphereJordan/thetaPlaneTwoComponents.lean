import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.thetaGraph_two_components
import Submission.Work.Smooth.SphereJordan.twoComponentsOfSimpleClosed
import Submission.Work.Smooth.JordanSeparation.nonempty_planeSeparation
import Submission.Work.Topology.PlaneCurve.compl_jordan_atMostTwo

/-!
# The plane theta graph has exactly two complementary components

Two disjoint embedded discs `D₁`, `D₂` joined by two arcs `α`, `β` whose interiors avoid the discs
and each other: the complement of the union `D₁ ∪ D₂ ∪ range α ∪ range β` is the disjoint union of
two non-empty open preconnected sets.

The mathematical content is in `Submission.Work.Smooth.SphereJordan.thetaGraph_two_components`,
where it is proved *unconditionally* (the Jordan separation of the two simple closed theta curves
is supplied by `Work.Smooth.SphereJordan.exists_jsep`, and the "at most two components" half by the
winding-number side determination); the present file states the result in the form requested by the
sibling chapter.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-- **Jordan separation for a merely continuous simple closed plane curve.**

The companion of `compl_jordan_atMostTwo` (at most two components, proved in the workspace from
Maehara's rectangle setup) and of `twoComponentsOfSimpleClosed` (at least two components, proved
from `exists_bounded_component_of_rectSetup`): the two together give the two-sided separation of
the complement of `Set.range γ`, with the bounded side `V`.  This is the axiom-clean structural
tool that the theta-graph argument needs; it replaces `Work.Smooth.SphereJordan.exists_jsep`, whose
proof goes through the (still missing) shifted-chord certificate of Maehara's argument. -/
theorem nonempty_planeSeparation_of_continuous {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) :
    Nonempty (Work.Smooth.Jordan.PlaneSeparation ⟨γ, hγ, hper⟩) :=
  Work.Smooth.JordanSeparation.nonempty_planeSeparation ⟨γ, hγ, hper⟩ hinj
    (fun x y z hx hy hz =>
      Work.Topology.PlaneCurve.compl_jordan_atMostTwo hγ hper hinj hx hy hz)
    (twoComponentsOfSimpleClosed hγ hper hinj)

/-- **A bounded complementary component exists, for any continuous simple closed plane curve.**

This is Maehara's boundedness lemma `Work.Topology.PlaneCurve.exists_bounded_component_of_rectSetup`
(proved, axiom-clean, in the "rectangle setup"), transported back along the diameter similarity
`toUnitHomeo` and a parameter shift.  Together with `compl_jordan_atMostTwo` it shows that the
complement of the trace has exactly two components (see `twoComponentsOfSimpleClosed` and
`nonempty_planeSeparation_of_continuous`), and it is the structural input of the winding-number
side comparison. -/
theorem exists_bounded_component_of_isSimple {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) :
    ∃ x : ℂ, x ∉ Set.range γ ∧
      Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ x) := by
  obtain ⟨a, ha, b, hb, hab, hmax⟩ := exists_diam_pair hγ hper hinj
  obtain ⟨sa, hsa⟩ := ha
  obtain ⟨sb, hsb⟩ := hb
  set c : ℂ := (a + b) / 2 with hc
  set w : ℂ := (b - a) / 2 with hw
  have hwne : w ≠ 0 := by
    rw [hw]; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hab)) (by norm_num)
  set Φ : ℂ ≃ₜ ℂ := toUnitHomeo a b hab with hΦ
  have hΦapp : ∀ z : ℂ, Φ z = (z - c) / w := by
    intro z; rw [hΦ, toUnitHomeo_apply, hc, hw]; field_simp
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
  obtain ⟨s, hs⟩ := hm1
  set γ' : ℝ → ℂ := fun t => Φ (γ (t + s)) with hγ'def
  have hγ' : Continuous γ' := Φ.continuous.comp (hγ.comp (continuous_id.add continuous_const))
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
  have hxrange : x ∉ Set.range γ := by
    intro hx
    have h1 : Φ x ∈ Φ '' (Set.range γ) := ⟨x, hx, rfl⟩
    rw [hphi_range, hΦx] at h1
    exact hz₀ h1
  refine ⟨x, hxrange, ?_⟩
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := M * ‖w‖ + ‖c‖)).subset ?_
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  have hpre : IsPreconnected (Φ '' connectedComponentIn (Set.range γ)ᶜ x) :=
    isPreconnected_connectedComponentIn.image Φ Φ.continuous.continuousOn
  have hsub2 : Φ '' connectedComponentIn (Set.range γ)ᶜ x ⊆ (Set.range γ')ᶜ := by
    rw [← hcompl]; exact Set.image_mono (connectedComponentIn_subset _ _)
  have hz₀mem : z₀ ∈ Φ '' connectedComponentIn (Set.range γ)ᶜ x :=
    ⟨x, mem_connectedComponentIn hxrange, hΦx⟩
  have hmem : Φ u ∈ connectedComponentIn (Set.range γ')ᶜ z₀ :=
    hpre.subset_connectedComponentIn hz₀mem hsub2 ⟨u, hu, rfl⟩
  have h2 : ‖Φ u‖ ≤ M := hM _ hmem
  rw [hΦapp, norm_div, div_le_iff₀ (norm_pos_iff.mpr hwne)] at h2
  calc ‖u‖ = ‖(u - c) + c‖ := by ring_nf
    _ ≤ ‖u - c‖ + ‖c‖ := norm_add_le _ _
    _ ≤ M * ‖w‖ + ‖c‖ := by linarith

theorem thetaPlaneTwoComponents
    {D₁ D₂ : Set ℂ}
    (hD₁ : ∃ f : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Work.Smooth.SphereJordan.Disc, ℂ), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    ∃ P₁ P₂ : Set ℂ, P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β)ᶜ ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ :=
  thetaPlaneTwoComponentsUncond hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint
    hsep hαβ₀ hαβ₁

end

end Work.Smooth.SphereJordan
