import Mathlib

/-!
# A nondegenerate compact connected Hausdorff space is uncountable

This is used in the equichordal point problem: the cluster set of a non-convergent path in the
torus `ℂ*/λ^ℤ` is a nondegenerate continuum, hence uncountable, which supplies the uncountably
many values needed for the final contradiction in Rychlik's Theorem 11.
-/

open Filter _root_.Topology MeasureTheory

/-- **A nondegenerate compact connected Hausdorff space is uncountable.**  (A countable compact
Hausdorff space is totally disconnected: Urysohn's lemma separates any two points by a continuous
map to `[0,1]`, whose image would be a countable connected subset of `ℝ` with more than one point.)
-/
theorem not_countable_of_isPreconnected_isCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    {s : Set X} (hs : IsPreconnected s) (hc : IsCompact s)
    (hne : ∃ x ∈ s, ∃ y ∈ s, x ≠ y) : ¬ s.Countable := by
  intro hcount
  obtain ⟨x, hxs, y, hys, hxy⟩ := hne
  haveI : CompactSpace ↥s := isCompact_iff_compactSpace.mp hc
  haveI : PreconnectedSpace ↥s := isPreconnected_iff_preconnectedSpace.mp hs
  haveI : NormalSpace ↥s := inferInstance
  obtain ⟨f, hf0, hf1, -⟩ := exists_continuous_zero_one_of_isClosed
    (s := {(⟨x, hxs⟩ : ↥s)}) (t := {(⟨y, hys⟩ : ↥s)}) isClosed_singleton isClosed_singleton
    (by
      rw [Set.disjoint_singleton]
      exact fun h => hxy (Subtype.ext_iff.mp h))
  have hfcont : Continuous f := f.continuous
  have himg : IsPreconnected (f '' (Set.univ : Set ↥s)) := isPreconnected_univ.image f hfcont.continuousOn
  have h0 : (0 : ℝ) ∈ f '' (Set.univ : Set ↥s) := ⟨⟨x, hxs⟩, trivial, by simpa using hf0 (by simp)⟩
  have h1 : (1 : ℝ) ∈ f '' (Set.univ : Set ↥s) := ⟨⟨y, hys⟩, trivial, by simpa using hf1 (by simp)⟩
  have hconv : Set.Icc (0 : ℝ) 1 ⊆ f '' (Set.univ : Set ↥s) := by
    intro t ht
    exact (himg.ordConnected.out h0 h1) ht
  haveI : Countable ↥s := hcount.to_subtype
  have hcnt : (f '' (Set.univ : Set ↥s)).Countable :=
    Set.countable_univ.image f
  have hIcc : (Set.Icc (0 : ℝ) 1).Countable := hcnt.mono hconv
  have hzero : volume (Set.Icc (0 : ℝ) 1) = 0 := hIcc.measure_zero volume
  rw [Real.volume_Icc] at hzero
  norm_num at hzero
