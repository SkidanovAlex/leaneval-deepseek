import Mathlib
import Submission.Work.HornCov.covering_of_components
import Submission.Work.HornCov.discreteTopology_fiber
import Submission.Work.HornCov.eq_of_section_of_isLocalHomeomorphOn
import Submission.Work.HornCov.isOpenEmbedding_of_section_of_isLocalHomeomorphOn

/-!
# `Work.HornCov.isCoveringMapOn_of_sections`

A map `p : X → ℂ` out of a Hausdorff space which is a local homeomorphism over `p ⁻¹' S`
(that is, on the preimage of an open, preconnected `S ⊆ ℂ`), and through every point of
`p ⁻¹' S` of which there passes a *global continuous section over `S`*, is a covering map over
`S`.

The construction is the classical one.  Fix a point `x₀ ∈ p ⁻¹' S` and let `y₀ = p x₀`.
For each point `i` of the fibre `p ⁻¹' {y₀}` choose a continuous section `σ i : ↥S → X` through
`i`.  Then

* `σ i` is an open embedding (`isOpenEmbedding_of_section_of_isLocalHomeomorphOn`), so its range
  `C i` is open and `p` restricts to a homeomorphism `C i ≃ₜ S`;
* the ranges are pairwise disjoint and their union is exactly `p ⁻¹' S`: given `w ∈ p ⁻¹' S` and a
  section `τ` through `w`, the chosen section through `τ y₀` agrees with `τ` at `y₀`, so by
  `eq_of_section_of_isLocalHomeomorphOn` (which needs `S` preconnected and `X` Hausdorff) the two
  sections are equal and `w ∈ range (σ ⟨τ y₀, _⟩)`.

Hence `p ⁻¹' S` is a disjoint union of open "sheets" each mapped homeomorphically onto `S`, and
`covering_of_components` converts this decomposition into `IsCoveringMapOn p S`.
-/

set_option linter.style.haveILetI false

namespace Work.HornCov

theorem isCoveringMapOn_of_sections {X : Type*} [TopologicalSpace X] [T2Space X]
    {p : X → ℂ} {S : Set ℂ} (hSopen : IsOpen S) (hSconn : IsPreconnected S)
    (hloc : IsLocalHomeomorphOn p (p ⁻¹' S))
    (hsec : ∀ x : X, ∀ hx : p x ∈ S, ∃ σ : ↥S → X, Continuous σ ∧
      (∀ u : ↥S, p (σ u) = (u : ℂ)) ∧ σ ⟨p x, hx⟩ = x) :
    IsCoveringMapOn p S := by
  rcases Set.eq_empty_or_nonempty (p ⁻¹' S) with h_empty | h_ne
  · -- `p ⁻¹' S = ∅`: every fibre above `S` is empty and therefore evenly covered.
    intro y hy
    haveI : IsEmpty (p ⁻¹' {y}) := Set.isEmpty_coe_sort.mpr
      (Set.eq_empty_of_subset_empty
        ((Set.preimage_mono (Set.singleton_subset_iff.mpr hy)).trans h_empty.le))
    exact IsEvenlyCovered.of_preimage_eq_empty (p ⁻¹' {y}) (hSopen.mem_nhds hy) h_empty
  · -- `p ⁻¹' S ≠ ∅`: the fibre over `y₀ = p x₀` indexes the sheets.
    obtain ⟨x₀, hx₀⟩ := h_ne
    have hy₀ : p x₀ ∈ S := hx₀
    haveI : DiscreteTopology ↥(p ⁻¹' {p x₀}) := discreteTopology_fiber hloc hy₀
    -- one section through each point of the fibre over `y₀`
    have hsec' : ∀ i : ↥(p ⁻¹' {p x₀}), ∃ σ : ↥S → X, Continuous σ ∧
        (∀ u : ↥S, p (σ u) = (u : ℂ)) ∧ σ ⟨p x₀, hy₀⟩ = (i : X) := by
      intro i
      have hi : p (i : X) ∈ S := by rw [i.2]; exact hy₀
      obtain ⟨σ, h1, h2, h3⟩ := hsec (i : X) hi
      refine ⟨σ, h1, h2, ?_⟩
      have hval : ((⟨p x₀, hy₀⟩ : ↥S) : ℂ) = p (i : X) := by rw [i.2]
      have hsub : (⟨p x₀, hy₀⟩ : ↥S) = ⟨p (i : X), hi⟩ := Subtype.ext hval
      exact (congrArg σ hsub).trans h3
    choose σ hσcont hσsec hσy using hsec'
    -- each `σ i` is an open embedding, so `p` is a homeomorphism on its range
    have hσemb : ∀ i, Topology.IsOpenEmbedding (σ i) := fun i =>
      isOpenEmbedding_of_section_of_isLocalHomeomorphOn hSopen hloc (hσcont i) (hσsec i)
    let G : ∀ i : ↥(p ⁻¹' {p x₀}), ↥S ≃ₜ ↥(Set.range (σ i)) :=
      fun i => (hσemb i).toIsEmbedding.toHomeomorph
    refine covering_of_components hSopen (fun i => Set.range (σ i))
      (fun i => (hσemb i).isOpen_range) ?_ ?_ (fun i => (G i).symm) ?_
    · -- the sheets are pairwise disjoint
      intro i j hij
      rw [Set.disjoint_left]
      rintro z ⟨u, rfl⟩ ⟨u', hu'⟩
      have huu : u = u' := by
        refine Subtype.ext ?_
        rw [← hσsec i u, ← hσsec j u', hu']
      have heq : σ i u = σ j u := by
        have h2 : σ j u = σ j u' := by rw [huu]
        rw [h2]; exact hu'.symm
      have hfun := eq_of_section_of_isLocalHomeomorphOn hSopen hSconn hloc
        (hσcont i) (hσcont j) (hσsec i) (hσsec j) heq
      have : (i : X) = (j : X) := by rw [← hσy i, ← hσy j, hfun]
      exact hij (Subtype.ext this)
    · -- the sheets cover `p ⁻¹' S`
      ext w
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_range]
      constructor
      · intro hw
        obtain ⟨τ, hτcont, hτsec, hτw⟩ := hsec w hw
        let i₀ : ↥(p ⁻¹' {p x₀}) :=
          ⟨τ ⟨p x₀, hy₀⟩,
            by simp only [Set.mem_preimage, Set.mem_singleton_iff]; rw [hτsec]⟩
        have hagree : σ i₀ ⟨p x₀, hy₀⟩ = τ ⟨p x₀, hy₀⟩ := by rw [hσy i₀]
        have hfun := eq_of_section_of_isLocalHomeomorphOn hSopen hSconn hloc
          (hσcont i₀) hτcont (hσsec i₀) hτsec hagree
        exact ⟨i₀, ⟨p w, hw⟩, by rw [hfun]; exact hτw⟩
      · rintro ⟨i, u, hu⟩
        rw [← hu, hσsec i u]
        exact u.2
    · -- `p` restricted to a sheet is the inverse of the corresponding section
      intro i z
      obtain ⟨u, hu⟩ := z.2
      have hz : z = (hσemb i).toIsEmbedding.toHomeomorph u := by
        apply Subtype.ext
        rw [Topology.IsEmbedding.toHomeomorph_apply_coe]
        exact hu.symm
      change (((G i).symm z : ↥S) : ℂ) = p (z : X)
      rw [hz, Topology.IsEmbedding.toHomeomorph_apply_coe, hσsec i u]
      exact congrArg Subtype.val (Homeomorph.symm_apply_apply _ u)

end Work.HornCov
