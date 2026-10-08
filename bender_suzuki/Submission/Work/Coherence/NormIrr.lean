import Submission.Work.Coherence.Basic
import Submission.Work.Coherence.Isometry
import Submission.Work.Coherence.irr_cfInner
import Submission.Work.Coherence.irr_degree_pos
import Submission.Work.Coherence.norm_one_of_mem_zSpan
import Submission.Work.Coherence.norm_two_of_mem_zSpan
import Submission.Work.Coherence.norm_zero_of_mem_zSpan
import Submission.Work.Coherence.norm_two_diff_of_mem_zSpan

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Norm-one and norm-two virtual characters, and isometries of `ℤ[Irr G]`

The corollaries of the lattice-level norm lemmas for the actual lattice `ℤ[Irr G]` of virtual
characters of `G`:

* `irr_orthonormal_finset` — a finite set of irreducible characters is orthonormal (Schur
  orthogonality);
* `vchar_norm_one` — a virtual character of norm one is `±` an irreducible character (this is
  "an isometry sends `±Irr` to `±Irr`", since an isometry preserves norms);
* `vchar_norm_two` — a virtual character of norm two is `±χ ± ψ` with `χ ≠ ψ` irreducible
  (Feit–Thompson's basic remark in the proof of Lemma 10.1);
* `vchar_norm_two_deg_zero` — if in addition its degree is zero, it is a *difference* of two
  distinct irreducible characters;
* `vchar_norm_zero` — a virtual character of norm zero vanishes;
* `isometry_image_irr` — the image of an element of an orthonormal set under an isometry of
  `ℤ[S]` which happens to be a virtual character is `±` an irreducible character of `G`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.Coherence

universe u v

variable {G : Type*}

section IrrNorm

variable [Group G] [Fintype G]

/-- A finite set of irreducible characters is orthonormal. -/
theorem irr_orthonormal_finset {s : Finset (G → ℂ)} (hs : (↑s : Set (G → ℂ)) ⊆ Irr G) :
    Orthonormal s := fun _ hx _ hy => irr_cfInner (hs hx) (hs hy)

/-- A virtual character of norm one is `±` an irreducible character. -/
theorem vchar_norm_one {f : G → ℂ} (hf : IsVChar f) (h : cfInner f f = 1) :
    ∃ χ ∈ Irr G, f = χ ∨ f = -χ := by
  obtain ⟨s, hs, hfs⟩ := isVChar_iff.mp hf
  obtain ⟨χ, hχs, hcase⟩ := norm_one_of_mem_zSpan (irr_orthonormal_finset hs) hfs h
  exact ⟨χ, hs hχs, hcase⟩

/-- A virtual character of norm two is `±χ ± ψ` for two distinct irreducible characters. -/
theorem vchar_norm_two {f : G → ℂ} (hf : IsVChar f) (h : cfInner f f = 2) :
    ∃ χ ∈ Irr G, ∃ ψ ∈ Irr G, χ ≠ ψ ∧
      (f = χ + ψ ∨ f = -(χ + ψ) ∨ f = χ - ψ ∨ f = ψ - χ) := by
  obtain ⟨s, hs, hfs⟩ := isVChar_iff.mp hf
  obtain ⟨χ, hχs, ψ, hψs, hne, hcase⟩ := norm_two_of_mem_zSpan (irr_orthonormal_finset hs) hfs h
  exact ⟨χ, hs hχs, ψ, hs hψs, hne, hcase⟩

/-- A virtual character of norm two and degree zero is the difference of two distinct
irreducible characters. -/
theorem vchar_norm_two_deg_zero {f : G → ℂ} (hf : IsVChar f) (h1 : f 1 = 0)
    (h : cfInner f f = 2) :
    ∃ χ ∈ Irr G, ∃ ψ ∈ Irr G, χ ≠ ψ ∧ (f = χ - ψ ∨ f = ψ - χ) := by
  obtain ⟨s, hs, hfs⟩ := isVChar_iff.mp hf
  have hdeg : ∀ z ∈ s, 1 ≤ (z 1).re := by
    intro z hz
    obtain ⟨n, hn, hzn⟩ := irr_degree_pos (hs hz)
    have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnr : (1 : ℝ) ≤ ((n : ℂ).re) := by simpa using h1n
    rwa [hzn]
  obtain ⟨χ, hχs, ψ, hψs, hne, hcase⟩ :=
    norm_two_diff_of_mem_zSpan (irr_orthonormal_finset hs) hfs h1 hdeg h
  exact ⟨χ, hs hχs, ψ, hs hψs, hne, hcase⟩

/-- A virtual character of norm zero vanishes. -/
theorem vchar_norm_zero {f : G → ℂ} (hf : IsVChar f) (h : cfInner f f = 0) : f = 0 := by
  obtain ⟨s, hs, hfs⟩ := isVChar_iff.mp hf
  exact norm_zero_of_mem_zSpan (irr_orthonormal_finset hs) hfs h

end IrrNorm

section IsometryImage

variable [Group G] [Fintype G] {G' : Type*} [Group G'] [Fintype G']

/-- **An isometry sends `±Irr` to `±Irr`.**  If `τ` is an isometry of `ℤ[S]` (`S` orthonormal) and
`τ χ` is a virtual character of `G'` for some `χ ∈ S`, then `τ χ` is `±` an irreducible character
of `G'`. -/
theorem isometry_image_irr {S : Finset (G → ℂ)} {τ : (G → ℂ) →ₗ[ℤ] (G' → ℂ)}
    (hS : Orthonormal S) (hτ : IsometryOnAll S τ) {χ : G → ℂ} (hχ : χ ∈ S)
    (hv : IsVChar (τ χ)) : ∃ ψ ∈ Irr G', τ χ = ψ ∨ τ χ = -ψ :=
  vchar_norm_one hv (by
    rw [hτ.inner_eq χ (self_mem_zSpan hχ) χ (self_mem_zSpan hχ), Orthonormal.cfInner_self hS hχ])

end IsometryImage

end Work.Coherence
