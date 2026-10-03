/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (JZLA20 Proposition 3.11)

# `ell2Sub n Z` is the orthogonal complement of `ell2Sub n Zᶜ`

`Work.ORP311.ell2Sub n Z` (defined in `Submission/Work/ORP311/LuckDim.lean`) is the closed span
of the vectors `e_i ⊗ δ_g ∈ ℓ²(G)ⁿ` with `g ∈ Z`.  The family `p ↦ e_{p.2} ⊗ δ_{p.1}`, indexed
by `G × Fin n`, is a Hilbert basis (`Work.ORP311.piLp_l2_hilbertBasis`), and the index set
`Z` corresponds to `{p : G × Fin n | p.1 ∈ Z}`, whose complement is
`{p : G × Fin n | p.1 ∈ Zᶜ}`.  For a Hilbert basis the closed span of the part of the basis
indexed by a set is the orthogonal complement of the closed span of the part indexed by the
complement, which is the statement proved here.

## Main results

* `Work.ORP311.hilbertBasis_span_image_orthogonal` — the general statement for a Hilbert basis;
* `Work.ORP311.ell2Sub_orthogonal` — `ell2Sub n Z = (ell2Sub n Zᶜ)ᗮ`.
-/
import Mathlib
import Submission.Work.ORP311.LuckDim
import Submission.Work.ORVonNeumann.Rep.HilbertBasis
import Submission.Work.ORP311.piLp_l2_hilbertBasis

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace InnerProduct
open Filter

namespace Work.ORP311

open Work.ORVonNeumann

/-- **A Hilbert-basis splitting.**  If `b` is a Hilbert basis of a complete inner product space
`E` over `ℂ`, then for any set `S` of indices the closed span of `b '' S` is the orthogonal
complement of the closed span of `b '' Sᶜ`.

The two closed subspaces are orthogonal because distinct basis vectors are orthogonal, and their
sum is everything because it contains the span of the whole basis, which is dense; the second
inclusion is obtained from the expansion `x = ∑' p, ⟪b p, x⟫ • b p` of an arbitrary vector. -/
theorem hilbertBasis_span_image_orthogonal {α E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (b : HilbertBasis α ℂ E) (S : Set α) :
    (Submodule.span ℂ (b '' S)).topologicalClosure
      = ((Submodule.span ℂ (b '' Sᶜ)).topologicalClosure)ᗮ := by
  classical
  -- `span (b '' S)` is orthogonal to `span (b '' Sᶜ)`: on generators this is orthonormality.
  have key : Submodule.span ℂ (b '' S) ≤ (Submodule.span ℂ (b '' Sᶜ))ᗮ := by
    rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]
    rintro u ⟨p, hp, rfl⟩ v ⟨q, hq, rfl⟩
    exact b.orthonormal.inner_eq_zero (by rintro rfl; exact hq hp)
  refine le_antisymm ?_ ?_
  · -- the orthogonal complement is closed, so the closure is contained in it
    rw [Submodule.orthogonal_closure]
    exact Submodule.topologicalClosure_minimal (Submodule.span ℂ (b '' S)) key
      (Submodule.isClosed_orthogonal (Submodule.span ℂ (b '' Sᶜ)))
  · -- conversely, a vector orthogonal to the `Sᶜ`-part has a basis expansion supported on `S`
    intro x hx
    rw [Submodule.mem_orthogonal] at hx
    have hterm : ∀ p ∈ Sᶜ, (b.repr x) p = 0 := by
      intro p hp
      rw [b.repr_apply_apply]
      exact hx (b p) (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨p, hp, rfl⟩))
    have hfun : (fun p => (b.repr x) p • b p)
        = fun p => (if p ∈ S then (b.repr x) p else 0) • b p := by
      funext p
      by_cases hp : p ∈ S
      · rw [if_pos hp]
      · rw [if_neg hp, hterm p hp, zero_smul]
    have hsum := b.hasSum_repr x
    rw [hfun] at hsum
    refine mem_closure_of_tendsto hsum (Eventually.of_forall fun s => ?_)
    simp only [SetLike.mem_coe]
    refine Submodule.sum_mem _ fun p hp => ?_
    by_cases hps : p ∈ S
    · rw [if_pos hps]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, hps, rfl⟩)
    · rw [if_neg hps, zero_smul]
      exact Submodule.zero_mem _

/-- The image of `{p : G × Fin n | p.1 ∈ Z}` under the basis-indexing map
`p ↦ e_{p.2} ⊗ δ_{p.1}` is exactly the generating set of `ell2Sub n Z`. -/
theorem piLpBasisVec_image {G : Type*} [Group G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (Z : Set G) :
    piLpBasisVec G n '' {p : G × Fin n | p.1 ∈ Z}
      = {x | ∃ g ∈ Z, ∃ i : Fin n,
          x = Work.ORVonNeumann.Rep.hinclude (G := G) n i
            (Work.ORVonNeumann.Rep.deltaG g)} := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, hp, p.2, rfl⟩
  · rintro ⟨g, hg, i, rfl⟩
    exact ⟨(g, i), hg, rfl⟩

theorem ell2Sub_orthogonal {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (n : ℕ) (Z : Set G) : Work.ORP311.ell2Sub (G := G) n Z = (Work.ORP311.ell2Sub (G := G) n Zᶜ)ᗮ := by
  classical
  -- the Hilbert basis of `ℓ²(G)ⁿ ≅ ⨁_{i : Fin n} ℓ²(G)` whose vectors are `e_i ⊗ δ_g`
  have hcoe : ⇑(HilbertBasis.mkOfOrthogonalEqBot (orthonormal_piLpBasisVec (G := G) n)
      (span_piLpBasisVec_orthogonal_eq_bot (G := G) n)) = piLpBasisVec G n :=
    HilbertBasis.coe_mkOfOrthogonalEqBot _ _
  have hmain := hilbertBasis_span_image_orthogonal
      (HilbertBasis.mkOfOrthogonalEqBot (orthonormal_piLpBasisVec (G := G) n)
        (span_piLpBasisVec_orthogonal_eq_bot (G := G) n))
      {p : G × Fin n | p.1 ∈ Z}
  rw [hcoe] at hmain
  rw [ell2Sub, ell2Sub]
  rw [← piLpBasisVec_image n Z, ← piLpBasisVec_image n Zᶜ]
  exact hmain

end Work.ORP311
