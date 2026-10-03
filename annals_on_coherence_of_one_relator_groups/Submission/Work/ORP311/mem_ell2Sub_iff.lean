/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORP311 area (JZLA20 Proposition 3.11, the Følner/Lück analytic input)

# Membership in the window-supported subspace `ell2Sub n Z`

`Work.ORP311.ell2Sub n Z` is the closed span of the vectors `e_i ⊗ δ_g`, `g ∈ Z`, `i : Fin n`,
of the finite `ℓ²`-sum `HSum n = ⊕_{i : Fin n} ℓ²(G)`.  This module identifies its elements:

  `x ∈ ell2Sub n Z ↔ ∀ g ∉ Z, ∀ i, ⟪hcoord n i x, δ_g⟫ = 0`,

i.e. `x` has no component along a `δ_g` with `g` outside the window.  This is the elementary
"complement of a basis sub-family" description used by the Følner/Lück argument to compute the
transversal dimension `tDim` on the pieces `X_k ∖ T_k`.

The general Hilbert-basis statement behind it is
`Work.ORP311.mem_topologicalClosure_span_image_compl_iff`: for a Hilbert basis `b : ι → E` of a
complete inner product space and a set `J` of indices, the closed span of the vectors with index
in `Jᶜ` is exactly the set of vectors orthogonal to all `b k`, `k ∈ J`.  Applying it to the
Hilbert basis `hsumHilbertBasis n` of `HSum n` (the family `(g, i) ↦ e_i ⊗ δ_g`) with
`J = {p | p.1 ∉ Z}` gives the claim.
-/
import Mathlib
import Submission.Work.ORP311.LuckDim
import Submission.Work.ORP311.piLp_l2_hilbertBasis

set_option autoImplicit false

open scoped InnerProductSpace InnerProduct

namespace Work.ORP311

open Work.ORVonNeumann

/-- **Characterisation of the closed span of a sub-family of a Hilbert basis.**

If `b` is a Hilbert basis of a complete inner product space `E` and `J ⊆ ι`, then the closed span
of the basis vectors indexed by `Jᶜ` is the set of vectors orthogonal to every basis vector
indexed by `J`.

The forward implication is that each `y ↦ ⟪b k, y⟫` is continuous and vanishes on the span; the
converse uses the Hilbert basis expansion `u = ∑' k, ⟪b k, u⟫ • b k` and
`Submodule.orthogonal_orthogonal_eq_closure`: for `u` orthogonal to the span of the `Jᶜ`-vectors,
every term of `∑' k, ⟪u, b k⟫ * ⟪b k, x⟫` vanishes, so `⟪u, x⟫ = 0`. -/
theorem mem_topologicalClosure_span_image_compl_iff {ι : Type*} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) (J : Set ι) (x : E) :
    x ∈ (Submodule.span ℂ (b '' Jᶜ)).topologicalClosure ↔ ∀ k ∈ J, inner ℂ (b k) x = 0 := by
  constructor
  · intro hx k hk
    have hsub : Submodule.span ℂ (b '' Jᶜ) ≤ (ℂ ∙ b k)ᗮ := by
      rw [Submodule.span_le]
      rintro _ ⟨l, hl, rfl⟩
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        (b.orthonormal.2 (fun h => hl (h ▸ hk)))
    have hle := Submodule.topologicalClosure_minimal (Submodule.span ℂ (b '' Jᶜ)) hsub
      (Submodule.isClosed_orthogonal (ℂ ∙ b k))
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hx)
  · intro hx
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h1 : ∀ k ∈ Jᶜ, inner ℂ u (b k) = 0 := by
      intro k hk
      exact (Submodule.mem_orthogonal' _ u).mp hu (b k)
        (Submodule.subset_span ⟨k, hk, rfl⟩)
    have hterm : ∀ k : ι, inner ℂ u (b k) * inner ℂ (b k) x = 0 := by
      intro k
      by_cases hk : k ∈ Jᶜ
      · rw [h1 k hk, zero_mul]
      · simp only [Set.mem_compl_iff, not_not] at hk
        rw [hx k hk, mul_zero]
    rw [← b.tsum_inner_mul_inner u x]
    simp [hterm]

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-- **The Hilbert basis of `HSum n` given by the vectors `e_i ⊗ δ_g`**, indexed by `G × Fin n`.
This is `Work.ORP311.piLp_l2_hilbertBasis`, made into a named basis so that its vectors can be
identified with `hinclude n i (deltaG g)`. -/
noncomputable def hsumHilbertBasis (n : ℕ) :
    HilbertBasis (G × Fin n) ℂ (Rep.HSum (G := G) n) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_piLpBasisVec (G := G) n)
    (span_piLpBasisVec_orthogonal_eq_bot (G := G) n)

/-- The `(g, i)`-th vector of `hsumHilbertBasis n` is `e_i ⊗ δ_g = hinclude n i (deltaG g)`. -/
theorem hsumHilbertBasis_apply (n : ℕ) (p : G × Fin n) :
    hsumHilbertBasis (G := G) n p = Rep.hinclude (G := G) n p.2 (Rep.deltaG p.1) := by
  rw [hsumHilbertBasis, HilbertBasis.coe_mkOfOrthogonalEqBot]
  rfl

/-- The pairing of `hinclude n i a` with `x` is the pairing of `a` with the `i`-th coordinate
of `x`. -/
theorem inner_hinclude (n : ℕ) (i : Fin n) (a : Work.ORVonNeumann.l2 G)
    (x : Rep.HSum (G := G) n) :
    inner ℂ (Rep.hinclude (G := G) n i a) x = inner ℂ a (Rep.hcoord (G := G) n i x) := by
  rw [show Rep.hinclude (G := G) n i a = PiLp.single 2 i a from rfl,
    inner_piLp_single (G := G) (n := n) i a x]
  exact congrArg (inner ℂ a) (Rep.hcoord_apply (G := G) n i x).symm

/-- Swapping the arguments of a vanishing inner product. -/
theorem inner_eq_zero_comm {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u v : E) : inner ℂ u v = 0 ↔ inner ℂ v u = 0 := by
  rw [← inner_conj_symm]
  exact star_eq_zero

theorem mem_ell2Sub_iff {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n : ℕ} {Z : Set G} (x : Work.ORVonNeumann.Rep.HSum (G := G) n) : x ∈ Work.ORP311.ell2Sub (G := G) n Z ↔ ∀ g : G, g ∉ Z → ∀ i : Fin n, inner ℂ (Work.ORVonNeumann.Rep.hcoord (G := G) n i x) (Work.ORVonNeumann.Rep.deltaG g) = 0 := by
  classical
  have hgen : (hsumHilbertBasis (G := G) n '' ({p : G × Fin n | p.1 ∉ Z}ᶜ) :
      Set (Rep.HSum (G := G) n))
      = {y : Rep.HSum (G := G) n |
          ∃ g ∈ Z, ∃ i : Fin n, y = Rep.hinclude (G := G) n i (Rep.deltaG g)} := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.1, ?_, p.2, hsumHilbertBasis_apply (G := G) n p⟩
      simpa using hp
    · rintro ⟨g, hg, i, rfl⟩
      refine ⟨(g, i), ?_, hsumHilbertBasis_apply (G := G) n (g, i)⟩
      simpa using hg
  have hE : ell2Sub (G := G) n Z
      = (Submodule.span ℂ
          (hsumHilbertBasis (G := G) n '' {p : G × Fin n | p.1 ∉ Z}ᶜ)).topologicalClosure := by
    rw [show ell2Sub (G := G) n Z = (Submodule.span ℂ
        {y : Rep.HSum (G := G) n |
          ∃ g ∈ Z, ∃ i : Fin n, y = Rep.hinclude (G := G) n i (Rep.deltaG g)}).topologicalClosure
        from rfl, ← hgen]
  rw [hE, mem_topologicalClosure_span_image_compl_iff]
  constructor
  · intro h g hg i
    have h1 : inner ℂ (hsumHilbertBasis (G := G) n (g, i)) x = 0 :=
      h (g, i) (by simpa using hg)
    rw [hsumHilbertBasis_apply, inner_hinclude] at h1
    exact (inner_eq_zero_comm (Rep.deltaG g) (Rep.hcoord (G := G) n i x)).mp h1
  · intro h p hp
    obtain ⟨g, i⟩ := p
    have hg : g ∉ Z := by simpa using hp
    rw [hsumHilbertBasis_apply, inner_hinclude]
    exact (inner_eq_zero_comm (Rep.deltaG g) (Rep.hcoord (G := G) n i x)).mpr (h g hg i)

end Work.ORP311
