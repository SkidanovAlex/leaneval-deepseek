import Mathlib
import Submission.Work.ORP311.P311Defs

/-!
# A vector supported in the Følner window with vanishing coset blocks is zero

`Work.ORP311.ell2Sub n Z` is the closed span of the vectors `e_i ⊗ δ_g ∈ ℓ²(G)ⁿ` with `g ∈ Z`,
and `Work.ORP311.P311.blk n N t j` is the orthogonal projection onto `ell2Sub n (coset N t j)`,
the space "supported on the right `N`-coset `N t ^ j`".

The window `X_m = Work.ORP311.window N t m = ⋃_{|j| ≤ m} N t^j` is exactly the union of those
cosets (`Work.ORP311.window_eq_iUnion_coset`), so the generators of `ell2Sub n X_m` are the union
of the generators of the `ell2Sub n (coset N t j)`, `|j| ≤ m`.  Hence a vector `η` that lies in
`ell2Sub n X_m` and whose projection onto each of these coset subspsaces vanishes must itself
vanish: `η` is orthogonal to every generator of `ell2Sub n X_m`, hence to its closure, and since
`η` itself lies in that closure, `⟪η, η⟫ = 0`.
-/

namespace Work.ORP311

/-- **A vector in the window whose every coset block vanishes is zero.**

If `η ∈ ell2Sub n (window N t m)` and `blk n N t j η = 0` for every `j` with `|j| ≤ m`, then
`η = 0`. -/
theorem eq_zero_of_blk_eq_zero {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {N : Subgroup G} {t : G} (n m : ℕ) {η : Work.ORVonNeumann.Rep.HSum (G := G) n} (hη : η ∈ Work.ORP311.ell2Sub (G := G) n (Work.ORP311.window N t m)) (h0 : ∀ j : ℤ, -(m : ℤ) ≤ j → j ≤ m → Work.ORP311.P311.blk n N t j η = 0) : η = 0 := by
  -- A vanishing block projection is orthogonality to the corresponding coset subspace.
  have horth : ∀ j : ℤ, -(m : ℤ) ≤ j → j ≤ (m : ℤ) →
      η ∈ (ell2Sub (G := G) n (coset N t j))ᗮ := by
    intro j hj1 hj2
    exact (Submodule.starProjection_apply_eq_zero_iff _).mp (h0 j hj1 hj2)
  -- Hence `η` is orthogonal to every generator of the window subspace.
  have hwin : ∀ g ∈ window N t m, ∀ i : Fin n,
      inner ℂ (Work.ORVonNeumann.Rep.hcoord (G := G) n i η) (Work.ORVonNeumann.Rep.deltaG g) = 0 := by
    intro g hg i
    obtain ⟨n', j, hj1, hj2, rfl⟩ := hg
    have hgen : Work.ORVonNeumann.Rep.hinclude (G := G) n i
        (Work.ORVonNeumann.Rep.deltaG ((n' : N) * t ^ j)) ∈
        ell2Sub (G := G) n (coset N t j) :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(n' : N) * t ^ j, ⟨n', rfl⟩, i, rfl⟩)
    have h1 : inner ℂ (Work.ORVonNeumann.Rep.hinclude (G := G) n i
        (Work.ORVonNeumann.Rep.deltaG ((n' : N) * t ^ j))) η = 0 :=
      (Submodule.mem_orthogonal _ _).mp (horth j hj1 hj2) _ hgen
    rw [inner_hinclude] at h1
    exact (inner_eq_zero_comm _ _).mp h1
  -- So `η` lies in the orthogonal complement of the window subspace.
  have hmem : η ∈ (ell2Sub (G := G) n (window N t m))ᗮ := by
    have heq : (ell2Sub (G := G) n (window N t m))ᗮ
        = ell2Sub (G := G) n (window N t m)ᶜ := by
      rw [ell2Sub_orthogonal (G := G) n (window N t m)ᶜ, compl_compl]
    rw [heq, mem_ell2Sub_iff]
    intro g hg i
    exact hwin g (by simpa using hg) i
  -- Since `η` also lies in the window subspace, it is orthogonal to itself.
  have h2 : inner ℂ η η = 0 := (Submodule.mem_orthogonal _ _).mp hmem η hη
  exact inner_self_eq_zero.mp h2

end Work.ORP311
