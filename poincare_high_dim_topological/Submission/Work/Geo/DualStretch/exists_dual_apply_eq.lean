import Mathlib

namespace Work.Geo.DualStretch

/-- Any linear functional prescribed on a linearly independent family extends to the whole
module: if `v : ι → M` is linearly independent over a field `R`, then every `c : ι → R`
is realized as the restriction of some linear map `M →ₗ[R] R`. -/
theorem exists_dual_apply_eq {R M ι : Type*} [Field R] [AddCommGroup M] [Module R M]
    {v : ι → M} (hv : LinearIndependent R v) (c : ι → R) :
    ∃ f : M →ₗ[R] R, ∀ i, f (v i) = c i := by
  classical
  -- `φ` reads off the coefficients of a vector of `span R (range v)` `(hv.repr)` and
  -- then evaluates `c` on them `(Finsupp.linearCombination R c)`.
  let φ : (Submodule.span R (Set.range v)) →ₗ[R] R :=
    (Finsupp.linearCombination R c).comp hv.repr
  -- Every linear map on a subspace of a vector space extends to the whole space.
  obtain ⟨g, hg⟩ := LinearMap.exists_extend φ
  refine ⟨g, fun i => ?_⟩
  have hmem : v i ∈ Submodule.span R (Set.range v) := Submodule.subset_span ⟨i, rfl⟩
  have key : g (v i) = φ ⟨v i, hmem⟩ := by
    have := LinearMap.congr_fun hg ⟨v i, hmem⟩
    simpa using this
  rw [key]
  have hrepr : hv.repr ⟨v i, hmem⟩ = Finsupp.single i 1 := hv.repr_eq_single i _ rfl
  simp [φ, hrepr]

end Work.Geo.DualStretch
