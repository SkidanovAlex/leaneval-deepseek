import Mathlib

namespace Work.WilE7.FrontierCS

/-- **N1a.** A zero of an analytic square system whose differential is surjective (hence, the
domain and codomain having the same dimension, invertible) is isolated.

Analyticity gives a *strict* derivative `HasStrictFDerivAt g (fderiv ℝ g e) e`.  Surjectivity of
the differential together with `finrank (Fin j → ℝ) = finrank (Fin j → ℝ)` makes it injective,
so it upgrades to a continuous linear equivalence `L`.  The inverse function theorem
(`HasStrictFDerivAt.toOpenPartialHomeomorph`) then exhibits `g` as an injective map on an open
neighbourhood of `e`, which is exactly the statement. -/
theorem eventually_ne_of_range_top {j : ℕ} {g : (Fin j → ℝ) → (Fin j → ℝ)} {e : Fin j → ℝ}
    (hg : AnalyticAt ℝ g e) (hrk : (fderiv ℝ g e).range = ⊤) :
    Filter.Eventually (fun e' => g e' ≠ g e) (nhdsWithin e {e}ᶜ) := by
  -- An analytic function has a strict derivative.
  have hstr : HasStrictFDerivAt g (fderiv ℝ g e) e := hg.hasStrictFDerivAt
  -- The differential is injective: it is surjective and domain/codomain have equal dimension.
  have hker : (↑(fderiv ℝ g e) : (Fin j → ℝ) →ₗ[ℝ] (Fin j → ℝ)).ker = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (↑(fderiv ℝ g e) : (Fin j → ℝ) →ₗ[ℝ] (Fin j → ℝ))
    rw [hrk, finrank_top, Module.finrank_fin_fun] at h1
    omega
  -- Upgrade the differential to a continuous linear equivalence.
  let L : (Fin j → ℝ) ≃L[ℝ] (Fin j → ℝ) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℝ g e) hker hrk
  have hstr' : HasStrictFDerivAt g (L : (Fin j → ℝ) →L[ℝ] (Fin j → ℝ)) e := by
    rw [show (L : (Fin j → ℝ) →L[ℝ] (Fin j → ℝ)) = fderiv ℝ g e from
      ContinuousLinearEquiv.coe_ofBijective _ _ _]
    exact hstr
  -- The inverse function theorem: `g` is injective on an open neighbourhood of `e`.
  let φ := hstr'.toOpenPartialHomeomorph g
  have hmem : e ∈ φ.source := hstr'.mem_toOpenPartialHomeomorph_source
  have hinjOn : Set.InjOn g φ.source := by
    have h := φ.injOn
    rwa [show (φ : (Fin j → ℝ) → (Fin j → ℝ)) = g from rfl] at h
  rw [eventually_nhdsWithin_iff]
  filter_upwards [IsOpen.mem_nhds φ.open_source hmem] with x hx hxe
  exact fun hgx => hxe (hinjOn hx hmem hgx)

end Work.WilE7.FrontierCS
