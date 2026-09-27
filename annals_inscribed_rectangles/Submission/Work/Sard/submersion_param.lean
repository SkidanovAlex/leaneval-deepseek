import Mathlib

namespace Work.Sard

/-- **Submersion parametrisation.**  Let `u : E → G` be smooth with `fderiv ℝ u x₀` surjective, and let
`C` be a complement of `ker (fderiv ℝ u x₀)`. Then the level sets of `u` near `x₀` are parametrised by
`Φ : G × ker (fderiv ℝ u x₀) → E`: `Φ` is smooth near the base point, `u (Φ y) = y.1` there, and `Φ` is a
local left inverse of `x ↦ (u x, π x)` where `π` is the projection onto `ker (fderiv ℝ u x₀)` along `C`.

Proof sketch: put `K := (fderiv ℝ u x₀).ker`, `π := Submodule.projectionOnto K C hC : E →ₗ[ℝ] K`, and
`Θ := fun x : E => (u x, π x) : E → G × K`.  Then `Θ` is smooth (`ContDiff ℝ ∞`), `fderiv ℝ Θ x₀` is
injective since its kernel is `K ⊓ ker π = K ⊓ C = ⊥`, and the domain and codomain have the same finite
dimension (`finrank ℝ E = finrank ℝ G + finrank ℝ K` because `fderiv ℝ u x₀` is surjective and
`K = ker`; use `LinearMap.finrank_range_add_finrank_ker` and `Submodule.finrank_add_eq_of_isCompl` for
`K` and `C`), so it is an isomorphism; build
`e : E ≃L[ℝ] G × K` with `ContinuousLinearEquiv.ofBijective` from its linear map and bijectivity.  Then
`ContDiffAt.localInverse` applied to `Θ` at `x₀` with the `HasFDerivAt` derived from `e` gives a global
`Φ : G × K → E`; `Φ (Θ x₀) = x₀`, `ContDiffAt ℝ ∞ Φ (Θ x₀)` and the two eventual properties are
`localInverse_apply_image`, `ContDiffAt.to_localInverse` and
`HasStrictFDerivAt.eventually_right_inverse` / `eventually_left_inverse` (with
`ContDiff ℝ ∞ u` giving `HasStrictFDerivAt Θ (fderiv ℝ Θ x₀) x₀` via `ContDiff.hasStrictFDerivAt`).
Note `(Submodule.projectionOnto K C hC) x₀` is the second component of `Θ x₀`, and `u x₀` its first. -/
theorem submersion_param {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (u : E → G) (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u) (x₀ : E)
    (hsurj : Function.Surjective (fderiv ℝ u x₀))
    (C : Submodule ℝ E) (hC : IsCompl (fderiv ℝ u x₀).ker C) :
    ∃ Φ : G × (fderiv ℝ u x₀).ker → E,
      Φ (u x₀, (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC) x₀) = x₀ ∧
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
        (u x₀, (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC) x₀) ∧
      (∀ᶠ y in nhds (u x₀, (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC) x₀),
        u (Φ y) = y.1) ∧
      (∀ᶠ x in nhds x₀,
        Φ (u x, (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC) x) = x) := by
  classical
  -- `fderiv ℝ u x₀` is surjective, hence onto `G`.
  have hAu : (fderiv ℝ u x₀).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  -- The projection `π` onto `K` along `C`, as a *continuous* linear map.
  have hπ : (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC).range = ⊤ :=
    LinearMap.range_eq_top.mpr (Submodule.projectionOnto_surjective hC)
  let π : E →L[ℝ] (fderiv ℝ u x₀).ker :=
    LinearMap.toContinuousLinearMap (Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC)
  have hπrange : (π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker).range = ⊤ := by
    rw [show (π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker) =
      Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC from
      LinearMap.coe_toContinuousLinearMap _]
    exact hπ
  have hπker : (π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker).ker = C := by
    rw [show (π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker) =
      Submodule.projectionOnto (fderiv ℝ u x₀).ker C hC from
      LinearMap.coe_toContinuousLinearMap _]
    exact Submodule.ker_projectionOnto hC
  have hcompl : IsCompl ((fderiv ℝ u x₀) : E →ₗ[ℝ] G).ker
      (π : E →ₗ[ℝ] (fderiv ℝ u x₀).ker).ker := by
    rw [hπker]
    exact hC
  -- The linear iso `E ≃L[ℝ] G × K` given by `x ↦ (fderiv ℝ u x₀ x, π x)`.
  let e : E ≃L[ℝ] G × (fderiv ℝ u x₀).ker :=
    (fderiv ℝ u x₀).equivProdOfSurjectiveOfIsCompl π hAu hπrange hcompl
  have hcoe : (e : E →L[ℝ] G × (fderiv ℝ u x₀).ker) = (fderiv ℝ u x₀).prod π := rfl
  -- `Θ x = (u x, π x)`.
  let Θ : E → G × (fderiv ℝ u x₀).ker := fun x => (u x, π x)
  have hΘc : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ x₀ :=
    (hu.contDiffAt).prodMk (π.contDiff.contDiffAt)
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hΘderiv : HasFDerivAt Θ (e : E →L[ℝ] G × (fderiv ℝ u x₀).ker) x₀ := by
    have h1 : HasFDerivAt u (fderiv ℝ u x₀) x₀ :=
      (hu.differentiable hn).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun x => π x) π x₀ := π.hasFDerivAt
    have h3 : HasFDerivAt (fun x => (u x, π x)) ((fderiv ℝ u x₀).prod π) x₀ := h1.prodMk h2
    rw [hcoe]
    exact h3
  let Φ : G × (fderiv ℝ u x₀).ker → E := hΘc.localInverse (f' := e) hΘderiv hn
  have hΘs : HasStrictFDerivAt Θ (e : E →L[ℝ] G × (fderiv ℝ u x₀).ker) x₀ :=
    hΘc.hasStrictFDerivAt' hΘderiv hn
  have hΦeq : Φ = hΘs.localInverse Θ e x₀ := rfl
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · rw [hΦeq]
    exact hΘs.localInverse_apply_image
  · exact hΘc.to_localInverse (f' := e) hΘderiv hn
  · rw [hΦeq]
    filter_upwards [hΘs.eventually_right_inverse] with y hy
    exact congrArg Prod.fst hy
  · rw [hΦeq]
    filter_upwards [hΘs.eventually_left_inverse] with x hx
    exact hx

end Work.Sard
