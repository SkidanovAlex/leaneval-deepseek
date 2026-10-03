import Mathlib

namespace Work.Horn

/-- **Local biholomorphicity of a holomorphic function with nonvanishing derivative.**

If `f` is complex differentiable on the open set `D`, `B ⊆ D` is open, `c ∈ B` and `deriv f c ≠ 0`,
then `f` is a local homeomorphism at `c` whose source can be taken inside `B`: there is an
`OpenPartialHomeomorph` of `ℂ` whose underlying function is *exactly* `f`, whose source contains
`c` and is contained in `B`.

The proof is the inverse function theorem: analyticity of `f` at `c` (from differentiability on the
open `D`) gives a strict derivative, nonzero derivative makes it invertible as a `ℂ`-linear map,
`HasStrictFDerivAt.toOpenPartialHomeomorph` produces a partial homeomorphism with `toFun = f`, and
restricting its source to the open set `B` (via `OpenPartialHomeomorph.restrOpen`) keeps `toFun = f`
while shrinking the source into `B`. -/
theorem localBiholo_source_subset {f : ℂ → ℂ} {D B : Set ℂ} (hD : IsOpen D) (hB : IsOpen B)
    (hBD : B ⊆ D) (hfD : DifferentiableOn ℂ f D) {c : ℂ} (hc : c ∈ B) (hne : deriv f c ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ B ∧ (⇑e : ℂ → ℂ) = f := by
  have hcD : c ∈ D := hBD hc
  -- `f` is analytic at `c`, hence has a strict derivative there
  have hana : AnalyticAt ℂ f c := hfD.analyticAt (hD.mem_nhds hcD)
  have hstrict : HasStrictDerivAt f (deriv f c) c := hana.hasStrictDerivAt
  -- the derivative, nonzero by hypothesis, is invertible as a `ℂ`-linear map
  have hfd : HasStrictFDerivAt f
      (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv f c) hne) : ℂ →L[ℂ] ℂ) c :=
    hstrict.hasStrictFDerivAt_equiv hne
  -- inverse function theorem: a partial homeomorphism whose function is exactly `f`
  let e₀ : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph f
  have hce₀ : c ∈ e₀.source := hfd.mem_toOpenPartialHomeomorph_source
  refine ⟨e₀.restrOpen B hB, ?_, ?_, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨hce₀, hc⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_subset_right
  · rw [OpenPartialHomeomorph.coe_restrOpen]
    exact hfd.toOpenPartialHomeomorph_coe

end Work.Horn
