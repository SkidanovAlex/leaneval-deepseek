import Mathlib
import Submission.Work.ORVonNeumann.Rep.HilbertBasis
import Submission.Work.ORVonNeumann.Rep

namespace Work.ORVonNeumann.Rep

/-- **Lifting `ℓ²(H)` into `ℓ²(G)` along the coset `H * q`.**

`{δ_h : h : ↥H}` is a Hilbert basis of `ℓ²(H)` and `{δ_{h q}}` is an orthonormal family in `ℓ²(G)`
(the map `h ↦ h q` is injective), so there is a linear isometry of `ℓ²(H)` into `ℓ²(G)` carrying
`δ_h` to `δ_{h q}`.  Concretely it is the composite of the coordinates map
`ℓ²(H) ≃ₗᵢ ℓ²(↥H, ℂ)` with the Hilbert-sum embedding of the orthogonal family
`LinearIsometry.toSpanSingleton ℂ (ℓ²(G)) ⟨δ_{h q}, 1⟩`. -/
theorem exists_cosetLiftIso {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (H : Subgroup G) (q : G) : ∃ e : Work.ORVonNeumann.l2 ↥H →ₗᵢ[ℂ] Work.ORVonNeumann.l2 G, ∀ h : ↥H, e (Work.ORVonNeumann.Rep.deltaG h) = Work.ORVonNeumann.Rep.deltaG ((h : G) * q) := by
  classical
  -- The family `h ↦ δ_{h q}` in `ℓ²(G)` is orthonormal, since `h ↦ h q` is injective.
  have hw : Orthonormal ℂ (fun h : ↥H => Work.ORVonNeumann.Rep.deltaG ((h : G) * q)) :=
    ⟨fun h => Work.ORVonNeumann.Rep.norm_deltaG ((h : G) * q),
     fun h k hhk => Work.ORVonNeumann.Rep.inner_deltaG_of_ne
       (fun hc => hhk (Subtype.ext (mul_right_cancel hc)))⟩
  refine ⟨(hw.orthogonalFamily).linearIsometry.comp
      (Work.ORVonNeumann.Rep.deltaGHilbertBasis (G := ↥H)).repr.toLinearIsometry,
    fun h => ?_⟩
  simp only [LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry]
  rw [show (Work.ORVonNeumann.Rep.deltaGHilbertBasis (G := ↥H)).repr
        (Work.ORVonNeumann.Rep.deltaG h) = lp.single 2 h (1 : ℂ) from by
      rw [← Work.ORVonNeumann.Rep.deltaGHilbertBasis_apply h, HilbertBasis.repr_self]]
  rw [OrthogonalFamily.linearIsometry_apply_single, LinearIsometry.toSpanSingleton_apply, one_smul]

end Work.ORVonNeumann.Rep
