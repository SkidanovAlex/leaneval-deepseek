import Mathlib
import Submission.Work.WilE7.FrontierCS.Defs
import Submission.Work.WilE7.FrontierCS.gc_defs
import Submission.Work.WilE7.FrontierCS.mem_closure_preimage

namespace Work.WilE7.FrontierCS

/-- The chart `Φ(t,e) = γ t + B e` has, at `(τ, 0)`, strict derivative `sliceDeriv γ B τ` and
value `γ τ`.  Hence if that derivative is invertible (bijective) and `γ τ` lies in the closure of
`W`, the point `(τ, 0)` lies in the closure of the preimage `Φ ⁻¹' W`. -/
theorem gc_closure_preimage {N d j : ℕ} {γ : (Fin d → ℝ) → (Fin N → ℝ)}
    (hγ : AnalyticOnNhd ℝ γ Set.univ) {B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ)}
    {W : Set (Fin N → ℝ)} {τ : Fin d → ℝ}
    (hBij : Function.Bijective (Work.WilE7.FrontierCS.sliceDeriv γ B τ))
    (h : γ τ ∈ closure W) :
    (τ, (0 : Fin j → ℝ)) ∈
      closure ((fun p : (Fin d → ℝ) × (Fin j → ℝ) => γ p.1 + B p.2) ⁻¹' W) := by
  -- View the (bijective) strict derivative as a continuous linear *equivalence* `L`.
  have hker : ((Work.WilE7.FrontierCS.sliceDeriv γ B τ :
      ((Fin d → ℝ) × (Fin j → ℝ)) →ₗ[ℝ] (Fin N → ℝ))).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hBij.1
  have hrange : ((Work.WilE7.FrontierCS.sliceDeriv γ B τ :
      ((Fin d → ℝ) × (Fin j → ℝ)) →ₗ[ℝ] (Fin N → ℝ))).range = ⊤ :=
    LinearMap.range_eq_top.mpr hBij.2
  let L : ((Fin d → ℝ) × (Fin j → ℝ)) ≃L[ℝ] (Fin N → ℝ) :=
    ContinuousLinearEquiv.ofBijective (Work.WilE7.FrontierCS.sliceDeriv γ B τ) hker hrange
  have hL : (L : ((Fin d → ℝ) × (Fin j → ℝ)) →L[ℝ] (Fin N → ℝ)) =
      Work.WilE7.FrontierCS.sliceDeriv γ B τ :=
    ContinuousLinearEquiv.coe_ofBijective _ hker hrange
  -- The strict derivative of the chart at `(τ, 0)`: split off the two summands.
  have hstrict : HasStrictFDerivAt (fun p : (Fin d → ℝ) × (Fin j → ℝ) => γ p.1 + B p.2)
      (Work.WilE7.FrontierCS.sliceDeriv γ B τ) (τ, 0) := by
    have h1 : HasStrictFDerivAt (fun p : (Fin d → ℝ) × (Fin j → ℝ) => γ p.1)
        ((fderiv ℝ γ τ).comp (ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin j → ℝ))) (τ, 0) :=
      (AnalyticAt.hasStrictFDerivAt (hγ τ (Set.mem_univ τ))).comp (τ, 0) hasStrictFDerivAt_fst
    have h2 : HasStrictFDerivAt (fun p : (Fin d → ℝ) × (Fin j → ℝ) => B p.2)
        (B.comp (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin j → ℝ))) (τ, 0) :=
      (ContinuousLinearMap.hasStrictFDerivAt B (x := (0 : Fin j → ℝ))).comp (τ, 0)
        hasStrictFDerivAt_snd
    have hsum := h1.add h2
    simpa [Work.WilE7.FrontierCS.sliceDeriv] using hsum
  -- The value of the chart at `(τ, 0)` is `γ τ`, which lies in the closure of `W`.
  have hΦp : (fun p : (Fin d → ℝ) × (Fin j → ℝ) => γ p.1 + B p.2) (τ, 0) ∈ closure W := by
    simpa using h
  exact mem_closure_preimage (Φ := fun p : (Fin d → ℝ) × (Fin j → ℝ) => γ p.1 + B p.2)
    (L := L) (by rw [hL]; exact hstrict) hΦp

end Work.WilE7.FrontierCS
