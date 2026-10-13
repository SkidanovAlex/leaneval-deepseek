import Mathlib
import Submission.Work.WilE9.Defs

namespace Work.WilE9.EaD

/-- The derivative of the "branch" map `x ↦ Sum.elim x (fun j => exp (ℓ_j x))` into
`(Fin N ⊕ Fin r) → ℝ`: the `inl i` coordinate is `x i` and the `inr j` coordinate is
`exp (c.ell j x) = exp (∑ i, c.a j i * x i + c.b j)`. -/
theorem hasFDerivAt_br {N r : ℕ} (c : WilkiesDesign.E.EAChain N r) (v : Fin N → ℝ) :
    HasFDerivAt (fun x : Fin N → ℝ => Sum.elim x (fun j => Real.exp (c.ell j x)))
      (ContinuousLinearMap.pi (fun s : Fin N ⊕ Fin r =>
        Sum.elim (fun i => (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ))
          (fun j => Real.exp (c.ell j v) •
            (∑ i, c.a j i • (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ))) s)) v := by
  -- The map is the product (over `Fin N ⊕ Fin r`) of its coordinates, so `hasFDerivAt_pi`
  -- reduces the claim to the two families of coordinates.
  rw [hasFDerivAt_pi]
  intro s
  rcases s with i | j
  · -- `inl i`: the coordinate is the projection `x ↦ x i`.
    simpa using (hasFDerivAt_apply i v :
      HasFDerivAt (fun x : Fin N → ℝ => x i) (ContinuousLinearMap.proj i) v)
  · -- `inr j`: the coordinate is `exp ∘ ℓ_j`, i.e. `exp` composed with an affine map.
    simp only [Sum.elim_inr]
    have hell : HasFDerivAt (fun x : Fin N → ℝ => c.ell j x)
        (∑ i, c.a j i • (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) v := by
      have h : (fun x : Fin N → ℝ => c.ell j x)
          = fun x => (∑ i, c.a j i •
              (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) x + c.b j := by
        funext x
        simp [WilkiesDesign.E.EAChain.ell]
      rw [h]
      exact (ContinuousLinearMap.hasFDerivAt _).add_const (c.b j)
    exact (Real.hasDerivAt_exp (c.ell j v)).comp_hasFDerivAt v hell

end Work.WilE9.EaD
