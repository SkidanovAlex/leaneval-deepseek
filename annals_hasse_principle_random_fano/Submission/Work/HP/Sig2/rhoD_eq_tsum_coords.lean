import Mathlib
import Submission.Work.HP.Sig2.ThetaPoissonSetup

namespace Work.HP.Sig2

/-- The dual theta sum `rhoD Λ s = ∑'_{w ∈ Λ*} exp(-π s² ‖w‖²)`, written as a sum over
`ℤ`-coordinates: with `latGram Λ` the Gram matrix of a `ℤ`-basis of the discrete lattice
`Λ ⊆ ι → ℝ` and `latDualEquiv Λ : ℤ^κ ≃ dualLat Λ` the bijection
`m ↦ ∑ i, ((latGram Λ)⁻¹ *ᵥ m) i • latCoe Λ i`,
`rhoD Λ s = ∑'_{m ∈ ℤ^κ} exp(-(π s²) mᵀ (latGram Λ)⁻¹ m)`. -/
theorem rhoD_eq_tsum_coords {ι : Type*} [Fintype ι] (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (s : ℝ) :
    rhoD Λ s = ∑' m : ThetaPoisson.Idx Λ → ℤ,
      Real.exp (-(Real.pi * s ^ 2) * (∑ i, ∑ j, (m i : ℝ) *
        (ThetaPoisson.latGram Λ)⁻¹ i j * (m j : ℝ))) := by
  rw [rhoD, ← Equiv.tsum_eq (ThetaPoisson.latDualEquiv Λ)
    (fun w : dualLat Λ => Real.exp (-(Real.pi * s ^ 2) * (rNorm (w : ι → ℝ)) ^ 2))]
  refine tsum_congr fun m => ?_
  rw [ThetaPoisson.latDualEquiv_apply, ThetaPoisson.rNorm_latDualMap_sq]

end Work.HP.Sig2
