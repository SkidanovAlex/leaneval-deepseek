import Mathlib
import Submission.Work.HP.Sig2.ThetaPoissonSetup

namespace Work.HP.Sig2

/-- The theta sum of a lattice, written as a sum over the `ℤ`-coordinates of a `ℤ`-basis:
for a discrete `Λ ⊆ ι → ℝ` with chosen `ℤ`-basis `latCoe Λ` and Gram matrix `latGram Λ`, and
`t = latMap Λ u = ∑ i, u i • latCoe Λ i`,
`theta Λ s t = ∑'_{n ∈ ℤ^κ} exp(-(π/s²) (n-u)ᵀ (latGram Λ) (n-u))`. -/
theorem theta_eq_tsum_coords {ι : Type*} [Fintype ι] (Λ : Submodule ℤ (ι → ℝ)) [DiscreteTopology Λ]
    (s : ℝ) (t : ι → ℝ) (u : ThetaPoisson.Idx Λ → ℝ) (hu : ThetaPoisson.latMap Λ u = t) :
    theta Λ s t = ∑' n : ThetaPoisson.Idx Λ → ℤ,
      Real.exp (-(Real.pi / s ^ 2) * (∑ i, ∑ j, ((n i : ℝ) - u i) *
        ThetaPoisson.latGram Λ i j * ((n j : ℝ) - u j))) := by
  classical
  rw [theta]
  -- Reindex the sum over the lattice `Λ` by the coordinates in the chosen `ℤ`-basis.
  rw [show (∑' z : Λ, Real.exp (-(Real.pi / s ^ 2) * (rNorm ((z : ι → ℝ) - t)) ^ 2))
      = ∑' n : ThetaPoisson.Idx Λ → ℤ,
          Real.exp (-(Real.pi / s ^ 2) *
            (rNorm (((((ThetaPoisson.latBasis Λ).equivFun.symm) n : Λ) : ι → ℝ) - t)) ^ 2) from
    (Equiv.tsum_eq (((ThetaPoisson.latBasis Λ).equivFun.symm).toEquiv)
      (fun z : Λ => Real.exp (-(Real.pi / s ^ 2) * (rNorm ((z : ι → ℝ) - t)) ^ 2))).symm]
  refine tsum_congr fun n => ?_
  -- In coordinates, `z = ∑ i, (n i) • latCoe Λ i` and `t = ∑ i, u i • latCoe Λ i`, so
  -- `‖z - t‖²` is the quadratic form with matrix `latGram Λ` applied to `n - u`.
  have key : rNorm (((((ThetaPoisson.latBasis Λ).equivFun.symm) n : Λ) : ι → ℝ) - t) ^ 2
      = ∑ i, ∑ j, ((n i : ℝ) - u i) * ThetaPoisson.latGram Λ i j * ((n j : ℝ) - u j) := by
    have h1 : ((((ThetaPoisson.latBasis Λ).equivFun.symm) n : Λ) : ι → ℝ)
        = ThetaPoisson.latMap Λ (fun i => (n i : ℝ)) := ThetaPoisson.latMap_equivFun Λ n
    rw [h1, ← hu]
    rw [show ThetaPoisson.latMap Λ (fun i => (n i : ℝ)) - ThetaPoisson.latMap Λ u
        = ThetaPoisson.latMap Λ (fun i => (n i : ℝ) - u i) from by
      rw [← map_sub]; rfl]
    rw [ThetaPoisson.latGram_quad]
  rw [key]

end Work.HP.Sig2
