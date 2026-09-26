import Mathlib
import Submission.Work.Asymptotics.KhatE1Defs

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-!
# The odd `E(z)^k`-coefficients `Bracket24B3`, `Bracket24B5` and their reductions (cycle-free copy)

This module reproduces the definitions `KhatE1.Bracket24B3`, `KhatE1.Bracket24B5` of
`Submission/Work/Asymptotics/KhatE1/Bracket24Tail_bound.lean` (the odd `E(z)^k`-coefficients of
`Sh τ z · Bracket24 ℓ τ z`, generated from the exact model `.mine24/model.py`) together with
their reduced normal forms `Bracket24B3_eq_red`, `Bracket24B5_eq_red`, but *without* importing
`Bracket24Tail_bound` itself.

The point is to remove a cycle: `KhatE1/Bracket24Tail_bound.lean` imports the target module
`KhatE1Core/Bracket24SharpCleared_hold.lean`, while the tail-bound proof
(`KhatE1Core/Bracket24TailCore_proof.lean`) *is* imported by the target module.  The two
`_eq_red` reductions are pure `field_simp; ring` identities, and the reductions
`Bracket24B3_reduced_big`/`Bracket24B5_reduced_big` (`Big 1`) are already proved in
`KhatE1Core/Bracket24P24Bound.lean`, so nothing is lost.
-/

/-- **The `E(z)³`-coefficient of the `Sh`-cleared bracket** (9 monomials, `τ`-only). -/
noncomputable def Bracket24B3 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
      (5634048 : ℂ) / (5 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.DeltaFun τ +
      (-35104 : ℂ) / (3 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ +
      (8 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.DeltaFun τ * (Work.Kernels.jInvariantFun τ) ^ 2 +
      (-4768 : ℂ) / (3 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ +
      (113 : ℂ) / (12 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ * Work.Kernels.jInvariantFun τ +
      (-1 : ℂ) / (144 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ * (Work.Kernels.jInvariantFun τ) ^ 2 +
      (13360 : ℂ) / (3 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.psi4 ℓ τ +
      (-161 : ℂ) / (12 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.psi4 ℓ τ * Work.Kernels.jInvariantFun τ +
      (1 : ℂ) / (144 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.psi4 ℓ τ * (Work.Kernels.jInvariantFun τ) ^ 2
/-- **The `E(z)⁵`-coefficient of the `Sh`-cleared bracket** (9 monomials, `τ`-only). -/
noncomputable def Bracket24B5 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
      (3826289664 : ℂ) / (7 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.DeltaFun τ +
      (-1290832 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ +
      (-192 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.DeltaFun τ * (Work.Kernels.jInvariantFun τ) ^ 2 +
      (-635664 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ +
      (27319 : ℂ) / (24 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ * Work.Kernels.jInvariantFun τ +
      (1 : ℂ) / (6 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ * Work.Kernels.psi2 ℓ τ * (Work.Kernels.jInvariantFun τ) ^ 2 +
      (1352760 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.psi4 ℓ τ +
      (-25015 : ℂ) / (24 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.psi4 ℓ τ * Work.Kernels.jInvariantFun τ +
      (-1 : ℂ) / (6 : ℂ) * ((Real.pi : ℂ)) ^ (-1 : ℤ) * (Work.Kernels.E4Fun τ) ^ 2 * Work.Kernels.psi4 ℓ τ * (Work.Kernels.jInvariantFun τ) ^ 2
/-- **The reduction of the `E(z)³`-coefficient.** -/
theorem Bracket24B3_eq_red (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ)
    (hD : Work.Kernels.DeltaFun τ ≠ 0) (hE4 : Work.Kernels.E4Fun τ ≠ 0) :
    Bracket24B3 ℓ τ = -( 84106543104 * (Work.Kernels.DeltaFun τ) ^ 2
        + 14745600 * Work.Kernels.DeltaFun τ * (Work.Kernels.E4Fun τ) ^ 3
        + 225780 * Work.Kernels.DeltaFun τ * (Work.Kernels.E4Fun τ) ^ 2 * E1combo8 ℓ τ
        + 8940 * Work.Kernels.DeltaFun τ * E1combo24 ℓ τ
        - 15 * (Work.Kernels.E4Fun τ) ^ 5 * E1combo8 ℓ τ
        - 25 * (Work.Kernels.E4Fun τ) ^ 3 * E1combo24 ℓ τ )
      / (88560 * Work.Kernels.DeltaFun τ * (Real.pi : ℂ)) := by
  rw [Bracket24B3, E1combo8, E1combo24]
  simp only [Work.Kernels.E8Fun, Work.Kernels.E10Fun, Work.Kernels.jInvariantFun]
  field_simp
  ring

/-- **The reduction of the `E(z)⁵`-coefficient.** -/
theorem Bracket24B5_eq_red (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ)
    (hD : Work.Kernels.DeltaFun τ ≠ 0) (hE4 : Work.Kernels.E4Fun τ ≠ 0) :
    Bracket24B5 ℓ τ = -( 5866622484480 * (Work.Kernels.DeltaFun τ) ^ 2
        - 82575360 * Work.Kernels.DeltaFun τ * (Work.Kernels.E4Fun τ) ^ 3
        + 5702403 * Work.Kernels.DeltaFun τ * (Work.Kernels.E4Fun τ) ^ 2 * E1combo8 ℓ τ
        + 834309 * Work.Kernels.DeltaFun τ * E1combo24 ℓ τ
        + 84 * (Work.Kernels.E4Fun τ) ^ 5 * E1combo8 ℓ τ
        + 140 * (Work.Kernels.E4Fun τ) ^ 3 * E1combo24 ℓ τ )
      / (20664 * Work.Kernels.DeltaFun τ * (Real.pi : ℂ)) := by
  rw [Bracket24B5, E1combo8, E1combo24]
  simp only [Work.Kernels.E8Fun, Work.Kernels.E10Fun, Work.Kernels.jInvariantFun]
  field_simp
  ring

end

end Work.Asymptotics.KhatE1
