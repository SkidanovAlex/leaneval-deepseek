import Submission.Work.ThomBordism.absThomComparePhi
import Submission.Work.ThomBordism.bijectiveThetaZ

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The canonical comparison `Phi`, and its naturality

`Work.ThomBordism.PhiZ Z N hn : H^n(Z, Z∖0) ≃ₗ H^n(Z⁺)` is the inverse of `ThetaZ`, i.e. the
*canonical* identification of the relative cohomology of the Thom pair with the cohomology of the
Thom space.  This is the `Φ` that `Work.ThomBordism.Grassmann.grassmannThomTarget` should be fed
with: it is a single, `V`-independent equivalence (a `noncomputable def`, not a `Classical.choose`),
and its naturality `Work.ThomBordism.thetaZNatural` gives, for a bundle map `g : Z' → Z` with
one-point extension `J`, the identity

  `Theta_Z' (J^* (Phi_Z a)) = g^*(a)`,   i.e.   `Phi_{Z'} (g^* a) = J^* (Phi_Z a)`,

which is the "description of the universal classes" (TUBULAR README §17): with
`Z = γ_{k,10}`, `Z' = ν` the normal bundle of an embedded `V`, and `a = p₁(γ)² ⌣ U_γ` the universal
class, it identifies the pullback of the universal class with the geometric class of `ν`.  See
`NOTES_round15_H4.md`.
-/

open CategoryTheory Limits
open Work.TangentClasses
open scoped Topology

namespace Work.ThomBordism

open Work.Cohomology

noncomputable section

variable {B : Type} [TopologicalSpace B] [CompactSpace B] [T2Space B]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {ι : Type}

/-- **The canonical comparison** `H^n(Z, Z∖0) ≃ₗ H^n(Z⁺)`: the inverse of `ThetaZ`.  Its defining
property is `ThetaZ Z N hn (PhiZ Z N hn x) = x` and, crucially, the *pairing* compatibility
`Work.ThomBordism.absRelKronHComparison` together with the naturality
`Work.ThomBordism.thetaZNatural`. -/
noncomputable def PhiZ (Z : RealBundle B F ι) (N : NormLike Z) {n : ℕ} (hn : 2 ≤ n) :
    Work.Thom.RelCoh ℤ n Z.TotalSpace (Work.Thom.zeroComplement Z) ≃ₗ[ℤ]
      Work.Thom.Coh ℤ n (OnePoint Z.TotalSpace) :=
  (LinearEquiv.ofBijective (ThetaZ Z N hn) (bijectiveThetaZ Z N hn)).symm

theorem ThetaZ_PhiZ (Z : RealBundle B F ι) (N : NormLike Z) {n : ℕ} (hn : 2 ≤ n)
    (x : Work.Thom.RelCoh ℤ n Z.TotalSpace (Work.Thom.zeroComplement Z)) :
    ThetaZ Z N hn (PhiZ Z N hn x) = x := by
  rw [PhiZ, ← LinearEquiv.ofBijective_apply (f := ThetaZ Z N hn) (hf := bijectiveThetaZ Z N hn)]
  exact LinearEquiv.apply_symm_apply _ _

theorem PhiZ_apply (Z : RealBundle B F ι) (N : NormLike Z) {n : ℕ} (hn : 2 ≤ n)
    (u : Work.Thom.Coh ℤ n (OnePoint Z.TotalSpace)) :
    PhiZ Z N hn (ThetaZ Z N hn u) = u := by
  rw [PhiZ, ← LinearEquiv.ofBijective_apply (f := ThetaZ Z N hn) (hf := bijectiveThetaZ Z N hn)]
  exact LinearEquiv.symm_apply_apply _ _

end

end Work.ThomBordism
