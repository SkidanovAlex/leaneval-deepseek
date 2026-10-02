import Mathlib
import Submission.Work.ThomBordism.tubeSign
import Submission.Work.ThomBordism.tubeNumberStep

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

/-!
# The two cast lemmas of the ν-side class description

`hν1` of `Work.Tubular.tubeThomRep_of_nuPairing` is stated at the *two* degrees `8 + k` and `k + 8`
(the interface `Work.Thom.Grassmann.grassmannThomTarget` lives in `k + 8`, the universal class
`U_γ.τ` and the comparison `PhiZ γ` live in `8 + k`).  The two transport lemmas below are the ones
the chain needs:

* `CohMap_cast` — the contravariant cohomology map commutes with a change of degrees;
* `PhiG_cast_symm'` — undoing the degree change built into the chosen comparison map `PhiG` returns
  `PhiZ` at degree `8 + k` (the `def`-unfolded form of `Work.ThomBordism.PhiG_cast_symm`, so that it
  rewrites the literal `(Nat.add_comm 8 k).symm ▸ D.p1sqU` occurring in `hν1`).
-/

open Work.Cohomology Work.Thom Work.TangentClasses

namespace Work.ThomBordism

noncomputable section

/-- **The cohomology pullback commutes with a change of degrees.** -/
theorem CohMap_cast {B₁ B₂ : Type} [TopologicalSpace B₁] [TopologicalSpace B₂]
    (f : C(B₁, B₂)) {k k' : ℕ} (h : k' = k) (x : Work.Thom.Coh ℤ k' B₂) :
    (Work.Thom.CohMap f ℤ k).hom (h ▸ x) = h ▸ ((Work.Thom.CohMap f ℤ k').hom x) := by
  cases h
  rfl

/-- **The degree change of the chosen comparison `Φ = PhiG` undone**: the literal term
`(Nat.add_comm 8 k).symm ▸ (PhiG k h2 a)` occurring in the ν-side pairing identity is
`PhiZ γ (8 + k) a`. -/
theorem PhiG_cast_symm' (k : ℕ) (h2 : 2 ≤ 8 + k)
    (a : Work.Thom.OpenThom (Grassmann.tautologicalBundle k 10) (8 + k)) :
    (Nat.add_comm 8 k).symm ▸ (PhiG k h2 a)
      = PhiZ (Grassmann.tautologicalBundle k 10) (tautNormLike k 10) h2 a :=
  PhiG_cast_symm k h2 a

end

end Work.ThomBordism
