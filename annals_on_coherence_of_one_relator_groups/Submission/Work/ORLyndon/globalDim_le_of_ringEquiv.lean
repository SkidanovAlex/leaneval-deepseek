import Mathlib
import Submission.Work.ORCoherence.GlobalDim
import Submission.Work.ORCoherence.Presentation

namespace Work.ORLyndon

open CategoryTheory

universe u

/-- The global dimension is monotone under a ring isomorphism: an isomorphism of rings
`e : R ≃+* S` identifies the categories of left modules (restriction of scalars along `e`),
and projective dimension is preserved by semilinear equivalences of modules
(`ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv`).  Consequently a bound
`globalDim R ≤ n` transfers to `globalDim S ≤ n`. -/
theorem globalDim_le_of_ringEquiv {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) {n : ℕ}
    (h : Work.ORCoherence.globalDim R ≤ (n : WithBot ℕ∞)) :
    Work.ORCoherence.globalDim S ≤ (n : WithBot ℕ∞) := by
  rw [Work.ORCoherence.globalDim_le_iff' S n]
  intro N
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv e.symm
  have hM : CategoryTheory.HasProjectiveDimensionLE
      ((ModuleCat.restrictScalars (e : R →+* S)).obj N) n :=
    (Work.ORCoherence.globalDim_le_iff' R n).mp h _
  have := hM
  have hev : (↑((ModuleCat.restrictScalars (e : R →+* S)).obj N) : Type u) ≃ₛₗ[RingHomClass.toRingHom e] ↑N :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e hev n

end Work.ORLyndon
