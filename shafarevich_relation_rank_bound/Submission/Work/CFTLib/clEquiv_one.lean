import Mathlib
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.classGroupMulEquiv_trans

namespace Work.CFTLib

open NumberField

/-- The action `clEquiv F K` of `Gal(K/F)` on the ideal class group `Cl(𝓞 K)` sends the identity
automorphism to the identity: `clEquiv F K 1` is the identity equivalence of `Cl(𝓞 K)`.

Indeed `clEquiv F K g = ClassGroup.mulEquiv (𝓞 K ≃+* 𝓞 K)` is the transport of the class group
along the ring isomorphism `𝓞 K ≃+* 𝓞 K` induced by `g`; for `g = 1` that ring isomorphism is the
identity, and `ClassGroup.mulEquiv` of a ring isomorphism acting as the identity fixes every class
(computed on `ClassGroup.mk0` via `ClassGroupTransport.mk0_mulEquiv`). -/
theorem clEquiv_one {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (c : ClassGroup (𝓞 K)) : Work.CFTLib.clEquiv F K 1 c = c := by
  have h1 : (NumberField.RingOfIntegers.mapAlgEquiv (1 : K ≃ₐ[F] K)).toRingEquiv =
      (1 : 𝓞 K ≃+* 𝓞 K) := by
    ext x
    exact rfl
  rw [clEquiv, h1]
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [Work.CFTLib.ClassGroupTransport.mk0_mulEquiv]
  congr 1
  exact Subtype.ext (Ideal.map_id I.1)

end Work.CFTLib
