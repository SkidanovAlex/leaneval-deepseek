/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The last step of [JZLA20, Theorem 6.1]: `D_{K[G],U}` a division ring ⟹ `U` one

If `φ : K[G] →+* U` is epic and the division closure `D = D_{K[G],U}` of `φ(K[G])` in `U` is a
division ring, then `U = D` and hence `U` is a division ring.

The argument (Stenström XI.1.4) avoids any `∗`-structure: `φ` factors as the composite of the
corestriction `K[G] →+* ↥D` with the inclusion `ι : ↥D →+* U`, so `IsEpic.of_comp` makes `ι` epic;
`↥D` is a division ring, hence von Neumann regular, and an epic homomorphism out of a von Neumann
regular ring is surjective ([JZLA20, §2.3], `Epic.surjective_of_isEpic_of_vonNeumannRegular`).
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.surjective_of_isEpic_of_vonNeumannRegular
import Submission.Work.ORHughesFree.DivisionClosure.isDivisionRing_of_ringEquiv
import Submission.Work.ORHughesFree.StarRegular

set_option autoImplicit false

namespace Work.ORHughesFree

/-- A division ring is von Neumann regular: a nonzero element is its own weak inverse up to its
inverse, and `0` is its own weak inverse. -/
theorem vonNeumannRegularRing_of_isDivisionRing {R : Type} [Ring R] (h : IsDivisionRing R) :
    VonNeumannRegularRing R := by
  refine ⟨fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  · obtain ⟨u, hu⟩ := h.2 x hx
    refine ⟨((↑u⁻¹ : R)), ?_⟩
    rw [← hu]
    simp

/-- **The last step of [JZLA20, Theorem 6.1].**  If `φ : K[G] →+* U` is epic and the division
closure of `φ(K[G])` in `U` is a division ring, then `U` is a division ring (indeed `U` is that
division closure). -/
theorem isDivisionRing_of_isDivisionRing_divisionClosure {K : Type} [Field K] {G : Type} [Group G]
    {U : Type} [Ring U] (φ : MonoidAlgebra K G →+* U) (hφ : IsEpic φ)
    (hD : IsDivisionRing ↥(divisionClosure (Set.range φ))) : IsDivisionRing U := by
  letI : VonNeumannRegularRing ↥(divisionClosure (Set.range φ)) :=
    vonNeumannRegularRing_of_isDivisionRing hD
  let φD : MonoidAlgebra K G →+* ↥(divisionClosure (Set.range φ)) :=
    φ.codRestrict _ fun x => subset_divisionClosure _ ⟨x, rfl⟩
  let ι : ↥(divisionClosure (Set.range φ)) →+* U :=
    Subring.subtype (divisionClosure (Set.range φ))
  have hcomp : ι.comp φD = φ := RingHom.ext fun _ => rfl
  have hepic : IsEpic ι := IsEpic.of_comp (hcomp ▸ hφ)
  exact DivisionClosure.isDivisionRing_of_ringEquiv
    (RingEquiv.ofBijective ι
      ⟨fun _ _ h => Subtype.ext h, Epic.surjective_of_isEpic_of_vonNeumannRegular ι hepic⟩) hD

end Work.ORHughesFree
