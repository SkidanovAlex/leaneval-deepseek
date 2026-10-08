import Mathlib
import Submission.Work.BG.ThmABCCharDefs

namespace Work.BG

theorem s02_bset_finite {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Fintype (OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0)]
    (f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ →
      OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) :
    (Work.GW2.C16.bset C f χ).Finite := by
  -- `𝒮(χ) = bset C f χ` consists of class functions `ν` that are irreducible characters,
  -- so it is the image of the (finite) type of irreducible characters under the forgetful
  -- map `ν ↦ (ν : ClassFunction ↥C.P.H0 ℂ)`; hence it is finite.
  refine (Set.finite_univ.image
    (fun ν : OddOrder.RepresentationTheory.IrreducibleCharacter ↥C.P.H0 =>
      (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ))).subset ?_
  intro ν hν
  exact ⟨⟨ν, hν.1⟩, Set.mem_univ _, rfl⟩

end Work.BG
