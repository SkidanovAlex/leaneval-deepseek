import Mathlib
import Submission.Work.CFT.GlobalClassFormation.Defs

namespace Work.CFT.GlobalClassFormation

/-- The `p`-torsion `Cl_F[p]` of the class group of a number field, viewed as an `𝔽_p`-vector
space (via `classGroupTorsion`), is finite of cardinality `p ^ dim_{𝔽_p} Cl_F[p]`.  Finiteness
comes from finiteness of the class group (`RingOfIntegers.instFintypeClassGroup`), and the count is
`Module.card_eq_pow_finrank`. -/
theorem card_classGroupTorsion_eq_pow_finrank (F : Type*) [Field F] [NumberField F] (p : ℕ)
    [Fact p.Prime] :
    Nat.card (Work.CFT.GlobalClassFormation.classGroupTorsion F p) =
      p ^ Module.finrank (ZMod p) (Work.CFT.GlobalClassFormation.classGroupTorsion F p) := by
  classical
  have h : Fintype.card (Work.CFT.GlobalClassFormation.classGroupTorsion F p) =
      Fintype.card (ZMod p) ^ Module.finrank (ZMod p)
        (Work.CFT.GlobalClassFormation.classGroupTorsion F p) :=
    Module.card_eq_pow_finrank
  rw [ZMod.card p, ← Nat.card_eq_fintype_card] at h
  exact h

end Work.CFT.GlobalClassFormation
