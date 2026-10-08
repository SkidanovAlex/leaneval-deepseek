import Mathlib
import Submission.Work.CORE2A.Defs

/-!
# A perfect group has no nontrivial homomorphism into an odd-order group

If `E` is perfect and `C` has odd order (hence is solvable, by the odd order theorem, available
here as the hypothesis `hft : Work.GW2.FeitThompsonProp`), then every homomorphism `E →* C` is
trivial.

Proof.  The image `φ.range ≤ C` is a subgroup of a solvable group, hence solvable, and it is a
quotient of the perfect group `E`, hence perfect.  A nontrivial perfect group is not solvable
(`Group.IsPerfect.not_isSolvable`), so `φ.range` must be trivial, i.e. `φ = 1`.
-/

namespace Work.CORE2A

theorem perfect_hom_odd_card {E C : Type} [Group E] [Group C] [Finite C]
    (hft : Work.GW2.FeitThompsonProp) (hodd : Odd (Nat.card C)) (φ : E →* C)
    [Group.IsPerfect E] : φ = 1 := by
  -- `C` is solvable by the odd order theorem.
  have hsol : Group.IsSolvable C := hft C hodd
  -- the image of a perfect group is perfect
  have hperf : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  -- a perfect subgroup of a solvable group is trivial
  have hsub : Subsingleton φ.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable φ.range (inferInstance : Group.IsSolvable φ.range)
  -- hence `φ = 1`
  ext x
  have h1 : (⟨φ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : φ.range) = ⟨1, φ.range.one_mem⟩ :=
    Subsingleton.elim _ _
  exact congrArg Subtype.val h1

end Work.CORE2A
