import Mathlib
import Submission.Work.A7F.Defs
import Submission.Work.AUTA7.A7.SylowTwoSubgroup

/-!
# Every Sylow `2`-subgroup of `A₇` is dihedral of order `8`

`|A₇| = 2520 = 2³ · 315`, so every Sylow `2`-subgroup of `A₇` has order `8`, and by Sylow's
theorem they are all conjugate (hence isomorphic).  It therefore suffices to exhibit *one* Sylow
`2`-subgroup of `A₇` isomorphic to `DihedralGroup 4`.

For this we use the explicit injective homomorphism `dihToA7 : DihedralGroup 4 →* A₇` from
`Submission/Work/AUTA7/A7/SylowTwoSubgroup.lean`, whose range `K` is a subgroup of `A₇` isomorphic
to `DihedralGroup 4`, hence of order `8`.  Being a subgroup of order `2³`, `K` is a `2`-group, so
it is contained in some Sylow `2`-subgroup `S₀`; since `S₀` also has order `8`, this forces
`S₀ = K`.  Finally `Sylow.equiv S₀ S : ↥S₀ ≃* ↥S` identifies any other Sylow `2`-subgroup `S`
with `S₀ = K`.
-/

open scoped MatrixGroups

namespace Work.A7F

open Subgroup

/-- The isomorphism induced by the explicit injective homomorphism
`dihToA7 : DihedralGroup 4 →* A₇`: its range is dihedral of order `8`. -/
noncomputable def sylow2_iso_range_equiv :
    ↥(Work.AUTA7.A7.dihToA7.range) ≃* DihedralGroup 4 :=
  (MonoidHom.ofInjective Work.AUTA7.A7.dihToA7_injective).symm

/-- `|A₇| = 2520 = 2³ · 315`. -/
theorem sylow2_iso_card_alternating : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 7)
  have h2 : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  rw [h2] at h
  omega

/-- The range of `dihToA7` has `8` elements. -/
theorem sylow2_iso_range_card : Nat.card ↥(Work.AUTA7.A7.dihToA7.range) = 8 := by
  rw [Nat.card_congr sylow2_iso_range_equiv.toEquiv, DihedralGroup.nat_card]

/-- The range of `dihToA7` is a `2`-group (of order `2³`). -/
theorem sylow2_iso_range_isPGroup : IsPGroup 2 ↥(Work.AUTA7.A7.dihToA7.range) := by
  apply IsPGroup.of_card (n := 3)
  rw [sylow2_iso_range_card]
  norm_num

theorem sylow2_iso : ∀ S : Sylow 2 (alternatingGroup (Fin 7)),
    Nonempty ((S : Subgroup (alternatingGroup (Fin 7))) ≃* DihedralGroup 4) := by
  intro S
  -- The range `K` of `dihToA7` is a `2`-subgroup, hence lies in some Sylow `2`-subgroup `S₀`.
  obtain ⟨S₀, hle⟩ :=
    IsPGroup.exists_le_sylow (p := 2) (G := alternatingGroup (Fin 7)) sylow2_iso_range_isPGroup
  -- Every Sylow `2`-subgroup of `A₇` has order `2 ^ (2520).factorization 2 = 2³ = 8`.
  have hcardS₀ : Nat.card ↥(S₀ : Subgroup (alternatingGroup (Fin 7))) = 8 := by
    rw [Sylow.card_eq_multiplicity, sylow2_iso_card_alternating]
    norm_num [Nat.factorization]
  -- `K ≤ S₀` with equal cardinalities, so `S₀ = K`.
  have hS₀ : (S₀ : Subgroup (alternatingGroup (Fin 7))) = Work.AUTA7.A7.dihToA7.range :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardS₀, sylow2_iso_range_card])).symm
  -- Sylow subgroups are isomorphic, and `↥K ≃* DihedralGroup 4` by construction.
  refine ⟨(Sylow.equiv S₀ S).symm.trans ?_⟩
  rw [hS₀]
  exact sylow2_iso_range_equiv

end Work.A7F
