import Mathlib
import Submission.Work.CORE2A.TorusDefs

/-!
# `L₂(q) ≤ PGL₂(q)` is perfect

`Work.GW2.Lsub p k` is the image of `PSL₂(q) → PGL₂(q)` (notation of Bender 1981 p. 220,
`q = p ^ k`).  For odd `q ≥ 5` this image is a quotient of `PSL₂(q)`, and `PSL₂(q)` is
perfect because `SL₂(q)` is perfect as soon as `q` has at least four elements.

This file records that `Lsub p k` is a perfect group, the auxiliary statement
`c14_aux_isPerfect_Lsub`.
-/

namespace Work.CORE2A

open scoped MatrixGroups

/-- A field with at least four elements contains a nonzero element whose square is not `1`.
(Also available as the private `field_cond_of_four_le_card` in `Mathlib`.) -/
private lemma exists_ne_zero_sq_ne_one_of_four_le_card {F : Type*} [Field F]
    (hF : 4 ≤ Nat.card F) : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  have : Finite F := (Nat.card_pos_iff.1 (by omega)).2
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hF
  omega

/-- **`L₂(q)` is perfect.**  For `q = p ^ k` with `p` an odd prime and `q ≥ 5`, the image
`L₂(q)` of `PSL₂(q)` in `PGL₂(q)` is a perfect group. -/
theorem c14_aux_isPerfect_Lsub (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k) :
    Group.IsPerfect ↥(Work.GW2.Lsub p k) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  -- `q = p ^ k ≥ 5 ≥ 4`, so the field `GF(q)` has at least four elements.
  have hcard : 4 ≤ Nat.card (GaloisField p k) := by
    rw [GaloisField.card p k hk0]
    omega
  -- `SL₂(q)` is perfect, hence so is its quotient `PSL₂(q)`.
  haveI : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    ⟨SL2Simple.PSL_commutator_eq_top (exists_ne_zero_sq_ne_one_of_four_le_card hcard)⟩
  -- `Lsub p k` is the image of `PSL₂(q)`, and an image of a perfect group is perfect.
  exact Group.IsPerfect.range (Matrix.ProjectiveSpecialLinearGroup.toPGL :
    PSL(2, GaloisField p k) →* PGL(2, GaloisField p k))

end Work.CORE2A
