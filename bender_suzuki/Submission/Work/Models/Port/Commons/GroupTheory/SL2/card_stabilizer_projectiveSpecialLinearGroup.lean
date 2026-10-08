import Mathlib.Algebra.Order.Ring.Star
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Submission.Work.Models.Port.Commons.GroupTheory.SL2.isMultiplyPretransitive_projectiveSpecialLinearGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.LinearGroup.card_specialLinearGroup_two
import Submission.Work.Models.Port.Commons.GroupTheory.LinearGroup.specialLinearGroup_two_mem_center_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Cardinality of the stabilizer of a projective point under `PSL(2, K)`, `K` of characteristic 2

For a finite field `K` of characteristic two, the projective special linear group
`PSL(2, K)` (which coincides with `SL(2, K)` because the centre is trivial) acts on the
projective line `ℙ K (Fin 2 → K)`.  The stabilizer of a point has cardinality
`|K| * (|K| - 1)`.

This is the orbit-stabilizer theorem applied to the (2-)transitive action of `PSL(2, K)` on
the projective line: the orbit of a point is everything, so `|stab| * |ℙ¹| = |PSL|`, and
`|ℙ¹| = |K| + 1`, `|PSL| = |SL| = |K| * (|K|² - 1)`.
-/

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace Commons.GroupTheory.SL2

/-- Orbit-stabilizer theorem, stated for `Nat.card`.  The orbit is considered as a subtype,
and we identify its cardinality with the index of the stabilizer. -/
theorem natCard_stabilizer_mul_natCard_orbit {G X : Type*} [Group G] [MulAction G X] (a : X) :
    Nat.card (MulAction.stabilizer G a) * Nat.card (MulAction.orbit G a) = Nat.card G := by
  have h : Nat.card (MulAction.orbit G a) = (MulAction.stabilizer G a).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G a)
  rw [h]
  exact Subgroup.card_mul_index _

/-- Orbit-stabilizer theorem for a pretransitive action: the orbit is the whole space. -/
theorem natCard_stabilizer_mul_natCard_eq_of_pretransitive {G X : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] (a : X) :
    Nat.card (MulAction.stabilizer G a) * Nat.card X = Nat.card G := by
  have h : Nat.card (MulAction.orbit G a) = Nat.card X := by
    rw [MulAction.orbit_eq_univ]
    exact Nat.card_congr (Equiv.Set.univ X)
  rw [← natCard_stabilizer_mul_natCard_orbit (G := G) (X := X) a, h]

/-- In characteristic two the centre of `SL(2, K)` is trivial: a central element is a
scalar matrix `c • 1` with `c ^ 2 = 1`, and in characteristic two `-1 = 1`. -/
theorem center_specialLinearGroup_two_eq_bot {K : Type*} [Field K] (hchar : CharP K 2) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  letI := hchar
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨c, hc⟩ :=
    (Commons.GroupTheory.LinearGroup.specialLinearGroup_two_mem_center_iff g).mp hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := g.2
  rw [hc, Matrix.det_smul] at hdet
  have hc2 : c ^ 2 = 1 := by simpa using hdet
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc2 with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  rw [hc1] at hc
  exact Subtype.ext (by simpa using hc)

/-- In characteristic two, `PSL(2, K) = SL(2, K) / Z(SL(2, K))` has the same cardinality as
`SL(2, K)`, because the centre is trivial. -/
theorem natCard_projectiveSpecialLinearGroup_two_eq_of_char_two {K : Type*} [Field K]
    (hchar : CharP K 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hcenter := center_specialLinearGroup_two_eq_bot (K := K) hchar
  have h := Subgroup.card_mul_index (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  rw [Subgroup.index_eq_card, hcenter] at h
  simpa [Matrix.ProjectiveSpecialLinearGroup, hcenter] using h

/-- The projective line over a finite field has `|K| + 1` points. -/
theorem natCard_projectivization_fin_two {K : Type*} [Field K] [Fintype K] :
    Nat.card (Projectivization K (Fin 2 → K)) = Nat.card K + 1 :=
  Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp)

theorem card_stabilizer_projectiveSpecialLinearGroup {K : Type*} [Field K] [Fintype K]
    (hchar : CharP K 2) (hcard : 2 ≤ Nat.card K) (a : Projectivization K (Fin 2 → K)) :
    Nat.card (MulAction.stabilizer (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) a) =
      Nat.card K * (Nat.card K - 1) := by
  haveI : MulAction.IsMultiplyPretransitive (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
      (Projectivization K (Fin 2 → K)) 2 :=
    Commons.GroupTheory.SL2.isMultiplyPretransitive_projectiveSpecialLinearGroup_two
  haveI : MulAction.IsPretransitive (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
      (Projectivization K (Fin 2 → K)) := MulAction.isPretransitive_of_is_two_pretransitive
  have hos := natCard_stabilizer_mul_natCard_eq_of_pretransitive
    (G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (X := Projectivization K (Fin 2 → K)) a
  have hPSL := natCard_projectiveSpecialLinearGroup_two_eq_of_char_two (K := K) hchar
  have hSL := Commons.GroupTheory.LinearGroup.card_specialLinearGroup_two (F := K)
  have hX := natCard_projectivization_fin_two (K := K)
  rw [hX, hPSL, hSL] at hos
  have h1 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
    have h := Nat.sq_sub_sq (Nat.card K) 1
    rw [mul_comm] at h
    simpa using h
  have harith : Nat.card K * (Nat.card K ^ 2 - 1) =
      (Nat.card K * (Nat.card K - 1)) * (Nat.card K + 1) := by
    rw [h1]; ring
  rw [harith] at hos
  exact Nat.mul_right_cancel (m := Nat.card K + 1) (by positivity) hos

end Commons.GroupTheory.SL2