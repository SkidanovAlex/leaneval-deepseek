import Mathlib
import Submission.Work.PSL2.Card

open scoped MatrixGroups

namespace Work.DSTR.D16

/-- Every field with at least four elements has a non-zero element `a` with `a ^ 2 ≠ 1`
(the hypothesis is what makes `SL(2, F)` perfect). -/
lemma exists_ne_zero_sq_ne_one (F : Type*) [Field F] (hF : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  have : Finite F := (Nat.card_pos_iff.1 (by omega)).2
  haveI : Fintype F := Fintype.ofFinite F
  have h3 : ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
  have hlt : ({0, 1, -1} : Finset F).card < (Finset.univ : Finset F).card := by
    rw [Finset.card_univ, Fintype.card_eq_nat_card]
    omega
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨a, ?_, ?_⟩
  · intro h; exact ha (by simp [h])
  · rw [sq_ne_one_iff]
    exact ⟨fun h => ha (by simp [h]), fun h => ha (by simp [h])⟩

/-- The centre of `SL(2, F)` has at most two elements: it is the set of square roots of `1`
among the scalars. -/
lemma card_center_SL2_le_two (F : Type*) [Field F] [Fintype F] :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ 2 := by
  have h := Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := F)).toEquiv
  rw [h, show max (Fintype.card (Fin 2)) 1 = 2 from by simp]
  exact card_rootsOfUnity F 2

/-- `|SL(2, GF(p, k))| = p ^ k * (p ^ (2 * k) - 1)`. -/
lemma card_SL2_galoisField (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k))
      = p ^ k * (p ^ (2 * k) - 1) := by
  letI : Fintype (GaloisField p k) := Fintype.ofFinite _
  rw [Work.PSL2.card_SL2, Fintype.card_eq_nat_card, GaloisField.card p k hk,
    ← pow_mul, Nat.mul_comm k 2]

theorem psl2_basic (p k : ℕ) [Fact p.Prime] (hq : 5 ≤ p ^ k) : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∧ Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∧ ¬ IsPGroup 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have h4 : 4 ≤ Nat.card (GaloisField p k) := by
    rw [GaloisField.card p k hk]; omega
  -- Simplicity: Mathlib's Iwasawa-structure proof of the simplicity of `PSL(2, F)`,
  -- valid as soon as `|F| ≥ 4`.
  have hsimple : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  -- Perfectness: `SL(2, F)` is its own commutator subgroup, hence so is its quotient `PSL(2, F)`.
  obtain ⟨a, ha0, ha2⟩ := exists_ne_zero_sq_ne_one (GaloisField p k) h4
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    ⟨Matrix.SL2.commutator_eq_top ha0 ha2⟩
  have hperfect :
      Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    inferInstance
  -- `PSL(2, q)` is not a `2`-group: a finite simple `2`-group has order `2`, whereas
  -- `|PSL(2, q)| ≥ |SL(2, q)| / 2 ≥ 60`.
  have hcenter :
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k))) ≤ 2 :=
    card_center_SL2_le_two _
  have hmul :
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k))) *
        Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))
        = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k)) := by
    have h := Subgroup.card_mul_index
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k)))
    rw [Subgroup.index_eq_card] at h
    exact h
  have hSLge : 120 ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k)) := by
    rw [card_SL2_galoisField p k hk]
    have h24 : 24 ≤ p ^ (2 * k) - 1 := by
      have h25 : 25 ≤ p ^ (2 * k) := by
        calc 25 ≤ (p ^ k) ^ 2 := by nlinarith
          _ = p ^ (2 * k) := by rw [← pow_mul, Nat.mul_comm k 2]
      omega
    calc 120 = 5 * 24 := by norm_num
      _ ≤ p ^ k * (p ^ (2 * k) - 1) := Nat.mul_le_mul hq h24
  have hnot : ¬ IsPGroup 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
    intro h2
    have hcard2 := (IsPGroup.isSimpleGroup_iff_card_eq h2).mp hsimple
    have hle : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k)) ≤
        2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) := by
      rw [← hmul]
      exact Nat.mul_le_mul_right _ hcenter
    omega
  exact ⟨hsimple, hperfect, hnot⟩

end Work.DSTR.D16
