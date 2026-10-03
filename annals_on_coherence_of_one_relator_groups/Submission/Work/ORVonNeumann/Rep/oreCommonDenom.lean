import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORVonNeumann.Rep

/-- **A common left multiple inside an Ore set.** Given finitely many denominators
`s j ∈ S` of a (left) Ore set, there is a single `e ∈ S` together with numerators `t j : R`
such that `e = t j * s j` for every `j`.

This is proved by induction on the index set, combining two denominators with the Ore
condition `oreCondition`. -/
lemma exists_common_left_multiple {R : Type*} [Ring R] {S : Submonoid R}
    [OreLocalization.OreSet S] {m : ℕ} (s : Fin m → S) :
    ∃ e : S, ∀ j, ∃ t : R, (e : R) = t * s j := by
  induction m with
  | zero => exact ⟨1, fun j => j.elim0⟩
  | succ n ih =>
    obtain ⟨e', he'⟩ := ih (fun j : Fin n => s j.castSucc)
    obtain ⟨r'', s'', hOre⟩ := OreLocalization.oreCondition (s (Fin.last n) : R) e'
    refine ⟨s'' * s (Fin.last n), fun j => ?_⟩
    refine Fin.lastCases ?_ ?_ j
    · exact ⟨s'', rfl⟩
    · intro i
      obtain ⟨t', ht'⟩ := he' i
      refine ⟨r'' * t', ?_⟩
      simp only [Submonoid.coe_mul]
      rw [hOre, ht', mul_assoc]

theorem oreCommonDenom {R : Type*} [Ring R] {S : Submonoid R} [OreLocalization.OreSet S] (hS : S ≤ nonZeroDivisors R) {m : ℕ} (a : Fin m → R) (s : Fin m → S) : ∃ (e : S) (t : Fin m → R) (b : Fin m → R), (∀ j, (e : R) = t j * s j) ∧ (∀ j, (a j /ₒ s j : OreLocalization S R) = (b j /ₒ e)) := by
  obtain ⟨e, hc⟩ := exists_common_left_multiple (S := S) s
  choose t ht using hc
  refine ⟨e, t, fun j => t j * a j, ht, fun j => ?_⟩
  rw [OreLocalization.oreDiv_eq_iff]
  refine ⟨1, t j, ?_, ?_⟩
  · simp [smul_eq_mul]
  · rw [Submonoid.coe_one, one_mul, ht j]

end Work.ORVonNeumann.Rep
