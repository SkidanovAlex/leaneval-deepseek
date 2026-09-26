import Mathlib
import Submission.Work.SG.Data.SellCheck

namespace Work.SG

/-- Membership in `boxVecs`: the elements are exactly the reconstructions
`⟨a-3, b-3, c-3⟩` with `a, b, c ∈ [0,7)` that are nonzero and satisfy the edge condition. -/
private lemma mem_boxVecs_aux (E : List (Fin 4 × Fin 4)) (y : Work.SG.Data.V3) :
    y ∈ Work.SG.Data.boxVecs E ↔
      ∃ a : ℕ, a < 7 ∧ ∃ b : ℕ, b < 7 ∧ ∃ c : ℕ, c < 7 ∧
        ((¬ (⟨(a : ℤ) - 3, (b : ℤ) - 3, (c : ℤ) - 3⟩ : Work.SG.Data.V3) = Work.SG.Data.V3.zero ∧
          (∀ (p q : Fin 4), (p, q) ∈ E →
            (((![0, (a : ℤ) - 3, (b : ℤ) - 3, (c : ℤ) - 3] : Fin 4 → ℤ) p) -
             ((![0, (a : ℤ) - 3, (b : ℤ) - 3, (c : ℤ) - 3] : Fin 4 → ℤ) q)).natAbs ≤ 1)) ∧
        (⟨(a : ℤ) - 3, (b : ℤ) - 3, (c : ℤ) - 3⟩ : Work.SG.Data.V3) = y) := by
  rw [Work.SG.Data.boxVecs]
  constructor
  · intro h
    simp only [List.mem_flatMap, List.mem_filterMap] at h
    simp at h
    exact h
  · intro h
    simp only [List.mem_flatMap, List.mem_filterMap]
    simp at h ⊢
    exact h

theorem boxVecs_iff (E : List (Fin 4 × Fin 4)) (y : Work.SG.Data.V3) :
    y ∈ Work.SG.Data.boxVecs E ↔
      y ≠ Work.SG.Data.V3.zero ∧
        (∀ e ∈ E, ((![0, y.x, y.y, y.z] : Fin 4 → ℤ) e.1 -
          (![0, y.x, y.y, y.z] : Fin 4 → ℤ) e.2).natAbs ≤ 1) ∧
        (∀ k : Fin 3, |y.toFun k| ≤ 3) := by
  refine (mem_boxVecs_aux E y).trans ⟨?_, ?_⟩
  · -- the enumerated triple determines a nonzero vector satisfying the edge condition,
    -- and the box bound gives the coordinate bound
    rintro ⟨a, ha7, b, hb7, c, hc7, ⟨⟨hne, hedge⟩, hyw⟩⟩
    have ha_eq : (a : ℤ) - 3 = y.x := by
      have h := congrArg Work.SG.Data.V3.x hyw; simpa using h
    have hb_eq : (b : ℤ) - 3 = y.y := by
      have h := congrArg Work.SG.Data.V3.y hyw; simpa using h
    have hc_eq : (c : ℤ) - 3 = y.z := by
      have h := congrArg Work.SG.Data.V3.z hyw; simpa using h
    refine ⟨?_, ?_, ?_⟩
    · rw [← hyw]; exact hne
    · intro e he
      obtain ⟨p, q⟩ := e
      have h := hedge p q he
      rw [ha_eq, hb_eq, hc_eq] at h
      exact h
    · intro k
      fin_cases k
      · change |y.x| ≤ 3; rw [← ha_eq, abs_le]; omega
      · change |y.y| ≤ 3; rw [← hb_eq, abs_le]; omega
      · change |y.z| ≤ 3; rw [← hc_eq, abs_le]; omega
  · -- conversely, coordinates bounded by `3` reconstruct an enumerated triple
    rintro ⟨hne, hedge, hb⟩
    have hx : |y.x| ≤ 3 := by simpa [Work.SG.Data.V3.toFun] using hb 0
    obtain ⟨hxl, hxu⟩ := abs_le.mp hx
    have hy : |y.y| ≤ 3 := by simpa [Work.SG.Data.V3.toFun] using hb 1
    obtain ⟨hyl, hyu⟩ := abs_le.mp hy
    have hz : |y.z| ≤ 3 := by simpa [Work.SG.Data.V3.toFun] using hb 2
    obtain ⟨hzl, hzu⟩ := abs_le.mp hz
    set a : ℕ := (y.x + 3).toNat with ha_def
    have ha3 : (a : ℤ) = y.x + 3 := by rw [ha_def]; exact Int.toNat_of_nonneg (by omega)
    have ha7 : a < 7 := by omega
    set b : ℕ := (y.y + 3).toNat with hb_def
    have hb3 : (b : ℤ) = y.y + 3 := by rw [hb_def]; exact Int.toNat_of_nonneg (by omega)
    have hb7 : b < 7 := by omega
    set c : ℕ := (y.z + 3).toNat with hc_def
    have hc3 : (c : ℤ) = y.z + 3 := by rw [hc_def]; exact Int.toNat_of_nonneg (by omega)
    have hc7 : c < 7 := by omega
    have ha_eq : (a : ℤ) - 3 = y.x := by omega
    have hb_eq : (b : ℤ) - 3 = y.y := by omega
    have hc_eq : (c : ℤ) - 3 = y.z := by omega
    have hweq : (⟨(a : ℤ) - 3, (b : ℤ) - 3, (c : ℤ) - 3⟩ : Work.SG.Data.V3) = y := by
      rw [show y = (⟨y.x, y.y, y.z⟩ : Work.SG.Data.V3) from rfl, Work.SG.Data.V3.mk.injEq]
      exact ⟨ha_eq, hb_eq, hc_eq⟩
    have hne' : ¬ (⟨(a : ℤ) - 3, (b : ℤ) - 3, (c : ℤ) - 3⟩ : Work.SG.Data.V3)
        = Work.SG.Data.V3.zero := by
      rw [hweq]; exact hne
    have hedge' : ∀ (p q : Fin 4), (p, q) ∈ E →
        (((![0, (a : ℤ) - 3, (b : ℤ) - 3, (c : ℤ) - 3] : Fin 4 → ℤ) p) -
         ((![0, (a : ℤ) - 3, (b : ℤ) - 3, (c : ℤ) - 3] : Fin 4 → ℤ) q)).natAbs ≤ 1 := by
      intro p q hpq
      have h := hedge (p, q) hpq
      rw [← ha_eq, ← hb_eq, ← hc_eq] at h
      exact h
    exact ⟨a, ha7, b, hb7, c, hc7, ⟨⟨hne', hedge'⟩, hweq⟩⟩

end Work.SG
