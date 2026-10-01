import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs

namespace Work.LinnikBurgess.frame_count_prov_aux

open scoped BigOperators

theorem sum_box3_eq_iterate (H : ℕ) (F : (Fin 3 → ℕ) → ℝ) :
    (∑ a ∈ box3 H, F a)
      = ∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
          F ![x0, x1, x2] := by
  set s : Finset ℕ := Finset.Icc 1 H with hs
  have hbox : box3 H = (s ×ˢ (s ×ˢ s)).map
      ⟨fun q : ℕ × (ℕ × ℕ) => (![q.1, q.2.1, q.2.2] : Fin 3 → ℕ), by
        rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
        simp only [Prod.mk.injEq]
        exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1,
          by simpa using congrFun h 2⟩⟩ := by
    ext y
    simp only [box3, Fintype.mem_piFinset, Finset.mem_map, Finset.mem_product,
      hs, Finset.mem_Icc]
    constructor
    · intro h
      exact ⟨(y 0, (y 1, y 2)), ⟨h 0, h 1, h 2⟩, by funext i; fin_cases i <;> rfl⟩
    · rintro ⟨q, hq, rfl⟩ i
      obtain ⟨h1, h2, h3⟩ := hq
      fin_cases i <;> assumption
  rw [hbox, Finset.sum_map]
  simp only [Finset.sum_product]
  rfl

end Work.LinnikBurgess.frame_count_prov_aux
