import Mathlib
import Submission.Work.LinnikBurgess.caseT_aux_defs

namespace Work.LinnikBurgess

theorem Afact_card_le (g : ℕ) :
    (Work.LinnikBurgess.Afact g).card ≤ g.divisors.card ^ 2 := by
  rcases eq_or_ne g 0 with hg0 | hg0
  · subst hg0
    simp [Afact, Nat.divisors_zero]
  · have hg : 0 < g := Nat.pos_of_ne_zero hg0
    obtain ⟨hinj, hmaps⟩ : Set.InjOn (fun a : Fin 3 → ℕ => (a 0, a 1)) ↑(Afact g) ∧
        Set.MapsTo (fun a : Fin 3 → ℕ => (a 0, a 1)) ↑(Afact g) ↑(g.divisors ×ˢ g.divisors) := by
      constructor
      · intro a ha b hb hab
        rw [Finset.mem_coe, mem_Afact hg] at ha hb
        simp only [Prod.mk.injEq] at hab
        obtain ⟨ha0, ha1⟩ := hab
        obtain ⟨haprod, hadvd⟩ := ha
        obtain ⟨hbprod, hbdvd⟩ := hb
        have hpos : 0 < a 0 * a 1 :=
          Nat.mul_pos (Nat.pos_of_dvd_of_pos (hadvd 0) hg) (Nat.pos_of_dvd_of_pos (hadvd 1) hg)
        rw [Fin.prod_univ_three] at haprod hbprod
        have h2 : a 2 = b 2 := by
          apply Nat.mul_left_cancel hpos
          rw [← ha0, ← ha1] at hbprod
          rw [hbprod, haprod]
        funext k
        fin_cases k
        · exact ha0
        · exact ha1
        · exact h2
      · intro a ha
        rw [Finset.mem_coe, mem_Afact hg] at ha
        obtain ⟨-, hadvd⟩ := ha
        simp only [Finset.mem_coe, Finset.mem_product]
        exact ⟨Nat.mem_divisors.mpr ⟨hadvd 0, hg0⟩, Nat.mem_divisors.mpr ⟨hadvd 1, hg0⟩⟩
    have hcard := Finset.card_le_card_of_injOn (fun a : Fin 3 → ℕ => (a 0, a 1)) hmaps hinj
    rw [Finset.card_product] at hcard
    simpa [pow_two] using hcard

end Work.LinnikBurgess
