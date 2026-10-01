import Mathlib

namespace Work.LinnikBurgess

/-- The number of triples of divisors of `g` whose product is `g` is at most the
square of the number of divisors of `g`: the map `a ↦ (a 0, a 1)` is injective on
the set of such triples. -/
theorem card_decompFinset_le {g : ℕ} (hg : 0 < g) :
    ((((Fintype.piFinset fun _ : Fin 3 => g.divisors).filter
        (fun a : Fin 3 → ℕ => ∏ l : Fin 3, a l = g)).card : ℕ) : ℝ)
      ≤ (((g.divisors.card : ℕ)) : ℝ) ^ 2 := by
  have key : ((Fintype.piFinset fun _ : Fin 3 => g.divisors).filter
        (fun a : Fin 3 → ℕ => ∏ l : Fin 3, a l = g)).card
      ≤ g.divisors.card * g.divisors.card := by
    have h1 : ((Fintype.piFinset fun _ : Fin 3 => g.divisors).filter
        (fun a : Fin 3 → ℕ => ∏ l : Fin 3, a l = g)).card
        ≤ (g.divisors ×ˢ g.divisors).card := by
      apply Finset.card_le_card_of_injOn (fun a : Fin 3 → ℕ => (a 0, a 1))
      · intro a ha
        simp only [Finset.mem_coe, Finset.mem_filter] at ha
        exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp ha.1 0,
                                      Fintype.mem_piFinset.mp ha.1 1⟩
      · intro a ha b hb hab
        simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
        simp only [Prod.mk.injEq] at hab
        obtain ⟨h0, h1⟩ := hab
        have hpa : a 0 * a 1 * a 2 = g := by
          have := ha.2; rwa [Fin.prod_univ_three] at this
        have hpb : b 0 * b 1 * b 2 = g := by
          have := hb.2; rwa [Fin.prod_univ_three] at this
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · have hpos : 0 < a 0 * a 1 := by
            have hd0 : a 0 ∣ g := (Nat.mem_divisors.mp (Fintype.mem_piFinset.mp ha.1 0)).1
            have hd1 : a 1 ∣ g := (Nat.mem_divisors.mp (Fintype.mem_piFinset.mp ha.1 1)).1
            exact Nat.mul_pos (Nat.pos_of_dvd_of_pos hd0 hg) (Nat.pos_of_dvd_of_pos hd1 hg)
          have hh : a 0 * a 1 * a 2 = a 0 * a 1 * b 2 := by
            rw [hpa, ← hpb, ← h0, ← h1]
          exact Nat.mul_left_cancel hpos hh
    rwa [Finset.card_product] at h1
  have hcast : ((((Fintype.piFinset fun _ : Fin 3 => g.divisors).filter
        (fun a : Fin 3 → ℕ => ∏ l : Fin 3, a l = g)).card : ℕ) : ℝ)
      ≤ ((g.divisors.card * g.divisors.card : ℕ) : ℝ) := by exact_mod_cast key
  calc ((((Fintype.piFinset fun _ : Fin 3 => g.divisors).filter
        (fun a : Fin 3 → ℕ => ∏ l : Fin 3, a l = g)).card : ℕ) : ℝ)
      ≤ ((g.divisors.card * g.divisors.card : ℕ) : ℝ) := hcast
    _ = ((g.divisors.card : ℕ) : ℝ) ^ 2 := by push_cast; ring

end Work.LinnikBurgess
