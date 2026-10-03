import Mathlib

namespace Work.FIArea1

open Finset

/-- **Sums of a function of `|z|` over the punctured symmetric interval.**

For any `h : ℕ → ℝ`, `Σ_{z ∈ [-L,L] ∖ {0}} h |z| = 2 · Σ_{1 ≤ m ≤ L} h m`: the punctured
interval is the disjoint union of its positive and its negative half, and `z ↦ |z|` identifies
each half with `[1,L]` (via `|−m| = m`). -/
private lemma sum_natAbs_Icc_erase (L : ℕ) (h : ℕ → ℝ) :
    ∑ z ∈ (Finset.Icc (-(L : ℤ)) (L : ℤ)).erase 0, h z.natAbs
      = 2 * ∑ m ∈ Finset.Icc 1 L, h m := by
  have hset : (Finset.Icc (-(L : ℤ)) (L : ℤ)).erase 0
      = (Finset.Icc 1 L).image (fun m : ℕ => (m : ℤ))
        ∪ (Finset.Icc 1 L).image (fun m : ℕ => -((m : ℤ))) := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hz0, h1, h2⟩
      by_cases h : 0 ≤ z
      · exact Or.inl ⟨z.toNat, ⟨by omega, by omega⟩, by omega⟩
      · exact Or.inr ⟨(-z).toNat, ⟨by omega, by omega⟩, by omega⟩
    · rintro (⟨m, ⟨hm1, hm2⟩, rfl⟩ | ⟨m, ⟨hm1, hm2⟩, rfl⟩) <;>
        exact ⟨by omega, by omega, by omega⟩
  rw [hset]
  have hdisj : Disjoint ((Finset.Icc 1 L).image (fun m : ℕ => (m : ℤ)))
      ((Finset.Icc 1 L).image (fun m : ℕ => -((m : ℤ)))) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    simp only [Finset.mem_image, Finset.mem_Icc] at hz hz'
    obtain ⟨m, ⟨hm1, _⟩, rfl⟩ := hz
    obtain ⟨m', ⟨hm1', _⟩, hm'⟩ := hz'
    omega
  rw [Finset.sum_union hdisj,
    Finset.sum_image (f := fun z : ℤ => h z.natAbs) (g := fun m : ℕ => (m : ℤ))
      (by intro a _ b _ hab; exact Nat.cast_injective hab),
    Finset.sum_image (f := fun z : ℤ => h z.natAbs) (g := fun m : ℕ => -((m : ℤ)))
      (by intro a _ b _ hab; exact Nat.cast_injective (neg_inj.mp hab))]
  simp only [Int.natAbs_neg, Int.natAbs_natCast]
  ring

/-- **Reduction of a sum over the signed square to the positive quadrant.**

For any `F : ℕ × ℕ → ℝ` which is nonnegative on the positive square `[1,L]²`,
`Σ_{c₁,c₂ ∈ [-L,L]∖{0}} F (|c₁|,|c₂|) ≤ 4 · Σ_{m₁,m₂ ∈ [1,L]} F (m₁,m₂)`.

*Route.* The map `cc ↦ (|cc.1|,|cc.2|)` sends `([-L,L] ∖ {0})²` onto `[1,L]²`, and each fibre
consists of the (at most four) pairs `(±m₁, ±m₂)`: inject the fibre into `Bool × Bool` via the
two signs (or note the fibre is contained in the explicit four-element set and use
`Finset.card_le_card`). Then collect by fibres, e.g. with
`Finset.card_eq_sum_card_fiberwise`/`Finset.sum_biUnion`. -/
theorem l51_sign_sum_le (L : ℕ) (F : ℕ × ℕ → ℝ)
    (hF : ∀ p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L), 0 ≤ F p) :
    (∑ cc ∈ ((Finset.Icc (-(L : ℤ)) (L : ℤ)).erase 0).product
              ((Finset.Icc (-(L : ℤ)) (L : ℤ)).erase 0),
        F (cc.1.natAbs, cc.2.natAbs))
      ≤ 4 * ∑ p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L), F p := by
  classical
  set A : Finset ℤ := (Finset.Icc (-(L : ℤ)) (L : ℤ)).erase 0 with hA
  -- Reflecting the sign of one coordinate multiplies the sum over `A` by exactly `2`.
  have key : ∀ g : ℕ → ℝ, (∑ z ∈ A, g z.natAbs) = 2 * ∑ m ∈ Finset.Icc 1 L, g m := by
    intro g
    rw [hA]
    exact sum_natAbs_Icc_erase L g
  have heq : (∑ cc ∈ A.product A, F (cc.1.natAbs, cc.2.natAbs))
      = 4 * ∑ p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L), F p := by
    rw [Finset.product_eq_sprod, Finset.sum_product]
    calc ∑ x ∈ A, ∑ y ∈ A, F (x.natAbs, y.natAbs)
        = 2 * ∑ m1 ∈ Finset.Icc 1 L, ∑ y ∈ A, F (m1, y.natAbs) := by
          rw [key (fun m => ∑ y ∈ A, F (m, y.natAbs))]
      _ = 2 * ∑ m1 ∈ Finset.Icc 1 L, 2 * ∑ m2 ∈ Finset.Icc 1 L, F (m1, m2) := by
          rw [Finset.sum_congr rfl (fun m _ => key (fun m2 => F (m, m2)))]
      _ = 2 * (2 * ∑ m1 ∈ Finset.Icc 1 L, ∑ m2 ∈ Finset.Icc 1 L, F (m1, m2)) := by
          rw [← Finset.mul_sum]
      _ = 4 * ∑ m1 ∈ Finset.Icc 1 L, ∑ m2 ∈ Finset.Icc 1 L, F (m1, m2) := by ring
      _ = 4 * ∑ p ∈ (Finset.Icc 1 L).product (Finset.Icc 1 L), F p := by
          rw [Finset.product_eq_sprod, Finset.sum_product]
  exact le_of_eq heq

end Work.FIArea1
