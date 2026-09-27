import Mathlib

namespace Work.Mostow

/-- The product of the natural ceilings `⌈c i⌉₊` is bounded by `2 ^ r * ∏ c i` when each
`c i ≥ 1`. Combined with the box-volume hypothesis this gives the counting condition. -/
theorem countingCondition (r : ℕ) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ)
    (ρ : Fin r → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hbig : ∀ i, 1 ≤ 2 * Real.pi / (δ / (2 * Real.sqrt (r : ℝ) * ρ i)))
    (J : ℕ)
    (hbox : (2 : ℝ) ^ r * ((4 * Real.pi * Real.sqrt (r : ℝ)) ^ r * (∏ i, ρ i) / δ ^ r)
      < (J : ℝ) + 1) :
    ∏ i, ⌈2 * Real.pi / (δ / (2 * Real.sqrt (r : ℝ) * ρ i))⌉₊ < J + 1 := by
  set c : Fin r → ℝ := fun i => 2 * Real.pi / (δ / (2 * Real.sqrt (r : ℝ) * ρ i)) with hc
  have hc_eq : ∀ i, c i = 2 * Real.pi / (δ / (2 * Real.sqrt (r : ℝ) * ρ i)) := fun i => by rw [hc]
  -- rewrite each factor in the simplified (denominator-cleared) form
  have hci : ∀ i, c i = (4 * Real.pi * Real.sqrt (r : ℝ) * ρ i) / δ := by
    intro i
    rw [hc_eq i]
    have hδ' : δ ≠ 0 := ne_of_gt hδ
    have hρi : ρ i ≠ 0 := ne_of_gt (hρ i)
    have hsq : Real.sqrt (r : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by exact_mod_cast hr))
    field_simp
    ring
  have hc_pos : ∀ i, 0 < c i := fun i => lt_of_lt_of_le zero_lt_one (by rw [hc_eq i]; exact hbig i)
  -- each ceiling is at most twice its argument, since the argument is at least `1`
  have hbound : ∀ i, ((⌈c i⌉₊ : ℕ) : ℝ) ≤ 2 * c i := by
    intro i
    have h1 : ((⌈c i⌉₊ : ℕ) : ℝ) < c i + 1 := Nat.ceil_lt_add_one (le_of_lt (hc_pos i))
    have h2 : 1 ≤ c i := by rw [hc_eq i]; exact hbig i
    linarith
  have hprod_le : (∏ i, ((⌈c i⌉₊ : ℕ) : ℝ)) ≤ ∏ i, 2 * c i :=
    Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hbound i)
  -- the product of the `c i` is exactly the box volume expression
  have hprod_c : ∏ i, c i = (4 * Real.pi * Real.sqrt (r : ℝ)) ^ r * (∏ i, ρ i) / δ ^ r := by
    rw [Finset.prod_congr rfl (fun i _ => hci i)]
    rw [Finset.prod_div_distrib]
    rw [Finset.prod_mul_distrib]
    simp [Finset.prod_const, Finset.card_univ]
  have hprod2 : (∏ i, 2 * c i) = (2 : ℝ) ^ r * ∏ i, c i := by
    rw [Finset.prod_mul_distrib]
    simp [Finset.prod_const, Finset.card_univ]
  have hfinal : ((∏ i, ⌈c i⌉₊ : ℕ) : ℝ) < ((J + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    calc ∏ i, ((⌈c i⌉₊ : ℕ) : ℝ) ≤ ∏ i, 2 * c i := hprod_le
      _ = (2 : ℝ) ^ r * ∏ i, c i := hprod2
      _ = (2 : ℝ) ^ r * ((4 * Real.pi * Real.sqrt (r : ℝ)) ^ r * (∏ i, ρ i) / δ ^ r) := by
            rw [hprod_c]
      _ < (J : ℝ) + 1 := hbox
      _ = ((J + 1 : ℕ) : ℝ) := by push_cast; ring
  exact_mod_cast hfinal

end Work.Mostow
