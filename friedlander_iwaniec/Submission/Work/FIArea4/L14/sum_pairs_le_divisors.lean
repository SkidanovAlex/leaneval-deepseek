import Mathlib

namespace Work.FIArea4.L14

theorem sum_pairs_le_divisors (D : ℕ) (Φ : ℕ → ℝ) (hΦ : ∀ q, 0 ≤ Φ q) : ∑ e1 ∈ (Finset.Icc 1 D).filter Odd, ∑ e2 ∈ (Finset.Icc 1 D).filter Odd, (((e1 * e2 : ℕ)) : ℝ)⁻¹ * Φ (e1 * e2) ≤ ∑ q ∈ Finset.Icc 1 (D * D), ((q.divisors.card : ℕ) : ℝ) * Φ q / (q : ℝ) := by
  set S : Finset ℕ := (Finset.Icc 1 D).filter Odd with hSdef
  have hSpos : ∀ e ∈ S, 0 < e := by
    intro e he; rw [hSdef] at he; simp only [Finset.mem_filter, Finset.mem_Icc] at he; omega
  have hSge : ∀ e ∈ S, 1 ≤ e := by
    intro e he; rw [hSdef] at he; simp only [Finset.mem_filter, Finset.mem_Icc] at he; exact he.1.1
  have hSle : ∀ e ∈ S, e ≤ D := by
    intro e he; rw [hSdef] at he; simp only [Finset.mem_filter, Finset.mem_Icc] at he; exact he.1.2
  have hmap : ∀ p ∈ S ×ˢ S, p.1 * p.2 ∈ Finset.Icc 1 (D * D) := by
    intro p hp
    rw [Finset.mem_product] at hp
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.mul_le_mul (hSle p.1 hp.1) (hSle p.2 hp.2)⟩
    have h := Nat.mul_le_mul (hSge p.1 hp.1) (hSge p.2 hp.2)
    simpa using h
  have key : ∑ q ∈ Finset.Icc 1 (D * D), ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = q),
        (((p.1 * p.2 : ℕ)) : ℝ)⁻¹ * Φ (p.1 * p.2)
      = ∑ p ∈ S ×ˢ S, (((p.1 * p.2 : ℕ)) : ℝ)⁻¹ * Φ (p.1 * p.2) :=
    Finset.sum_fiberwise_of_maps_to hmap (fun p => (((p.1 * p.2 : ℕ)) : ℝ)⁻¹ * Φ (p.1 * p.2))
  have hper : ∀ q ∈ Finset.Icc 1 (D * D),
      ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = q), (((p.1 * p.2 : ℕ)) : ℝ)⁻¹ * Φ (p.1 * p.2)
      ≤ ((q.divisors.card : ℕ) : ℝ) * Φ q / (q : ℝ) := by
    intro q hq
    set fiber : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun p => p.1 * p.2 = q) with hfiberdef
    have hstep1 : ∑ p ∈ fiber, (((p.1 * p.2 : ℕ)) : ℝ)⁻¹ * Φ (p.1 * p.2)
        = ∑ p ∈ fiber, (((q : ℕ)) : ℝ)⁻¹ * Φ q := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [hfiberdef, Finset.mem_filter] at hp
      rw [hp.2]
    rw [hstep1, Finset.sum_const, nsmul_eq_mul]
    have hcard : fiber.card ≤ q.divisors.card := by
      have hinj : Set.InjOn Prod.fst (↑fiber : Set (ℕ × ℕ)) := by
        intro p hp p' hp' h
        simp only [Finset.mem_coe, hfiberdef, Finset.mem_filter, Finset.mem_product] at hp hp'
        obtain ⟨hpS, hpq⟩ := hp
        obtain ⟨hp'S, hp'q⟩ := hp'
        have h2 : p.2 = p'.2 := Nat.mul_left_cancel (hSpos p.1 hpS.1) (by rw [hpq, h, hp'q])
        exact Prod.ext h h2
      have hcard_eq : (fiber.image Prod.fst).card = fiber.card := Finset.card_image_of_injOn hinj
      rw [← hcard_eq]
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      simp only [hfiberdef, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨hpS, hpq⟩ := hp
      have hp1 : 0 < p.1 := hSpos p.1 hpS.1
      have hp2 : 0 < p.2 := hSpos p.2 hpS.2
      rw [Nat.mem_divisors]
      exact ⟨⟨p.2, hpq.symm⟩, by rw [← hpq]; exact (Nat.mul_pos hp1 hp2).ne'⟩
    have hcardR : ((fiber.card : ℕ) : ℝ) ≤ ((q.divisors.card : ℕ) : ℝ) := by exact_mod_cast hcard
    have hnn : (0 : ℝ) ≤ (((q : ℕ)) : ℝ)⁻¹ * Φ q := by
      apply mul_nonneg (inv_nonneg.mpr (by positivity)) (hΦ q)
    calc ((fiber.card : ℕ) : ℝ) * ((((q : ℕ)) : ℝ)⁻¹ * Φ q)
        ≤ ((q.divisors.card : ℕ) : ℝ) * ((((q : ℕ)) : ℝ)⁻¹ * Φ q) :=
          mul_le_mul_of_nonneg_right hcardR hnn
      _ = ((q.divisors.card : ℕ) : ℝ) * Φ q / (q : ℝ) := by ring
  calc (∑ e1 ∈ S, ∑ e2 ∈ S, (((e1 * e2 : ℕ)) : ℝ)⁻¹ * Φ (e1 * e2))
      = ∑ p ∈ S ×ˢ S, (((p.1 * p.2 : ℕ)) : ℝ)⁻¹ * Φ (p.1 * p.2) :=
        (Finset.sum_product S S (fun p => (((p.1 * p.2 : ℕ)) : ℝ)⁻¹ * Φ (p.1 * p.2))).symm
    _ = ∑ q ∈ Finset.Icc 1 (D * D), ∑ p ∈ (S ×ˢ S).filter (fun p => p.1 * p.2 = q),
          (((p.1 * p.2 : ℕ)) : ℝ)⁻¹ * Φ (p.1 * p.2) := key.symm
    _ ≤ ∑ q ∈ Finset.Icc 1 (D * D), ((q.divisors.card : ℕ) : ℝ) * Φ q / (q : ℝ) :=
        Finset.sum_le_sum hper

end Work.FIArea4.L14
