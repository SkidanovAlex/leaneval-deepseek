import Mathlib

namespace Work.ZeroDensity.Montgomery

/-- For `m ≠ 0`, `(m.divisors.card : ℝ) / (m : ℝ)` equals the sum of
`(1/p.1) * (1/p.2)` over the antidiagonal of pairs with `p.1 * p.2 = m`. -/
lemma card_div_eq_sum_divisorsAntidiagonal (m : ℕ) (_hm : m ≠ 0) :
    (m.divisors.card : ℝ) / (m : ℝ)
      = ∑ p ∈ m.divisorsAntidiagonal, (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ)) := by
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (1 / (a : ℝ)) * (1 / (b : ℝ)))]
  rw [Finset.sum_congr rfl (fun d hd => ?_)]
  · rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  · have hdvd : d ∣ m := (Nat.mem_divisors.mp hd).1
    have hcast : ((m / d : ℕ) : ℝ) * (d : ℝ) = (m : ℝ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    rw [one_div, one_div, mul_comm, ← mul_inv, hcast]

/-- `∑_{1 ≤ d ≤ M} 1/d ≤ 1 + log M`. -/
lemma sum_Ioc_inv_le_one_add_log (M : ℕ) :
    ∑ d ∈ Finset.Ioc 0 M, (1 / (d : ℝ)) ≤ 1 + Real.log (M : ℝ) := by
  have h := harmonic_le_one_add_log M
  have h1 : (harmonic M : ℝ) = ∑ i ∈ Finset.Icc 1 M, (1 / (i : ℝ)) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  rw [h1] at h
  rwa [show Finset.Icc 1 M = Finset.Ioc 0 M from by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega] at h

/-- Reindexing (hyperbola method): summing `G p` over `1 ≤ m ≤ M` and pairs `p` with
`p.1 * p.2 = m` is the same as summing `G p` over all pairs `p` with `1 ≤ p.1, p.2 ≤ M`
and `p.1 * p.2 ≤ M`. -/
lemma divisorsAntidiagonal_reindex (M : ℕ) (G : ℕ × ℕ → ℝ) :
    ∑ m ∈ Finset.Ioc 0 M, ∑ p ∈ m.divisorsAntidiagonal, G p
      = ∑ p ∈ ((Finset.Ioc 0 M) ×ˢ (Finset.Ioc 0 M)).filter (fun q => q.1 * q.2 ≤ M), G p := by
  set s : Finset (Sigma (fun _ : ℕ => ℕ × ℕ)) :=
    (Finset.Ioc 0 M).sigma (fun m => m.divisorsAntidiagonal) with hs
  set T : Finset (ℕ × ℕ) :=
    ((Finset.Ioc 0 M) ×ˢ (Finset.Ioc 0 M)).filter (fun q => q.1 * q.2 ≤ M) with hT
  have hL : (∑ m ∈ Finset.Ioc 0 M, ∑ p ∈ m.divisorsAntidiagonal, G p) = ∑ x ∈ s, G x.2 := by
    rw [hs]
    exact (Finset.sum_sigma (Finset.Ioc 0 M) (fun m => m.divisorsAntidiagonal)
      (fun x => G x.2)).symm
  have hbij : ∑ x ∈ s, G x.2 = ∑ p ∈ T, G p := by
    refine Finset.sum_bij' (fun x _ => x.2) (fun p _ => ⟨p.1 * p.2, p⟩) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [hs, Finset.mem_sigma] at hx
      obtain ⟨hm, hx2⟩ := hx
      rw [Nat.mem_divisorsAntidiagonal] at hx2
      obtain ⟨hprod, -⟩ := hx2
      obtain ⟨hm1, hm2⟩ := Finset.mem_Ioc.mp hm
      have hpos1 : 0 < x.2.1 := Nat.pos_of_mul_pos_right (by rw [hprod]; exact hm1)
      have hpos2 : 0 < x.2.2 := Nat.pos_of_mul_pos_left (by rw [hprod]; exact hm1)
      have hle1 : x.2.1 ≤ M := by
        calc x.2.1 ≤ x.2.1 * x.2.2 := Nat.le_mul_of_pos_right _ hpos2
          _ = x.1 := hprod
          _ ≤ M := hm2
      have hle2 : x.2.2 ≤ M := by
        calc x.2.2 ≤ x.2.1 * x.2.2 := Nat.le_mul_of_pos_left _ hpos1
          _ = x.1 := hprod
          _ ≤ M := hm2
      rw [hT, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨Finset.mem_Ioc.mpr ⟨hpos1, hle1⟩, Finset.mem_Ioc.mpr ⟨hpos2, hle2⟩⟩,
        by rw [hprod]; exact hm2⟩
    · intro p hp
      rw [hT, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hle⟩ := hp
      obtain ⟨hp1', -⟩ := Finset.mem_Ioc.mp hp1
      obtain ⟨hp2', -⟩ := Finset.mem_Ioc.mp hp2
      rw [hs, Finset.mem_sigma]
      exact ⟨Finset.mem_Ioc.mpr ⟨Nat.mul_pos hp1' hp2', hle⟩,
        Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, (Nat.mul_pos hp1' hp2').ne'⟩⟩
    · intro x hx
      rw [hs, Finset.mem_sigma] at hx
      obtain ⟨-, hx2⟩ := hx
      rw [Nat.mem_divisorsAntidiagonal] at hx2
      obtain ⟨hprod, -⟩ := hx2
      rw [hprod]
    · intro p hp; rfl
    · intro x hx; rfl
  rw [hL, hbij]

theorem divisorsCardDivSum_le (M : ℕ) :
    ∑ m ∈ Finset.Ioc 0 M, ((m.divisors.card : ℝ) / (m : ℝ)) ≤ (1 + Real.log (M : ℝ)) ^ 2 := by
  have h1 : ∑ m ∈ Finset.Ioc 0 M, ((m.divisors.card : ℝ) / (m : ℝ))
      = ∑ m ∈ Finset.Ioc 0 M, ∑ p ∈ m.divisorsAntidiagonal,
          (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ)) :=
    Finset.sum_congr rfl fun m hm =>
      card_div_eq_sum_divisorsAntidiagonal m (by
        have : 0 < m := (Finset.mem_Ioc.mp hm).1; omega)
  rw [h1, divisorsAntidiagonal_reindex M (fun p => (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ)))]
  calc ∑ p ∈ ((Finset.Ioc 0 M) ×ˢ (Finset.Ioc 0 M)).filter (fun q => q.1 * q.2 ≤ M),
          (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ))
      ≤ ∑ p ∈ (Finset.Ioc 0 M) ×ˢ (Finset.Ioc 0 M),
          (1 / (p.1 : ℝ)) * (1 / (p.2 : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro p hp _
        exact mul_nonneg (by rw [one_div]; exact inv_nonneg.mpr (Nat.cast_nonneg _))
          (by rw [one_div]; exact inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (∑ d ∈ Finset.Ioc 0 M, (1 / (d : ℝ))) ^ 2 := by
        rw [Finset.sum_product]
        change ∑ x ∈ Finset.Ioc 0 M, ∑ y ∈ Finset.Ioc 0 M,
          (1 / (x : ℝ)) * (1 / (y : ℝ)) = _
        rw [← Finset.sum_mul_sum]; ring
    _ ≤ (1 + Real.log (M : ℝ)) ^ 2 :=
        pow_le_pow_left₀
          (Finset.sum_nonneg fun d _ => by rw [one_div]; exact inv_nonneg.mpr (Nat.cast_nonneg d))
          (sum_Ioc_inv_le_one_add_log M) 2

end Work.ZeroDensity.Montgomery
