import Mathlib

namespace Work.LinnikAreas2.S3HardAux

/-- The map `d ↦ (gcd d r, d / gcd d r)` sends a divisor `d` of `r * t` to a pair of
divisors of `r` and `t` respectively. -/
theorem sigma_half_supermul (r t : ℕ) :
    (∑ d ∈ (r * t).divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
      ≤ (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
        * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) := by
  -- The quotient `d / gcd d r` is a divisor of `t` whenever `d ∣ r * t`.
  have hdvd_quot : ∀ d ∈ (r * t).divisors, d / d.gcd r ∣ t := by
    intro d hd
    have hmem : d ∈ (r * t).divisors := hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, hne⟩ := hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hne)
    have hgpos : 0 < d.gcd r := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left d r) hdpos
    have h1 : d.gcd r * (d / d.gcd r) ∣ (d.gcd r * (r / d.gcd r)) * t := by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d r),
          Nat.mul_div_cancel' (Nat.gcd_dvd_right d r)]
      exact hdvd
    rw [mul_assoc] at h1
    have h2 : d / d.gcd r ∣ (r / d.gcd r) * t := Nat.dvd_of_mul_dvd_mul_left hgpos h1
    exact (Nat.coprime_div_gcd_div_gcd (m := d) (n := r) hgpos).dvd_of_dvd_mul_left h2
  -- The map lands in `r.divisors ×ˢ t.divisors`.
  have hφmem : ∀ d ∈ (r * t).divisors, (d.gcd r, d / d.gcd r) ∈ r.divisors ×ˢ t.divisors := by
    intro d hd
    have hmem := hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, hne⟩ := hd
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
    exact ⟨⟨Nat.gcd_dvd_right d r, (Nat.mul_ne_zero_iff.mp hne).1⟩,
           ⟨hdvd_quot d hmem, (Nat.mul_ne_zero_iff.mp hne).2⟩⟩
  -- The map is injective, since `gcd d r * (d / gcd d r) = d`.
  have hφinj : Function.Injective (fun d : ℕ => (d.gcd r, d / d.gcd r)) := by
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    calc a = a.gcd r * (a / a.gcd r) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a r)).symm
      _ = b.gcd r * (b / b.gcd r) := by rw [hab.2, hab.1]
      _ = b := Nat.mul_div_cancel' (Nat.gcd_dvd_left b r)
  -- Splitting the reciprocal square root along `d = gcd d r * (d / gcd d r)`.
  have hterm : ∀ d : ℕ, (1 : ℝ) / Real.sqrt (d : ℝ)
      = (1 / Real.sqrt (d.gcd r : ℝ)) * (1 / Real.sqrt ((d / d.gcd r : ℕ) : ℝ)) := by
    intro d
    have hmul : ((d.gcd r) * (d / d.gcd r) : ℕ) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d r)
    have hcast : (d : ℝ) = (d.gcd r : ℝ) * ((d / d.gcd r : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, hmul]
    rw [hcast, Real.sqrt_mul (by positivity), div_mul_div_comm, one_mul]
  -- Expanding the product of the two divisor sums as a double sum.
  have hprod : (∑ a ∈ r.divisors, (1 : ℝ) / Real.sqrt (a : ℝ))
        * (∑ b ∈ t.divisors, (1 : ℝ) / Real.sqrt (b : ℝ))
      = ∑ p ∈ r.divisors ×ˢ t.divisors,
          (1 / Real.sqrt (p.1 : ℝ)) * (1 / Real.sqrt (p.2 : ℝ)) := by
    rw [Finset.sum_mul_sum]
    exact (Finset.sum_product r.divisors t.divisors
      (fun p : ℕ × ℕ => (1 / Real.sqrt (p.1 : ℝ)) * (1 / Real.sqrt (p.2 : ℝ)))).symm
  calc (∑ d ∈ (r * t).divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
      = ∑ d ∈ (r * t).divisors,
          (1 / Real.sqrt (d.gcd r : ℝ)) * (1 / Real.sqrt ((d / d.gcd r : ℕ) : ℝ)) :=
        Finset.sum_congr rfl (fun d _ => hterm d)
    _ = ∑ p ∈ ((r * t).divisors).image (fun d : ℕ => (d.gcd r, d / d.gcd r)),
          (1 / Real.sqrt (p.1 : ℝ)) * (1 / Real.sqrt (p.2 : ℝ)) :=
        (Finset.sum_image
          (f := fun p : ℕ × ℕ => (1 / Real.sqrt (p.1 : ℝ)) * (1 / Real.sqrt (p.2 : ℝ)))
          (g := fun d : ℕ => (d.gcd r, d / d.gcd r))
          (s := (r * t).divisors)
          (fun x _ y _ h => hφinj h)).symm
    _ ≤ ∑ p ∈ r.divisors ×ˢ t.divisors,
          (1 / Real.sqrt (p.1 : ℝ)) * (1 / Real.sqrt (p.2 : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp => by
            rcases Finset.mem_image.mp hp with ⟨d, hd, rfl⟩
            exact hφmem d hd)
          (fun p _ _ => by positivity)
    _ = (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
        * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) := hprod.symm

end Work.LinnikAreas2.S3HardAux
