import Mathlib

namespace Work.ZeroDensity.Montgomery

theorem sumDivisorsRecip_eq (N : ℕ) (a b : ℕ → ℝ) :
    ∑ n ∈ Finset.Ioc 0 N, (1 / (n : ℝ)) * ∑ d ∈ n.divisors, a d * b (n / d)
      = ∑ d ∈ Finset.Ioc 0 N, (a d / (d : ℝ)) * ∑ m ∈ Finset.Ioc 0 (N / d), (b m / (m : ℝ)) := by
  have key :
      (∑ x ∈ (Finset.Ioc 0 N).sigma (fun n => n.divisors),
          (1 / (x.1 : ℝ)) * (a x.2 * b (x.1 / x.2)))
        = ∑ y ∈ (Finset.Ioc 0 N).sigma (fun d => Finset.Ioc 0 (N / d)),
          (a y.1 / (y.1 : ℝ)) * (b y.2 / (y.2 : ℝ)) := by
    refine Finset.sum_bij
      (fun (x : Sigma (fun _ : ℕ => ℕ)) _ => (⟨x.2, x.1 / x.2⟩ : Sigma (fun _ : ℕ => ℕ)))
      ?_ ?_ ?_ ?_
    · rintro ⟨n, d⟩ hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hn, hd⟩ := hx
      rw [Finset.mem_sigma]
      refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, Finset.mem_Ioc.mpr ⟨?_, ?_⟩⟩
      · exact Nat.pos_of_mem_divisors hd
      · exact le_trans (Nat.divisor_le hd) (Finset.mem_Ioc.mp hn).2
      · exact Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
      · exact Nat.div_le_div_right (Finset.mem_Ioc.mp hn).2
    · rintro ⟨n, d⟩ hx ⟨n', d'⟩ hx' h
      rw [Finset.mem_sigma] at hx hx'
      injection h with h1 h2
      have h1' : d = d' := h1
      have h2' : n / d = n' / d' := h2
      have hd : d ∣ n := (Nat.mem_divisors.mp hx.2).1
      have hd' : d' ∣ n' := (Nat.mem_divisors.mp hx'.2).1
      have hn : n = n' := by
        calc n = d * (n / d) := (Nat.mul_div_cancel' hd).symm
          _ = d' * (n' / d') := by rw [h2', h1']
          _ = n' := Nat.mul_div_cancel' hd'
      rw [hn, h1']
    · rintro ⟨d, m⟩ hy
      rw [Finset.mem_sigma] at hy
      obtain ⟨hd, hm⟩ := hy
      have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
      have hm0 : 0 < m := (Finset.mem_Ioc.mp hm).1
      have hmul : d * m ≤ N := by
        rw [Nat.mul_comm]
        exact (Nat.le_div_iff_mul_le hd0).mp (Finset.mem_Ioc.mp hm).2
      refine ⟨⟨d * m, d⟩, ?_, ?_⟩
      · rw [Finset.mem_sigma]
        exact ⟨Finset.mem_Ioc.mpr ⟨Nat.mul_pos hd0 hm0, hmul⟩,
          Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right d m, (Nat.mul_pos hd0 hm0).ne'⟩⟩
      · show (⟨d, d * m / d⟩ : Sigma (fun _ : ℕ => ℕ)) = ⟨d, m⟩
        rw [Nat.mul_div_cancel_left m hd0]
    · rintro ⟨n, d⟩ hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hn, hd⟩ := hx
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hmdpos : 0 < n / d := Nat.div_pos (Nat.divisor_le hd) hdpos
      have hcast : (n : ℝ) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      rw [hcast]
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
      have hm0 : ((n / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hmdpos.ne'
      field_simp
  have hL : (∑ n ∈ Finset.Ioc 0 N, (1 / (n : ℝ)) * ∑ d ∈ n.divisors, a d * b (n / d))
      = ∑ x ∈ (Finset.Ioc 0 N).sigma (fun n => n.divisors),
          (1 / (x.1 : ℝ)) * (a x.2 * b (x.1 / x.2)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma']
  have hR : (∑ d ∈ Finset.Ioc 0 N, (a d / (d : ℝ)) * ∑ m ∈ Finset.Ioc 0 (N / d),
        (b m / (m : ℝ)))
      = ∑ y ∈ (Finset.Ioc 0 N).sigma (fun d => Finset.Ioc 0 (N / d)),
          (a y.1 / (y.1 : ℝ)) * (b y.2 / (y.2 : ℝ)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_sigma']
  rw [hL, hR]
  exact key

end Work.ZeroDensity.Montgomery
