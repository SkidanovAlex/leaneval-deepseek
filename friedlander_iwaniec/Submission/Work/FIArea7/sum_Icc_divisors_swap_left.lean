import Mathlib

namespace Work.FIArea7

/-- Swap the order of summation in a double sum over `n ∈ [1,N]` and the divisors
`a` of `n` that are `≤ Y`: reindex by writing `n = a * m`. -/
theorem sum_Icc_divisors_swap_left {M : Type*} [AddCommMonoid M] (N Y : ℕ) (G : ℕ → ℕ → M) :
    (∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => a ≤ Y), G a n)
      = ∑ a ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 (N / a), G a (a * m) := by
  rw [Finset.sum_sigma' (Finset.Icc 1 N) (fun n => n.divisors.filter (fun a => a ≤ Y))
        (fun n a => G a n),
      Finset.sum_sigma' (Finset.Icc 1 Y) (fun a => Finset.Icc 1 (N / a))
        (fun a m => G a (a * m))]
  refine Finset.sum_bij (fun x _ => ⟨x.snd, x.fst / x.snd⟩) ?_ ?_ ?_ ?_
  · -- The map lands in the target set `t`.
    intro x hx
    simp only [Finset.mem_sigma] at hx
    obtain ⟨hn, hmem⟩ := hx
    simp only [Finset.mem_Icc] at hn
    obtain ⟨hn1, hn2⟩ := hn
    simp only [Finset.mem_filter] at hmem
    obtain ⟨hdiv, hleY⟩ := hmem
    obtain ⟨hdvd, hnne⟩ := Nat.mem_divisors.mp hdiv
    have hapos : 0 < x.snd := Nat.pos_of_mem_divisors hdiv
    simp only [Finset.mem_sigma, Finset.mem_Icc]
    refine ⟨⟨?_, hleY⟩, ?_, ?_⟩
    · omega
    · exact (Nat.one_le_div_iff hapos).mpr (Nat.le_of_dvd (by omega) hdvd)
    · exact Nat.div_le_div_right hn2
  · -- The map is injective.
    intro x1 hx1 x2 hx2 heq
    simp only [Finset.mem_sigma, Finset.mem_filter] at hx1 hx2
    obtain ⟨_, hdiv1, _⟩ := hx1
    obtain ⟨_, hdiv2, _⟩ := hx2
    obtain ⟨hdvd1, _⟩ := Nat.mem_divisors.mp hdiv1
    obtain ⟨hdvd2, _⟩ := Nat.mem_divisors.mp hdiv2
    have h2 : x1.snd = x2.snd := by
      have := congrArg Sigma.fst heq; simpa using this
    have hq : x1.fst / x1.snd = x2.fst / x2.snd := by
      have := congrArg Sigma.snd heq; simpa using this
    have h1 : x1.fst = x2.fst := by
      rw [← Nat.mul_div_cancel' hdvd1, hq, h2, Nat.mul_div_cancel' hdvd2]
    exact Sigma.ext h1 (heq_of_eq h2)
  · -- The map is surjective.
    intro b hb
    obtain ⟨a, m⟩ := b
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hb
    obtain ⟨⟨ha1, ha2⟩, hm1, hm2⟩ := hb
    refine ⟨⟨a * m, a⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · simp only [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · have hpa : 0 < a := by omega
          have hpm : 0 < m := by omega
          have := Nat.mul_pos hpa hpm
          omega
        · have hpa : 0 < a := by omega
          have hle : m * a ≤ N := (Nat.le_div_iff_mul_le hpa).mp hm2
          calc a * m = m * a := Nat.mul_comm a m
            _ ≤ N := hle
      · simp only [Finset.mem_filter]
        refine ⟨?_, ha2⟩
        rw [Nat.mem_divisors]
        exact ⟨dvd_mul_right a m, Nat.mul_ne_zero (by omega) (by omega)⟩
    · have hdiv : a * m / a = m := Nat.mul_div_right m (by omega)
      change ⟨a, a * m / a⟩ = (⟨a, m⟩ : Sigma (fun _ : ℕ => ℕ))
      rw [hdiv]
  · -- The summands agree.
    intro x hx
    simp only [Finset.mem_sigma, Finset.mem_filter] at hx
    obtain ⟨_, hdiv, _⟩ := hx
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hdiv
    dsimp only
    rw [Nat.mul_div_cancel' hdvd]

end Work.FIArea7
