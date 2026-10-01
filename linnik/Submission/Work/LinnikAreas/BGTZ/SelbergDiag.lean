import Mathlib

open scoped BigOperators

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ}

/-- Permutation of a triple sum. -/
private lemma sum3_swap (T : Finset ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T, F l d e) = ∑ d ∈ T, ∑ e ∈ T, ∑ l ∈ T, F l d e := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  exact Finset.sum_comm

/-- **Diagonalisation of the `lcm`-kernel double sum.** -/
theorem lcm_diagonalization (T : Finset ℕ) (hTpos : ∀ d ∈ T, 0 < d)
    (hTclosed : ∀ {l d : ℕ}, l ∣ d → d ∈ T → l ∈ T)
    (g h w : ℕ → ℝ) (hne : ∀ d ∈ T, ∀ e ∈ T, h d ≠ 0 ∧ h e ≠ 0 ∧ h (Nat.lcm d e) ≠ 0)
    (hlcm : ∀ d ∈ T, ∀ e ∈ T, h d * h e = h (Nat.lcm d e) * h (Nat.gcd d e))
    (hg : ∀ n ∈ T, h n = ∑ δ ∈ n.divisors, g δ) :
    (∑ d ∈ T, ∑ e ∈ T, w d * w e / h (Nat.lcm d e))
      = ∑ l ∈ T, g l * (∑ d ∈ T.filter (fun d => l ∣ d), w d / h d) ^ 2 := by
  classical
  set A : ℕ → ℝ := fun d => w d / h d with hA
  have hfilt : ∀ d ∈ T, ∀ e ∈ T,
      (∑ l ∈ T.filter (fun l => l ∣ d ∧ l ∣ e), g l) = h (Nat.gcd d e) := by
    intro d hd e he
    have hd0 : d ≠ 0 := ne_of_gt (hTpos d hd)
    have hg0 : Nat.gcd d e ≠ 0 := fun h => hd0 (Nat.gcd_eq_zero_iff.mp h).1
    have hset : T.filter (fun l => l ∣ d ∧ l ∣ e) = (Nat.gcd d e).divisors := by
      ext l
      rw [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Nat.dvd_gcd h2.1 h2.2, hg0⟩
      · rintro ⟨h1, -⟩
        exact ⟨hTclosed (Nat.dvd_trans h1 (Nat.gcd_dvd_left d e)) hd,
          Nat.dvd_trans h1 (Nat.gcd_dvd_left d e), Nat.dvd_trans h1 (Nat.gcd_dvd_right d e)⟩
    rw [hset]
    exact (hg (Nat.gcd d e) (hTclosed (Nat.gcd_dvd_left d e) hd)).symm
  have hterm : ∀ d ∈ T, ∀ e ∈ T,
      w d * w e / h (Nat.lcm d e)
        = A d * A e * (∑ l ∈ T.filter (fun l => l ∣ d ∧ l ∣ e), g l) := by
    intro d hd e he
    obtain ⟨hdne, hene, hlne⟩ := hne d hd e he
    have hkey := hlcm d hd e he
    have hgne : h (Nat.gcd d e) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hkey
      exact (mul_ne_zero hdne hene) hkey
    rw [hfilt d hd e he, hA, div_mul_div_comm, div_mul_eq_mul_div,
      div_eq_div_iff hlne (mul_ne_zero hdne hene), hkey]
    ring
  have hR1 : (∑ l ∈ T, g l * (∑ d ∈ T.filter (fun d => l ∣ d), A d) ^ 2)
      = ∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T,
          (if l ∣ d ∧ l ∣ e then g l * (A d * A e) else 0) := by
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [Finset.sum_filter, pow_two, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => ?_))
    by_cases h1 : l ∣ d <;> by_cases h2 : l ∣ e <;> simp [h1, h2, mul_assoc, mul_left_comm, mul_comm]
  have hR2 : (∑ l ∈ T, ∑ d ∈ T, ∑ e ∈ T,
        (if l ∣ d ∧ l ∣ e then g l * (A d * A e) else 0))
      = ∑ d ∈ T, ∑ e ∈ T, A d * A e * (∑ l ∈ T.filter (fun l => l ∣ d ∧ l ∣ e), g l) := by
    rw [sum3_swap]
    refine Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => ?_))
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    by_cases h : l ∣ d ∧ l ∣ e <;> simp [h, mul_assoc, mul_left_comm, mul_comm]
  rw [hR1, hR2]
  exact Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun e he => hterm d hd e he))

end Work.LinnikAreas.BGTZ
