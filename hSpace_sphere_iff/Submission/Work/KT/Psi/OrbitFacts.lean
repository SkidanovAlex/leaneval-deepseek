import Mathlib
import Submission.Work.KT.Psi.OrbitBasic

namespace Work.KT.Psi

variable {M : Type} [Ring M]

/-- The `i`-th conjugate `g^i F g^(k-i)`, when `i ≤ k`, is idempotent as soon as `F` is. -/
lemma orbSum_conj_idem (g F : M) (k i : ℕ) (hi : i ≤ k) (hF : F * F = F) (hg : g ^ k = 1) :
    (g ^ i * F * g ^ (k - i)) * (g ^ i * F * g ^ (k - i)) = g ^ i * F * g ^ (k - i) := by
  have h : g ^ (k - i) * g ^ i = g ^ k := by rw [← pow_add, Nat.sub_add_cancel hi]
  calc (g ^ i * F * g ^ (k - i)) * (g ^ i * F * g ^ (k - i))
      = g ^ i * F * (g ^ (k - i) * g ^ i) * F * g ^ (k - i) := by noncomm_ring
    _ = g ^ i * F * g ^ k * F * g ^ (k - i) := by rw [h]
    _ = g ^ i * F * g ^ (k - i) := by
        rw [hg]
        rw [show g ^ i * F * 1 * F * g ^ (k - i) = g ^ i * (F * F) * g ^ (k - i) by noncomm_ring, hF]

/-- The orbit sum is idempotent when `F` is idempotent and the `k` conjugates are pairwise
orthogonal. -/
lemma orbSum_mul_self (k : ℕ) (_hk : 0 < k) (F g : M) (hF : F * F = F) (hg : g ^ k = 1)
    (horth : ∀ i j : ℕ, i < k → j < k → i ≠ j →
      (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) = 0) :
    orbSum g F k * orbSum g F k = orbSum g F k := by
  simp only [orbSum]
  calc (∑ i ∈ Finset.range k, g ^ i * F * g ^ (k - i))
        * (∑ i ∈ Finset.range k, g ^ i * F * g ^ (k - i))
      = ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range k,
          (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range k, g ^ i * F * g ^ (k - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_eq_single i]
        · exact orbSum_conj_idem g F k i (le_of_lt (Finset.mem_range.mp hi)) hF hg
        · intro j hj hji
          exact horth i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (fun h => hji h.symm)
        · intro hmem
          exact absurd (Finset.mem_range.mpr (Finset.mem_range.mp hi)) hmem

/-- `F` absorbs the orbit sum on the left: `F * orbSum g F k = F`. -/
lemma orbSum_absorb (k : ℕ) (hk : 0 < k) (F g : M) (hF : F * F = F) (hg : g ^ k = 1)
    (horth : ∀ i j : ℕ, i < k → j < k → i ≠ j →
      (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) = 0) :
    F * orbSum g F k = F := by
  have h0 : g ^ 0 * F * g ^ (k - 0) = F := by simp [hg]
  simp only [orbSum]
  calc F * (∑ i ∈ Finset.range k, g ^ i * F * g ^ (k - i))
      = (g ^ 0 * F * g ^ (k - 0)) * (∑ i ∈ Finset.range k, g ^ i * F * g ^ (k - i)) := by
        rw [h0]
    _ = ∑ i ∈ Finset.range k, (g ^ 0 * F * g ^ (k - 0)) * (g ^ i * F * g ^ (k - i)) := by
        rw [Finset.mul_sum]
    _ = g ^ 0 * F * g ^ (k - 0) := by
        rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hk)]
        · rw [h0, hF]
        · intro j hj hji
          exact horth 0 j hk (Finset.mem_range.mp hj) (fun h => hji h.symm)
    _ = F := h0

/-- The orbit sum commutes with the generator: `g * orbSum g F k = orbSum g F k * g`. -/
lemma orbSum_comm_g (k : ℕ) (_hk : 0 < k) (F g : M) (hg : g ^ k = 1) :
    g * orbSum g F k = orbSum g F k * g := by
  simp only [orbSum]
  have hshift : ∀ i, i < k →
      g * (g ^ i * F * g ^ (k - i)) = (g ^ (i + 1) * F * g ^ (k - (i + 1))) * g := by
    intro i hi
    have h1 : k - (i + 1) + 1 = k - i := by omega
    calc g * (g ^ i * F * g ^ (k - i))
        = (g * g ^ i) * F * g ^ (k - i) := by noncomm_ring
      _ = g ^ (i + 1) * F * g ^ (k - i) := by rw [← pow_succ']
      _ = g ^ (i + 1) * F * g ^ (k - (i + 1)) * g := by
          rw [show g ^ (k - i) = g ^ (k - (i + 1)) * g by rw [← pow_succ, h1]]
          noncomm_ring
  have hre : (∑ i ∈ Finset.range k, g ^ (i + 1) * F * g ^ (k - (i + 1)))
      = (∑ i ∈ Finset.range k, g ^ i * F * g ^ (k - i)) := by
    have h1 := Finset.sum_range_succ' (fun i => g ^ i * F * g ^ (k - i)) k
    have h2 := Finset.sum_range_succ (fun i => g ^ i * F * g ^ (k - i)) k
    have key : (∑ i ∈ Finset.range k, g ^ (i + 1) * F * g ^ (k - (i + 1)))
          + g ^ 0 * F * g ^ (k - 0)
        = (∑ i ∈ Finset.range k, g ^ i * F * g ^ (k - i)) + g ^ k * F * g ^ (k - k) := by
      rw [← h1, h2]
    have h0 : g ^ 0 * F * g ^ (k - 0) = F := by simp [hg]
    have hkF : g ^ k * F * g ^ (k - k) = F := by simp [hg]
    rw [h0, hkF] at key
    exact add_right_cancel key
  calc g * (∑ i ∈ Finset.range k, g ^ i * F * g ^ (k - i))
      = ∑ i ∈ Finset.range k, g * (g ^ i * F * g ^ (k - i)) := by rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range k, (g ^ (i + 1) * F * g ^ (k - (i + 1))) * g := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hshift i (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range k, g ^ (i + 1) * F * g ^ (k - (i + 1))) * g := by
        rw [Finset.sum_mul]
    _ = (∑ i ∈ Finset.range k, g ^ i * F * g ^ (k - i)) * g := by rw [hre]

/-- The orbit sum commutes with any `P` commuting with both `g` and `F`. -/
lemma orbSum_comm_P (k : ℕ) (P F g : M) (hPg : P * g = g * P) (hPF : P * F = F * P) :
    P * orbSum g F k = orbSum g F k * P := by
  simp only [orbSum]
  have hPg' : Commute P g := hPg
  have hPF' : Commute P F := hPF
  have hterm : ∀ i, Commute P (g ^ i * F * g ^ (k - i)) := fun i =>
    ((hPg'.pow_right i).mul_right hPF').mul_right (hPg'.pow_right (k - i))
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => hterm i)


/-- Orbit-side facts about `orbSum g F k = Σ_{i<k} g^i F g^{k-i}`: it is idempotent, it absorbs `F` (`F * O = F`), and it commutes with `g` and with any `P` that commutes with `g` and `F`.  Here `M` is a `ℂ`-algebra, `g^k = 1`, `F*F = F`, and the `k` conjugates of `F` are pairwise orthogonal (`horth`). -/
theorem OrbitFacts {M : Type} [Ring M] [Algebra ℂ M] (k : ℕ) (hk : 0 < k) (P F g : M)
    (hF : F * F = F) (hg : g ^ k = 1) (hPg : P * g = g * P) (hPF : P * F = F * P)
    (horth : ∀ i j : ℕ, i < k → j < k → i ≠ j →
      (g ^ i * F * g ^ (k - i)) * (g ^ j * F * g ^ (k - j)) = 0) :
    (orbSum g F k * orbSum g F k = orbSum g F k) ∧
    (F * orbSum g F k = F) ∧
    (g * orbSum g F k = orbSum g F k * g) ∧
    (P * orbSum g F k = orbSum g F k * P) :=
  ⟨orbSum_mul_self k hk F g hF hg horth, orbSum_absorb k hk F g hF hg horth,
   orbSum_comm_g k hk F g hg, orbSum_comm_P k P F g hPg hPF⟩

end Work.KT.Psi
