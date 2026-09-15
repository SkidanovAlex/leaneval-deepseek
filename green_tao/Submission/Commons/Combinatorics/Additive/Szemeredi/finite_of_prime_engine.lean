import Mathlib
import Submission.Commons.Combinatorics.Additive.AP.exists_ap_of_cyclic_consecutive_mod

namespace Commons.Combinatorics.Additive.Szemeredi

/-- **Finite Szemerédi from a prime engine.** If for every length `k` and density `δ > 0` there is
a threshold `P` such that every `δ`-dense subset of `ZMod p` (for every prime `p ≥ P`) contains a
non-trivial length-`k` arithmetic progression, then every `δ`-dense subset of `{0, …, N-1}`
contains a non-trivial length-`k` arithmetic progression of *natural* numbers, for all large `N`.

The reduction picks, for a dense `B ⊆ {0,…,N-1}`, a prime `p` with `2N+1 < p ≤ 4N+2`
(Bertrand's postulate).  Reducing `B` mod `p` is injective, and the resulting set is `(δ/8)`-dense
in `ZMod p`; the prime engine produces a length-`k` AP there.  Since all the elements lie in the
short interval `{0,…,N-1}` and `p ≥ 2N+1`, consecutive (integer) differences are congruent modulo
`p`, hence equal, so the cyclic progression is a genuine progression of naturals. -/
theorem finite_of_prime_engine
    (h : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ P : ℕ, ∀ p : ℕ, Nat.Prime p → P ≤ p →
        ∀ A : Finset (ZMod p), δ * (p : ℝ) ≤ (A.card : ℝ) →
          ∃ a b : ZMod p, b ≠ 0 ∧ ∀ j : ℕ, j < k → a + (j : ZMod p) * b ∈ A) :
    ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ B : Finset ℕ, B ⊆ Finset.range N →
      δ * (N : ℝ) ≤ (B.card : ℝ) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ (B : Set ℕ) := by
  intro k δ hδ
  by_cases hk : k ≤ 1
  · -- lengths 0 and 1 are trivial
    refine ⟨1, ?_⟩
    intro N hN B hBsub hBcard
    have hNpos : 0 < N := by omega
    have hBpos : 0 < B.card := by
      have h1 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have h2 : (0 : ℝ) < (B.card : ℝ) := lt_of_lt_of_le (by positivity) hBcard
      exact_mod_cast h2
    by_cases hk0 : k = 0
    · exact ⟨0, 1, le_refl 1, fun j hj => by omega⟩
    · have hk1 : k = 1 := by omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hBpos
      refine ⟨a, 1, le_refl 1, ?_⟩
      intro j hj
      have hj0 : j = 0 := by omega
      rw [hj0]
      simpa using ha
  · push Not at hk
    have hk2 : 2 ≤ k := by omega
    have hδ8 : 0 < δ / 8 := by positivity
    obtain ⟨P, hP⟩ := h k (δ / 8) hδ8
    refine ⟨P + 1, ?_⟩
    intro N hN B hBsub hBcard
    have hNpos : 0 < N := by omega
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
    -- A prime `p` with `2N+1 < p ≤ 4N+2`.
    have hPN : 2 * N + 1 ≠ 0 := by omega
    obtain ⟨p, hpprime, hpgt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N + 1) hPN
    have hp_le : p ≤ 4 * N + 2 := by omega
    have hpP : P ≤ p := by omega
    have : NeZero p := ⟨hpprime.ne_zero⟩
    -- Reduce `B` mod `p`.
    let A : Finset (ZMod p) := B.image (fun m : ℕ => (m : ZMod p))
    have hcard : A.card = B.card := by
      dsimp only [A]
      apply Finset.card_image_of_injOn
      intro m1 hm1 m2 hm2 heq
      have h1 : m1 < p := by
        have := Finset.mem_range.mp (hBsub hm1); omega
      have h2 : m2 < p := by
        have := Finset.mem_range.mp (hBsub hm2); omega
      have hmod : m1 % p = m2 % p := (ZMod.natCast_eq_natCast_iff' m1 m2 p).mp heq
      rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
    have hdens : (δ / 8) * (p : ℝ) ≤ (A.card : ℝ) := by
      rw [hcard]
      have hpR : (p : ℝ) ≤ 4 * (N : ℝ) + 2 := by exact_mod_cast hp_le
      calc (δ / 8) * (p : ℝ) ≤ (δ / 8) * (4 * (N : ℝ) + 2) := by
              apply mul_le_mul_of_nonneg_left hpR (by positivity)
        _ = δ * ((4 * (N : ℝ) + 2) / 8) := by ring
        _ ≤ δ * (N : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hδ)
              linarith
        _ ≤ (B.card : ℝ) := hBcard
    obtain ⟨a0, b0, hb0, hap⟩ := hP p hpprime hpP A hdens
    let y : ℕ → ZMod p := fun j => a0 + (j : ZMod p) * b0
    have hyval_mem : ∀ j, j < k → (y j).val ∈ B := by
      intro j hj
      have hyA : y j ∈ A := hap j hj
      obtain ⟨m, hmB, hm⟩ := Finset.mem_image.mp hyA
      rw [← hm]
      have hmM : m < p := by
        have := Finset.mem_range.mp (hBsub hmB); omega
      rw [ZMod.val_cast_of_lt hmM]
      exact hmB
    have hyval_lt : ∀ j, j < k → (y j).val < N := by
      intro j hj
      exact Finset.mem_range.mp (hBsub (hyval_mem j hj))
    let n : ℕ := k - 2
    have hnk : n + 2 = k := by dsimp [n]; omega
    let afun : Fin (n + 2) → ℕ := fun j => (y j.val).val
    have haA : ∀ j : Fin (n + 2), afun j ∈ B := by
      intro j
      exact hyval_mem j.val (by have := j.isLt; omega)
    have haN : ∀ j : Fin (n + 2), afun j < N := by
      intro j
      exact hyval_lt j.val (by have := j.isLt; omega)
    have hstep : ∀ j : Fin (n + 1),
        ((afun j.succ : ℤ) - (afun (j.castSucc : Fin (n + 2)) : ℤ) : ZMod p) = b0 := by
      intro j
      have h1 : ((afun j.succ : ℤ) : ZMod p) = y (j.succ).val := by
        rw [Int.cast_natCast]
        exact ZMod.natCast_zmod_val _
      have h2 : ((afun (j.castSucc : Fin (n + 2)) : ℤ) : ZMod p)
          = y ((j.castSucc : Fin (n + 2))).val := by
        rw [Int.cast_natCast]
        exact ZMod.natCast_zmod_val _
      rw [h1, h2]
      rw [Fin.val_succ, Fin.val_castSucc]
      dsimp only [y]
      have hcast : ((j.val + 1 : ℕ) : ZMod p) = (j.val : ZMod p) + 1 := by
        push_cast; ring
      rw [hcast]
      ring
    have hpge : 2 * N + 1 ≤ p := by omega
    obtain ⟨c, b, hb, hmem⟩ :=
      Commons.Combinatorics.Additive.AP.exists_ap_of_cyclic_consecutive_mod
        (n := n) (N := N) (M := p) (A := B) hpge afun haA haN b0 hb0 hstep
    refine ⟨c, b, hb, ?_⟩
    intro j hj
    have hj' : j < n + 2 := by omega
    have := hmem j hj'
    simpa using this

end Commons.Combinatorics.Additive.Szemeredi
