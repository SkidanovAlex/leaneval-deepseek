import Mathlib

namespace Commons.Combinatorics.Additive.Szemeredi

/-- Auxiliary transfer: a finite-interval Szemerédi-type statement yields,
for `k ≥ 2`, arbitrarily long nondegenerate arithmetic progressions in
`ZMod p` for all sufficiently large primes `p`, for subsets of density `≥ δ`.

The proof lifts `A ⊆ ZMod p` to the set `B := A.image ZMod.val ⊆ [0,p)` of
its integer representatives (same cardinality), applies the finite statement
to `B`, and pushes the resulting integer progression back to `ZMod p`; the
common difference is nonzero modulo `p` because the progression lies inside
the interval `[0,p)`. -/
private theorem prime_engine_aux
    (hfin : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ B : Finset ℕ,
      B ⊆ Finset.range N → δ * (N : ℝ) ≤ (B.card : ℝ) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ (B : Set ℕ))
    {k : ℕ} (hk : 2 ≤ k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ P : ℕ, ∀ (p : ℕ) [NeZero p], Nat.Prime p → P ≤ p →
      ∀ A : Finset (ZMod p), δ * (p : ℝ) ≤ (A.card : ℝ) →
        ∃ a b : ZMod p, b ≠ 0 ∧ ∀ j : ℕ, j < k → a + (j : ZMod p) * b ∈ A := by
  obtain ⟨N₀, hN₀⟩ := hfin k δ hδ
  refine ⟨N₀, ?_⟩
  intro p _ hp hPp A hAcard
  let B : Finset ℕ := A.image ZMod.val
  have hBsub : B ⊆ Finset.range p := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp (show x ∈ A.image ZMod.val from hx)
    exact Finset.mem_range.mpr (ZMod.val_lt y)
  have hBcard : (B.card : ℝ) = (A.card : ℝ) := by
    have hc : B.card = A.card :=
      Finset.card_image_of_injective A (ZMod.val_injective p)
    rw [hc]
  obtain ⟨a, b, hb, hAP⟩ :=
    hN₀ p hPp B hBsub (by rw [hBcard]; exact hAcard)
  have h1k : 1 < k := by omega
  have hmemb : a + b * 1 ∈ B := hAP 1 h1k
  have hltp : a + b < p := by
    have h := hBsub hmemb
    simp only [Finset.mem_range] at h
    omega
  have hb_lt : b < p := by omega
  have hbne : (b : ZMod p) ≠ 0 := by
    intro h0
    have hv : (b : ZMod p).val = 0 := by rw [h0, ZMod.val_zero]
    rw [ZMod.val_cast_of_lt hb_lt] at hv
    omega
  refine ⟨(a : ZMod p), (b : ZMod p), hbne, ?_⟩
  intro j hj
  have hjB : a + b * j ∈ A.image ZMod.val := hAP j hj
  obtain ⟨x, hxA, hxval⟩ := Finset.mem_image.mp hjB
  convert hxA using 1
  rw [← ZMod.natCast_zmod_val x, hxval]
  push_cast
  ring

theorem prime_engine_of_finite_szemeredi
    (hfin : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ B : Finset ℕ,
      B ⊆ Finset.range N → δ * (N : ℝ) ≤ (B.card : ℝ) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ (B : Set ℕ)) :
    ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ P : ℕ, ∀ (p : ℕ) [NeZero p], Nat.Prime p → P ≤ p →
      ∀ A : Finset (ZMod p), δ * (p : ℝ) ≤ (A.card : ℝ) →
        ∃ a b : ZMod p, b ≠ 0 ∧ ∀ j : ℕ, j < k → a + (j : ZMod p) * b ∈ A := by
  intro k δ hδ
  by_cases hk : 2 ≤ k
  · exact prime_engine_aux hfin hk δ hδ
  · -- `k ≤ 1`: a `2`-term progression settles every shorter request.
    have hk1 : k ≤ 1 := by omega
    obtain ⟨P, hP⟩ := prime_engine_aux hfin (k := 2) (by norm_num) δ hδ
    refine ⟨P, ?_⟩
    intro p _ hp hPp A hAcard
    obtain ⟨a, b, hbne, hAP⟩ := hP p hp hPp A hAcard
    exact ⟨a, b, hbne, fun j hj => hAP j (by omega)⟩

end Commons.Combinatorics.Additive.Szemeredi
