import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

/-- Pure arithmetic: for `a ≥ 5` and any `m`, `4 * (m * a) ≤ 5 * (m * (a - 1))`. -/
lemma endgame_contrib_ge (m a : ℕ) (ha : 5 ≤ a) : 4 * (m * a) ≤ 5 * (m * (a - 1)) := by
  have h : 4 * a ≤ 5 * (a - 1) := by omega
  calc 4 * (m * a) = m * (4 * a) := by ring
    _ ≤ m * (5 * (a - 1)) := Nat.mul_le_mul_left m h
    _ = 5 * (m * (a - 1)) := by ring

/-- Rational form of `endgame_contrib_ge`. -/
lemma endgame_contrib_ge_rat (m a : ℕ) (ha : 5 ≤ a) :
    (4 : ℚ) * ((m : ℚ) * (a : ℚ)) ≤ 5 * ((m : ℚ) * ((a : ℚ) - 1)) := by
  have h := endgame_contrib_ge m a ha
  have h1 : 1 ≤ a := by omega
  have h' : ((4 * (m * a) : ℕ) : ℚ) ≤ ((5 * (m * (a - 1)) : ℕ) : ℚ) := by
    exact_mod_cast h
  push_cast [Nat.cast_sub h1] at h'
  linarith

/-- Endgame cardinality bound: the set `V` of admissible primes has at most three
elements.

Each `a ∈ V` satisfies `m a * a * k a = q^2 (q-1) (q^2+1)` with `k a ∈ {2,4}`, and
`q - 1 ∈ V` with `k (q-1) = 2`.  Dividing the defining relation by `a * k a` and
using `a ≥ 5` bounds each contribution `m a * (a-1)` from below by `Q/5` (and by
`2Q/5` for `a = q - 1`, where `k = 2`), with `Q = q^2 (q-1) (q^2+1)`.  Summing
and comparing with the given total `Q - q^4 - B ≤ Q - q^4` yields
`(V.card - 1) · Q/5 ≤ 3Q/5 - q^4 < 3Q/5`, hence `V.card - 1 < 3`. -/
lemma endgame_card_le_three {q B : ℕ} {V : Finset ℕ} {m k : ℕ → ℕ}
    (hq : 1 ≤ q)
    (hV : ∀ a ∈ V, 5 ≤ a)
    (hk : ∀ a ∈ V, k a = 2 ∨ k a = 4)
    (hm : ∀ a ∈ V, m a * a * k a = q ^ 2 * (q - 1) * (q ^ 2 + 1))
    (hsum1 : ∑ a ∈ V, (m a : ℚ) * (a - 1)
        = (q ^ 2 * (q - 1) * (q ^ 2 + 1) : ℚ) - (q : ℚ) ^ 4 - (B : ℚ))
    (hD : q - 1 ∈ V) (hDk : k (q - 1) = 2) :
    V.card ≤ 3 := by
  set Qn : ℕ := q ^ 2 * (q - 1) * (q ^ 2 + 1) with hQn
  have hQr : ((Qn : ℕ) : ℚ) = (q : ℚ) ^ 2 * ((q : ℚ) - 1) * ((q : ℚ) ^ 2 + 1) := by
    rw [hQn]; push_cast [Nat.cast_sub hq]; ring
  rw [← hQr] at hsum1
  have hq6 : 6 ≤ q := by have := hV (q - 1) hD; omega
  have hQnpos_nat : 0 < Qn := by
    rw [hQn]
    have h1 : 0 < q ^ 2 := pow_pos (by omega : 0 < q) 2
    have h2 : 0 < q - 1 := by omega
    have h3 : 0 < q ^ 2 + 1 := by omega
    exact mul_pos (mul_pos h1 h2) h3
  have hQnpos : (0 : ℚ) < (Qn : ℚ) := by exact_mod_cast hQnpos_nat
  -- every `a ∈ V` contributes at least `Qn/5`
  have hgen : ∀ a ∈ V, (Qn : ℚ) / 5 ≤ (m a : ℚ) * ((a : ℚ) - 1) := by
    intro a ha
    have ha5 : 5 ≤ a := hV a ha
    have hc := endgame_contrib_ge_rat (m a) a ha5
    have hQa : (Qn : ℚ) = (m a : ℚ) * (a : ℚ) * (k a : ℚ) := by
      rw [← hm a ha]; push_cast; ring
    rcases hk a ha with hk2 | hk4
    · rw [hQa, hk2]
      have hnn : 0 ≤ (m a : ℚ) * (a : ℚ) := by positivity
      linarith [hc, hnn]
    · rw [hQa, hk4]
      linarith [hc]
  -- the special element `q - 1` (with `k = 2`) contributes at least `2 Qn/5`
  have hspec : 2 * ((Qn : ℚ) / 5) ≤ (m (q - 1) : ℚ) * (((q - 1 : ℕ) : ℚ) - 1) := by
    have h1 : 5 ≤ q - 1 := hV (q - 1) hD
    have hc := endgame_contrib_ge_rat (m (q - 1)) (q - 1) h1
    have hQa : (Qn : ℚ) = (m (q - 1) : ℚ) * ((q - 1 : ℕ) : ℚ) * (k (q - 1) : ℚ) := by
      rw [← hm (q - 1) hD]; push_cast; ring
    rw [hQa, hDk]
    linarith [hc]
  have hbound_rest : ((V.erase (q - 1)).card : ℚ) * ((Qn : ℚ) / 5)
      ≤ ∑ a ∈ V.erase (q - 1), (m a : ℚ) * ((a : ℚ) - 1) := by
    have := Finset.card_nsmul_le_sum (V.erase (q - 1))
      (fun a => (m a : ℚ) * ((a : ℚ) - 1)) ((Qn : ℚ) / 5) (by
        intro a ha
        exact hgen a (Finset.mem_of_mem_erase ha))
    simpa [nsmul_eq_mul] using this
  have hsum_decomp : ∑ a ∈ V, (m a : ℚ) * ((a : ℚ) - 1)
      = (m (q - 1) : ℚ) * (((q - 1 : ℕ) : ℚ) - 1)
        + ∑ a ∈ V.erase (q - 1), (m a : ℚ) * ((a : ℚ) - 1) := by
    rw [← Finset.sum_erase_add V (fun a => (m a : ℚ) * ((a : ℚ) - 1)) hD]
    ring
  have hle : 2 * ((Qn : ℚ) / 5) + ((V.erase (q - 1)).card : ℚ) * ((Qn : ℚ) / 5)
      ≤ ∑ a ∈ V, (m a : ℚ) * ((a : ℚ) - 1) := by
    rw [hsum_decomp]; linarith [hspec, hbound_rest]
  have hle2 : 2 * ((Qn : ℚ) / 5) + ((V.erase (q - 1)).card : ℚ) * ((Qn : ℚ) / 5)
      ≤ (Qn : ℚ) - (q : ℚ) ^ 4 - (B : ℚ) := by
    rw [← hsum1]; exact hle
  have hce : (V.erase (q - 1)).card = V.card - 1 := Finset.card_erase_of_mem hD
  rw [hce] at hle2
  have hBnn : (0 : ℚ) ≤ (B : ℚ) := by positivity
  have hcard : ((V.card - 1 : ℕ) : ℚ) * ((Qn : ℚ) / 5) ≤ 3 * ((Qn : ℚ) / 5) - (q : ℚ) ^ 4 := by
    linarith [hle2, hBnn]
  have hpos5 : (0 : ℚ) < (Qn : ℚ) / 5 := by linarith [hQnpos]
  have hq4pos : (0 : ℚ) < (q : ℚ) ^ 4 := by
    have : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by omega : 0 < q)
    positivity
  have hlt : ((V.card - 1 : ℕ) : ℚ) * ((Qn : ℚ) / 5) < 3 * ((Qn : ℚ) / 5) := by
    linarith [hcard, hq4pos]
  have hlt' : ((V.card - 1 : ℕ) : ℚ) < 3 := lt_of_mul_lt_mul_right hlt (le_of_lt hpos5)
  have : V.card - 1 < 3 := by exact_mod_cast hlt'
  omega

end Work.ZassenhausSuzuki.Odd
