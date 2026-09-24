import Mathlib
import Submission.Work.GM.Affine.divisor_bound
import Submission.Work.GM.Affine.card_int_in_interval_le
import Submission.Work.GM.Affine.fiber_card_le_card_divisors

namespace Work.GM.Affine

/-- **Resonance count.** For `r ≥ 0` and `r < |ξ| ≤ X`, the number of pairs `(a,b) ∈ ℤ × ℤ` with
`M₁ ≤ |a|` and `|a*b - ξ| ≤ r` is at most `C_ε (X+r+2)^ε (2r+1)`, where `C_ε` depends only on
`ε` (and not on `M₁`, `r`, `X`, `ξ`). -/
theorem card_mul_pairs_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₁ r X : ℝ), 0 < M₁ → 0 ≤ r → 1 ≤ X →
      ∀ ξ : ℝ, r < |ξ| → |ξ| ≤ X → ∀ P : Finset (ℤ × ℤ),
        (∀ p ∈ P, M₁ ≤ |(p.1 : ℝ)|) →
        (∀ p ∈ P, |((p.1 : ℝ) * (p.2 : ℝ)) - ξ| ≤ r) →
        (P.card : ℝ) ≤ C * (X + r + 2) ^ ε * (2 * r + 1) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := card_divisors_le_const_mul_rpow hε
  refine ⟨2 * Cd, by positivity, ?_⟩
  intro M₁ r X hM₁ hr hX ξ hξr hξX P hP1 hP2
  -- Every product occurring in `P` is non-zero.
  have hPnz : ∀ p ∈ P, p.1 * p.2 ≠ 0 := by
    intro p hp h
    have h2 := hP2 p hp
    have hcast : ((p.1 : ℝ) * (p.2 : ℝ)) = 0 := by rw [← Int.cast_mul, h]; simp
    rw [hcast] at h2
    rw [zero_sub, abs_neg] at h2
    linarith
  -- The set of products occurring in `P`.
  let Q : Finset ℤ := P.image (fun p : ℤ × ℤ => p.1 * p.2)
  have hmap : Set.MapsTo (fun p : ℤ × ℤ => p.1 * p.2) ↑P ↑Q :=
    fun p hp => Finset.mem_image_of_mem _ hp
  have hsum : P.card = ∑ n ∈ Q, (P.filter (fun p => p.1 * p.2 = n)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hQnz : ∀ n ∈ Q, n ≠ 0 := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    exact hPnz p hp
  have hQabs : ∀ n ∈ Q, |(n : ℝ) - ξ| ≤ r := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    have h := hP2 p hp
    rwa [← Int.cast_mul] at h
  -- `Q` has at most `2r + 1` elements.
  have hQcard : (Q.card : ℝ) ≤ 2 * r + 1 := card_int_in_interval_le hr Q hQabs
  -- Every `n ∈ Q` has `|n| ≤ X + r + 2`.
  have hnat : ∀ n ∈ Q, ((n.natAbs : ℕ) : ℝ) ≤ X + r + 2 := by
    intro n hn
    have h := hQabs n hn
    have hn_abs : |(n : ℝ)| ≤ |ξ| + r := by
      calc |(n : ℝ)| = |((n : ℝ) - ξ) + ξ| := by rw [sub_add_cancel]
        _ ≤ |(n : ℝ) - ξ| + |ξ| := abs_add_le _ _
        _ ≤ |ξ| + r := by linarith [h]
    have hcast : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [hcast]
    linarith [hξX, hn_abs]
  -- Each fibre over `n ∈ Q` is bounded by the divisor count.
  have hterm : ∀ n ∈ Q, ((P.filter (fun p => p.1 * p.2 = n)).card : ℝ)
      ≤ 2 * Cd * (X + r + 2) ^ ε := by
    intro n hn
    have hfib : ((P.filter (fun p => p.1 * p.2 = n)).card : ℝ)
        ≤ 2 * ((n.natAbs.divisors.card : ℕ) : ℝ) := by
      have := fiber_card_le_card_divisors hM₁ P hP1 n (hQnz n hn)
      exact_mod_cast this
    have hdiv := hCd n.natAbs
    have hrpow : ((n.natAbs : ℕ) : ℝ) ^ ε ≤ (X + r + 2) ^ ε :=
      Real.rpow_le_rpow (by positivity) (hnat n hn) hε.le
    calc ((P.filter (fun p => p.1 * p.2 = n)).card : ℝ)
        ≤ 2 * ((n.natAbs.divisors.card : ℕ) : ℝ) := hfib
      _ ≤ 2 * (Cd * ((n.natAbs : ℕ) : ℝ) ^ ε) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ ≤ 2 * (Cd * (X + r + 2) ^ ε) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow hCdpos.le) (by norm_num)
      _ = 2 * Cd * (X + r + 2) ^ ε := by ring
  have hPcard : (P.card : ℝ) = ∑ n ∈ Q, ((P.filter (fun p => p.1 * p.2 = n)).card : ℝ) := by
    rw [hsum]; push_cast; rfl
  calc (P.card : ℝ)
      = ∑ n ∈ Q, ((P.filter (fun p => p.1 * p.2 = n)).card : ℝ) := hPcard
    _ ≤ ∑ n ∈ Q, 2 * Cd * (X + r + 2) ^ ε := Finset.sum_le_sum hterm
    _ = (Q.card : ℝ) * (2 * Cd * (X + r + 2) ^ ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * r + 1) * (2 * Cd * (X + r + 2) ^ ε) :=
        mul_le_mul_of_nonneg_right hQcard (by positivity)
    _ = 2 * Cd * (X + r + 2) ^ ε * (2 * r + 1) := by ring

end Work.GM.Affine
