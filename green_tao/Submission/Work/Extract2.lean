import Submission.Work.Extract
import Submission.Commons.NumberTheory.PrimesInAP.infinite_affine_prime_set

/-!
# Extraction with a `p`-dependent `W`-trick modulus

Green–Tao's W-trick uses a modulus `W = W(N)` (a primorial) which necessarily *grows* with `N`
(the errors in the pseudorandomness are `O(1/w(N))`).  The extraction lemma of
`Submission.Work.Extract` fixes `W` once and for all, which is therefore unusable for the actual
Green–Tao argument.  This file removes that restriction: `W` is existentially quantified together
with the majorant data, and the conclusion is drawn directly about the primes (no fixed modulus is
needed, since the progression `a + b·j` in `{n | W·n+1 prime}` lifts to the prime progression
`(Wa+1) + (Wb)·j`).
-/

open Finset
open scoped BigOperators

namespace GTTrans

/-- **The extraction with a `p`-dependent W-trick modulus.** -/
theorem contains_arith_prog_of_data_var {εw : ℝ} (hεw : 0 < εw) (hεw4 : 4 * εw < 1)
    (hdata : ∀ (k : ℕ), 3 ≤ k → ∃ (cd : ℝ) (P₁ : ℕ), 0 < cd ∧
      ∀ (p : ℕ) [Fact p.Prime], P₁ ≤ p →
        ∃ (W : ℕ) (f : ZMod p → ℝ) (B : ℝ),
          1 ≤ W ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ B) ∧
          B ^ (k - 1) * (∑ x, f x) < cd * (p : ℝ) ^ 2 ∧
          cd * (p : ℝ) ^ 2 ≤ ∑ x : ZMod p, ∑ r : ZMod p,
            ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r) ∧
          (∀ x, f x ≠ 0 → εw * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * εw * (p : ℝ) ∧
            Nat.Prime (W * x.val + 1))) :
    ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → Nat.Prime (a + b * j) := by
  classical
  intro k
  by_cases hk3 : 3 ≤ k
  · obtain ⟨cd, P₁, hcd, hdat⟩ := hdata k hk3
    obtain ⟨p, hpP, hpprime⟩ := Nat.exists_infinite_primes (max P₁ 2)
    haveI : Fact p.Prime := ⟨hpprime⟩
    have hpP₁ : P₁ ≤ p := le_trans (le_max_left _ _) hpP
    obtain ⟨W, f, B, hW1, hf0, hfB, hBk, hcdle, hsupp⟩ := hdat p hpP₁
    have hB0 : 0 ≤ B := le_trans (hf0 0) (hfB 0)
    obtain ⟨x, r, hr, hterm⟩ :=
      exists_nonzero_term_of_apcount (k := k) (by omega) hf0 hB0 hfB
        (lt_of_lt_of_le hBk hcdle)
    obtain ⟨a, b, hb, hab⟩ :=
      exists_ap_of_nonzero_term (k := k) (p := p) (W := W) (by omega) hεw hεw4 hsupp hr hterm
    refine ⟨W * a + 1, W * b, by simpa using Nat.mul_le_mul hW1 hb, fun j hj => ?_⟩
    have h := hab j hj
    have : W * (a + b * j) + 1 = (W * a + 1) + (W * b) * j := by ring
    rwa [← this]
  · obtain ⟨n₀, hn₀⟩ :=
      (Commons.NumberTheory.PrimesInAP.infinite_affine_prime_set (W := 1) (r := 1)
        (by norm_num) (by simp)).nonempty
    obtain ⟨n₁, hn₁, hlt⟩ :=
      (Commons.NumberTheory.PrimesInAP.infinite_affine_prime_set (W := 1) (r := 1)
        (by norm_num) (by simp)).exists_gt n₀
    refine ⟨n₀ + 1, n₁ - n₀, by omega, fun j hj => ?_⟩
    have hj2 : j = 0 ∨ j = 1 := by omega
    rcases hj2 with rfl | rfl
    · simpa using hn₀
    · have h1 : n₀ + 1 + (n₁ - n₀) * 1 = n₁ + 1 := by omega
      rw [h1]; simpa using hn₁

end GTTrans
