import Submission.Helpers
import Mathlib
import Submission.Commons.NumberTheory.PrimesInAP.infinite_affine_prime_set
import Submission.Commons.Combinatorics.Additive.AP.zmod_window_ap

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Extracting an arithmetic progression in `{n : W*n + 1 prime}` from an AP count

If `f : ZMod p → ℝ` is supported (with nonzero values) on residues `x` whose representative
`x.val` lies in the window `[ε p, 2ε p]` and satisfies `Nat.Prime (W * x.val + 1)`, then any
nonzero term of the length-`k` AP count with `r ≠ 0` yields a genuine length-`k` arithmetic
progression in `{n : ℕ | Nat.Prime (W*n+1)}`.

The point is the "no-wraparound" lemma `Commons.Combinatorics.Additive.AP.zmod_window_ap`: for
`4ε < 1` the window `[ε p, 2ε p]` is short enough that the residues
`v, v+r, …, v+(k-1)r` (all of whose representatives lie in the window) already form an
arithmetic progression in `ℕ`.
-/

open Finset
open scoped BigOperators

namespace GTTrans

/-- **Extraction of a prime AP from a nonzero AP-count term with `r ≠ 0`.** -/
theorem exists_ap_of_nonzero_term {k : ℕ} (hk : 2 ≤ k) {p : ℕ} [Fact p.Prime] {W : ℕ}
    {εw : ℝ} (hεw : 0 < εw) (hεw4 : 4 * εw < 1) {f : ZMod p → ℝ}
    (hsupp : ∀ x : ZMod p, f x ≠ 0 →
      εw * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * εw * (p : ℝ) ∧
        Nat.Prime (W * x.val + 1))
    {x r : ZMod p} (hr : r ≠ 0)
    (hterm : (∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r)) ≠ 0) :
    ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → Nat.Prime (W * (a + b * j) + 1) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hne : ∀ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r) ≠ 0 := by
    intro i h
    exact hterm (Finset.prod_eq_zero (Finset.mem_univ i) h)
  obtain ⟨a, b, hb, hab⟩ :=
    Commons.Combinatorics.Additive.AP.zmod_window_ap (N := p) (k := k) hk hεw hεw4 x r hr
      (fun i hi => by
        have h := hsupp _ (hne ⟨i, hi⟩)
        exact ⟨h.1, h.2.1⟩)
  refine ⟨a, b, hb, fun j hj => ?_⟩
  obtain ⟨i, hi, hval⟩ := hab j hj
  have hp := (hsupp _ (hne ⟨i, hi⟩)).2.2
  rwa [hval] at hp


/-- **A nonzero AP-count term with `r ≠ 0` exists.**  If the single-orbit contribution
`Σ_x f(x)^k` — bounded by `B^{k-1}·Σ f` when `0 ≤ f ≤ B` — is strictly smaller than the full AP
count, then some `r ≠ 0` term of the count is nonzero. -/
theorem exists_nonzero_term_of_apcount {k : ℕ} (hk : 2 ≤ k) {p : ℕ} [Fact p.Prime]
    {f : ZMod p → ℝ} (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, f x ≤ B)
    (hlt : B ^ (k - 1) * (∑ x, f x)
      < ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r)) :
    ∃ x r : ZMod p, r ≠ 0 ∧ (∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r)) ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  set G : ZMod p → ZMod p → ℝ :=
    fun x r => ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r) with hG
  have hzero : ∀ x : ZMod p, ∑ r ∈ Finset.univ.erase (0 : ZMod p), G x r = 0 := by
    intro x
    apply Finset.sum_eq_zero
    intro r hr
    exact h x r (Finset.mem_erase.mp hr).1
  have hG0 : ∀ x : ZMod p, G x 0 = f x ^ k := by
    intro x
    rw [hG]
    simp only [mul_zero, add_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsplit : ∀ x : ZMod p, ∑ r : ZMod p, G x r
      = G x 0 + ∑ r ∈ Finset.univ.erase (0 : ZMod p), G x r := by
    intro x
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p)), add_comm]
  have hbound : ∀ x : ZMod p, G x 0 ≤ B ^ (k - 1) * f x := by
    intro x
    rw [hG0]
    have h1 : f x ^ k = f x ^ (k - 1) * f x := by
      rw [← pow_succ]; congr 1; omega
    rw [h1]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hf0 x) (hB x) (k - 1)) (hf0 x)
  have hmain : (∑ x : ZMod p, ∑ r : ZMod p, G x r)
      = (∑ x : ZMod p, G x 0) + ∑ x : ZMod p, ∑ r ∈ Finset.univ.erase (0 : ZMod p), G x r := by
    have h1 : (∑ x : ZMod p, ∑ r : ZMod p, G x r)
        = ∑ x : ZMod p, (G x 0 + ∑ r ∈ Finset.univ.erase (0 : ZMod p), G x r) :=
      Finset.sum_congr rfl (fun x _ => hsplit x)
    rw [h1, Finset.sum_add_distrib]
  have hfinal : (∑ x : ZMod p, ∑ r : ZMod p, G x r) ≤ B ^ (k - 1) * (∑ x, f x) := by
    rw [hmain]
    have h1 : (∑ x : ZMod p, G x 0) ≤ ∑ x : ZMod p, B ^ (k - 1) * f x :=
      Finset.sum_le_sum (fun x _ => hbound x)
    have h2 : (∑ x : ZMod p, B ^ (k - 1) * f x) = B ^ (k - 1) * (∑ x, f x) :=
      (Finset.mul_sum Finset.univ f (B ^ (k - 1))).symm
    have h3 : (∑ x : ZMod p, ∑ r ∈ Finset.univ.erase (0 : ZMod p), G x r) = 0 :=
      Finset.sum_eq_zero (fun x _ => hzero x)
    rw [h3, add_zero]
    linarith [h1, h2]
  change B ^ (k - 1) * (∑ x, f x) < (∑ x : ZMod p, ∑ r : ZMod p, G x r) at hlt
  linarith [hfinal, hlt]

end GTTrans

namespace GTTrans

open scoped BigOperators

/-- **The final assembly.**  Suppose that for every `k ≥ 3` there is a constant `cd > 0` and a
threshold `P₁` such that for every prime `p ≥ P₁` there is a function `f : ZMod p → ℝ` with

* `0 ≤ f ≤ B` for some `B`, and `B^{k-1}·Σ f < cd·p²` (so the `r = 0` contribution to the AP count
  cannot be the only positive term),
* `cd·p² ≤` the length-`k` AP count of `f`,
* the support of `f` lies in the window `[ε p, 2ε p]` and `f x ≠ 0 ⟹ W·x.val+1` is prime,

and that `4ε < 1`.  Then `{n : ℕ | Nat.Prime (W*n+1)}` contains arbitrarily long APs. -/
theorem contains_arith_prog_of_data {W : ℕ} (hW : 1 ≤ W) {εw : ℝ} (hεw : 0 < εw)
    (hεw4 : 4 * εw < 1)
    (hdata : ∀ (k : ℕ), 3 ≤ k → ∃ (cd : ℝ) (P₁ : ℕ), 0 < cd ∧
      ∀ (p : ℕ) [Fact p.Prime], P₁ ≤ p →
        ∃ (f : ZMod p → ℝ) (B : ℝ),
          (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ B) ∧
          B ^ (k - 1) * (∑ x, f x) < cd * (p : ℝ) ^ 2 ∧
          cd * (p : ℝ) ^ 2 ≤ ∑ x : ZMod p, ∑ r : ZMod p,
            ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r) ∧
          (∀ x, f x ≠ 0 → εw * (p : ℝ) ≤ (x.val : ℝ) ∧ (x.val : ℝ) ≤ 2 * εw * (p : ℝ) ∧
            Nat.Prime (W * x.val + 1))) :
    ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → Nat.Prime (W * (a + b * j) + 1) := by
  classical
  intro k
  by_cases hk3 : 3 ≤ k
  · -- `k ≥ 3`: use the data family.
    obtain ⟨cd, P₁, hcd, hdat⟩ := hdata k hk3
    obtain ⟨p, hpP, hpprime⟩ := Nat.exists_infinite_primes (max P₁ 2)
    haveI : Fact p.Prime := ⟨hpprime⟩
    have hpP₁ : P₁ ≤ p := le_trans (le_max_left _ _) hpP
    obtain ⟨f, B, hf0, hfB, hBk, hcdle, hsupp⟩ := hdat p hpP₁
    have hB0 : 0 ≤ B := le_trans (hf0 0) (hfB 0)
    obtain ⟨x, r, hr, hterm⟩ :=
      exists_nonzero_term_of_apcount (k := k) (by omega) hf0 hB0 hfB
        (lt_of_lt_of_le hBk hcdle)
    obtain ⟨a, b, hb, hab⟩ :=
      exists_ap_of_nonzero_term (k := k) (p := p) (by omega) hεw hεw4 hsupp hr hterm
    exact ⟨a, b, hb, fun j hj => hab j hj⟩
  · -- `k ≤ 2`: use two distinct primes of the form `W n + 1` (Dirichlet).
    have hinf : Set.Infinite {n : ℕ | Nat.Prime (W * n + 1)} :=
      Commons.NumberTheory.PrimesInAP.infinite_affine_prime_set (W := W) (r := 1) hW (by simp)
    obtain ⟨n₀, hn₀⟩ := hinf.nonempty
    obtain ⟨n₁, hn₁, hlt⟩ := hinf.exists_gt n₀
    refine ⟨n₀, n₁ - n₀, by omega, fun j hj => ?_⟩
    have hj2 : j = 0 ∨ j = 1 := by omega
    rcases hj2 with rfl | rfl
    · simpa using hn₀
    · have h1 : n₀ + (n₁ - n₀) * 1 = n₁ := by omega
      rw [h1]; exact hn₁

end GTTrans

namespace GTTrans

open scoped BigOperators

/-- **The entire remaining gap, in one statement.**  If the data family of
`contains_arith_prog_of_data` exists (for the `W`-trick with `W = 1` and window parameter
`εw = 1/8`), then the primes contain arbitrarily long arithmetic progressions. -/
theorem green_tao_of_data
    (hdata : ∀ (k : ℕ), 3 ≤ k → ∃ (cd : ℝ) (P₁ : ℕ), 0 < cd ∧
      ∀ (p : ℕ) [Fact p.Prime], P₁ ≤ p →
        ∃ (f : ZMod p → ℝ) (B : ℝ),
          (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ B) ∧
          B ^ (k - 1) * (∑ x, f x) < cd * (p : ℝ) ^ 2 ∧
          cd * (p : ℝ) ^ 2 ≤ ∑ x : ZMod p, ∑ r : ZMod p,
            ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r) ∧
          (∀ x, f x ≠ 0 → (1 / 8 : ℝ) * (p : ℝ) ≤ (x.val : ℝ) ∧
            (x.val : ℝ) ≤ 2 * (1 / 8 : ℝ) * (p : ℝ) ∧ Nat.Prime (1 * x.val + 1))) :
    LeanEval.NumberTheory.ContainsArbitraryAPs {p : ℕ | Nat.Prime p} := by
  refine Submission.Helpers.green_tao_of_tricked 1 1 (by norm_num) ?_
  have h := contains_arith_prog_of_data (W := 1) (by norm_num) (εw := 1 / 8)
    (by norm_num) (by norm_num) hdata
  intro k
  obtain ⟨a, b, hb, hab⟩ := h k
  exact ⟨a, b, hb, fun j hj => hab j hj⟩

end GTTrans
