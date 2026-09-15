import Mathlib
import Submission.Commons.Combinatorics.Additive.Gowers.ap_count_prod_add

namespace Commons.Combinatorics.Transference

theorem ap_count_decomp_lower {p : ℕ} [Fact p.Prime] {k : ℕ}
    (f g h : ZMod p → ℝ) (hfg : ∀ x, f x = g x + h x)
    {c η Bnd : ℝ}
    (hdense : (1 + η) ^ k * c * (p : ℝ) ^ 2 ≤
      ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, g (x + ((i : ℕ) : ZMod p) * r))
    (hmixed : ∀ t ∈ (Finset.univ : Finset (Fin k)).powerset, t ≠ Finset.univ →
      |∑ x : ZMod p, ∑ r : ZMod p,
        (∏ i ∈ t, g (x + ((i : ℕ) : ZMod p) * r)) *
          (∏ i ∈ tᶜ, h (x + ((i : ℕ) : ZMod p) * r))|
        ≤ (p : ℝ) ^ 2 * Bnd) :
    (1 + η) ^ k * c * (p : ℝ) ^ 2 - ((2 : ℝ) ^ k - 1) * ((p : ℝ) ^ 2 * Bnd)
      ≤ ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r) := by
  classical
  set P : Finset (Fin k) → ℝ := fun t =>
      ∑ x : ZMod p, ∑ r : ZMod p,
        (∏ i ∈ t, g (x + ((i : ℕ) : ZMod p) * r)) *
          (∏ i ∈ tᶜ, h (x + ((i : ℕ) : ZMod p) * r)) with hP
  set D : ℝ := ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, g (x + ((i : ℕ) : ZMod p) * r) with hD
  set e : Finset (Finset (Fin k)) := (Finset.univ : Finset (Fin k)).powerset.erase Finset.univ with he
  -- Step 1: rewrite f as g + h and expand the product over subsets of `Fin k`.
  have hprodeq : (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r))
      = ∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k,
          (g (x + ((i : ℕ) : ZMod p) * r) + h (x + ((i : ℕ) : ZMod p) * r)) := by
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro r _
    apply Finset.prod_congr rfl; intro i _
    exact hfg _
  have hsum1 : (∑ x : ZMod p, ∑ r : ZMod p, ∏ i : Fin k, f (x + ((i : ℕ) : ZMod p) * r))
      = ∑ t ∈ (Finset.univ : Finset (Fin k)).powerset, P t := by
    rw [hprodeq, Commons.Combinatorics.Additive.Gowers.ap_count_prod_add k g h]
  -- Step 2: split off the `t = univ` term (the all-`g` term).
  have hsplit : ∑ t ∈ (Finset.univ : Finset (Fin k)).powerset, P t
      = P Finset.univ + ∑ t ∈ e, P t := by
    have hmem : (Finset.univ : Finset (Fin k)) ∈ (Finset.univ : Finset (Fin k)).powerset :=
      Finset.mem_powerset_self _
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin k)).powerset P hmem
    rw [← h, he]
    ring
  -- Step 3: the `t = univ` term is exactly the all-`g` sum.
  have hPu : P Finset.univ = D := by
    simp only [hP, hD, Finset.compl_univ, Finset.prod_empty, mul_one]
  -- Step 4: dense lower bound on the all-`g` term.
  have hDbound : (1 + η) ^ k * c * (p : ℝ) ^ 2 ≤ P Finset.univ := by
    rw [hPu]
    exact hdense
  -- Step 5: each proper subset has a bounded mixed contribution.
  have hbound : ∀ t ∈ e, |P t| ≤ (p : ℝ) ^ 2 * Bnd := by
    intro t ht
    rw [he, Finset.mem_erase] at ht
    obtain ⟨hne, hmem⟩ := ht
    simpa only [hP] using hmixed t hmem hne
  -- Step 6: lower bound on the sum of mixed contributions.
  have hR : -(((2 : ℝ) ^ k - 1) * ((p : ℝ) ^ 2 * Bnd)) ≤ ∑ t ∈ e, P t := by
    have hsumabs : -∑ t ∈ e, |P t| ≤ ∑ t ∈ e, P t := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum (fun t _ => neg_abs_le (P t))
    have hcard_bound : ∑ t ∈ e, |P t| ≤ (e.card : ℝ) * ((p : ℝ) ^ 2 * Bnd) := by
      have h1 := Finset.sum_le_card_nsmul e (fun t => |P t|) ((p : ℝ) ^ 2 * Bnd) hbound
      simpa only [nsmul_eq_mul] using h1
    have hcard : e.card = 2 ^ k - 1 := by
      rw [he, Finset.card_erase_of_mem (Finset.mem_powerset_self _), Finset.card_powerset,
        Finset.card_univ, Fintype.card_fin]
    have hcardR : (e.card : ℝ) = (2 : ℝ) ^ k - 1 := by
      rw [hcard, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]; norm_num
    have hcK : -((e.card : ℝ) * ((p : ℝ) ^ 2 * Bnd)) ≤ ∑ t ∈ e, P t := by
      linarith [hsumabs, hcard_bound]
    rwa [hcardR] at hcK
  -- Step 7: assemble.
  rw [hsum1, hsplit]
  linarith [hDbound, hR]

end Commons.Combinatorics.Transference
