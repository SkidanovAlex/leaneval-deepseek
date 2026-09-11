import Mathlib

/-!
# Ground-set size forced by a large uniform family

If `F` is a family of `k`-subsets of a set `X` of size `n` with `|F| ≥ R^k`, then
`R ≤ n` (trivial counting) and, under `R`-spreadness with `R > 6`, `6k ≤ n`
(pigeonhole on elements).
-/
open Finset
open scoped BigOperators

namespace Submission.Ground

variable {α : Type*} [DecidableEq α]

/-- number of k-subsets of X is `n.choose k`; `F ⊆` those when members are k-subsets. -/
lemma card_le_choose {X : Finset α} {F : Finset (Finset α)} {k : ℕ}
    (huni : ∀ A ∈ F, A ⊆ X ∧ A.card = k) :
    F.card ≤ X.card.choose k := by
  have hsub : F ⊆ X.powersetCard k := by
    intro A hA
    exact (Finset.mem_powersetCard).2 ⟨(huni A hA).1, (huni A hA).2⟩
  calc
    F.card ≤ (X.powersetCard k).card := Finset.card_le_card hsub
    _ = X.card.choose k := Finset.card_powersetCard k X

/-- `n.choose k ≤ n^k` -/
lemma choose_le_pow (n k : ℕ) : n.choose k ≤ n ^ k := by
  exact Nat.choose_le_pow n k

/-- if `|F| ≥ R^k` and members are k-subsets of X then `R ≤ |X|`. -/
lemma r_le_card {X : Finset α} {F : Finset (Finset α)} {k : ℕ} {R : ℝ}
    (huni : ∀ A ∈ F, A ⊆ X ∧ A.card = k)
    (hFR : (F.card : ℝ) ≥ R ^ k) (hR : 0 ≤ R) (hk : 1 ≤ k) :
    R ≤ (X.card : ℝ) := by
  have hpow : R ^ k ≤ (X.card : ℝ) ^ k := by
    calc
      R ^ k ≤ (F.card : ℝ) := hFR
      _ ≤ (X.card.choose k : ℝ) := by exact_mod_cast card_le_choose huni
      _ ≤ ((X.card ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_pow X.card k
      _ = (X.card : ℝ) ^ k := by rw [Nat.cast_pow]
  exact le_of_pow_le_pow_left₀ (by omega) (by positivity) hpow

/-- if `|F| ≥ R^k > 6^k` (R > 6) and F is R-spread then `6k ≤ |X|`. -/
lemma sixk_le_card {X : Finset α} {F : Finset (Finset α)} {k : ℕ} {R : ℝ}
    (huni : ∀ A ∈ F, A ⊆ X ∧ A.card = k)
    (hspread : ∀ T : Finset α, T ⊆ X → T.Nonempty →
      (#(F.filter (fun A : Finset α => T ⊆ A)) : ℝ) ≤ R ^ (k - T.card))
    (hFR : (F.card : ℝ) ≥ R ^ k) (hR6 : 6 < R) (hk : 1 ≤ k) :
    6 * k ≤ X.card := by
  by_contra hnot
  have hcardlt : X.card < 6 * k := Nat.lt_of_not_ge hnot
  -- elementwise spreadness: for every x ∈ X, the fiber over x has size ≤ R^(k-1)
  have hsp : ∀ x : α, x ∈ X →
      ((F.filter (fun A : Finset α => x ∈ A)).card : ℝ) ≤ R ^ (k - 1) := by
    intro x hx
    have hsub : ({x} : Finset α) ⊆ X := Finset.singleton_subset_iff.mpr hx
    have hnon : ({x} : Finset α).Nonempty := Finset.singleton_nonempty x
    simpa [Finset.singleton_subset_iff, Finset.card_singleton] using hspread {x} hsub hnon
  -- a member A of F consists exactly of the elements of X belonging to A
  have hfix (A : Finset α) (hA : A ∈ F) : X.filter (fun x : α => x ∈ A) = A := by
    have hsub : A ⊆ X := (huni A hA).1
    apply Finset.Subset.antisymm
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x hx
      exact Finset.mem_filter.mpr ⟨hsub hx, hx⟩
  -- double counting (as naturals): Σ_{x∈X} #{A∈F : x∈A} = k * |F|
  have hsum_nat :
      (∑ x ∈ X, (F.filter (fun A : Finset α => x ∈ A)).card) = k * F.card := by
    calc
      (∑ x ∈ X, (F.filter (fun A : Finset α => x ∈ A)).card)
          = ∑ x ∈ X, ∑ A ∈ F, if x ∈ A then 1 else 0 := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [Finset.card_filter]
      _ = ∑ A ∈ F, ∑ x ∈ X, if x ∈ A then 1 else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ A ∈ F, (X.filter (fun x : α => x ∈ A)).card := by
              refine Finset.sum_congr rfl ?_
              intro A hA
              rw [Finset.card_filter]
      _ = ∑ A ∈ F, A.card := by
              refine Finset.sum_congr rfl ?_
              intro A hA
              rw [hfix A hA]
      _ = ∑ A ∈ F, k := by
              refine Finset.sum_congr rfl ?_
              intro A hA
              rw [(huni A hA).2]
      _ = k * F.card := by
              rw [Finset.sum_const_nat (by intro A hA; rfl)]
              rw [mul_comm]
  -- same identity in ℝ
  have hsum : (∑ x ∈ X, ((F.filter (fun A : Finset α => x ∈ A)).card : ℝ))
      = (k : ℝ) * (F.card : ℝ) := by
    calc
      (∑ x ∈ X, ((F.filter (fun A : Finset α => x ∈ A)).card : ℝ))
          = ↑(∑ x ∈ X, (F.filter (fun A : Finset α => x ∈ A)).card) := by
              rw [Nat.cast_sum]
      _ = ((k * F.card : ℕ) : ℝ) := by rw [hsum_nat]
      _ = (k : ℝ) * (F.card : ℝ) := by rw [Nat.cast_mul]
  -- upper bound: Σ_{x∈X} #{A∈F : x∈A} ≤ |X| * R^(k-1)
  have hsumUB : (∑ x ∈ X, ((F.filter (fun A : Finset α => x ∈ A)).card : ℝ))
      ≤ (X.card : ℝ) * R ^ (k - 1) := by
    calc
      (∑ x ∈ X, ((F.filter (fun A : Finset α => x ∈ A)).card : ℝ))
          ≤ ∑ x ∈ X, R ^ (k - 1) := Finset.sum_le_sum (fun x hx => hsp x hx)
      _ = X.card • R ^ (k - 1) := by rw [Finset.sum_const]
      _ = (X.card : ℝ) * R ^ (k - 1) := by rw [nsmul_eq_mul]
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hRpos : 0 < R := lt_trans (by norm_num) hR6
  have hRkm1pos : 0 < R ^ (k - 1) := pow_pos hRpos (k - 1)
  have hFRle : R ^ k ≤ (F.card : ℝ) := hFR
  -- the strict chain forcing R < 6
  have hchain : (k : ℝ) * R ^ k < (6 : ℝ) * (k : ℝ) * R ^ (k - 1) := by
    calc
      (k : ℝ) * R ^ k ≤ (k : ℝ) * (F.card : ℝ) :=
          mul_le_mul_of_nonneg_left hFRle (le_of_lt hkpos)
      _ = ∑ x ∈ X, ((F.filter (fun A : Finset α => x ∈ A)).card : ℝ) := hsum.symm
      _ ≤ (X.card : ℝ) * R ^ (k - 1) := hsumUB
      _ < (6 : ℝ) * (k : ℝ) * R ^ (k - 1) := by
          have hc1 : (X.card : ℝ) < (6 : ℝ) * (k : ℝ) := by
            have hc : (X.card : ℝ) < ((6 * k : ℕ) : ℝ) := by exact_mod_cast hcardlt
            rwa [Nat.cast_mul] at hc
          exact mul_lt_mul_of_pos_right hc1 hRkm1pos
  -- rewrite R^k = R^(k-1) * R and cancel the positive factor k * R^(k-1)
  have hRpow : R ^ k = R ^ (k - 1) * R := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_add]
    simp
  have hchain2 : (k : ℝ) * R ^ (k - 1) * R < (k : ℝ) * R ^ (k - 1) * (6 : ℝ) := by
    have h1 := hchain
    rw [hRpow] at h1
    ring_nf at h1 ⊢
    exact h1
  have hRlt6 : R < 6 :=
    lt_of_mul_lt_mul_left hchain2 (le_of_lt (mul_pos hkpos hRkm1pos))
  linarith

end Submission.Ground
