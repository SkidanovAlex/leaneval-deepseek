import Mathlib
import Submission.Work.BMF.Uspt.base
import Submission.Work.BMF.vkford51_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The fibre-square identity for `ncount` and Vinogradov's count `J`

`Work.BMF.ncount r k M₁ c` is the number of `r`-tuples `a` in `[1,M₁]^r` whose vector of
power sums `psVec k r M₁ a = (Σᵢ aᵢ^1, …, Σᵢ aᵢ^k)` equals `c`, and `Work.BMF.Cbox r M₁ k`
is the box `∏_{j<k} [1, r M₁^{j+1}]` containing all such vectors.

This file proves

`∑_{c ∈ Cbox} ncount r k M₁ c ^ 2 = J r k M₁`,

where `J r k M₁` is Vinogradov's mean-value count, i.e. the number of pairs of `r`-tuples
`(x, y)` in `[1, M₁]^r` with equal power sums of all degrees `0 ≤ j ≤ k`.

The proof is pure counting: grouping the pairs `(a, b)` of tuples by the common value of
their power-sum vector turns the pair count into a sum of squares of fibre sizes
(`card_filter_pair_eq_sum_sq`), and the condition `psVec a = psVec b` is the same as the
condition appearing in `J` (`psVec_eq_iff_forall_powersum`).
-/

namespace Work.BMF.Uspt

open Finset
open scoped BigOperators

noncomputable section

/-- Counting identity: if `g` maps the finite set `T` into `B`, then the number of ordered
pairs from `T` on which `g` takes equal values is the sum of the squares of the sizes of the
fibres of `g` over `B` (fibres of `g` over `B` outside the image being empty). -/
theorem card_filter_pair_eq_sum_sq {α β : Type*} [DecidableEq β]
    (T : Finset α) (B : Finset β) (g : α → β) (hB : ∀ a ∈ T, g a ∈ B) :
    ((T ×ˢ T).filter (fun p : α × α => g p.1 = g p.2)).card
      = ∑ b ∈ B, (T.filter (fun a => g a = b)).card ^ 2 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : α × α => g p.1) (t := B)
    (H := fun p hp => hB p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)]
  apply Finset.sum_congr rfl
  intro b hb
  have hfiber : ((T ×ˢ T).filter (fun p : α × α => g p.1 = g p.2)).filter
        (fun p => g p.1 = b)
      = (T.filter (fun a => g a = b)) ×ˢ (T.filter (fun a => g a = b)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · intro h
      exact ⟨⟨h.1.1.1, h.2⟩, h.1.1.2, h.1.2.symm.trans h.2⟩
    · intro h
      exact ⟨⟨⟨h.1.1, h.2.1⟩, h.1.2.trans h.2.2.symm⟩, h.1.2⟩
  rw [hfiber, Finset.card_product, pow_two]

/-- Two tuples of `[1, M₁]^r` have the same `psVec` (power sums of degrees `1, …, k`) if and
only if they have the same power sums of every degree `0 ≤ j ≤ k` (the degree `0` case being
automatic).  This is the condition appearing in the definition of `J`. -/
theorem psVec_eq_iff_forall_powersum (r k M₁ : ℕ)
    (p : (Fin r → Finset.Icc 1 M₁) × (Fin r → Finset.Icc 1 M₁)) :
    (psVec k r M₁ p.1 = psVec k r M₁ p.2) ↔
      ∀ j, j ≤ k → (∑ i, (p.1 i).1 ^ j) = (∑ i, (p.2 i).1 ^ j) := by
  rw [funext_iff]
  simp only [psVec]
  constructor
  · intro h j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0; simp
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hmk : m < k := by omega
      have hh : (∑ i, (((p.1 i).1 : ℤ) ^ (m + 1))) = (∑ i, (((p.2 i).1 : ℤ) ^ (m + 1))) := by
        simpa using h ⟨m, hmk⟩
      rw [hm]
      exact_mod_cast hh
  · intro h j
    have hj : (j : ℕ) + 1 ≤ k := by have := j.isLt; omega
    exact_mod_cast h ((j : ℕ) + 1) hj

/-- The sum of the squares of the multiplicities `ncount r k M₁ c` over the frequency box
`Cbox r M₁ k` is Vinogradov's mean value count `J r k M₁`. -/
theorem sum_ncount_sq_eq_J (r k M₁ : ℕ) (hr : 1 ≤ r) (hM₁ : 1 ≤ M₁) :
    ∑ c ∈ Work.BMF.Cbox r M₁ k, ((Work.BMF.ncount r k M₁ c : ℝ)) ^ 2
      = LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁ := by
  classical
  have hcard : (((Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)) ×ˢ
        (Finset.univ : Finset (Fin r → Finset.Icc 1 M₁))).filter
        (fun p : (Fin r → Finset.Icc 1 M₁) × (Fin r → Finset.Icc 1 M₁) =>
          psVec k r M₁ p.1 = psVec k r M₁ p.2)).card
      = ∑ c ∈ Work.BMF.Cbox r M₁ k, Work.BMF.ncount r k M₁ c ^ 2 := by
    rw [card_filter_pair_eq_sum_sq (T := (Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)))
      (B := Work.BMF.Cbox r M₁ k) (g := psVec k r M₁)
      (hB := fun a _ => psVec_mem_Cbox hr hM₁ a)]
    apply Finset.sum_congr rfl
    intro c _
    rw [ncount_eq_card_filter]
  have hfilter : (((Finset.univ : Finset (Fin r → Finset.Icc 1 M₁)) ×ˢ
        (Finset.univ : Finset (Fin r → Finset.Icc 1 M₁))).filter
        (fun p : (Fin r → Finset.Icc 1 M₁) × (Fin r → Finset.Icc 1 M₁) =>
          psVec k r M₁ p.1 = psVec k r M₁ p.2))
      = (Finset.univ.filter (fun p : (Fin r → Finset.Icc 1 M₁) × (Fin r → Finset.Icc 1 M₁) =>
          ∀ j, j ≤ k → (∑ i, (p.1 i).1 ^ j) = (∑ i, (p.2 i).1 ^ j))) := by
    rw [Finset.univ_product_univ]
    exact Finset.filter_congr (fun p _ => psVec_eq_iff_forall_powersum r k M₁ p)
  have hcast : (∑ c ∈ Work.BMF.Cbox r M₁ k, ((Work.BMF.ncount r k M₁ c : ℝ)) ^ 2)
      = ((∑ c ∈ Work.BMF.Cbox r M₁ k, Work.BMF.ncount r k M₁ c ^ 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nat.cast_pow]
  have hJ : LeanEval.NumberTheory.VinogradovMeanValue.J r k M₁
      = (((Finset.univ.filter (fun p : (Fin r → Finset.Icc 1 M₁) × (Fin r → Finset.Icc 1 M₁) =>
          ∀ j, j ≤ k → (∑ i, (p.1 i).1 ^ j) = (∑ i, (p.2 i).1 ^ j))).card : ℕ) : ℝ) := rfl
  rw [hcast, ← hcard, hfilter]
  exact hJ.symm

end

end Work.BMF.Uspt
