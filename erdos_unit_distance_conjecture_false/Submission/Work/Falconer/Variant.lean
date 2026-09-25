import Mathlib
import Submission.Work.Defs.Basic
import Submission.Work.Geometry.two_mul_cDist

/-!
# The Falconer variant of the unit-distance problem

Suppose a fixed `δ > 0` admits planar point sets `P` with `|P|` arbitrarily large whose
unit-distance count is superlinear, `|P| ^ (1 + δ) ≤ cDist P`.  Then for every `k` there is a
finite set `Q ⊆ ℂ` in which *every* point has at least `k` unit-distance neighbours inside `Q`
(and then necessarily `|Q| ≥ k`): a `k`-rich configuration.

The argument is the greedy trimming lemma.  Writing `sumDeg P = 2 * cDist P` for the number of
*ordered* unit-distance pairs of `P`, the hypothesis gives `sumDeg P ≥ 2 |P| ^ (1+δ)`.  Delete
from `P` repeatedly a point of degree `< ⌈|P| ^ δ⌉`; each deletion lowers `sumDeg` by less than
`2 ⌈|P| ^ δ⌉ < 2 |P| ^ δ + 2`, so after `|P|` deletions the count is still positive and a
nonempty subset with minimum degree `≥ ⌈|P| ^ δ⌉` survives.  Choosing `|P|` with `|P| ^ δ ≥ k`
finishes.
-/

namespace Work.Falconer

open scoped nonZeroDivisors

/-- The number of *ordered* unit-distance pairs of a finite set `P ⊆ ℂ`, written as the sum
over the points of `P` of the number of their unit-distance neighbours in `P`. -/
noncomputable def sumDeg (P : Finset ℂ) : ℕ :=
  ∑ x ∈ P, (P.filter (fun y => ‖x - y‖ = 1)).card

/-- `sumDeg` unfolded as a double sum of edge indicators. -/
lemma sumDeg_eq_sum_sum (P : Finset ℂ) :
    sumDeg P = ∑ a ∈ P, ∑ b ∈ P, (if ‖a - b‖ = 1 then 1 else 0) := by
  unfold sumDeg
  exact Finset.sum_congr rfl fun a _ => Finset.card_filter _ P

/-- `sumDeg P` counts the ordered unit-distance pairs, i.e. the filtered off-diagonal of `P`. -/
lemma sumDeg_eq_card_offDiag (P : Finset ℂ) :
    sumDeg P = (P.offDiag.filter (fun pq => ‖pq.1 - pq.2‖ = 1)).card := by
  have h1 : P.offDiag.filter (fun pq => ‖pq.1 - pq.2‖ = 1)
      = (P ×ˢ P).filter (fun pq => ‖pq.1 - pq.2‖ = 1) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product]
    constructor
    · rintro ⟨⟨hx, hy, _⟩, hnorm⟩
      exact ⟨⟨hx, hy⟩, hnorm⟩
    · rintro ⟨⟨hx, hy⟩, hnorm⟩
      exact ⟨⟨hx, hy, fun h => by rw [h] at hnorm; simp at hnorm⟩, hnorm⟩
  rw [h1, Finset.card_filter, Finset.sum_product, sumDeg_eq_sum_sum]

/-- The ordered pair count is twice the number of unordered unit-distance pairs. -/
lemma sumDeg_eq_two_mul_cDist (P : Finset ℂ) :
    sumDeg P = 2 * Work.Defs.cDist P := by
  rw [sumDeg_eq_card_offDiag, ← Work.Geometry.two_mul_cDist]

/-- Removing a point `x ∈ P` lowers `sumDeg` by twice its degree in `P`. -/
lemma sumDeg_erase_add (P : Finset ℂ) {x : ℂ} (hx : x ∈ P) :
    sumDeg (P.erase x) + 2 * (P.filter (fun y => ‖x - y‖ = 1)).card = sumDeg P := by
  have eXX : (if ‖x - x‖ = 1 then (1 : ℕ) else 0) = 0 := by simp
  have key1 : ∑ a ∈ P, ∑ b ∈ P, (if ‖a - b‖ = 1 then 1 else 0)
      = ∑ a ∈ P, ((∑ b ∈ P.erase x, (if ‖a - b‖ = 1 then 1 else 0))
          + (if ‖a - x‖ = 1 then 1 else 0)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.add_sum_erase P (fun b => if ‖a - b‖ = 1 then 1 else 0) hx]
    exact add_comm _ _
  have key2 : ∑ a ∈ P, ((∑ b ∈ P.erase x, (if ‖a - b‖ = 1 then 1 else 0))
        + (if ‖a - x‖ = 1 then 1 else 0))
      = (∑ a ∈ P, ∑ b ∈ P.erase x, (if ‖a - b‖ = 1 then 1 else 0))
        + ∑ a ∈ P, (if ‖a - x‖ = 1 then 1 else 0) := Finset.sum_add_distrib
  have key3 : ∑ a ∈ P, ∑ b ∈ P.erase x, (if ‖a - b‖ = 1 then 1 else 0)
      = (∑ a ∈ P.erase x, ∑ b ∈ P.erase x, (if ‖a - b‖ = 1 then 1 else 0))
        + ∑ b ∈ P.erase x, (if ‖x - b‖ = 1 then 1 else 0) := by
    rw [← Finset.add_sum_erase P
      (fun a => ∑ b ∈ P.erase x, (if ‖a - b‖ = 1 then 1 else 0)) hx]
    exact add_comm _ _
  have key4 : ∑ a ∈ P, (if ‖a - x‖ = 1 then 1 else 0)
      = ∑ a ∈ P.erase x, (if ‖a - x‖ = 1 then 1 else 0) := by
    have hsum := Finset.sum_erase_add P (fun a => if ‖a - x‖ = 1 then 1 else 0) hx
    rw [eXX, add_zero] at hsum
    exact hsum.symm
  have key5 : ∑ a ∈ P.erase x, (if ‖a - x‖ = 1 then 1 else 0)
      = ∑ b ∈ P.erase x, (if ‖x - b‖ = 1 then 1 else 0) :=
    Finset.sum_congr rfl fun a _ => by rw [norm_sub_rev]
  have key6 : ∑ b ∈ P.erase x, (if ‖x - b‖ = 1 then 1 else 0)
      = (P.filter (fun y => ‖x - y‖ = 1)).card := by
    have hsum := Finset.sum_erase_add P (fun b => if ‖x - b‖ = 1 then 1 else 0) hx
    rw [eXX, add_zero] at hsum
    rw [hsum, ← Finset.card_filter]
  have hD : ∑ a ∈ P, ∑ b ∈ P, (if ‖a - b‖ = 1 then 1 else 0)
      = (∑ a ∈ P.erase x, ∑ b ∈ P.erase x, (if ‖a - b‖ = 1 then 1 else 0))
        + 2 * (P.filter (fun y => ‖x - y‖ = 1)).card := by
    rw [key1, key2, key3, key4, key5, key6]
    ring
  rw [sumDeg_eq_sum_sum (P.erase x), sumDeg_eq_sum_sum P, hD]

/-- **Trimming lemma.**  If the ordered unit-distance count of `P` exceeds `2 (t-1) |P|` then
`P` contains a nonempty subset `Q` in which every point has at least `t` unit-distance
neighbours inside `Q`. -/
theorem trim : ∀ n : ℕ, ∀ P : Finset ℂ, P.card ≤ n → ∀ t : ℕ,
    2 * (t - 1) * P.card < sumDeg P →
    ∃ Q : Finset ℂ, Q ⊆ P ∧ Q.Nonempty ∧
      ∀ x ∈ Q, t ≤ (Q.filter (fun y => ‖x - y‖ = 1)).card := by
  intro n
  induction n with
  | zero =>
    intro P hP t h
    exfalso
    have hP0 : P = ∅ := by
      rw [← Finset.card_eq_zero]
      exact Nat.le_zero.mp hP
    subst hP0
    simp [sumDeg] at h
  | succ n ih =>
    intro P hP t h
    by_cases hAll : ∀ x ∈ P, t ≤ (P.filter (fun y => ‖x - y‖ = 1)).card
    · refine ⟨P, fun a ha => ha, ?_, hAll⟩
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty] at h
      simp [sumDeg] at h
    · simp only [not_forall, not_le] at hAll
      obtain ⟨x, hx, hxdeg⟩ := hAll
      have ht1 : 1 ≤ t := by omega
      have hxdeg' : (P.filter (fun y => ‖x - y‖ = 1)).card ≤ t - 1 := Nat.le_pred_of_lt hxdeg
      have hrec := sumDeg_erase_add P hx
      have h2 : 2 * (t - 1) * (P.erase x).card < sumDeg (P.erase x) := by
        have hdeg2 : 2 * (P.filter (fun y => ‖x - y‖ = 1)).card ≤ 2 * (t - 1) := by omega
        have hce : (P.erase x).card + 1 = P.card := Finset.card_erase_add_one hx
        have step1 : 2 * (t - 1) * (P.erase x).card + 2 * (t - 1) = 2 * (t - 1) * P.card := by
          rw [← hce, mul_add, mul_one]
        have step2 : 2 * (t - 1) * (P.erase x).card + 2 * (t - 1) < sumDeg P := by
          rw [step1]; exact h
        have step3 : 2 * (t - 1) * (P.erase x).card
            + 2 * (P.filter (fun y => ‖x - y‖ = 1)).card < sumDeg (P.erase x)
            + 2 * (P.filter (fun y => ‖x - y‖ = 1)).card := by
          rw [hrec]
          exact lt_of_le_of_lt (Nat.add_le_add_left hdeg2 _) step2
        exact Nat.lt_of_add_lt_add_right step3
      have hcardle : (P.erase x).card ≤ n := by
        rw [Finset.card_erase_of_mem hx]
        omega
      obtain ⟨Q, hQP, hQne, hQdeg⟩ := ih (P.erase x) hcardle t h2
      exact ⟨Q, hQP.trans (Finset.erase_subset x P), hQne, hQdeg⟩

open scoped nonZeroDivisors
theorem Variant (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ N : ℕ, ∃ P : Finset ℂ, N ≤ P.card ∧ (P.card : ℝ) ^ (1 + δ) ≤ (Work.Defs.cDist P : ℝ)) :
    ∀ k : ℕ, ∃ Q : Finset ℂ, k ≤ Q.card ∧
      ∀ x ∈ Q, k ≤ (Q.filter (fun y => ‖x - y‖ = 1)).card := by
  intro k
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exact ⟨∅, le_refl 0, fun x hx => (Finset.notMem_empty x hx).elim⟩
  obtain ⟨N, hN⟩ := exists_nat_gt ((k : ℝ) ^ (1 / δ))
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hδne : δ ≠ 0 := hδ.ne'
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) ^ (1 / δ) := Real.one_le_rpow hkR (by positivity)
    have h2 : (1 : ℝ) < (N : ℝ) := lt_of_le_of_lt h1 hN
    have h3 : (1 : ℕ) < N := by exact_mod_cast h2
    omega
  obtain ⟨P, hPN, hPc⟩ := h N
  have hcard1 : 1 ≤ P.card := le_trans hN1 hPN
  have hcardR : (0 : ℝ) < (P.card : ℝ) := by
    have : (0 : ℕ) < P.card := lt_of_lt_of_le Nat.zero_lt_one hcard1
    exact_mod_cast this
  have hkk : ((k : ℝ) ^ (1 / δ)) ^ δ = (k : ℝ) := by
    rw [← Real.rpow_mul (Nat.cast_nonneg k), one_div_mul_cancel hδne, Real.rpow_one]
  have hkPow : (k : ℝ) ≤ (P.card : ℝ) ^ δ := by
    rw [← hkk]
    refine Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg k) _) ?_ hδ.le
    have hxy : ((k : ℝ) ^ (1 / δ)) ≤ (N : ℝ) := le_of_lt hN
    have hNy : (N : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hPN
    linarith
  set t : ℕ := ⌈(P.card : ℝ) ^ δ⌉₊ with ht
  have hceil1 : (1 : ℝ) ≤ (P.card : ℝ) ^ δ :=
    Real.one_le_rpow (by exact_mod_cast hcard1) hδ.le
  have ht1 : 1 ≤ t := by
    have h2 : (1 : ℝ) ≤ (t : ℝ) := by
      have h3 := Nat.le_ceil ((P.card : ℝ) ^ δ)
      rw [← ht] at h3
      exact le_trans hceil1 h3
    exact_mod_cast h2
  have hkt : k ≤ t := by
    have h2 : (k : ℝ) ≤ (t : ℝ) := by
      have h3 := Nat.le_ceil ((P.card : ℝ) ^ δ)
      rw [← ht] at h3
      exact le_trans hkPow h3
    exact_mod_cast h2
  have htsub : ((t : ℝ) - 1) < (P.card : ℝ) ^ δ := by
    have h1 := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg P.card) δ)
    rw [← ht] at h1
    linarith
  have hSbound : 2 * (t - 1) * P.card < sumDeg P := by
    have key : ((2 * (t - 1) * P.card : ℕ) : ℝ) < (sumDeg P : ℝ) := by
      have e1 : ((2 * (t - 1) * P.card : ℕ) : ℝ) = 2 * ((t : ℝ) - 1) * (P.card : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub ht1]
        norm_num
      have e2 : (sumDeg P : ℝ) = 2 * (Work.Defs.cDist P : ℝ) := by
        rw [sumDeg_eq_two_mul_cDist, Nat.cast_mul, Nat.cast_ofNat]
      rw [e1, e2]
      have h2 : (2 : ℝ) * ((t : ℝ) - 1) * (P.card : ℝ)
          < 2 * (P.card : ℝ) ^ δ * (P.card : ℝ) := by
        have h1 : ((t : ℝ) - 1) * (P.card : ℝ) < (P.card : ℝ) ^ δ * (P.card : ℝ) :=
          mul_lt_mul_of_pos_right htsub hcardR
        have h1' := mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 2)
        linarith [h1']
      have h3 : 2 * (P.card : ℝ) ^ δ * (P.card : ℝ) = 2 * (P.card : ℝ) ^ (1 + δ) := by
        rw [Real.rpow_add hcardR, Real.rpow_one]
        ring
      have h4 : 2 * (P.card : ℝ) ^ (1 + δ) ≤ 2 * (Work.Defs.cDist P : ℝ) :=
        mul_le_mul_of_nonneg_left hPc (by norm_num)
      linarith [h2, h3, h4]
    exact_mod_cast key
  obtain ⟨Q, hQP, hQne, hQdeg⟩ := trim P.card P le_rfl t hSbound
  refine ⟨Q, ?_, fun x hx => le_trans hkt (hQdeg x hx)⟩
  obtain ⟨x, hx⟩ := hQne
  exact le_trans hkt (le_trans (hQdeg x hx) (Finset.card_filter_le Q (fun y => ‖x - y‖ = 1)))

end Work.Falconer
