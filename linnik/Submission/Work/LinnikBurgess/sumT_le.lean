import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.frame_count_prov_helpers
import Submission.Work.LinnikBurgess.frame_count_prov_aux.caseT_defs
import Submission.Work.LinnikBurgess.frame_count_prov_aux.sum_box3_eq_iterate
import Submission.Work.LinnikBurgess.caseT_aux_defs
import Submission.Work.LinnikBurgess.a2_dist_le_two_Icc
import Submission.Work.LinnikBurgess.exists_fin3_decomp
import Submission.Work.LinnikBurgess.caseT_slot_le
import Submission.Work.LinnikBurgess.caseT_sum_le
import Submission.Work.LinnikBurgess.caseT_Asum_le
import Submission.Work.LinnikBurgess.caseT_Bsum_le
import Submission.Work.LinnikBurgess.Afact_card_le
import Submission.Work.LinnikBurgess.caseT_final_arith

/-!
# The Case-T estimate of the frame count (`sumT_le`)

`sumT` is the part of the frame count (master sum) in which the two non-pivot `a`-entries
`a 1 ≠ a 2` both occur among the entries of `b`.  This file proves

`sumT H m d g ≤ 30000 · τ(m d g)^8 · (H^6/(d g) + H^5/g)`.

The strategy, and the division of labour between the files:

* `caseT_slot_le` (child) rewrites the `b`-sum for a *fixed* choice of the two slots
  `l1 ≠ l2` carrying `x1` and `x2` as a sum over the single free coordinate `γ`;
* `caseT_inner_le` (here) uses it to bound the inner `b`-sum for fixed `a = (x0,x1,x2)` by
  `(wg x0 x1)^2 (wg x0 x2)^2 · 6 · ∑_γ [γ ≠ x0, g ∣ d₁d₂d₃] wg x0 γ`
  (the factor `6` is the number of ordered pairs of distinct slots: every admissible `b`
  appears for at least one such pair, and each pair contributes the same expression);
* `caseT_sum_le` (child) expands the divisibility condition `g ∣ d₁ d₂ d₃` over the ordered
  factorisations `g = a 0 · a 1 · a 2`;
* `caseT_Asum_le` / `caseT_Bsum_le` (children) bound the resulting coordinate sums by
  `2 (H/e) τ(m)`, and `Afact_card_le` (child) bounds the number of factorisations by `τ(g)^2`;
* `caseT_final_arith` (child) is the final numerical comparison.

Result: `sumT ≤ 6 · H · τ(g)^2 · 8 τ(m)^3 H^3 / g ≤ 30000 τ(m d g)^8 (H^6/(dg) + H^5/g)`.
-/

namespace Work.LinnikBurgess

open Classical
open scoped BigOperators

/-- If `x 1 ≠ x 2` and both occur among the entries of `b`, then they occur in distinct slots. -/
lemma exists_slots_of_inB {x1 x2 : ℕ} {b : Fin 3 → ℕ} (h1 : inB x1 b) (h2 : inB x2 b)
    (hne : x1 ≠ x2) :
    ∃ l1 l2 : Fin 3, l1 ≠ l2 ∧ b l1 = x1 ∧ b l2 = x2 := by
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2
  · exact absurd (h1.symm.trans h2) hne
  · exact ⟨0, 1, by decide, h1, h2⟩
  · exact ⟨0, 2, by decide, h1, h2⟩
  · exact ⟨1, 0, by decide, h1, h2⟩
  · exact absurd (h1.symm.trans h2) hne
  · exact ⟨1, 2, by decide, h1, h2⟩
  · exact ⟨2, 0, by decide, h1, h2⟩
  · exact ⟨2, 1, by decide, h1, h2⟩
  · exact absurd (h1.symm.trans h2) hne

/-- **The pivotal Case-T step.**  For a fixed `a = (x0,x1,x2)` with `x1 ≠ x0 ≠ x2`, the `b`-sum
in Case T is at most `(wg x0 x1)^2 (wg x0 x2)^2 · 6 · ∑_γ [...]`.

Every admissible `b ∈ box3 H` (i.e. `condAB` and Case T hold) has `x1` and `x2` in two distinct
slots and its remaining coordinate `γ`; its weight is then exactly
`(wg x0 x1)^2 (wg x0 x2)^2 wg x0 γ`, and `g ∣ contAB a b ∣ d₁d₂d₃` with
`d₁ = del x0 x1`, `d₂ = del x0 x2`, `d₃ = del x0 γ`.  Summing over the six pairs of distinct
slots (`caseT_slot_le`) bounds the `b`-sum by `6` times the `γ`-sum. -/
lemma caseT_inner_le (d g H m x0 x1 x2 : ℕ) (hx1 : x1 ≠ x0) (hx2 : x2 ≠ x0) :
    (∑ b ∈ box3 H, (if condAB d g ![x0, x1, x2] b ∧ CaseT ![x0, x1, x2] b
        then wtAB m ![x0, x1, x2] b else 0))
      ≤ (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2
        * (6 * ∑ γ ∈ Finset.Icc 1 H,
            (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)) := by
  classical
  set P : (Fin 3 → ℕ) → ℝ := fun b => ∏ k : Fin 3, (if b k ≠ x0 then wg m x0 (b k) else 0) with hP
  have hPnn : ∀ b, 0 ≤ P b := by
    intro b
    rw [hP]
    refine Finset.prod_nonneg (fun k _ => ?_)
    by_cases hk : b k ≠ x0
    · rw [if_pos hk]; exact wg_nonneg _ _ _
    · rw [if_neg hk]
  have hwt : ∀ b : Fin 3 → ℕ, condAB d g ![x0, x1, x2] b →
      wtAB m ![x0, x1, x2] b = wg m x0 x1 * wg m x0 x2 * P b := by
    intro b hb
    have hnb : ∀ k : Fin 3, b k ≠ x0 := fun k => by simpa using (hb.1 k).symm
    simp only [hP]
    rw [Fin.prod_univ_three, if_pos (hnb 0), if_pos (hnb 1), if_pos (hnb 2)]
    simp only [wtAB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
  have h1 : (∑ b ∈ box3 H, (if condAB d g ![x0, x1, x2] b ∧ CaseT ![x0, x1, x2] b
        then wtAB m ![x0, x1, x2] b else 0))
      ≤ wg m x0 x1 * wg m x0 x2 * (∑ b ∈ box3 H,
          (if CaseT ![x0, x1, x2] b ∧ g ∣ ∏ k : Fin 3, del x0 (b k) then P b else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun b _ => ?_)
    by_cases h : condAB d g ![x0, x1, x2] b ∧ CaseT ![x0, x1, x2] b
    · have hgd : g ∣ ∏ k : Fin 3, del x0 (b k) :=
        dvd_trans h.1.2.2.2.2 (by simpa using contAB_dvd_prod_del ![x0, x1, x2] b 0)
      rw [if_pos h, if_pos ⟨h.2, hgd⟩, hwt b h.1]
    · rw [if_neg h]
      refine mul_nonneg (mul_nonneg (wg_nonneg _ _ _) (wg_nonneg _ _ _)) ?_
      by_cases hc : CaseT ![x0, x1, x2] b ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
      · rw [if_pos hc]; exact hPnn b
      · rw [if_neg hc]
  set pairs : Finset (Fin 3 × Fin 3) :=
    ((Finset.univ : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 3))).filter
      (fun p => p.1 ≠ p.2) with hpairs
  set S : Fin 3 × Fin 3 → ℝ := fun p => ∑ b ∈ box3 H,
      (if b p.1 = x1 ∧ b p.2 = x2 ∧ g ∣ ∏ k : Fin 3, del x0 (b k) then P b else 0) with hS
  have hSnn : ∀ p, 0 ≤ S p := by
    intro p
    rw [hS]
    refine Finset.sum_nonneg (fun b _ => ?_)
    by_cases hc : b p.1 = x1 ∧ b p.2 = x2 ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
    · rw [if_pos hc]; exact hPnn b
    · rw [if_neg hc]
  have hcard : pairs.card = 6 := by rw [hpairs]; decide
  have h2a : (∑ b ∈ box3 H,
        (if CaseT ![x0, x1, x2] b ∧ g ∣ ∏ k : Fin 3, del x0 (b k) then P b else 0))
      ≤ ∑ b ∈ box3 H, ∑ p ∈ pairs, (if b p.1 = x1 ∧ b p.2 = x2 ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
          then P b else 0) := by
    refine Finset.sum_le_sum (fun b hb => ?_)
    by_cases h : CaseT ![x0, x1, x2] b ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
    · rw [if_pos h]
      have hin1 : inB x1 b := by simpa using h.1.1
      have hin2 : inB x2 b := by simpa using h.1.2.1
      have hne : x1 ≠ x2 := by simpa using h.1.2.2
      obtain ⟨l1, l2, hne', hl1, hl2⟩ := exists_slots_of_inB hin1 hin2 hne
      have hmem : (l1, l2) ∈ pairs := by rw [hpairs]; simp [hne']
      have hterm : (if b l1 = x1 ∧ b l2 = x2 ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
          then P b else 0) = P b := by rw [if_pos ⟨hl1, hl2, h.2⟩]
      refine le_trans (le_of_eq hterm.symm) (Finset.single_le_sum
        (f := fun p => if b p.1 = x1 ∧ b p.2 = x2 ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
          then P b else 0) (fun p _ => ?_) hmem)
      by_cases hc : b p.1 = x1 ∧ b p.2 = x2 ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
      · rw [if_pos hc]; exact hPnn b
      · rw [if_neg hc]
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun p _ => by
        by_cases hc : b p.1 = x1 ∧ b p.2 = x2 ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
        · rw [if_pos hc]; exact hPnn b
        · rw [if_neg hc])
  have h2 : (∑ b ∈ box3 H,
        (if CaseT ![x0, x1, x2] b ∧ g ∣ ∏ k : Fin 3, del x0 (b k) then P b else 0))
      ≤ ∑ p ∈ pairs, S p := by
    refine le_trans h2a (le_of_eq ?_)
    rw [Finset.sum_comm]
  have h4 : (∑ p ∈ pairs, S p) ≤ 6 * ∑ γ ∈ Finset.Icc 1 H,
      (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ
        then wg m x0 x1 * wg m x0 x2 * wg m x0 γ else 0) := by
    have h3 : ∀ p ∈ pairs, S p ≤ ∑ γ ∈ Finset.Icc 1 H,
        (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ
          then wg m x0 x1 * wg m x0 x2 * wg m x0 γ else 0) := by
      intro p hp
      rw [hpairs, Finset.mem_filter] at hp
      have hpp : p.1 ≠ p.2 := hp.2
      rw [hS]
      simp only [hP]
      exact caseT_slot_le p.1 p.2 hpp hx1 hx2
    calc ∑ p ∈ pairs, S p ≤ ∑ _p ∈ pairs, (∑ γ ∈ Finset.Icc 1 H,
          (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ
            then wg m x0 x1 * wg m x0 x2 * wg m x0 γ else 0)) := Finset.sum_le_sum h3
      _ = 6 * ∑ γ ∈ Finset.Icc 1 H,
          (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ
            then wg m x0 x1 * wg m x0 x2 * wg m x0 γ else 0) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        norm_num
  have hV0 : (∑ γ ∈ Finset.Icc 1 H,
        (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ
          then wg m x0 x1 * wg m x0 x2 * wg m x0 γ else 0))
      = wg m x0 x1 * wg m x0 x2 * (∑ γ ∈ Finset.Icc 1 H,
          (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    by_cases hc : γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, mul_zero]
  have hAB : 0 ≤ wg m x0 x1 * wg m x0 x2 := mul_nonneg (wg_nonneg _ _ _) (wg_nonneg _ _ _)
  calc (∑ b ∈ box3 H, (if condAB d g ![x0, x1, x2] b ∧ CaseT ![x0, x1, x2] b
        then wtAB m ![x0, x1, x2] b else 0))
      ≤ wg m x0 x1 * wg m x0 x2 * (∑ b ∈ box3 H,
          (if CaseT ![x0, x1, x2] b ∧ g ∣ ∏ k : Fin 3, del x0 (b k) then P b else 0)) := h1
    _ ≤ wg m x0 x1 * wg m x0 x2 * (∑ p ∈ pairs, S p) :=
        mul_le_mul_of_nonneg_left h2 hAB
    _ ≤ wg m x0 x1 * wg m x0 x2 * (6 * ∑ γ ∈ Finset.Icc 1 H,
          (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ
            then wg m x0 x1 * wg m x0 x2 * wg m x0 γ else 0)) :=
        mul_le_mul_of_nonneg_left h4 hAB
    _ = (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2
        * (6 * ∑ γ ∈ Finset.Icc 1 H,
            (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)) := by
        rw [hV0]
        ring

/-- The `b`-sum in Case T is bounded by the Case-T expression with the `6` and the guard
`x1 ≠ x0 ∧ x2 ≠ x0` in front.  (The guard is what makes the estimate non-trivial: if `x1 = x0`
then `condAB` fails and the sum vanishes.) -/
lemma caseT_inner_le' (d g H m x0 x1 x2 : ℕ) :
    (∑ b ∈ box3 H, (if condAB d g ![x0, x1, x2] b ∧ CaseT ![x0, x1, x2] b
        then wtAB m ![x0, x1, x2] b else 0))
      ≤ (if x1 ≠ x0 ∧ x2 ≠ x0 then (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2 else 0)
        * (6 * ∑ γ ∈ Finset.Icc 1 H,
            (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)) := by
  classical
  by_cases hcond : x1 ≠ x0 ∧ x2 ≠ x0
  · rw [if_pos hcond]
    exact caseT_inner_le d g H m x0 x1 x2 hcond.1 hcond.2
  · have hzero : (∑ b ∈ box3 H, (if condAB d g ![x0, x1, x2] b ∧ CaseT ![x0, x1, x2] b
        then wtAB m ![x0, x1, x2] b else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      by_cases h : condAB d g ![x0, x1, x2] b ∧ CaseT ![x0, x1, x2] b
      · exfalso
        have h01 : x0 ≠ x1 := by simpa using h.1.2.1
        have h02 : x0 ≠ x2 := by simpa using h.1.2.2.1
        exact hcond ⟨fun hx => h01 hx.symm, fun hx => h02 hx.symm⟩
      · exact if_neg h
    rw [hzero, if_neg hcond, zero_mul]

/-- **Case T estimate** (`a 1 ≠ a 2`, both occurring among the `b`-entries).  With `m` squarefree, `gcd(m,d) = gcd(m,g) = 1`, `0 < d`, `0 < g`, this part of the master sum is at most `30000 · τ(m d g)^8 · (H^6/(dg) + H^5/g)`. -/
theorem sumT_le {H m d g : ℕ} (hm : Squarefree m) (hmd : Nat.Coprime m d) (hmg : Nat.Coprime m g)
    (hd : 0 < d) (hg : 0 < g) :
    sumT H m d g ≤ rhsC 30000 H m d g := by
  classical
  have hm0 : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  -- **Step 1**: iterate the outer `a`-sum and bound the inner `b`-sum by `caseT_inner_le'`.
  have hstep1 : sumT H m d g
      ≤ ∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
          (if x1 ≠ x0 ∧ x2 ≠ x0 then (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2 else 0)
            * (6 * ∑ γ ∈ Finset.Icc 1 H,
                (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)) := by
    rw [sumT]
    rw [frame_count_prov_aux.sum_box3_eq_iterate H (fun a => ∑ b ∈ box3 H,
      (if condAB d g a b ∧ CaseT a b then wtAB m a b else 0))]
    refine Finset.sum_le_sum (fun x0 _ => Finset.sum_le_sum (fun x1 _ =>
      Finset.sum_le_sum (fun x2 _ => ?_)))
    exact caseT_inner_le' d g H m x0 x1 x2
  -- **Step 2**: pull the factor `6` out of the sum and expand the divisibility condition.
  have hshape : (∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
        (if x1 ≠ x0 ∧ x2 ≠ x0 then (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2 else 0)
          * (6 * ∑ γ ∈ Finset.Icc 1 H,
              (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)))
      = 6 * (∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
          (if x1 ≠ x0 ∧ x2 ≠ x0 then (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2 else 0)
            * ∑ γ ∈ Finset.Icc 1 H,
                (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)) := by
    rw [show (∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
        (if x1 ≠ x0 ∧ x2 ≠ x0 then (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2 else 0)
          * (6 * ∑ γ ∈ Finset.Icc 1 H,
              (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)))
        = ∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
          6 * ((if x1 ≠ x0 ∧ x2 ≠ x0 then (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2 else 0)
            * ∑ γ ∈ Finset.Icc 1 H,
                (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0))
        from Finset.sum_congr rfl (fun x0 _ => Finset.sum_congr rfl (fun x1 _ =>
          Finset.sum_congr rfl (fun x2 _ => by ring)))]
    simp only [Finset.mul_sum]
  have hstep2 : (∑ x0 ∈ Finset.Icc 1 H, ∑ x1 ∈ Finset.Icc 1 H, ∑ x2 ∈ Finset.Icc 1 H,
        (if x1 ≠ x0 ∧ x2 ≠ x0 then (wg m x0 x1) ^ 2 * (wg m x0 x2) ^ 2 else 0)
          * (6 * ∑ γ ∈ Finset.Icc 1 H,
              (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ then wg m x0 γ else 0)))
      ≤ 6 * ∑ x0 ∈ Finset.Icc 1 H, ∑ a ∈ Afact g,
          frame_count_prov_aux.Asum H m (a 0) x0 * frame_count_prov_aux.Asum H m (a 1) x0
            * frame_count_prov_aux.Bsum H m (a 2) x0 := by
    rw [hshape]
    exact mul_le_mul_of_nonneg_left (caseT_sum_le hg) (by norm_num)
  -- **Step 3**: bound each summand by `2 (H/e) τ(m)` and count the factorisations.
  have hterm : ∀ x0 ∈ Finset.Icc 1 H, ∀ a ∈ Afact g,
      frame_count_prov_aux.Asum H m (a 0) x0 * frame_count_prov_aux.Asum H m (a 1) x0
        * frame_count_prov_aux.Bsum H m (a 2) x0
      ≤ 8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ) := by
    intro x0 hx0 a ha
    obtain ⟨hprod, hdiv⟩ := (mem_Afact hg).mp ha
    have ha0 : 0 < a 0 := Nat.pos_of_dvd_of_pos (hdiv 0) hg
    have ha1 : 0 < a 1 := Nat.pos_of_dvd_of_pos (hdiv 1) hg
    have ha2 : 0 < a 2 := Nat.pos_of_dvd_of_pos (hdiv 2) hg
    have hc0 : Nat.Coprime m (a 0) := Nat.Coprime.coprime_dvd_right (hdiv 0) hmg
    have hc1 : Nat.Coprime m (a 1) := Nat.Coprime.coprime_dvd_right (hdiv 1) hmg
    have hc2 : Nat.Coprime m (a 2) := Nat.Coprime.coprime_dvd_right (hdiv 2) hmg
    have hA0 : frame_count_prov_aux.Asum H m (a 0) x0
        ≤ 2 * ((H : ℝ) / (a 0)) * ((m.divisors.card : ℕ) : ℝ) :=
      caseT_Asum_le hm0 ha0 hc0 hx0
    have hA1 : frame_count_prov_aux.Asum H m (a 1) x0
        ≤ 2 * ((H : ℝ) / (a 1)) * ((m.divisors.card : ℕ) : ℝ) :=
      caseT_Asum_le hm0 ha1 hc1 hx0
    have hB2 : frame_count_prov_aux.Bsum H m (a 2) x0
        ≤ 2 * ((H : ℝ) / (a 2)) * ((m.divisors.card : ℕ) : ℝ) :=
      caseT_Bsum_le hm0 ha2 hc2 hx0
    have hprodR : (a 0 : ℝ) * (a 1 : ℝ) * (a 2 : ℝ) = (g : ℝ) := by
      have h := hprod
      rw [Fin.prod_univ_three] at h
      exact_mod_cast h
    have hp : frame_count_prov_aux.Asum H m (a 0) x0 * frame_count_prov_aux.Asum H m (a 1) x0
        * frame_count_prov_aux.Bsum H m (a 2) x0
        ≤ (2 * ((H : ℝ) / (a 0)) * ((m.divisors.card : ℕ) : ℝ))
            * (2 * ((H : ℝ) / (a 1)) * ((m.divisors.card : ℕ) : ℝ))
            * (2 * ((H : ℝ) / (a 2)) * ((m.divisors.card : ℕ) : ℝ)) :=
      mul_le_mul (mul_le_mul hA0 hA1 (frame_count_prov_aux.Asum_nonneg _ _ _ _) (by positivity))
        hB2 (frame_count_prov_aux.Bsum_nonneg _ _ _ _) (by positivity)
    refine hp.trans (le_of_eq ?_)
    calc (2 * ((H : ℝ) / (a 0)) * ((m.divisors.card : ℕ) : ℝ))
          * (2 * ((H : ℝ) / (a 1)) * ((m.divisors.card : ℕ) : ℝ))
          * (2 * ((H : ℝ) / (a 2)) * ((m.divisors.card : ℕ) : ℝ))
        = 8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3
            / ((a 0 : ℝ) * (a 1 : ℝ) * (a 2 : ℝ)) := by ring
      _ = 8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ) := by rw [hprodR]
  have hstep3 : (∑ x0 ∈ Finset.Icc 1 H, ∑ a ∈ Afact g,
        frame_count_prov_aux.Asum H m (a 0) x0 * frame_count_prov_aux.Asum H m (a 1) x0
          * frame_count_prov_aux.Bsum H m (a 2) x0)
      ≤ (H : ℝ) * (((g.divisors.card : ℕ) : ℝ) ^ 2
          * (8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ))) := by
    have hsum_a : ∀ x0 ∈ Finset.Icc 1 H,
        (∑ a ∈ Afact g, frame_count_prov_aux.Asum H m (a 0) x0
            * frame_count_prov_aux.Asum H m (a 1) x0 * frame_count_prov_aux.Bsum H m (a 2) x0)
          ≤ ((g.divisors.card : ℕ) : ℝ) ^ 2
              * (8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ)) := by
      intro x0 hx0
      calc (∑ a ∈ Afact g, frame_count_prov_aux.Asum H m (a 0) x0
              * frame_count_prov_aux.Asum H m (a 1) x0 * frame_count_prov_aux.Bsum H m (a 2) x0)
          ≤ ∑ _a ∈ Afact g, (8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ)) :=
            Finset.sum_le_sum (fun a ha => hterm x0 hx0 a ha)
        _ = ((Afact g).card : ℝ)
              * (8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((g.divisors.card : ℕ) : ℝ) ^ 2
              * (8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast Afact_card_le g) (by positivity)
    calc (∑ x0 ∈ Finset.Icc 1 H, ∑ a ∈ Afact g,
            frame_count_prov_aux.Asum H m (a 0) x0 * frame_count_prov_aux.Asum H m (a 1) x0
              * frame_count_prov_aux.Bsum H m (a 2) x0)
        ≤ ∑ _x0 ∈ Finset.Icc 1 H, (((g.divisors.card : ℕ) : ℝ) ^ 2
              * (8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ))) :=
          Finset.sum_le_sum hsum_a
      _ = (H : ℝ) * (((g.divisors.card : ℕ) : ℝ) ^ 2
              * (8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          norm_num
  -- **Step 4**: the final numerical comparison.
  have hfinal : 6 * ((H : ℝ) * (((g.divisors.card : ℕ) : ℝ) ^ 2
        * (8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ))))
      = 48 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * ((g.divisors.card : ℕ) : ℝ) ^ 2
          * (H : ℝ) ^ 4 / (g : ℝ) := by
    ring
  calc sumT H m d g
      ≤ _ := hstep1
    _ ≤ 6 * _ := hstep2
    _ ≤ 6 * ((H : ℝ) * (((g.divisors.card : ℕ) : ℝ) ^ 2
          * (8 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * (H : ℝ) ^ 3 / (g : ℝ)))) :=
        mul_le_mul_of_nonneg_left hstep3 (by norm_num)
    _ = 48 * ((m.divisors.card : ℕ) : ℝ) ^ 3 * ((g.divisors.card : ℕ) : ℝ) ^ 2
          * (H : ℝ) ^ 4 / (g : ℝ) := hfinal
    _ ≤ rhsC 30000 H m d g := caseT_final_arith hd hg

end Work.LinnikBurgess
