import Mathlib
import Submission.Work.FIArea4.jacobi_congruence_count
import Submission.Work.FIArea4.Vflip.count_coset_supp

namespace Work.FIArea4.Vflip.Vfd

open Finset

/-!
# A crude count for the congruence `m ∣ a y - b x` in a box

We bound the number of pairs `(x,y)` with `1 ≤ x ≤ 2A`, `1 ≤ y ≤ 2B` and `m ∣ a y - b x`
(equivalently `a y ≡ b x (mod m)`) by `4AB/m + 2·min(A,B)`.

Two ingredients: for fixed `x`, all solutions `y` of `a y ≡ b x (mod m)` lie in a single residue
class modulo `m / (a,m)`; and a solution can exist only when `(a,m) ∣ x`.  Counting the `x` in one
direction gives `≤ 4AB/m + 2A`, counting in the other gives `≤ 4AB/m + 2B`; the minimum of the two
is the claim.
-/

/-- Two solutions `y, y'` of `a y ≡ b x (mod m)` are congruent modulo `m / (a,m)`. -/
lemma modEq_of_sol (m a b x y y0 : ℕ) (hm : 1 ≤ m)
    (hy : (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ))
    (hy0 : (m : ℤ) ∣ (a : ℤ) * (y0 : ℤ) - (x : ℤ) * (b : ℤ)) :
    y ≡ y0 [MOD m / Nat.gcd a m] := by
  have hdiff : (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (a : ℤ) * (y0 : ℤ) := by
    have h := dvd_sub hy hy0
    have heq : (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ)
        - ((a : ℤ) * (y0 : ℤ) - (x : ℤ) * (b : ℤ)) = (a : ℤ) * (y : ℤ) - (a : ℤ) * (y0 : ℤ) := by
      ring
    rwa [heq] at h
  have hme : a * y ≡ a * y0 [MOD m] := by
    rw [Nat.modEq_iff_dvd]
    have heq : ((a * y0 : ℕ) : ℤ) - ((a * y : ℕ) : ℤ)
        = -((a : ℤ) * (y : ℤ) - (a : ℤ) * (y0 : ℤ)) := by push_cast; ring
    rw [heq]
    exact dvd_neg.mpr hdiff
  have hcan := Nat.ModEq.cancel_left_div_gcd (by omega : 0 < m) hme
  rw [Nat.gcd_comm] at hcan
  exact hcan

/-- If `a y ≡ b x (mod m)` has a solution `y` and `(b, (a,m)) = 1`, then `(a,m) ∣ x`. -/
lemma dvd_of_sol (m a b x y : ℕ) (hcop : Nat.Coprime b (Nat.gcd a m))
    (hy : (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ)) : Nat.gcd a m ∣ x := by
  have hgm : ((Nat.gcd a m : ℕ) : ℤ) ∣ (m : ℤ) := by
    exact_mod_cast (Nat.gcd_dvd_right a m)
  have hga : ((Nat.gcd a m : ℕ) : ℤ) ∣ (a : ℤ) := by
    exact_mod_cast (Nat.gcd_dvd_left a m)
  have h1 : ((Nat.gcd a m : ℕ) : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ) :=
    dvd_trans hgm hy
  have h2 : ((Nat.gcd a m : ℕ) : ℤ) ∣ (a : ℤ) * (y : ℤ) := dvd_mul_of_dvd_left hga y
  have h3 : ((Nat.gcd a m : ℕ) : ℤ) ∣ (x : ℤ) * (b : ℤ) := by
    have h := dvd_sub h2 h1
    have heq : (a : ℤ) * (y : ℤ) - ((a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ)) = (x : ℤ) * (b : ℤ) := by
      ring
    rwa [heq] at h
  have h3' : ((Nat.gcd a m : ℕ) : ℤ) ∣ ((x * b : ℕ) : ℤ) := by push_cast; exact h3
  have h3'' : Nat.gcd a m ∣ x * b := Int.natCast_dvd_natCast.mp h3'
  exact hcop.symm.dvd_of_dvd_mul_right h3''

/-- For fixed `x`, the set of `y ∈ [1, 2B]` solving `a y ≡ b x (mod m)` has at most
`2B / (m/(a,m)) + 1` elements. -/
lemma fiber_card_le (m B a b x : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 1 (2 * B)).filter
        (fun y : ℕ => (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ))).card
      ≤ 2 * B / (m / Nat.gcd a m) + 1 := by
  have hm0 : 0 < m := by omega
  have hgpos : 0 < Nat.gcd a m := Nat.gcd_pos_of_pos_right a hm0
  have hgd : Nat.gcd a m ∣ m := Nat.gcd_dvd_right a m
  have hglem : Nat.gcd a m ≤ m := Nat.le_of_dvd hm0 hgd
  have hpos : 0 < m / Nat.gcd a m := Nat.div_pos hglem hgpos
  by_cases hne : ((Finset.Icc 1 (2 * B)).filter
      (fun y : ℕ => (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ))).Nonempty
  · obtain ⟨y0, hy0⟩ := hne
    have hy0' : (m : ℤ) ∣ (a : ℤ) * (y0 : ℤ) - (x : ℤ) * (b : ℤ) :=
      (Finset.mem_filter.mp hy0).2
    have hsub : ((Finset.Icc 1 (2 * B)).filter
        (fun y : ℕ => (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ)))
        ⊆ (Finset.Icc 1 (2 * B)).filter
            (fun y : ℕ => y % (m / Nat.gcd a m) = y0 % (m / Nat.gcd a m)) := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      refine ⟨hy.1, ?_⟩
      exact modEq_of_sol m a b x y y0 hm hy.2 hy0'
    calc ((Finset.Icc 1 (2 * B)).filter
          (fun y : ℕ => (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ))).card
        ≤ ((Finset.Icc 1 (2 * B)).filter
            (fun y : ℕ => y % (m / Nat.gcd a m) = y0 % (m / Nat.gcd a m))).card :=
          Finset.card_le_card hsub
      _ ≤ 2 * B / (m / Nat.gcd a m) + 1 :=
          Work.FIArea4.card_filter_mod_le (m / Nat.gcd a m) (2 * B)
            (y0 % (m / Nat.gcd a m)) hpos
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact Nat.zero_le _

/-- Arithmetic: `(2A/g)·(2B/(m/g) + 1) ≤ 4AB/m + 2A` in `ℝ` when `g ∣ m`, `g ≥ 1`, `m ≥ 1`. -/
lemma real_arith (A B m g : ℕ) (hm : 1 ≤ m) (hg : 1 ≤ g) (hgd : g ∣ m) :
    (((2 * A / g) * (2 * B / (m / g) + 1) : ℕ) : ℝ)
      ≤ 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (A : ℝ) := by
  set e := m / g with he
  have hmul : g * e = m := by rw [he]; exact Nat.mul_div_cancel' hgd
  have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hge : g ≤ m := Nat.le_of_dvd (by omega) hgd
  have he1 : 1 ≤ e := by rw [he]; exact Nat.div_pos hge (by omega)
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
  have hgem : (g : ℝ) * (e : ℝ) = (m : ℝ) := by rw [← hmul]; push_cast; ring
  have h1 : (((2 * A / g) : ℕ) : ℝ) ≤ 2 * (A : ℝ) / g := by
    calc (((2 * A / g) : ℕ) : ℝ) ≤ ((2 * A : ℕ) : ℝ) / (g : ℝ) := Nat.cast_div_le
      _ = 2 * (A : ℝ) / g := by push_cast; ring
  have h2 : (((2 * B / e) : ℕ) : ℝ) ≤ 2 * (B : ℝ) / e := by
    calc (((2 * B / e) : ℕ) : ℝ) ≤ ((2 * B : ℕ) : ℝ) / (e : ℝ) := Nat.cast_div_le
      _ = 2 * (B : ℝ) / e := by push_cast; ring
  have hL : (((2 * A / g) * (2 * B / e + 1) : ℕ) : ℝ)
      = (((2 * A / g) : ℕ) : ℝ) * ((((2 * B / e) : ℕ) : ℝ) + 1) := by push_cast; ring
  rw [hL]
  calc (((2 * A / g) : ℕ) : ℝ) * ((((2 * B / e) : ℕ) : ℝ) + 1)
      ≤ (2 * (A : ℝ) / g) * (2 * (B : ℝ) / e + 1) := by
        apply mul_le_mul h1 (by linarith) (by positivity) (by positivity)
    _ = 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (A : ℝ) / g := by
        rw [← hgem]
        field_simp
        ring
    _ ≤ 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (A : ℝ) := by
        have hle : 2 * (A : ℝ) / g ≤ 2 * (A : ℝ) := by
          rw [div_le_iff₀ hgR]
          have hg1 : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg
          have hAn : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
          nlinarith [hg1, hAn]
        linarith

/-- Swapping the two coordinates relates the two forms of the congruence count. -/
lemma card_congr_swap (A B m a b : ℕ) :
    (((Finset.Icc 1 (2 * A) ×ˢ Finset.Icc 1 (2 * B)).filter
        (fun p : ℕ × ℕ => (m : ℤ) ∣ (a : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (b : ℤ))).card)
      = (((Finset.Icc 1 (2 * B) ×ˢ Finset.Icc 1 (2 * A)).filter
        (fun p : ℕ × ℕ => (m : ℤ) ∣ (b : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (a : ℤ))).card) := by
  refine Finset.card_bij' (fun p _ => (p.2, p.1)) (fun q _ => (q.2, q.1)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hpmem, hpc⟩ := hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpmem
    refine ⟨Finset.mem_product.mpr ⟨hp2, hp1⟩, ?_⟩
    have : (b : ℤ) * (p.1 : ℤ) - (p.2 : ℤ) * (a : ℤ)
        = -((a : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (b : ℤ)) := by ring
    rw [this]; exact dvd_neg.mpr hpc
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    obtain ⟨hqmem, hqc⟩ := hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hqmem
    refine ⟨Finset.mem_product.mpr ⟨hq2, hq1⟩, ?_⟩
    have : (a : ℤ) * (q.1 : ℤ) - (q.2 : ℤ) * (b : ℤ)
        = -((b : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (a : ℤ)) := by ring
    rw [this]; exact dvd_neg.mpr hqc
  · intro p hp; exact Prod.ext rfl rfl
  · intro q hq; exact Prod.ext rfl rfl

/-- The first-coordinate count: `≤ 4AB/m + 2A`. -/
lemma card_congr_fst (A B m a b : ℕ) (hm : 1 ≤ m) (hab : Nat.Coprime a b) :
    (((Finset.Icc 1 (2 * A) ×ˢ Finset.Icc 1 (2 * B)).filter
        (fun p : ℕ × ℕ => (m : ℤ) ∣ (a : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (b : ℤ))).card : ℝ)
      ≤ 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (A : ℝ) := by
  have hm0 : 0 < m := by omega
  have hgpos : 0 < Nat.gcd a m := Nat.gcd_pos_of_pos_right a hm0
  have hgd : Nat.gcd a m ∣ m := Nat.gcd_dvd_right a m
  have hcop : Nat.Coprime b (Nat.gcd a m) := hab.symm.coprime_dvd_right (Nat.gcd_dvd_left a m)
  have hN : (((Finset.Icc 1 (2 * A) ×ˢ Finset.Icc 1 (2 * B)).filter
      (fun p : ℕ × ℕ => (m : ℤ) ∣ (a : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (b : ℤ))).card)
      ≤ (2 * A / Nat.gcd a m) * (2 * B / (m / Nat.gcd a m) + 1) := by
    have hsum : (((Finset.Icc 1 (2 * A) ×ˢ Finset.Icc 1 (2 * B)).filter
        (fun p : ℕ × ℕ => (m : ℤ) ∣ (a : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (b : ℤ))).card)
        = ∑ x ∈ Finset.Icc 1 (2 * A),
            ((Finset.Icc 1 (2 * B)).filter
              (fun y : ℕ => (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ))).card :=
      Work.FIArea4.card_filter_product_eq_sum_fst _ _ _
    rw [hsum]
    have hbound : ∀ x ∈ Finset.Icc 1 (2 * A),
        ((Finset.Icc 1 (2 * B)).filter
            (fun y : ℕ => (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ))).card
          ≤ (if Nat.gcd a m ∣ x then 2 * B / (m / Nat.gcd a m) + 1 else 0) := by
      intro x _
      by_cases hx : Nat.gcd a m ∣ x
      · rw [if_pos hx]; exact fiber_card_le m B a b x hm
      · rw [if_neg hx]
        have hempty : ((Finset.Icc 1 (2 * B)).filter
            (fun y : ℕ => (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ))) = ∅ := by
          rw [← Finset.not_nonempty_iff_eq_empty]
          rintro ⟨y, hy⟩
          exact hx (dvd_of_sol m a b x y hcop (Finset.mem_filter.mp hy).2)
        rw [hempty, Finset.card_empty]
    calc ∑ x ∈ Finset.Icc 1 (2 * A),
          ((Finset.Icc 1 (2 * B)).filter
            (fun y : ℕ => (m : ℤ) ∣ (a : ℤ) * (y : ℤ) - (x : ℤ) * (b : ℤ))).card
        ≤ ∑ x ∈ Finset.Icc 1 (2 * A),
            (if Nat.gcd a m ∣ x then 2 * B / (m / Nat.gcd a m) + 1 else 0) :=
          Finset.sum_le_sum hbound
      _ = ((Finset.Icc 1 (2 * A)).filter (fun x => Nat.gcd a m ∣ x)).card
            * (2 * B / (m / Nat.gcd a m) + 1) := by
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      _ ≤ (2 * A / Nat.gcd a m) * (2 * B / (m / Nat.gcd a m) + 1) := by
          apply Nat.mul_le_mul_right
          exact card_multiples_le (2 * A) (Nat.gcd a m) hgpos _
            (fun x hx => (Finset.mem_filter.mp hx).2)
            (fun x hx => (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).1)
            (fun x hx => (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).2)
  calc (((Finset.Icc 1 (2 * A) ×ˢ Finset.Icc 1 (2 * B)).filter
        (fun p : ℕ × ℕ => (m : ℤ) ∣ (a : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (b : ℤ))).card : ℝ)
      ≤ (((2 * A / Nat.gcd a m) * (2 * B / (m / Nat.gcd a m) + 1) : ℕ) : ℝ) := by
        exact_mod_cast hN
    _ ≤ 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (A : ℝ) :=
        real_arith A B m (Nat.gcd a m) hm (by omega) hgd

theorem card_congr_crude (A B m a b : ℕ) (hm : 1 ≤ m) (hab : Nat.Coprime a b) :
    (((Finset.Icc 1 (2 * A) ×ˢ Finset.Icc 1 (2 * B)).filter
        (fun p : ℕ × ℕ => (m : ℤ) ∣ (a : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (b : ℤ))).card : ℝ)
      ≤ 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * min (A : ℝ) (B : ℝ) := by
  set S1 := ((Finset.Icc 1 (2 * A) ×ˢ Finset.Icc 1 (2 * B)).filter
    (fun p : ℕ × ℕ => (m : ℤ) ∣ (a : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (b : ℤ))) with hS1
  set S2 := ((Finset.Icc 1 (2 * B) ×ˢ Finset.Icc 1 (2 * A)).filter
    (fun p : ℕ × ℕ => (m : ℤ) ∣ (b : ℤ) * (p.2 : ℤ) - (p.1 : ℤ) * (a : ℤ))) with hS2
  have hfst : (S1.card : ℝ) ≤ 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (A : ℝ) := by
    rw [hS1]; exact card_congr_fst A B m a b hm hab
  have hsnd : (S2.card : ℝ) ≤ 4 * (B : ℝ) * (A : ℝ) / (m : ℝ) + 2 * (B : ℝ) := by
    rw [hS2]; exact card_congr_fst B A m b a hm hab.symm
  have hsw : S1.card = S2.card := by
    rw [hS1, hS2]; exact card_congr_swap A B m a b
  have hB : (S1.card : ℝ) ≤ 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (B : ℝ) := by
    rw [show (S1.card : ℝ) = (S2.card : ℝ) by rw [hsw]]
    calc (S2.card : ℝ) ≤ 4 * (B : ℝ) * (A : ℝ) / (m : ℝ) + 2 * (B : ℝ) := hsnd
      _ = 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (B : ℝ) := by ring
  have hgoal : min (4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (A : ℝ))
        (4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (B : ℝ))
      = 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * min (A : ℝ) (B : ℝ) := by
    rcases le_total (A : ℝ) B with h | h
    · rw [min_eq_left (by linarith), min_eq_left h]
    · rw [min_eq_right (by linarith), min_eq_right h]
  calc (S1.card : ℝ)
      ≤ min (4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (A : ℝ))
          (4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * (B : ℝ)) := le_min hfst hB
    _ = 4 * (A : ℝ) * (B : ℝ) / (m : ℝ) + 2 * min (A : ℝ) (B : ℝ) := hgoal

end Work.FIArea4.Vflip.Vfd
