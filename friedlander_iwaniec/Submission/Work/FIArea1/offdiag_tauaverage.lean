import Mathlib
import Submission.Work.FIArea1.boxZ_dvd_count_le
import Submission.Work.FIArea1.l51arith_defs
import Submission.Work.FIArea1.l51_arith_bound
import Submission.Work.FIArea1.l51_local_count
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `d ∣ Q.natAbs ↔ (d : ℤ) ∣ Q` for `d : ℕ`, `Q : ℤ`. -/
lemma nat_dvd_natAbs_iff (d : ℕ) (Q : ℤ) : d ∣ Q.natAbs ↔ (d : ℤ) ∣ Q := by
  rw [← Int.dvd_natAbs (a := ((d : ℕ) : ℤ)) (b := Q), Int.natCast_dvd_natCast]

/-- **Box count for the form `a c₁² - b c₂²`.** For `D ≥ 1`, the number of pairs
`(c₁,c₂) ∈ [-L,L]²` with `D ∣ a c₁² - b c₂²` is at most the number of solutions modulo `D` of
`a γ₁² ≡ b γ₂²`, times `(2L/D + 2)²`. -/
lemma card_box_dvd_quad_le (L : ℕ) (D : ℕ) [NeZero D] (a b : ℤ) :
    (((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
        (fun p : ℤ × ℤ => (D : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card
      ≤ ((Finset.univ.filter (fun z : ZMod D × ZMod D =>
            (a : ZMod D) * z.1 ^ 2 = (b : ZMod D) * z.2 ^ 2)).card)
          * (2 * L / D + 2) ^ 2 := by
  classical
  set B : ℕ := 2 * L / D + 2 with hB
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  set S : Finset (ℤ × ℤ) :=
    ((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
      (fun p : ℤ × ℤ => (D : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2) with hS
  set T : Finset (ZMod D × ZMod D) :=
    Finset.univ.filter (fun z : ZMod D × ZMod D =>
      (a : ZMod D) * z.1 ^ 2 = (b : ZMod D) * z.2 ^ 2) with hT
  set f : ℤ × ℤ → ZMod D × ZMod D := fun p => ((p.1 : ZMod D), (p.2 : ZMod D)) with hf
  have hfiber : ∀ b0 : ZMod D × ZMod D, (S.filter (fun p => f p = b0)).card ≤ B ^ 2 := by
    intro b0
    have hsub : S.filter (fun p => f p = b0) ⊆
        ((Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (fun x : ℤ => (x : ZMod D) = b0.1)) ×ˢ
        ((Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (fun x : ℤ => (x : ZMod D) = b0.2)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hp2⟩ := hp
      rw [hS, Finset.mem_filter] at hpS
      obtain ⟨hpbox, _⟩ := hpS
      rw [Finset.mem_product] at hpbox
      rw [hf, Prod.mk.injEq] at hp2
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨hpbox.1, hp2.1⟩, hpbox.2, hp2.2⟩
    calc (S.filter (fun p => f p = b0)).card
        ≤ (((Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (fun x : ℤ => (x : ZMod D) = b0.1)) ×ˢ
           ((Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (fun x : ℤ => (x : ZMod D) = b0.2))).card :=
          Finset.card_le_card hsub
      _ = _ * _ := Finset.card_product _ _
      _ ≤ B * B := Nat.mul_le_mul (by simpa [hB] using int_card_mod_le L D hD b0.1)
                                  (by simpa [hB] using int_card_mod_le L D hD b0.2)
      _ = B ^ 2 := by ring
  have himage : (S.image f).card ≤ T.card := by
    apply Finset.card_le_card
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_filter] at hp
    obtain ⟨hpS, hdvd⟩ := hp
    have hthis : (((a * p.1 ^ 2 - b * p.2 ^ 2 : ℤ)) : ZMod D) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ D).mpr hdvd
    push_cast at hthis
    simp only [hf]
    exact sub_eq_zero.mp hthis
  calc S.card = ∑ b0 ∈ S.image f, (S.filter (fun p => f p = b0)).card :=
        Finset.card_eq_sum_card_image f S
    _ ≤ ∑ b0 ∈ S.image f, B ^ 2 := Finset.sum_le_sum (fun b0 _ => hfiber b0)
    _ = (S.image f).card * B ^ 2 := by
        rw [Finset.sum_const_nat]; intro x _; rfl
    _ ≤ T.card * B ^ 2 := Nat.mul_le_mul_right _ himage

/-- `τ(n) ≤ 9 Σ_{d ≤ 2L, d ∣ n} τ(d)` for `1 ≤ n ≤ 8L³` (the divisor-splitting Lemma 2.2, part 3,
with the range of `d` restricted to `d ≤ 2L`). -/
lemma tau_le_sum_Icc {n L : ℕ} (hn : 1 ≤ n) (hnL : n ≤ 8 * L ^ 3) :
    ((n.divisors.card : ℝ))
      ≤ 9 * ∑ d ∈ Finset.Icc 1 (2 * L), (if d ∣ n then ((d.divisors.card : ℝ)) else 0) := by
  have hsub : (n.divisors.filter (fun d => d ^ 3 ≤ n))
      ⊆ (Finset.Icc 1 (2 * L)).filter (fun d => d ∣ n) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨hddiv, hdcube⟩ := hd
    rw [Nat.mem_divisors] at hddiv
    obtain ⟨hddvd, hn0⟩ := hddiv
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.pos_of_dvd_of_pos hddvd (by omega), ?_⟩, hddvd⟩
    have h3 : d ^ 3 ≤ (2 * L) ^ 3 := by
      calc d ^ 3 ≤ n := hdcube
        _ ≤ 8 * L ^ 3 := hnL
        _ = (2 * L) ^ 3 := by ring
    exact (Nat.pow_le_pow_iff_left (by norm_num : (3:ℕ) ≠ 0)).mp h3
  have hnat : n.divisors.card
      ≤ 9 * ((n.divisors.filter (fun d => d ^ 3 ≤ n)).sum (fun d => d.divisors.card)) :=
    Commons.NumberTheory.FriedlanderIwaniec.tau_le_nine_sum_divisors_cube hn
  have hstep : ((n.divisors.filter (fun d => d ^ 3 ≤ n)).sum (fun d => d.divisors.card) : ℝ)
      ≤ (((Finset.Icc 1 (2 * L)).filter (fun d => d ∣ n)).sum (fun d => d.divisors.card) : ℝ) := by
    exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => Nat.zero_le _)
  have hfin : (((Finset.Icc 1 (2 * L)).filter (fun d => d ∣ n)).sum (fun d => d.divisors.card) : ℝ)
      = ∑ d ∈ Finset.Icc 1 (2 * L), (if d ∣ n then ((d.divisors.card : ℝ)) else 0) := by
    rw [Finset.sum_filter]
  rw [← hfin]
  calc (n.divisors.card : ℝ)
      ≤ 9 * ((n.divisors.filter (fun d => d ^ 3 ≤ n)).sum (fun d => (d.divisors.card : ℕ)) : ℝ) := by
        exact_mod_cast hnat
    _ ≤ 9 * (((Finset.Icc 1 (2 * L)).filter (fun d => d ∣ n)).sum
            (fun d => (d.divisors.card : ℕ)) : ℝ) := by linarith [hstep]

/-- Bound on the value of the form: for `|c₁|, |c₂| ≤ L` and `|a|,|b| ≤ 4L`,
`|a c₁² - b c₂²| ≤ 8L³`. -/
lemma quad_natAbs_le (a b : ℤ) (L : ℕ) (ha : a.natAbs ≤ 4 * L) (hb : b.natAbs ≤ 4 * L)
    {c1 c2 : ℤ} (hc1 : c1 ∈ Finset.Icc (-(L : ℤ)) (L : ℤ))
    (hc2 : c2 ∈ Finset.Icc (-(L : ℤ)) (L : ℤ)) :
    (a * c1 ^ 2 - b * c2 ^ 2).natAbs ≤ 8 * L ^ 3 := by
  rw [Finset.mem_Icc] at hc1 hc2
  have h1 : c1 ^ 2 ≤ (L : ℤ) ^ 2 := by nlinarith [hc1.1, hc1.2]
  have h2 : c2 ^ 2 ≤ (L : ℤ) ^ 2 := by nlinarith [hc2.1, hc2.2]
  have hA : |a| ≤ (4 * L : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast ha
  have hB : |b| ≤ (4 * L : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hb
  have key : |a * c1 ^ 2 - b * c2 ^ 2| ≤ (4 * L : ℤ) * (L : ℤ) ^ 2 + (4 * L : ℤ) * (L : ℤ) ^ 2 := by
    calc |a * c1 ^ 2 - b * c2 ^ 2| ≤ |a * c1 ^ 2| + |b * c2 ^ 2| := by
          have h := abs_add_le (a * c1 ^ 2) (-(b * c2 ^ 2))
          simpa [sub_eq_add_neg] using h
      _ = |a| * c1 ^ 2 + |b| * c2 ^ 2 := by
          simp [abs_mul, abs_of_nonneg (sq_nonneg c1), abs_of_nonneg (sq_nonneg c2)]
      _ ≤ (4 * L : ℤ) * (L : ℤ) ^ 2 + (4 * L : ℤ) * (L : ℤ) ^ 2 := by
          have hc1nn : (0:ℤ) ≤ c1 ^ 2 := sq_nonneg _
          have hc2nn : (0:ℤ) ≤ c2 ^ 2 := sq_nonneg _
          nlinarith [h1, h2, hA, hB, hc1nn, hc2nn]
  have hfin : (4 * L : ℤ) * (L : ℤ) ^ 2 + (4 * L : ℤ) * (L : ℤ) ^ 2 = ((8 * L ^ 3 : ℕ) : ℤ) := by
    push_cast; ring
  apply Int.ofNat_le.mp
  rw [Int.natCast_natAbs, ← hfin]
  exact key

/-- Pointwise divisor-function bound, splitting on the vanishing of the form. -/
lemma key_pointwise (a b : ℤ) (L : ℕ) (ha : a.natAbs ≤ 4 * L) (hb : b.natAbs ≤ 4 * L)
    {c1 c2 : ℤ} (hc1 : c1 ∈ Finset.Icc (-(L : ℤ)) (L : ℤ))
    (hc2 : c2 ∈ Finset.Icc (-(L : ℤ)) (L : ℤ)) :
    (if a * c1 ^ 2 - b * c2 ^ 2 = 0 then 0
      else (((a * c1 ^ 2 - b * c2 ^ 2).natAbs).divisors.card : ℝ))
      ≤ 9 * ∑ d ∈ Finset.Icc 1 (2 * L),
          (if (d : ℤ) ∣ a * c1 ^ 2 - b * c2 ^ 2 then ((d.divisors.card : ℝ)) else 0) := by
  by_cases hQ : a * c1 ^ 2 - b * c2 ^ 2 = 0
  · rw [if_pos hQ]
    have : (0:ℝ) ≤ ∑ d ∈ Finset.Icc 1 (2 * L),
        (if (d : ℤ) ∣ a * c1 ^ 2 - b * c2 ^ 2 then ((d.divisors.card : ℝ)) else 0) := by
      apply Finset.sum_nonneg
      intro d _
      split_ifs with h <;> positivity
    linarith
  · rw [if_neg hQ]
    have hnat : (a * c1 ^ 2 - b * c2 ^ 2).natAbs ≠ 0 := fun h => hQ (Int.natAbs_eq_zero.mp h)
    have hn1 : 1 ≤ (a * c1 ^ 2 - b * c2 ^ 2).natAbs := by omega
    have hnL : (a * c1 ^ 2 - b * c2 ^ 2).natAbs ≤ 8 * L ^ 3 := quad_natAbs_le a b L ha hb hc1 hc2
    refine (tau_le_sum_Icc hn1 hnL).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro d _
    by_cases hd : (d : ℤ) ∣ a * c1 ^ 2 - b * c2 ^ 2
    · rw [if_pos hd, if_pos ((nat_dvd_natAbs_iff d _).mpr hd)]
    · rw [if_neg hd, if_neg (fun h => hd ((nat_dvd_natAbs_iff d _).mp h))]

/-- The double sum is at most `9` times the `d`-sum with the box counts. -/
lemma main_reduction (a b : ℤ) (L : ℕ) (ha : a.natAbs ≤ 4 * L) (hb : b.natAbs ≤ 4 * L) :
    (∑ p ∈ (Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ)),
        (if a * p.1 ^ 2 - b * p.2 ^ 2 = 0 then 0
          else (((a * p.1 ^ 2 - b * p.2 ^ 2).natAbs).divisors.card : ℝ)))
      ≤ 9 * ∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) *
          ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
            (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ) := by
  classical
  set P : Finset (ℤ × ℤ) :=
    (Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ)) with hP
  have h1 : (∑ p ∈ P, (if a * p.1 ^ 2 - b * p.2 ^ 2 = 0 then 0
        else (((a * p.1 ^ 2 - b * p.2 ^ 2).natAbs).divisors.card : ℝ)))
      ≤ 9 * ∑ p ∈ P, ∑ d ∈ Finset.Icc 1 (2 * L),
          (if (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2 then ((d.divisors.card : ℝ)) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [hP, Finset.mem_product] at hp
    exact key_pointwise a b L ha hb hp.1 hp.2
  have heq : (∑ p ∈ P, ∑ d ∈ Finset.Icc 1 (2 * L),
        (if (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2 then ((d.divisors.card : ℝ)) else 0))
      = ∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) *
          ((P.filter (fun p => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc (∑ p ∈ P, (if a * p.1 ^ 2 - b * p.2 ^ 2 = 0 then 0
        else (((a * p.1 ^ 2 - b * p.2 ^ 2).natAbs).divisors.card : ℝ)))
      ≤ 9 * ∑ p ∈ P, ∑ d ∈ Finset.Icc 1 (2 * L),
          (if (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2 then ((d.divisors.card : ℝ)) else 0) := h1
    _ = 9 * ∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) *
          ((P.filter (fun p => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ) := by rw [heq]

/-- Counting + local count: the box count at `d` is at most `d·τ(d)·sP d·(2L/d+2)²`. -/
lemma box_count_le (a b : ℤ) (L : ℕ) (hcop : Nat.Coprime a.natAbs b.natAbs) (d : ℕ)
    (hd : d ∈ Finset.Icc 1 (2 * L)) :
    ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
        (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ)
      ≤ (d : ℝ) * (d.divisors.card : ℝ) * (sP d : ℝ) * (((2 * L / d + 2 : ℕ)) : ℝ) ^ 2 := by
  classical
  rw [Finset.mem_Icc] at hd
  haveI : NeZero d := ⟨by omega⟩
  set B : ℕ := 2 * L / d + 2 with hB
  set N : ℕ := (Finset.univ.filter (fun z : ZMod d × ZMod d =>
      (a : ZMod d) * z.1 ^ 2 = (b : ZMod d) * z.2 ^ 2)).card with hN
  have hloc : (N : ℝ) ≤ (d : ℝ) * (d.divisors.card : ℝ) * (sP d : ℝ) := by
    rw [hN]; simpa [sP] using l51_local_count d a b hcop
  have hcard := card_box_dvd_quad_le L d a b
  rw [← hN, ← hB] at hcard
  have hbound : ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
        (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ)
      ≤ (N : ℝ) * (B : ℝ) ^ 2 := by
    have hh : ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ
          (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
        (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ)
        ≤ ((N * B ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast hcard
    calc ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
          (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ)
        ≤ ((N * B ^ 2 : ℕ) : ℝ) := hh
      _ = (N : ℝ) * (B : ℝ) ^ 2 := by rw [Nat.cast_mul, Nat.cast_pow]
  calc ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
        (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ)
      ≤ (N : ℝ) * (B : ℝ) ^ 2 := hbound
    _ ≤ ((d : ℝ) * (d.divisors.card : ℝ) * (sP d : ℝ)) * (B : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hloc (by positivity)
    _ = (d : ℝ) * (d.divisors.card : ℝ) * (sP d : ℝ) * (B : ℝ) ^ 2 := by ring
    _ = (d : ℝ) * (d.divisors.card : ℝ) * (sP d : ℝ) * (((2 * L / d + 2 : ℕ)) : ℝ) ^ 2 := by
        rw [hB]


/-- Elementary bound: for `1 ≤ d ≤ 2L`,
`d · (⌊2L/d⌋ + 2)² ≤ 16L²/d + 16d`. -/
lemma le_16 (L d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 2 * L) :
    (d : ℝ) * ((((2 * L / d + 2 : ℕ)) : ℝ)) ^ 2 ≤ 16 * (L : ℝ) ^ 2 / (d : ℝ) + 16 * (d : ℝ) := by
  have hdpos : (0:ℝ) < d := by exact_mod_cast hd1
  have hBle : (((2 * L / d + 2 : ℕ)) : ℝ) ≤ 2 * (L : ℝ) / (d : ℝ) + 2 := by
    have h1 : (((2 * L / d : ℕ)) : ℝ) ≤ 2 * (L : ℝ) / (d : ℝ) := by
      have h := Nat.cast_div_le (α := ℝ) (m := 2 * L) (n := d)
      push_cast at h
      exact h
    have h2 : (((2 * L / d + 2 : ℕ)) : ℝ) = (((2 * L / d : ℕ)) : ℝ) + 2 := by push_cast; ring
    rw [h2]; linarith
  have hsq : ((((2 * L / d + 2 : ℕ)) : ℝ)) ^ 2 ≤ (2 * (L : ℝ) / (d : ℝ) + 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hBle 2
  have hdl : (d : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hd2
  have hLnn : (0:ℝ) ≤ L := by positivity
  have hdnn : (0:ℝ) ≤ d := by positivity
  calc (d : ℝ) * ((((2 * L / d + 2 : ℕ)) : ℝ)) ^ 2
      ≤ (d : ℝ) * (2 * (L : ℝ) / (d : ℝ) + 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 4 * (L : ℝ) ^ 2 / (d : ℝ) + 8 * (L : ℝ) + 4 * (d : ℝ) := by
        field_simp
        ring
    _ ≤ 16 * (L : ℝ) ^ 2 / (d : ℝ) + 16 * (d : ℝ) := by
        field_simp
        nlinarith [sq_nonneg ((L : ℝ) - (d : ℝ)), hLnn, hdnn]

/-- Sum-level bound: the `d`-sum of `τ(d) · #{box points divisible by d}` is at most
`80 L² · Σ_d τ(d)² sP d / d`. -/
lemma sum_tau_card_le (a b : ℤ) (L : ℕ) (hcop : Nat.Coprime a.natAbs b.natAbs) :
    (∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) *
        ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
          (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ))
      ≤ 80 * ((L : ℝ)) ^ 2 *
          (∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ) / (d : ℝ)) := by
  have hpt : ∀ d ∈ Finset.Icc 1 (2 * L),
      ((d.divisors.card : ℝ)) *
        ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
          (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ)
      ≤ ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ) * (16 * (L : ℝ) ^ 2 / (d : ℝ) + 16 * (d : ℝ)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    haveI : NeZero d := ⟨by omega⟩
    have hbox := box_count_le a b L hcop d (by rw [Finset.mem_Icc]; exact hd)
    calc ((d.divisors.card : ℝ)) *
          ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
            (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ)
        ≤ ((d.divisors.card : ℝ)) * ((d : ℝ) * (d.divisors.card : ℝ) * (sP d : ℝ)
            * (((2 * L / d + 2 : ℕ)) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hbox (by positivity)
      _ = ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ)
            * ((d : ℝ) * ((((2 * L / d + 2 : ℕ)) : ℝ)) ^ 2) := by ring
      _ ≤ ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ)
            * (16 * (L : ℝ) ^ 2 / (d : ℝ) + 16 * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left (le_16 L d hd.1 hd.2) (by positivity)
  have h1 : (∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) *
        ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
          (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 (2 * L),
          ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ)
            * (16 * (L : ℝ) ^ 2 / (d : ℝ) + 16 * (d : ℝ)) :=
    Finset.sum_le_sum hpt
  set V : ℝ := ∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ) / (d : ℝ)
    with hV
  have h2 : (∑ d ∈ Finset.Icc 1 (2 * L),
          ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ)
            * (16 * (L : ℝ) ^ 2 / (d : ℝ) + 16 * (d : ℝ)))
      ≤ 16 * (L : ℝ) ^ 2 * V + 16 * (4 * (L : ℝ) ^ 2 * V) := by
    have heq : (∑ d ∈ Finset.Icc 1 (2 * L),
          ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ)
            * (16 * (L : ℝ) ^ 2 / (d : ℝ) + 16 * (d : ℝ)))
        = 16 * (L : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 (2 * L),
              ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ) / (d : ℝ))
          + 16 * (∑ d ∈ Finset.Icc 1 (2 * L),
              (d : ℝ) * (((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hdpos : (0:ℝ) < d := by exact_mod_cast hd.1
      field_simp
    have h3 : (∑ d ∈ Finset.Icc 1 (2 * L),
              (d : ℝ) * (((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ))) ≤ 4 * (L : ℝ) ^ 2 * V := by
      have heq2 : (∑ d ∈ Finset.Icc 1 (2 * L),
              (d : ℝ) * (((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ)))
          = ∑ d ∈ Finset.Icc 1 (2 * L), (d : ℝ) ^ 2 *
              (((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ) / (d : ℝ)) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.mem_Icc] at hd
        have hdpos : (0:ℝ) < d := by exact_mod_cast hd.1
        field_simp
      rw [heq2]
      have h4 : (∑ d ∈ Finset.Icc 1 (2 * L), (d : ℝ) ^ 2 *
              (((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ) / (d : ℝ)))
          ≤ (2 * (L : ℝ)) ^ 2 * V := by
        rw [hV, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro d hd
        rw [Finset.mem_Icc] at hd
        have hdle : (d : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast hd.2
        have hnn : (0:ℝ) ≤ ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ) / (d : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hdle 2) hnn
      calc _ ≤ (2 * (L : ℝ)) ^ 2 * V := h4
        _ = 4 * (L : ℝ) ^ 2 * V := by ring
    rw [heq]
    linarith [h3]
  calc (∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) *
        ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
          (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 (2 * L),
          ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ)
            * (16 * (L : ℝ) ^ 2 / (d : ℝ) + 16 * (d : ℝ)) := h1
    _ ≤ 16 * (L : ℝ) ^ 2 * V + 16 * (4 * (L : ℝ) ^ 2 * V) := h2
    _ = 80 * (L : ℝ) ^ 2 * V := by ring
    _ = 80 * ((L : ℝ)) ^ 2 *
          (∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ) / (d : ℝ)) := by
        rw [hV]


/-- **Divisor average on the binary quadratic form `a c₁² - b c₂²`** (the arithmetic input of the
off-diagonal of `FI` Lemma 5.1). For coprime `a, b` with `|a|, |b| ≤ 4L` and `L ≥ 1`, the sum of
`τ(|a c₁² - b c₂²|)` over `|c₁|, |c₂| ≤ L` is at most `C·(L+1)²·(log(2(L+2)))^{510}`, where
`τ(m) = m.divisors.card` and the summand is `0` when the form vanishes.

*Route.* Write `τ(n) = n.divisors.card ≤ 9·∑_{d ∈ Icc 1 (2L), d ∣ n} τ(d)` for `1 ≤ n ≤ 8L³`
(FI Lemma 2.2 with `k = 3`; the value `|a c₁² − b c₂²| ≤ 8L³`). Then
`∑_{c₁,c₂} τ(|Q|) ≤ 9 ∑_{d ≤ 2L} τ(d)·#{(c₁,c₂) ∈ [-L,L]² : d ∣ Q}`. For each `d`,
`#{(c₁,c₂) ∈ [-L,L]² : d ∣ Q} ≤ N(d)·(2L/d+2)²` where `N(d) = #{γ ∈ (ZMod d)² : aγ₁² ≡ bγ₂²}`,
and `N(d) ≤ C·d·τ(d)·sP(d)` for `sP(d) = ∏_{p ∈ d.primeFactors} p^{d.factorization p / 2}`
(the refined local count, integer coefficients: reduce to `a.natAbs`, `b.natAbs` via the
sign bijection `γ₂ ↦ uγ₂` when `-1` is a square, and use the FI §9 local count
`Submission.Work.FIArea1.card_sq_congr_l51`; note `N(d;a,b) ≤ N(d;|a|,|b|) + N(d;|a|,-|b|)`
and each of the two terms is `≤ C d τ(d) sP(d)`). Collecting and using `d(2L/d+2)² ≤ 36L²/d`
for `d ≤ 2L`, the sum is at most `324C·L²·∑_{d ≤ 2L} τ(d)² sP(d)/d`, and
`∑_{d ≤ D} τ(d)² sP(d)/d ≤ C′(log(D+2))^{20}` (the Euler factor `1 + 4/p + O(1/p²)`).
Hence the total is `≪ L²(log(2L+4))^{20} ≤ C(L+1)²(log(2(L+2)))^{510}`. -/
theorem offdiag_tauaverage : ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℤ) (L : ℕ),
    Nat.Coprime a.natAbs b.natAbs → 1 ≤ L → a.natAbs ≤ 4 * L → b.natAbs ≤ 4 * L →
    (∑ c1 ∈ Finset.Icc (-(L : ℤ)) (L : ℤ), ∑ c2 ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
        (if a * c1 ^ 2 - b * c2 ^ 2 = 0 then 0
         else (((a * c1 ^ 2 - b * c2 ^ 2).natAbs).divisors.card : ℝ)))
      ≤ C * (((L : ℝ) + 1) ^ 2) * (Real.log (2 * ((L : ℝ) + 2))) ^ 510 := by
  obtain ⟨Ca, hCapos, hCa⟩ := l51_arith_bound
  refine ⟨720 * Ca, by positivity, ?_⟩
  intro a b L hcop hL ha hb
  have hLr : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hLnn : (0:ℝ) ≤ L := by positivity
  have hlog1 : (1:ℝ) ≤ Real.log (2 * ((L : ℝ) + 2)) := by
    have h6 : Real.exp 1 ≤ 2 * ((L : ℝ) + 2) := by
      nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 * ((L : ℝ) + 2)) := Real.log_le_log (Real.exp_pos 1) h6
  have hlogmono : Real.log (2 * (L : ℝ) + 2) ≤ Real.log (2 * ((L : ℝ) + 2)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogpos : (0:ℝ) ≤ Real.log (2 * (L : ℝ) + 2) := Real.log_nonneg (by linarith)
  set V : ℝ := ∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) ^ 2 * (sP d : ℝ) / (d : ℝ)
    with hV
  have hVb : V ≤ Ca * (Real.log (2 * (L : ℝ) + 2)) ^ (20 : ℕ) := by
    rw [hV]
    have h := hCa (2 * L) (by omega)
    push_cast at h
    exact h
  have hprod : (∑ c1 ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
        ∑ c2 ∈ Finset.Icc (-(L : ℤ)) (L : ℤ),
        (if a * c1 ^ 2 - b * c2 ^ 2 = 0 then 0
         else (((a * c1 ^ 2 - b * c2 ^ 2).natAbs).divisors.card : ℝ)))
      = ∑ p ∈ (Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ)),
          (if a * p.1 ^ 2 - b * p.2 ^ 2 = 0 then 0
           else (((a * p.1 ^ 2 - b * p.2 ^ 2).natAbs).divisors.card : ℝ)) :=
    (Finset.sum_product _ _ (fun p : ℤ × ℤ => (if a * p.1 ^ 2 - b * p.2 ^ 2 = 0 then 0
      else (((a * p.1 ^ 2 - b * p.2 ^ 2).natAbs).divisors.card : ℝ)))).symm
  rw [hprod]
  refine (main_reduction a b L ha hb).trans ?_
  have hsum := sum_tau_card_le a b L hcop
  have hstep2 : 9 * (∑ d ∈ Finset.Icc 1 (2 * L), ((d.divisors.card : ℝ)) *
        ((((Finset.Icc (-(L : ℤ)) (L : ℤ)) ×ˢ (Finset.Icc (-(L : ℤ)) (L : ℤ))).filter
          (fun p : ℤ × ℤ => (d : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card : ℝ))
      ≤ 9 * (80 * (L : ℝ) ^ 2 * V) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [hV]
    exact hsum
  refine hstep2.trans ?_
  have hL2 : (L : ℝ) ^ 2 ≤ ((L : ℝ) + 1) ^ 2 := by nlinarith [hLnn]
  have hlogle : (Real.log (2 * (L : ℝ) + 2)) ^ (20 : ℕ)
      ≤ (Real.log (2 * ((L : ℝ) + 2))) ^ (510 : ℕ) := by
    have h1 : (Real.log (2 * (L : ℝ) + 2)) ^ (20 : ℕ)
        ≤ (Real.log (2 * ((L : ℝ) + 2))) ^ (20 : ℕ) :=
      pow_le_pow_left₀ hlogpos hlogmono 20
    have h2 : (Real.log (2 * ((L : ℝ) + 2))) ^ (20 : ℕ)
        ≤ (Real.log (2 * ((L : ℝ) + 2))) ^ (510 : ℕ) :=
      pow_le_pow_right₀ hlog1 (by norm_num)
    linarith [h1, h2]
  have hVb2 : V ≤ Ca * (Real.log (2 * ((L : ℝ) + 2))) ^ (510 : ℕ) := by
    have h0 : (0:ℝ) < Ca := hCapos
    calc V ≤ Ca * (Real.log (2 * (L : ℝ) + 2)) ^ (20 : ℕ) := hVb
      _ ≤ Ca * (Real.log (2 * ((L : ℝ) + 2))) ^ (510 : ℕ) :=
          mul_le_mul_of_nonneg_left hlogle (le_of_lt hCapos)
  calc 9 * (80 * (L : ℝ) ^ 2 * V)
      = 720 * (L : ℝ) ^ 2 * V := by ring
    _ ≤ 720 * (L : ℝ) ^ 2 * (Ca * (Real.log (2 * ((L : ℝ) + 2))) ^ (510 : ℕ)) :=
        mul_le_mul_of_nonneg_left hVb2 (by positivity)
    _ ≤ 720 * Ca * (((L : ℝ) + 1) ^ 2) * (Real.log (2 * ((L : ℝ) + 2))) ^ 510 := by
        have h720 : (0:ℝ) ≤ 720 * Ca := by positivity
        calc 720 * (L : ℝ) ^ 2 * (Ca * (Real.log (2 * ((L : ℝ) + 2))) ^ (510 : ℕ))
            = 720 * Ca * ((L : ℝ) ^ 2 * (Real.log (2 * ((L : ℝ) + 2))) ^ (510 : ℕ)) := by ring
          _ ≤ 720 * Ca * ((((L : ℝ) + 1) ^ 2) *
                (Real.log (2 * ((L : ℝ) + 2))) ^ 510) := by
              apply mul_le_mul_of_nonneg_left _ h720
              exact mul_le_mul hL2 (le_of_eq rfl) (by positivity) (by positivity)
          _ = 720 * Ca * (((L : ℝ) + 1) ^ 2) * (Real.log (2 * ((L : ℝ) + 2))) ^ 510 := by ring

end

end Work.FIArea1
