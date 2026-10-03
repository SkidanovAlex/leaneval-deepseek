import Mathlib
import Submission.Work.FIArea4.flat_defs
import Submission.Work.FIArea4.Vflip.count_coset_supp

namespace Work.FIArea4.Vflip

open Finset

/-!
# The support count of the flat part over `Ioc R (2R)`

`Work.FIArea4.suppCount S R d a` counts the pairs `(r,s)` with `r ∈ (R, 2R]`, `s ∈ suppBox S` and
`s ≡ r·a (mod d)`.  The box `suppBox S = (S/2-1, 5S/2]` has at most `2S+1` elements, and the pairs
are counted in the two ways standard for such congruence counts:

* for each `r` the integer `s ∈ suppBox S` is determined modulo `d`, giving
  `# ≤ R·(⌊(2S+1)/d⌋ + 1) ≤ 2RS/d + 2R`;
* for each `s` (with `g = (a,d) ∣ s`) the integer `r ∈ (R,2R]` is determined modulo `d/g`, so
  `# ≤ ⌊(5S/2)/g⌋·(⌊R/(d/g)⌋ + 1) ≤ 5RS/(2d) + 5S/2`.

In the range `R ≤ S` the first bound is `≤ 40(RS/d + min(R,S) + 1)`, and in the range `S ≤ R` the
second is; taking the appropriate one in each range gives the claim.
-/

/-- The cast of an integer division is at least the real division minus one. -/
lemma count_supp_Ioc_cast_div_ge (m d : ℕ) (hd : 0 < d) :
    (m : ℝ) / (d : ℝ) - 1 ≤ ((m / d : ℕ) : ℝ) := by
  have h : m < d * (m / d + 1) := by
    have h1 : m = d * (m / d) + m % d := (Nat.div_add_mod m d).symm
    have h2 : m % d < d := Nat.mod_lt m hd
    nlinarith
  have hcast : (m : ℝ) < (d : ℝ) * (((m / d : ℕ) : ℝ) + 1) := by
    have h' : (m : ℝ) < ((d * (m / d + 1) : ℕ) : ℝ) := by exact_mod_cast h
    simpa using h'
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h3 : (m : ℝ) / (d : ℝ) < ((m / d : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hdR]
    linarith
  linarith

/-- At most `(2*S+1)/d + 1` elements of `suppBox S` lie in a fixed residue class modulo `d`. -/
lemma count_supp_Ioc_card_suppBox_filter_mod_le (S d c : ℕ) (hd : 0 < d) :
    ((Work.FIArea4.suppBox S).filter (fun s => s % d = c)).card ≤ (2 * S + 1) / d + 1 := by
  have h5 : 5 * S / 2 = S / 2 + 2 * S := by
    have h : 5 * S = S + 2 * (2 * S) := by ring
    rw [h, Nat.add_mul_div_left S (2 * S) (by norm_num : 0 < 2)]
  have hsub : (Work.FIArea4.suppBox S).filter (fun s => s % d = c)
      ⊆ (Finset.Ioc (S / 2 - 1) ((S / 2 - 1) + (2 * S + 1))).filter
          (fun s => s % d = c) := by
    intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨hs1, hs2⟩ := hs
    rw [Work.FIArea4.suppBox, Finset.mem_Ioc] at hs1
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hs1.1, by omega⟩, hs2⟩
  exact le_trans (Finset.card_le_card hsub)
    (card_filter_mod_Ioc_le (S / 2 - 1) (2 * S + 1) d c hd)

/-- The `r`-count of the support count: for each `r ∈ (R,2R]` the integer `s ∈ suppBox S` of the
class is determined modulo `d`. -/
lemma count_supp_Ioc_le_R (S R d a : ℕ) (hd : 0 < d) :
    Work.FIArea4.suppCount S R d a ≤ R * ((2 * S + 1) / d + 1) := by
  rw [Work.FIArea4.suppCount]
  rw [Work.FIArea4.card_filter_product_eq_sum_fst]
  calc ∑ r ∈ Finset.Ioc R (2 * R), ((Work.FIArea4.suppBox S).filter
        (fun s => s % d = (r * a) % d)).card
      ≤ ∑ _r ∈ Finset.Ioc R (2 * R), ((2 * S + 1) / d + 1) :=
        Finset.sum_le_sum
          (fun r _ => count_supp_Ioc_card_suppBox_filter_mod_le S d ((r * a) % d) hd)
    _ = (Finset.Ioc R (2 * R)).card * ((2 * S + 1) / d + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = R * ((2 * S + 1) / d + 1) := by
        rw [Nat.card_Ioc]
        congr 1
        omega

/-- The `s`-count of the support count: writing `g = (a,d)`, every `s` of the class is a multiple
of `g`, and for such an `s` the integer `r ∈ (R,2R]` of the class is determined modulo `d/g`. -/
lemma count_supp_Ioc_le_S (S R d a : ℕ) (hd : 0 < d) :
    Work.FIArea4.suppCount S R d a
      ≤ ((5 * S / 2) / Nat.gcd a d) * (R / (d / Nat.gcd a d) + 1) := by
  have hg : 0 < Nat.gcd a d := Nat.gcd_pos_of_pos_right a hd
  have hgd : Nat.gcd a d ∣ d := Nat.gcd_dvd_right a d
  have hhpos : 0 < d / Nat.gcd a d := Nat.div_pos (Nat.le_of_dvd hd hgd) hg
  rw [Work.FIArea4.suppCount]
  rw [Work.FIArea4.card_filter_product_eq_sum_snd]
  have hb : ∀ s ∈ Work.FIArea4.suppBox S,
      ((Finset.Ioc R (2 * R)).filter (fun r => s % d = (r * a) % d)).card
        ≤ (if Nat.gcd a d ∣ s then R / (d / Nat.gcd a d) + 1 else 0) := by
    intro s _
    by_cases hgs : Nat.gcd a d ∣ s
    · rw [if_pos hgs]
      by_cases hne : ((Finset.Ioc R (2 * R)).filter
          (fun r => s % d = (r * a) % d)).Nonempty
      · obtain ⟨r0, hr0⟩ := hne
        have hr0' : s % d = (r0 * a) % d := (Finset.mem_filter.mp hr0).2
        have hsub : (Finset.Ioc R (2 * R)).filter (fun r => s % d = (r * a) % d)
            ⊆ (Finset.Ioc R (2 * R)).filter
                (fun r => r % (d / Nat.gcd a d) = r0 % (d / Nat.gcd a d)) := by
          intro r hr
          rw [Finset.mem_filter] at hr ⊢
          refine ⟨hr.1, ?_⟩
          have hme : r * a ≡ r0 * a [MOD d] := by
            show (r * a) % d = (r0 * a) % d
            rw [← hr.2, ← hr0']
          have hcan := Nat.ModEq.cancel_right_div_gcd hd hme
          have hge : d.gcd a = Nat.gcd a d := Nat.gcd_comm d a
          rw [hge] at hcan
          exact hcan
        calc ((Finset.Ioc R (2 * R)).filter (fun r => s % d = (r * a) % d)).card
            ≤ ((Finset.Ioc R (2 * R)).filter
                (fun r => r % (d / Nat.gcd a d) = r0 % (d / Nat.gcd a d))).card :=
              Finset.card_le_card hsub
          _ ≤ R / (d / Nat.gcd a d) + 1 := by
              have h2R : 2 * R = R + R := by ring
              rw [h2R]
              exact card_filter_mod_Ioc_le R R (d / Nat.gcd a d)
                (r0 % (d / Nat.gcd a d)) hhpos
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne]
        exact Nat.zero_le _
    · rw [if_neg hgs]
      have hempty : (Finset.Ioc R (2 * R)).filter (fun r => s % d = (r * a) % d) = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨r, hr⟩
        rw [Finset.mem_filter] at hr
        have hme : r * a ≡ s [MOD d] := by
          show (r * a) % d = s % d
          rw [hr.2]
        have hiff := Nat.ModEq.dvd_iff hme hgd
        exact hgs (hiff.mp (dvd_mul_of_dvd_right (Nat.gcd_dvd_left a d) r))
      rw [hempty]
      exact Nat.zero_le _
  calc ∑ s ∈ Work.FIArea4.suppBox S,
        ((Finset.Ioc R (2 * R)).filter (fun r => s % d = (r * a) % d)).card
      ≤ ∑ s ∈ Work.FIArea4.suppBox S,
          (if Nat.gcd a d ∣ s then R / (d / Nat.gcd a d) + 1 else 0) :=
        Finset.sum_le_sum hb
    _ = ((Work.FIArea4.suppBox S).filter (fun s => Nat.gcd a d ∣ s)).card
          * (R / (d / Nat.gcd a d) + 1) := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    _ ≤ ((5 * S / 2) / Nat.gcd a d) * (R / (d / Nat.gcd a d) + 1) := by
        refine Nat.mul_le_mul_right _ (card_multiples_le (5 * S / 2) (Nat.gcd a d) hg _ ?_ ?_ ?_)
        · intro x hx
          exact (Finset.mem_filter.mp hx).2
        · intro x hx
          have hxmem : x ∈ Work.FIArea4.suppBox S := (Finset.mem_filter.mp hx).1
          rw [Work.FIArea4.suppBox, Finset.mem_Ioc] at hxmem
          omega
        · intro x hx
          have hxmem : x ∈ Work.FIArea4.suppBox S := (Finset.mem_filter.mp hx).1
          rw [Work.FIArea4.suppBox, Finset.mem_Ioc] at hxmem
          exact hxmem.2

theorem count_supp_Ioc (S R d a : ℕ) (hR : 1 ≤ R) (hS : 1 ≤ S) (hd : 1 ≤ d) :
    Work.FIArea4.suppCount S R d a ≤ 40 * (((R * S) / d : ℕ) + min R S + 1) := by
  have hd0 : 0 < d := by omega
  set q : ℕ := R * S / d with hq
  set x : ℝ := (R : ℝ) * (S : ℝ) / (d : ℝ) with hx
  have hqle : x - 1 ≤ (q : ℝ) := by
    have h := count_supp_Ioc_cast_div_ge (R * S) d hd0
    rw [hx]
    simpa [Nat.cast_mul] using h
  have hqnn : (0 : ℝ) ≤ x := by rw [hx]; positivity
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hS0 : (0 : ℝ) ≤ (S : ℝ) := by positivity
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  rcases le_total R S with hRS | hSR
  · rw [min_eq_left hRS]
    have h1 : (Work.FIArea4.suppCount S R d a : ℝ) ≤ 2 * x + 2 * (R : ℝ) := by
      have hnat := count_supp_Ioc_le_R S R d a hd0
      have hdiv : (((2 * S + 1) / d : ℕ) : ℝ) ≤ 2 * (S : ℝ) / (d : ℝ) + 1 := by
        have h1 := Nat.cast_div_le (α := ℝ) (m := 2 * S + 1) (n := d)
        have h2 : ((2 * S + 1 : ℕ) : ℝ) = 2 * (S : ℝ) + 1 := by push_cast; ring
        have h3 : (1 : ℝ) / (d : ℝ) ≤ 1 := by
          rw [div_le_one hdR]
          exact_mod_cast hd
        have h4 : ((2 * S + 1 : ℕ) : ℝ) / (d : ℝ)
            = 2 * (S : ℝ) / (d : ℝ) + 1 / (d : ℝ) := by
          rw [h2]; ring
        rw [h4] at h1
        linarith
      calc (Work.FIArea4.suppCount S R d a : ℝ)
          ≤ ((R * ((2 * S + 1) / d + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = (R : ℝ) * ((((2 * S + 1) / d : ℕ) : ℝ) + 1) := by push_cast; ring
        _ ≤ (R : ℝ) * (2 * (S : ℝ) / (d : ℝ) + 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith
        _ = 2 * x + 2 * (R : ℝ) := by rw [hx]; ring
    have hmain : (Work.FIArea4.suppCount S R d a : ℝ)
        ≤ ((40 * (q + R + 1) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hmain
  · rw [min_eq_right hSR]
    have hg : 0 < Nat.gcd a d := Nat.gcd_pos_of_pos_right a hd0
    have hgd : Nat.gcd a d ∣ d := Nat.gcd_dvd_right a d
    have hgR : (0 : ℝ) < (Nat.gcd a d : ℝ) := by exact_mod_cast hg
    have hg1 : (1 : ℝ) ≤ (Nat.gcd a d : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hg)
    have hAn : (((5 * S / 2) / Nat.gcd a d : ℕ) : ℝ)
        ≤ 5 * (S : ℝ) / (2 * (Nat.gcd a d : ℝ)) := by
      have h1 : (((5 * S / 2) / Nat.gcd a d : ℕ) : ℝ)
          ≤ (((5 * S / 2 : ℕ)) : ℝ) / (Nat.gcd a d : ℝ) := Nat.cast_div_le
      have h2 : (((5 * S / 2 : ℕ)) : ℝ) ≤ 5 * (S : ℝ) / 2 := by
        have h3 := Nat.cast_div_le (α := ℝ) (m := 5 * S) (n := 2)
        have h4 : ((5 * S : ℕ) : ℝ) = 5 * (S : ℝ) := by push_cast; ring
        rw [h4] at h3
        exact h3
      have h3 : ((((5 * S / 2 : ℕ)) : ℝ) / (Nat.gcd a d : ℝ))
          ≤ (5 * (S : ℝ) / 2) / (Nat.gcd a d : ℝ) :=
        div_le_div_of_nonneg_right h2 (le_of_lt hgR)
      have h4 : (5 * (S : ℝ) / 2) / (Nat.gcd a d : ℝ)
          = 5 * (S : ℝ) / (2 * (Nat.gcd a d : ℝ)) := by ring
      linarith
    have hBR : (((R / (d / Nat.gcd a d) : ℕ) : ℝ) + 1)
        ≤ (R : ℝ) * (Nat.gcd a d : ℝ) / (d : ℝ) + 1 := by
      have h1 : (((R / (d / Nat.gcd a d) : ℕ)) : ℝ)
          ≤ (R : ℝ) / (((d / Nat.gcd a d : ℕ)) : ℝ) := Nat.cast_div_le
      have h2 : (((d / Nat.gcd a d : ℕ)) : ℝ) = (d : ℝ) / (Nat.gcd a d : ℝ) :=
        Nat.cast_div hgd (Nat.cast_ne_zero.mpr hg.ne')
      rw [h2] at h1
      have h3 : (R : ℝ) / ((d : ℝ) / (Nat.gcd a d : ℝ))
          = (R : ℝ) * (Nat.gcd a d : ℝ) / (d : ℝ) := by
        rw [div_div_eq_mul_div]
      rw [h3] at h1
      linarith
    have h2 : (Work.FIArea4.suppCount S R d a : ℝ) ≤ 5 * x / 2 + 5 * (S : ℝ) / 2 := by
      have hnat := count_supp_Ioc_le_S S R d a hd0
      have hA : (Work.FIArea4.suppCount S R d a : ℝ)
          ≤ ((((5 * S / 2) / Nat.gcd a d) * (R / (d / Nat.gcd a d) + 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      refine le_trans hA ?_
      have hcast : ((((5 * S / 2) / Nat.gcd a d) * (R / (d / Nat.gcd a d) + 1) : ℕ) : ℝ)
          = (((5 * S / 2) / Nat.gcd a d : ℕ) : ℝ)
              * (((R / (d / Nat.gcd a d) : ℕ) : ℝ) + 1) := by push_cast; ring
      rw [hcast]
      have hstep : (((5 * S / 2) / Nat.gcd a d : ℕ) : ℝ)
            * (((R / (d / Nat.gcd a d) : ℕ) : ℝ) + 1)
          ≤ (5 * (S : ℝ) / (2 * (Nat.gcd a d : ℝ)))
              * ((R : ℝ) * (Nat.gcd a d : ℝ) / (d : ℝ) + 1) :=
        mul_le_mul hAn hBR (by positivity) (by positivity)
      have hfin : (5 * (S : ℝ) / (2 * (Nat.gcd a d : ℝ)))
            * ((R : ℝ) * (Nat.gcd a d : ℝ) / (d : ℝ) + 1)
          ≤ 5 * x / 2 + 5 * (S : ℝ) / 2 := by
        have heq : (5 * (S : ℝ) / (2 * (Nat.gcd a d : ℝ)))
              * ((R : ℝ) * (Nat.gcd a d : ℝ) / (d : ℝ) + 1)
            = 5 * ((R : ℝ) * (S : ℝ) / (d : ℝ)) / 2
                + 5 * (S : ℝ) / (2 * (Nat.gcd a d : ℝ)) := by
          field_simp
        rw [heq, hx]
        have hle : 5 * (S : ℝ) / (2 * (Nat.gcd a d : ℝ)) ≤ 5 * (S : ℝ) / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [hg1, hS0]
        linarith
      linarith
    have hmain : (Work.FIArea4.suppCount S R d a : ℝ)
        ≤ ((40 * (q + S + 1) : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hmain

end Work.FIArea4.Vflip
