import Mathlib
import Submission.Work.FIArea4.Vflip.count_coset_supp

namespace Work.FIArea4.Vflip

open Finset

/-- Arithmetic: `(M/g) * (R/h) ≤ R*M/d` when `g*h = d`, both positive. -/
lemma mul_div_mul_div_le (R M g h d : ℕ) (hg : 0 < g) (hh : 0 < h) (hgh : g * h = d) :
    (M / g) * (R / h) ≤ R * M / d := by
  have hd0 : 0 < d := by rw [← hgh]; exact Nat.mul_pos hg hh
  rw [Nat.le_div_iff_mul_le hd0]
  have h1 : M / g * g ≤ M := Nat.div_mul_le_self M g
  have h2 : R / h * h ≤ R := Nat.div_mul_le_self R h
  calc (M / g) * (R / h) * d = (M / g * g) * (R / h * h) := by rw [← hgh]; ring
    _ ≤ M * R := Nat.mul_le_mul h1 h2
    _ = R * M := by ring

/-- `X ≤ 10 * (Y + X + 1)`. -/
lemma le_ten_mul (X Y : ℕ) : X ≤ 10 * (Y + X + 1) := by nlinarith [Nat.zero_le Y]

/-- `4 * X ≤ 10 * (X + Y + 1)`. -/
lemma four_le_ten_mul (X Y : ℕ) : 4 * X ≤ 10 * (X + Y + 1) := by nlinarith [Nat.zero_le Y]

theorem count_coset_box (lo M R d a : ℕ) (hR : 1 ≤ R) (hM : 1 ≤ M) (hd : 1 ≤ d)
    (hlo : lo ≤ 4 * M) :
    (((Finset.Ioc R (2 * R)).product (Finset.Ioc lo (lo + M))).filter
        (fun p : ℕ × ℕ => p.2 % d = (p.1 * a) % d)).card
      ≤ 10 * (R * M / d + min R M + 1) := by
  have hd0 : 0 < d := by omega
  have hM0 : 0 < M := by omega
  set A : Finset ℕ := Finset.Ioc R (2 * R) with hA
  set B : Finset ℕ := Finset.Ioc lo (lo + M) with hB
  set C : ℕ := ((A.product B).filter (fun p : ℕ × ℕ => p.2 % d = (p.1 * a) % d)).card with hC
  have hcardA : A.card = R := by rw [hA, Nat.card_Ioc]; omega
  have hcardB : B.card = M := by rw [hB, Nat.card_Ioc]; omega
  rcases le_total R M with hRS | hSR
  · -- Case `R ≤ M`: bound each `r`-fibre by `M / d + 1`.
    have hper : C ≤ R * (M / d + 1) := by
      rw [hC, Work.FIArea4.card_filter_product_eq_sum_fst]
      have hb : ∀ r ∈ A, (B.filter (fun s => s % d = (r * a) % d)).card ≤ M / d + 1 := by
        intro r _
        rw [hB]
        exact card_filter_mod_Ioc_le lo M d ((r * a) % d) hd0
      calc ∑ r ∈ A, (B.filter (fun s => s % d = (r * a) % d)).card
          ≤ ∑ _r ∈ A, (M / d + 1) := Finset.sum_le_sum hb
        _ = A.card * (M / d + 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ = R * (M / d + 1) := by rw [hcardA]
    have hmul : R * (M / d) ≤ R * M / d := Nat.mul_div_le_mul_div_assoc R M d
    calc C ≤ R * (M / d + 1) := hper
      _ = R * (M / d) + R := by ring
      _ ≤ R * M / d + R := by omega
      _ ≤ 10 * (R * M / d + R + 1) := by
        simpa using le_ten_mul (R * M / d + R) 0
      _ = 10 * (R * M / d + min R M + 1) := by rw [min_eq_left hRS]
  · -- Case `M ≤ R`: bound each `s`-fibre, splitting on `g = gcd a d`.
    have hmin : min R M = M := min_eq_right hSR
    set g : ℕ := Nat.gcd a d with hg
    set h : ℕ := d / g with hh
    have hgd : g ∣ d := by rw [hg]; exact Nat.gcd_dvd_right a d
    have hgpos : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_right a hd0
    have hhpos : 0 < h := by
      rw [hh]; exact Nat.div_pos (Nat.le_of_dvd hd0 hgd) hgpos
    have hgh : g * h = d := by
      rw [hh, mul_comm]
      rw [hg]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_right a d)
    have hdga : d.gcd a = g := by rw [hg]; exact Nat.gcd_comm d a
    have hmodh : d / d.gcd a = h := by rw [hdga, hh]
    set n : ℕ := (B.filter (fun s => g ∣ s)).card with hn
    -- The `s`-fibre bound.
    have hpers : C ≤ n * (R / h + 1) := by
      rw [hC, Work.FIArea4.card_filter_product_eq_sum_snd]
      have hb : ∀ s ∈ B, (A.filter (fun r => s % d = (r * a) % d)).card ≤
          (if g ∣ s then R / h + 1 else 0) := by
        intro s _
        by_cases hgs : g ∣ s
        · rw [if_pos hgs]
          by_cases hne : (A.filter (fun r => s % d = (r * a) % d)).Nonempty
          · obtain ⟨r0, hr0⟩ := hne
            have hr0' : s % d = (r0 * a) % d := (Finset.mem_filter.mp hr0).2
            have hsub : A.filter (fun r => s % d = (r * a) % d) ⊆
                A.filter (fun r => r % h = r0 % h) := by
              intro r hr
              rw [Finset.mem_filter] at hr ⊢
              refine ⟨hr.1, ?_⟩
              have hr' : s % d = (r * a) % d := hr.2
              have hme : r * a ≡ r0 * a [MOD d] := by
                show (r * a) % d = (r0 * a) % d
                rw [← hr', ← hr0']
              have hcan := Nat.ModEq.cancel_right_div_gcd hd0 hme
              rw [hmodh] at hcan
              exact hcan
            calc (A.filter (fun r => s % d = (r * a) % d)).card
                ≤ (A.filter (fun r => r % h = r0 % h)).card := Finset.card_le_card hsub
              _ ≤ R / h + 1 := by
                  have h2R : 2 * R = R + R := by ring
                  rw [hA, h2R]
                  exact card_filter_mod_Ioc_le R R h (r0 % h) hhpos
          · rw [Finset.not_nonempty_iff_eq_empty] at hne
            rw [hne]; exact Nat.zero_le _
        · rw [if_neg hgs]
          have hempty : A.filter (fun r => s % d = (r * a) % d) = ∅ := by
            rw [← Finset.not_nonempty_iff_eq_empty]
            rintro ⟨r, hr⟩
            rw [Finset.mem_filter] at hr
            have hme : r * a ≡ s [MOD d] := by
              show (r * a) % d = s % d
              rw [← hr.2]
            have hiff := Nat.ModEq.dvd_iff hme hgd
            exact hgs (hiff.mp (dvd_mul_of_dvd_right (by rw [hg]; exact Nat.gcd_dvd_left a d) r))
          rw [hempty]; exact Nat.zero_le _
      calc ∑ s ∈ B, (A.filter (fun r => s % d = (r * a) % d)).card
          ≤ ∑ s ∈ B, (if g ∣ s then R / h + 1 else 0) := Finset.sum_le_sum hb
        _ = n * (R / h + 1) := by
              rw [hn, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    -- Bounds on `n`.
    have hnM : n ≤ M := by
      rw [hn]
      exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (le_of_eq hcardB)
    have hng1 : n ≤ M / g + 1 := by
      have heq : B.filter (fun s => g ∣ s) = B.filter (fun s => s % g = 0) :=
        Finset.filter_congr (fun s _ => Nat.dvd_iff_mod_eq_zero)
      rw [hn, heq, hB]
      exact card_filter_mod_Ioc_le lo M g 0 hgpos
    have hng5 : n ≤ 5 * M / g := by
      rw [hn]
      refine card_multiples_le (5 * M) g hgpos (B.filter (fun s => g ∣ s)) ?_ ?_ ?_
      · intro x hx; exact (Finset.mem_filter.mp hx).2
      · intro x hx
        have hxmem : x ∈ B := (Finset.mem_filter.mp hx).1
        rw [hB] at hxmem
        have := (Finset.mem_Ioc.mp hxmem).1
        omega
      · intro x hx
        have hxmem : x ∈ B := (Finset.mem_filter.mp hx).1
        rw [hB] at hxmem
        have h2 := (Finset.mem_Ioc.mp hxmem).2
        omega
    rcases lt_or_ge (5 * M) g with h5g | hg5
    · -- `g > 5M`: no element of `B` is a multiple of `g`, so `n = 0`.
      have hz : 5 * M / g = 0 := Nat.div_eq_of_lt h5g
      have hn0 : n = 0 := by omega
      calc C ≤ n * (R / h + 1) := hpers
        _ = 0 := by rw [hn0]; ring
        _ ≤ 10 * (R * M / d + min R M + 1) := Nat.zero_le _
    · rcases lt_or_ge M g with hMg | hgM
      · -- `M < g ≤ 5M`: at most one `s` is a multiple of `g`.
        have hz : M / g = 0 := Nat.div_eq_of_lt hMg
        have hn1 : n ≤ 1 := by omega
        have hdle : d ≤ 5 * M * h := by
          calc d = g * h := hgh.symm
            _ ≤ 5 * M * h := Nat.mul_le_mul_right h hg5
        have hstep : R / (5 * h) ≤ R * M / d := by
          have h1 : R * M / (5 * M * h) ≤ R * M / d := Nat.div_le_div_left hdle hd0
          have h2 : R * M / (5 * M * h) = R / (5 * h) := by
            have e : 5 * M * h = M * (5 * h) := by ring
            rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_comm R M, Nat.mul_div_right R hM0]
          rwa [h2] at h1
        have hkey : R / h + 1 ≤ 10 * (R * M / d + M + 1) := by
          have h3 : R / h + 1 ≤ 10 * (R / (5 * h)) + 10 * M + 9 := by
            have h1 : R / h / 5 = R / (5 * h) := by
              rw [Nat.div_div_eq_div_mul, mul_comm]
            rw [← h1]
            have h2 : R / h = 5 * (R / h / 5) + (R / h) % 5 :=
              (Nat.div_add_mod (R / h) 5).symm
            have h4 : (R / h) % 5 < 5 := Nat.mod_lt _ (by norm_num)
            omega
          nlinarith [h3, hstep]
        calc C ≤ n * (R / h + 1) := hpers
          _ ≤ 1 * (R / h + 1) := Nat.mul_le_mul_right _ hn1
          _ = R / h + 1 := by ring
          _ ≤ 10 * (R * M / d + M + 1) := hkey
          _ = 10 * (R * M / d + min R M + 1) := by rw [hmin]
      · -- `g ≤ M`: two crude bounds on the `g`-multiples in `B`.
        have hmg0 : 0 < M / g := Nat.div_pos hgM hgpos
        by_cases hr0 : R / h = 0
        · calc C ≤ n * (R / h + 1) := hpers
            _ = n := by rw [hr0]; ring
            _ ≤ M := hnM
            _ ≤ 10 * (R * M / d + M + 1) := le_ten_mul M (R * M / d)
            _ = 10 * (R * M / d + min R M + 1) := by rw [hmin]
        · have hr1 : 1 ≤ R / h := Nat.one_le_iff_ne_zero.mpr hr0
          have h1 : M / g + 1 ≤ 2 * (M / g) := by omega
          have h2 : R / h + 1 ≤ 2 * (R / h) := by omega
          have h3 : (M / g) * (R / h) ≤ R * M / d :=
            mul_div_mul_div_le R M g h d hgpos hhpos hgh
          calc C ≤ n * (R / h + 1) := hpers
            _ ≤ (M / g + 1) * (R / h + 1) := Nat.mul_le_mul hng1 (le_refl _)
            _ ≤ (2 * (M / g)) * (2 * (R / h)) := Nat.mul_le_mul h1 h2
            _ = 4 * ((M / g) * (R / h)) := by ring
            _ ≤ 4 * (R * M / d) := Nat.mul_le_mul_left 4 h3
            _ ≤ 10 * (R * M / d + M + 1) := four_le_ten_mul (R * M / d) M
            _ = 10 * (R * M / d + min R M + 1) := by rw [hmin]

end Work.FIArea4.Vflip
