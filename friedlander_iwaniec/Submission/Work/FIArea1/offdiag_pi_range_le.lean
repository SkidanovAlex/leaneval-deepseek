import Mathlib
import Submission.Work.FIArea1.conjunct2_defs
import Submission.Work.FIArea1.L51Defs
import Submission.Work.FIArea1.offdiag_count_l51
import Submission.Work.FIArea1.gauss_prime_dvd_card_le
import Submission.Work.FIArea1.QboxDefs
import Submission.Work.FIArea1.PiRangeReduce
import Submission.Work.FIArea1.pi_range_helpers
import Submission.Work.FIArea1.offdiag_count_Qbim
import Submission.Work.FIArea1.offdiag_count_Qre_cross
import Submission.Work.FIArea1.pi_dvd_card_log_le
import Submission.Work.FIArea1.pi_w_group_le
import Submission.Work.FIArea1.Yset_pair_le
import Submission.Work.FIArea1.pi_range_arith

set_option maxHeartbeats 4000000

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem offdiag_pi_range_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℝ) (M N : ℝ),
      1 ≤ q → 2 ≤ N → N ≤ M →
      (∑ π ∈ (Work.FIPlan.gBox (Work.FIArea1.KZ N)).filter
            (fun π => Prime π ∧ q < (Work.FIPlan.gnorm π : ℝ)
              ∧ (Work.FIPlan.gnorm π : ℝ) ≤ 2 * q),
        ∑ w ∈ (Work.FIPlan.gBox (Work.FIArea1.KR M)).erase 0,
        ∑ z1 ∈ Work.FIArea1.Zbox N, ∑ z2 ∈ Work.FIArea1.Zbox N,
          (if Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2) then 0
           else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ)))
      ≤ C * (M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
          * (Real.log (M * N + 2)) ^ (516 : ℕ) := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FIArea1.offdiag_count_Qbim
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FIArea1.offdiag_count_Qre_cross
  obtain ⟨C3, hC3pos, hC3⟩ := Work.FIArea1.pi_dvd_card_log_le
  obtain ⟨C4, hC4pos, hC4⟩ := Work.FIArea1.pi_range_arith
  refine ⟨(C1 + 4 * C2) * 3 * C3 * C4 + 1, by positivity, ?_⟩
  intro q M N hq hN hNM
  have hconst_pos : (0 : ℝ) < (C1 + 4 * C2) * 3 * C3 * C4 + 1 := by
    have h4 : (0 : ℝ) ≤ (C1 + 4 * C2) * 3 * C3 * C4 := by
      refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (by norm_num)) hC3pos.le) hC4pos.le
      linarith [hC1pos, hC2pos]
    linarith
  by_cases hbig : 8 * N + 2 ≤ q
  · have hempty : (Work.FIPlan.gBox (Work.FIArea1.KZ N)).filter
        (fun π => Prime π ∧ q < (Work.FIPlan.gnorm π : ℝ)
          ∧ (Work.FIPlan.gnorm π : ℝ) ≤ 2 * q) = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨π, hπ⟩
      obtain ⟨hmem, -, hlt, -⟩ := Finset.mem_filter.mp hπ
      have hgn : ((Work.FIPlan.gnorm π : ℕ) : ℝ)
          ≤ 2 * ((Work.FIArea1.KZ N).natAbs : ℝ) ^ 2 := by
        have h := Work.FIArea2.gnorm_le_of_mem_gBox (Work.FIArea1.KZ_nonneg N) hmem
        exact_mod_cast h
      have hKZ : ((Work.FIArea1.KZ N).natAbs : ℝ) ≤ Real.sqrt (2 * N) + 1 := by
        rw [Work.FIArea1.KZ, Int.natAbs_natCast]
        exact (Nat.ceil_lt_add_one (Real.sqrt_nonneg (2 * N))).le
      have hsN : Real.sqrt (2 * N) ≤ N := by
        have hNN : 2 * N ≤ N ^ 2 := by
          have h3 : (0 : ℝ) ≤ N * (N - 2) := mul_nonneg (by linarith) (by linarith)
          nlinarith
        conv_rhs => rw [show N = Real.sqrt (N ^ 2) from (Real.sqrt_sq (by linarith)).symm]
        exact Real.sqrt_le_sqrt hNN
      have hKZ0 : (0 : ℝ) ≤ ((Work.FIArea1.KZ N).natAbs : ℝ) := by positivity
      have hs0 : (0 : ℝ) ≤ Real.sqrt (2 * N) := Real.sqrt_nonneg _
      have hsq2 : Real.sqrt (2 * N) ^ 2 = 2 * N := Real.sq_sqrt (by linarith)
      have hstep : ((Work.FIArea1.KZ N).natAbs : ℝ) ^ 2 ≤ (Real.sqrt (2 * N) + 1) ^ 2 :=
        pow_le_pow_left₀ hKZ0 hKZ 2
      have hle8 : ((Work.FIPlan.gnorm π : ℕ) : ℝ) ≤ 8 * N + 2 := by
        nlinarith [hgn, hstep, hsN, hs0, hsq2, hKZ0]
      exact absurd hle8 (by linarith)
    rw [hempty]
    simp only [Finset.sum_empty]
    have h1 : (0 : ℝ) ≤ M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q :=
      div_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (by linarith) _)) (by linarith)
    have h2 : (0 : ℝ) ≤ (Real.log (M * N + 2)) ^ (516 : ℕ) :=
      pow_nonneg (Real.log_nonneg (by nlinarith)) _
    exact mul_nonneg (mul_nonneg hconst_pos.le h1) h2
  · push_neg at hbig
    have hqpos : 0 < q := by linarith
    have hMpos : (0 : ℝ) < M := by linarith
    have hNpos : (0 : ℝ) < N := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log (M * N + 2) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
      nlinarith
    set X : ℝ := max (N / q) 2 with hXdef
    have hX2 : 2 ≤ X := le_max_right _ _
    have hX1 : 1 ≤ X := by linarith
    have hXR : 2 * Real.sqrt X ≤ ((Work.FIArea1.KR (16 * M * q) : ℤ) : ℝ) := by
      rw [hXdef]
      exact two_sqrt_max_le_KR_cast M N q hq hN hNM
    have hRge1 : (1 : ℤ) ≤ Work.FIArea1.KR (16 * M * q) :=
      one_le_KR M q (by linarith) hq
    set Wbox : Finset GaussianInt := (Work.FIPlan.gBox (Work.FIArea1.KR M)).erase 0 with hWbox
    set Rbox : Finset GaussianInt := (Work.FIPlan.gBox (Work.FIArea1.KR (16 * M * q))).erase 0
      with hRbox
    set Nabs : ℝ := ((Work.FIArea1.KR (16 * M * q)).natAbs : ℝ) with hNabs
    set Pw : ℝ := X ^ ((3 : ℝ) / 2) with hPw
    set Lg : ℝ := (Real.log (2 * (((Work.FIArea1.KR (16 * M * q)).natAbs : ℝ) + X + 2)))
      ^ (514 : ℕ) with hLg
    set KK : ℝ := 3 * C3 * Real.log (M * N + 2) with hKK
    set A : GaussianInt → ℝ := fun W =>
      ∑ y ∈ Work.FIArea1.Qbim X, (Work.FIPlan.Zint (Work.FIPlan.cForm W y) : ℝ) with hAdef
    set B : GaussianInt → ℝ := fun W =>
      (Work.FIPlan.Zint W.re : ℝ) + (Work.FIPlan.Zint (-W.re) : ℝ) with hBdef
    set G : GaussianInt → ℝ := fun W => ∑ y1 ∈ Work.FIArea1.Qbim X,
      ∑ y2 ∈ Work.FIArea1.Qbim X,
        (if Work.FIPlan.Delta y1 y2 = 0 then 0
         else (Work.FIPlan.Zint (Work.FIPlan.cForm W y1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm W y2) : ℝ)) with hGdef
    set PP : GaussianInt → GaussianInt → GaussianInt → ℝ := fun W y1 y2 =>
      (if Work.FIPlan.Delta y1 y2 = 0 then 0
       else (Work.FIPlan.Zint (Work.FIPlan.cForm W y1) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm W y2) : ℝ)) with hPP
    have hPw0 : (0 : ℝ) ≤ Pw := by
      rw [hPw]; exact Real.rpow_nonneg (by rw [hXdef]; positivity) _
    have hNabs0 : (0 : ℝ) ≤ Nabs := by rw [hNabs]; positivity
    have hLg1 : (1 : ℝ) ≤ Lg := by
      rw [hLg]
      have h4 : (1 : ℝ) ≤ ((Work.FIArea1.KR (16 * M * q)).natAbs : ℝ) := by
        have h := one_le_KR M q (by linarith) hq
        have h1 : (1 : ℤ) ≤ (Work.FIArea1.KR (16 * M * q)).natAbs := by
          rw [← Int.natAbs_of_nonneg (Work.FIArea1.KR_nonneg _)]
          exact h
        exact_mod_cast h1
      have h5 : (1 : ℝ) ≤ Real.log (2 * (((Work.FIArea1.KR (16 * M * q)).natAbs : ℝ) + X + 2)) := by
        rw [Real.le_log_iff_exp_le (by positivity)]
        have h3 : Real.exp 1 < 3 := Real.exp_one_lt_three
        nlinarith
      calc (1 : ℝ) = 1 ^ (514 : ℕ) := by norm_num
        _ ≤ _ := pow_le_pow_left₀ (by norm_num) h5 514
    have hK0 : (0 : ℝ) ≤ KK := by
      rw [hKK]
      have := hlog1
      positivity
    have hred := Work.FIArea1.pi_range_reduce (q := q) (M := M) (N := N) hqpos
    have hpad : (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox,
          ∑ y1 ∈ Work.FIArea1.Yset (N / q), ∑ y2 ∈ Work.FIArea1.Yset (N / q),
            PP (w * π) y1 y2)
        ≤ (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox,
            ∑ y1 ∈ Work.FIArea1.Yset X, ∑ y2 ∈ Work.FIArea1.Yset X, PP (w * π) y1 y2) := by
      refine Finset.sum_le_sum (fun π _ => Finset.sum_le_sum (fun w _ => ?_))
      calc (∑ y1 ∈ Work.FIArea1.Yset (N / q), ∑ y2 ∈ Work.FIArea1.Yset (N / q),
              PP (w * π) y1 y2)
          ≤ (∑ y1 ∈ Work.FIArea1.Yset (N / q), ∑ y2 ∈ Work.FIArea1.Yset X,
              PP (w * π) y1 y2) := by
            apply Finset.sum_le_sum
            intro y1 _
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Work.FIArea1.Yset_mono (le_max_left (N / q) 2)) (fun b _ _ => by
                change (0 : ℝ) ≤ (if Work.FIPlan.Delta y1 b = 0 then 0
                  else (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) y1) : ℝ)
                       * (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) b) : ℝ))
                split_ifs <;> positivity)
        _ ≤ (∑ y1 ∈ Work.FIArea1.Yset X, ∑ y2 ∈ Work.FIArea1.Yset X,
              PP (w * π) y1 y2) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (Work.FIArea1.Yset_mono (le_max_left (N / q) 2)) ?_
            intro a ha _
            refine Finset.sum_nonneg (fun b _ => ?_)
            change (0 : ℝ) ≤ (if Work.FIPlan.Delta a b = 0 then 0
              else (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) a) : ℝ)
                   * (Work.FIPlan.Zint (Work.FIPlan.cForm (w * π) b) : ℝ))
            split_ifs <;> positivity
    have hsplit : (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox,
          ∑ y1 ∈ Work.FIArea1.Yset X, ∑ y2 ∈ Work.FIArea1.Yset X, PP (w * π) y1 y2)
        ≤ (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox,
            (G (w * π) + 2 * (B (w * π) * A (w * π)))) := by
      refine Finset.sum_le_sum (fun π _ => Finset.sum_le_sum (fun w _ => ?_))
      exact Work.FIArea1.Yset_pair_le X (w * π)
    have hsep : (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox,
          (G (w * π) + 2 * (B (w * π) * A (w * π))))
        = (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox, G (w * π))
          + 2 * (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox,
              B (w * π) * A (w * π)) := by
      have h1 : ∀ π : GaussianInt,
          (∑ w ∈ Wbox, (G (w * π) + 2 * (B (w * π) * A (w * π))))
            = (∑ w ∈ Wbox, G (w * π)) + 2 * (∑ w ∈ Wbox, B (w * π) * A (w * π)) := by
        intro π
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [h1]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hcard : ∀ W ∈ Rbox, ((Work.FIArea1.PiDvd q N W).card : ℝ) ≤ KK := by
      intro W hW
      rw [hRbox] at hW
      obtain ⟨hWne, hWmem⟩ := Finset.mem_erase.mp hW
      have hgnW : (Work.FIPlan.gnorm W : ℝ) ≤ 64 * (4 * M) * q := by
        have h := piRange_gnorm_le_of_mem_gBox_KR M q (by linarith) hq hWmem
        linarith
      have hc := hC3 q (4 * M) N W hq hN (by linarith) (by linarith) hWne hgnW
      rw [hKK]
      have hlog4 : Real.log (4 * M * N + 2) ≤ Real.log (4 * (M * N + 2)) := by
        apply Real.log_le_log (by nlinarith [hMpos, hNpos])
        nlinarith
      have hmul' : Real.log (4 * (M * N + 2)) = Real.log 4 + Real.log (M * N + 2) :=
        Real.log_mul (by norm_num) (by intro h; nlinarith [hMpos, hNpos])
      rw [hmul'] at hlog4
      have hlog4' : Real.log 4 ≤ 2 * Real.log (M * N + 2) := by
        have h14 : Real.log 4 ≤ 2 := by
          have h2 : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
            norm_num
          have h3 : Real.log 2 < 0.7 := by linarith [Real.log_two_lt_d9]
          rw [h2]
          linarith
        linarith
      have hcd : C3 * Real.log (4 * M * N + 2) ≤ 3 * C3 * Real.log (M * N + 2) :=
        by nlinarith [hC3pos.le, hlog4, hlog4']
      exact hc.trans hcd
    have hGnonneg : ∀ W ∈ Rbox, 0 ≤ G W := by
      intro W _
      rw [hGdef]
      refine Finset.sum_nonneg (fun y1 _ => Finset.sum_nonneg (fun y2 _ => ?_))
      split_ifs <;> positivity
    have hGbound : (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox, G (w * π))
        ≤ KK * (C1 * (Nabs * Pw) * Lg) := by
      have hgrp := Work.FIArea1.pi_w_group_le q M N KK G hq hN hNM hK0 hcard hGnonneg
      have hswap : (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox, G (π * w))
          = (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox, G (w * π)) := by
        apply Finset.sum_congr rfl
        intro π _
        apply Finset.sum_congr rfl
        intro w _
        rw [mul_comm π w]
      rw [hswap] at hgrp
      have hb := hC1 (Work.FIArea1.KR (16 * M * q)) X hRge1 hX2 hXR
      rw [← hNabs, ← hPw, ← hLg] at hb
      exact hgrp.trans (mul_le_mul_of_nonneg_left hb hK0)
    have hBAnonneg : ∀ W ∈ Rbox, 0 ≤ B W * A W := by
      intro W _
      apply mul_nonneg
      · rw [hBdef]; positivity
      · rw [hAdef]; positivity
    have hnegA : ∀ W : GaussianInt, A (-W) = A W := fun W => Qbim_A_neg X W
    have hBAinner : (∑ W ∈ Rbox, B W * A W) ≤ 2 * (C2 * (Nabs * Pw)) := by
      have h1 : (∑ W ∈ Rbox, (Work.FIPlan.Zint W.re : ℝ) * A W) ≤ C2 * (Nabs * Pw) := by
        have h := hC2 (Work.FIArea1.KR (16 * M * q)) X hRge1 hX1
        rwa [← hNabs, ← hPw] at h
      have himg : Rbox.image (fun z => -z) = Rbox := by
        rw [hRbox]; exact erase_gBox_neg_image _
      have hinj : Set.InjOn (fun z : GaussianInt => -z) ↑Rbox :=
        fun a _ b _ h => neg_injective h
      have h2 : (∑ W ∈ Rbox, (Work.FIPlan.Zint (-W.re) : ℝ) * A W)
          = ∑ W ∈ Rbox, (Work.FIPlan.Zint W.re : ℝ) * A W := by
        calc (∑ W ∈ Rbox, (Work.FIPlan.Zint (-W.re) : ℝ) * A W)
            = ∑ W ∈ Rbox.image (fun z => -z), (Work.FIPlan.Zint (-W.re) : ℝ) * A W := by
              rw [himg]
          _ = ∑ W ∈ Rbox, (Work.FIPlan.Zint (-(-W).re) : ℝ) * A (-W) :=
              Finset.sum_image (s := Rbox) (g := fun z : GaussianInt => -z)
                (f := fun W => (Work.FIPlan.Zint (-W.re) : ℝ) * A W) hinj
          _ = ∑ W ∈ Rbox, (Work.FIPlan.Zint W.re : ℝ) * A W := by
              apply Finset.sum_congr rfl
              intro W _
              rw [neg_re, neg_neg, hnegA W]
      have h3 : (∑ W ∈ Rbox, B W * A W)
          = (∑ W ∈ Rbox, (Work.FIPlan.Zint W.re : ℝ) * A W)
            + (∑ W ∈ Rbox, (Work.FIPlan.Zint (-W.re) : ℝ) * A W) := by
        rw [hBdef]
        simp only [add_mul]
        rw [Finset.sum_add_distrib]
      rw [h3, h2]
      linarith
    have hBAbound : (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox, B (w * π) * A (w * π))
        ≤ KK * (2 * (C2 * (Nabs * Pw))) := by
      have hgrp := Work.FIArea1.pi_w_group_le q M N KK (fun W => B W * A W)
        hq hN hNM hK0 hcard hBAnonneg
      have hswap : (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox, B (π * w) * A (π * w))
          = (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox, B (w * π) * A (w * π)) := by
        apply Finset.sum_congr rfl
        intro π _
        apply Finset.sum_congr rfl
        intro w _
        rw [mul_comm π w]
      rw [hswap] at hgrp
      exact hgrp.trans (mul_le_mul_of_nonneg_left hBAinner hK0)
    have hstepA : KK * (C1 * (Nabs * Pw) * Lg) + 2 * (KK * (2 * (C2 * (Nabs * Pw))))
        ≤ ((C1 + 4 * C2) * 3 * C3) * (Nabs * Pw * Lg * Real.log (M * N + 2)) := by
      have hkey : C1 * Lg + 4 * C2 ≤ (C1 + 4 * C2) * Lg := by
        nlinarith [hLg1, hC1pos.le, hC2pos.le]
      have hfac : (0 : ℝ) ≤ 3 * C3 * Real.log (M * N + 2) * Nabs * Pw := by
        refine mul_nonneg (mul_nonneg ?_ hNabs0) hPw0
        rw [hKK] at hK0
        exact hK0
      have h1 : 3 * C3 * Real.log (M * N + 2) * Nabs * Pw * (C1 * Lg + 4 * C2)
          ≤ 3 * C3 * Real.log (M * N + 2) * Nabs * Pw * ((C1 + 4 * C2) * Lg) :=
        mul_le_mul_of_nonneg_left hkey hfac
      calc KK * (C1 * (Nabs * Pw) * Lg) + 2 * (KK * (2 * (C2 * (Nabs * Pw))))
          = 3 * C3 * Real.log (M * N + 2) * Nabs * Pw * (C1 * Lg + 4 * C2) := by
            rw [hKK]; ring
        _ ≤ 3 * C3 * Real.log (M * N + 2) * Nabs * Pw * ((C1 + 4 * C2) * Lg) := h1
        _ = ((C1 + 4 * C2) * 3 * C3) * (Nabs * Pw * Lg * Real.log (M * N + 2)) := by ring
    have hstepB : ((C1 + 4 * C2) * 3 * C3) * (Nabs * Pw * Lg * Real.log (M * N + 2))
        ≤ ((C1 + 4 * C2) * 3 * C3)
          * (C4 * (M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
              * (Real.log (M * N + 2)) ^ (516 : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hNabs, hPw, hLg, hXdef]
      exact hC4 q M N hq hN hNM (by linarith)
    have hstepC : ((C1 + 4 * C2) * 3 * C3)
          * (C4 * (M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
              * (Real.log (M * N + 2)) ^ (516 : ℕ))
        ≤ ((C1 + 4 * C2) * 3 * C3 * C4 + 1)
          * (M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
          * (Real.log (M * N + 2)) ^ (516 : ℕ) := by
      have h1 : (0 : ℝ) ≤ M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q :=
        div_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
          (Real.rpow_nonneg (by linarith) _)) (by linarith)
      have h2 : (0 : ℝ) ≤ (Real.log (M * N + 2)) ^ (516 : ℕ) :=
        pow_nonneg (Real.log_nonneg (by nlinarith)) _
      have hle : ((C1 + 4 * C2) * 3 * C3) * C4 ≤ (C1 + 4 * C2) * 3 * C3 * C4 + 1 := by linarith
      calc ((C1 + 4 * C2) * 3 * C3)
            * (C4 * (M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
                * (Real.log (M * N + 2)) ^ (516 : ℕ))
          = (((C1 + 4 * C2) * 3 * C3) * C4)
            * ((M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
                * (Real.log (M * N + 2)) ^ (516 : ℕ)) := by ring
        _ ≤ (((C1 + 4 * C2) * 3 * C3 * C4) + 1)
            * ((M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
                * (Real.log (M * N + 2)) ^ (516 : ℕ)) :=
            mul_le_mul_of_nonneg_right hle (mul_nonneg h1 h2)
        _ = ((C1 + 4 * C2) * 3 * C3 * C4 + 1)
            * (M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
            * (Real.log (M * N + 2)) ^ (516 : ℕ) := by ring
    calc (∑ π ∈ (Work.FIPlan.gBox (Work.FIArea1.KZ N)).filter
            (fun π => Prime π ∧ q < (Work.FIPlan.gnorm π : ℝ)
              ∧ (Work.FIPlan.gnorm π : ℝ) ≤ 2 * q),
        ∑ w ∈ (Work.FIPlan.gBox (Work.FIArea1.KR M)).erase 0,
        ∑ z1 ∈ Work.FIArea1.Zbox N, ∑ z2 ∈ Work.FIArea1.Zbox N,
          (if Work.FIPlan.Delta z1 z2 = 0 ∨ ¬ (π ∣ z1 ∧ π ∣ z2) then 0
           else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ)))
        ≤ (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox,
            ∑ y1 ∈ Work.FIArea1.Yset (N / q), ∑ y2 ∈ Work.FIArea1.Yset (N / q),
              PP (w * π) y1 y2) := hred
      _ ≤ (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox,
            ∑ y1 ∈ Work.FIArea1.Yset X, ∑ y2 ∈ Work.FIArea1.Yset X,
              PP (w * π) y1 y2) := hpad
      _ ≤ (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox,
            (G (w * π) + 2 * (B (w * π) * A (w * π)))) := hsplit
      _ = (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox, G (w * π))
          + 2 * (∑ π ∈ Work.FIArea1.PiSet q N, ∑ w ∈ Wbox,
              B (w * π) * A (w * π)) := hsep
      _ ≤ KK * (C1 * (Nabs * Pw) * Lg) + 2 * (KK * (2 * (C2 * (Nabs * Pw)))) :=
          add_le_add hGbound (by linarith [hBAbound])
      _ ≤ ((C1 + 4 * C2) * 3 * C3) * (Nabs * Pw * Lg * Real.log (M * N + 2)) := hstepA
      _ ≤ ((C1 + 4 * C2) * 3 * C3)
          * (C4 * (M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
              * (Real.log (M * N + 2)) ^ (516 : ℕ)) := hstepB
      _ ≤ ((C1 + 4 * C2) * 3 * C3 * C4 + 1)
          * (M ^ ((1 : ℝ) / 2) * N ^ ((3 : ℝ) / 2) / q)
          * (Real.log (M * N + 2)) ^ (516 : ℕ) := hstepC

end

end Work.FIArea1
