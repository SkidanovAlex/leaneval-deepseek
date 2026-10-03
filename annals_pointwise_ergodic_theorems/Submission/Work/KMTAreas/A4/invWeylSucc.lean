/-
# `Work.KMTAreas.A4.invWeylSucc`: the induction step of the inverse Weyl estimate

This module proves the cascade step of the inverse Weyl estimate `IWP`:
given the degree-`d` instance `IWP d C K`, one van der Corput step `VdcStatement` and the two
arithmetic inputs of Green--Tao (`AmplifyStatement`, `DenseExists`), there is a degree-`(d+1)`
instance `IWP (d + 1) C' K'`.

The analytic content (the pigeonhole over the shifts `h ∈ H`, the amplification by the `k`-fold
sumset, the choice of the good denominator, and the extraction of the rational approximation of
`ξ · lc Q`) is discharged by `Work.KMTAreas.A4.invWeylStep` (proved in that module).  What is left
here is the *assembly*:

* the amplitude hypothesis `ε L ≤ ‖∑_{n ∈ [a,b]} c · ph Q ξ n‖` is fed to `VdcStatement` to
  produce the finite set `H` of shifts with the four properties required by `invWeylStep`;
* for each `h ∈ H` the degree-`d` instance `IWP d C K` is applied to the *differenced* polynomial
  `Q - Q(X + h)` (of degree `d`, with unimodular character `c · star c`), at the amplitude
  `ε²/64`, over the overlap window `ovl a b h`;
* the resulting constants `(C₁, K₁)` of `invWeylStep` are enlarged to a pair `(C', K')` which
  dominates `64^{K+1} C` (for the length reduction `ε²/64 ↦ ε`) and `2K + 2` (for the amplitude
  reduction `ε ↦ ε²`), together with `8` and the two members of `(C₁, K₁)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.invWeylStep

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

/-- The cardinality of the interval `[a,b] ⊆ ℤ`, as a real number. -/
theorem card_Icc_Int_cast (a b : ℤ) (h : a ≤ b) :
    ((Finset.Icc a b).card : ℝ) = (((b - a : ℤ) : ℝ) + 1) := by
  have h1 : (Finset.Icc a b).card = (b + 1 - a).toNat := Int.card_Icc a b
  have h2 : (0 : ℤ) ≤ b + 1 - a := by omega
  have h3 : (((b + 1 - a).toNat : ℤ)) = b + 1 - a := Int.toNat_of_nonneg h2
  rw [h1]
  calc (((b + 1 - a).toNat : ℕ) : ℝ) = ((((b + 1 - a).toNat : ℤ)) : ℝ) := by push_cast; ring
    _ = ((b + 1 - a : ℤ) : ℝ) := by rw [h3]
    _ = (((b - a : ℤ) : ℝ) + 1) := by push_cast; ring

theorem invWeylSucc (d : ℕ) (hd : 1 ≤ d) (C K : ℝ) (hC : 0 < C) (hK : 0 < K) (hIW : Work.KMTAreas.A4.IWP d C K) (hVdc : Work.KMTAreas.A4.VdcStatement) (hAmp : Work.KMTAreas.A4.AmplifyStatement) (hDense : Work.KMTAreas.A4.DenseExists) : ∃ C' K' : ℝ, 0 < C' ∧ 0 < K' ∧ Work.KMTAreas.A4.IWP (d + 1) C' K' := by
  obtain ⟨C₁, K₁, hC₁, hK₁, hstep⟩ := invWeylStep d hd C K hC hK hAmp hDense
  set C' : ℝ := max (max C₁ (64 ^ (K + 1) * C)) 8 with hC'def
  set K' : ℝ := max (max K₁ (2 * K + 2)) 2 with hK'def
  have hC'pos : 0 < C' := by
    rw [hC'def]
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 8) (le_max_right _ _)
  have hK'pos : 0 < K' := by
    rw [hK'def]
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (le_max_right _ _)
  have hC₁C' : C₁ ≤ C' := by
    rw [hC'def]
    exact le_trans (le_max_left C₁ (64 ^ (K + 1) * C))
      (le_max_left (max C₁ (64 ^ (K + 1) * C)) 8)
  have hK₁K' : K₁ ≤ K' := by
    rw [hK'def]
    exact le_trans (le_max_left K₁ (2 * K + 2)) (le_max_left (max K₁ (2 * K + 2)) 2)
  have h64C' : 64 ^ (K + 1) * C ≤ C' := by
    rw [hC'def]
    exact le_trans (le_max_right C₁ (64 ^ (K + 1) * C))
      (le_max_left (max C₁ (64 ^ (K + 1) * C)) 8)
  have h8C' : (8 : ℝ) ≤ C' := by
    rw [hC'def]; exact le_max_right _ _
  have h2KK' : 2 * K + 2 ≤ K' := by
    rw [hK'def]
    exact le_trans (le_max_right K₁ (2 * K + 2)) (le_max_left (max K₁ (2 * K + 2)) 2)
  have h2K' : (2 : ℝ) ≤ K' := by
    rw [hK'def]; exact le_max_right _ _
  refine ⟨C', K', hC'pos, hK'pos, ?_⟩
  intro Q ξ c hQ hc a b ε hab hε0 hε1 hlen hampl
  have hL1 : (1 : ℝ) ≤ (((b - a : ℤ) : ℝ) + 1) := by
    have h0 : (0 : ℤ) ≤ b - a := by omega
    have h1 : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast h0
    linarith
  have hLpos : 0 < (((b - a : ℤ) : ℝ) + 1) := lt_of_lt_of_le zero_lt_one hL1
  have hC'nonneg : (0 : ℝ) ≤ C' := le_of_lt hC'pos
  have hrpow2 : (1 : ℝ) ≤ ε ^ (2 - K') := by
    have h := Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (show 2 - K' ≤ 0 by linarith)
    rwa [Real.rpow_zero] at h
  have hkey : ε ^ 2 * (C' * ε ^ (-K')) = C' * ε ^ (2 - K') := by
    have h1 : ε ^ 2 * (C' * ε ^ (-K')) = C' * (ε ^ 2 * ε ^ (-K')) := by ring
    have h2 : ε ^ 2 * ε ^ (-K') = ε ^ (2 - K') := by
      rw [← Real.rpow_natCast ε 2, ← Real.rpow_add hε0]
      ring_nf
    rw [h1, h2]
  have h8 : 8 ≤ ε ^ 2 * (((b - a : ℤ) : ℝ) + 1) := by
    have h1 : ε ^ 2 * (C' * ε ^ (-K')) ≤ ε ^ 2 * (((b - a : ℤ) : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hlen (by positivity)
    have h2 : C' ≤ ε ^ 2 * (C' * ε ^ (-K')) := by
      rw [hkey]
      exact le_mul_of_one_le_right hC'nonneg hrpow2
    linarith
  have hu1 : ∀ n : ℤ, ‖c * ph Q ξ n‖ = 1 := by
    intro n; rw [norm_mul, hc, ph_norm, one_mul]
  obtain ⟨H, hHnz, hHbd, hHlen, hHsum, hHcorr⟩ :=
    hVdc a b (fun n => c * ph Q ξ n) ε hab hε0 hε1 h8 hu1 hampl
  have hhyp : ∀ h ∈ H, ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * (ε ^ 2 / 64) ^ (-K) ∧
      ∃ m : ℤ, |(q : ℝ) * ξ * (((Q - Q.comp (Polynomial.X + Polynomial.C h)).coeff d : ℤ) : ℝ)
          - (m : ℝ)| ≤ C * (ε ^ 2 / 64) ^ (-K) / (((ovl a b h).card : ℝ)) ^ d := by
    intro h hh
    have hne0 : h ≠ 0 := hHnz h hh
    have hcoeff := coeff_comp_add_C_sub Q (d + 1) hQ (by omega) h hne0
    have hdeg : (Q - Q.comp (Polynomial.X + Polynomial.C h)).natDegree = d := by
      have := hcoeff.1
      omega
    have hcstar : ‖c * star c‖ = 1 := by rw [norm_mul, hc, norm_star, hc, one_mul]
    have hcardpos : 0 < ((ovl a b h).card : ℝ) := by
      have hpos : (0 : ℝ) < (ε ^ 2 / 64) * (((b - a : ℤ) : ℝ) + 1) :=
        mul_pos (by positivity) hLpos
      exact lt_of_lt_of_le hpos (hHlen h hh)
    have hAB : max a (a - h) ≤ min b (b - h) := by
      have hne' : (Finset.Icc (max a (a - h)) (min b (b - h))).Nonempty := by
        have h1 : (ovl a b h).Nonempty := Finset.card_pos.mp (by exact_mod_cast hcardpos)
        simpa [ovl] using h1
      exact Finset.nonempty_Icc.mp hne'
    have hcardeq : ((ovl a b h).card : ℝ) =
        (((min b (b - h) - max a (a - h) : ℤ) : ℝ) + 1) := by
      rw [ovl]
      exact card_Icc_Int_cast (max a (a - h)) (min b (b - h)) hAB
    have hlen' : C * (ε ^ 2 / 64) ^ (-K) ≤
        (((min b (b - h) - max a (a - h) : ℤ) : ℝ) + 1) := by
      have h64pow : (64 : ℝ) ^ (K + 1) = 64 ^ K * 64 := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 64), Real.rpow_one]
      have hcoef : C * 64 ^ K ≤ C' / 64 := by
        have hd1 : (64 ^ K * 64 * C) / 64 ≤ C' / 64 := by
          rw [← h64pow]
          exact div_le_div_of_nonneg_right h64C' (by norm_num : (0 : ℝ) ≤ 64)
        have hs : (64 ^ K * 64 * C) / 64 = C * 64 ^ K := by ring
        rwa [hs] at hd1
      have hA : C * (ε ^ 2 / 64) ^ (-K) = (C * 64 ^ K) * ε ^ (-(2 * K)) := by
        rw [div64_rpow_neg hε0 K]
        ring
      have hB : (ε ^ 2 / 64) * (C' * ε ^ (-K')) = (C' / 64) * ε ^ (2 - K') := by
        have h1 : (ε ^ 2 / 64) * (C' * ε ^ (-K')) = (C' / 64) * (ε ^ 2 * ε ^ (-K')) := by
          ring
        have h2 : ε ^ 2 * ε ^ (-K') = ε ^ (2 - K') := by
          rw [← Real.rpow_natCast ε 2, ← Real.rpow_add hε0]
          ring_nf
        rw [h1, h2]
      have hexp : ε ^ (-(2 * K)) ≤ ε ^ (2 - K') := by
        have h1 := rpow_neg_mono hε0 hε1 (show 2 * K ≤ K' - 2 by linarith)
        have h2 : -(K' - 2) = 2 - K' := by ring
        rwa [h2] at h1
      have hLC : C * (ε ^ 2 / 64) ^ (-K) ≤ (ε ^ 2 / 64) * (C' * ε ^ (-K')) := by
        calc C * (ε ^ 2 / 64) ^ (-K) = (C * 64 ^ K) * ε ^ (-(2 * K)) := hA
          _ ≤ (C' / 64) * ε ^ (-(2 * K)) :=
              mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hε0.le _)
          _ ≤ (C' / 64) * ε ^ (2 - K') := mul_le_mul_of_nonneg_left hexp (by positivity)
          _ = (ε ^ 2 / 64) * (C' * ε ^ (-K')) := hB.symm
      have hHlen' : (ε ^ 2 / 64) * (((b - a : ℤ) : ℝ) + 1) ≤
          (((min b (b - h) - max a (a - h) : ℤ) : ℝ) + 1) :=
        le_trans (hHlen h hh) hcardeq.le
      calc C * (ε ^ 2 / 64) ^ (-K) ≤ (ε ^ 2 / 64) * (C' * ε ^ (-K')) := hLC
        _ ≤ (ε ^ 2 / 64) * (((b - a : ℤ) : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hlen (by positivity)
        _ ≤ (((min b (b - h) - max a (a - h) : ℤ) : ℝ) + 1) := hHlen'
    have hamp : (ε ^ 2 / 64) * (((min b (b - h) - max a (a - h) : ℤ) : ℝ) + 1) ≤
        ‖∑ n ∈ ovl a b h, (c * star c)
            * ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n‖ := by
      rw [← hcardeq]
      have hcorr : (∑ n ∈ ovl a b h, (c * ph Q ξ n) * star (c * ph Q ξ (n + h)))
          = ∑ n ∈ ovl a b h, (c * star c)
              * ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n := by
        apply Finset.sum_congr rfl
        intro n _
        have h2 : ph Q ξ n * star (ph Q ξ (n + h))
            = ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n :=
          ph_mul_conj_ph Q ξ n h
        calc (c * ph Q ξ n) * star (c * ph Q ξ (n + h))
            = (c * star c) * (ph Q ξ n * star (ph Q ξ (n + h))) := by
              rw [star_mul]
              ring
          _ = (c * star c) * ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n := by
              rw [h2]
      rw [← hcorr]
      exact hHcorr h hh
    obtain ⟨q, hq1, hqC, m, hm⟩ :=
      hIW (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ (c * star c) hdeg hcstar
        (max a (a - h)) (min b (b - h)) (ε ^ 2 / 64) hAB (by positivity)
        (by nlinarith [hε0, hε1, sq_nonneg ε]) hlen' hamp
    refine ⟨q, hq1, hqC, m, ?_⟩
    rw [hcardeq]
    exact hm
  obtain ⟨q, hq1, hqC, m, hm⟩ :=
    hstep Q hQ ξ a b ε H hab hε0 hε1 hHnz hHbd hHlen hHsum hhyp
  have hnum : C₁ * ε ^ (-K₁) ≤ C' * ε ^ (-K') :=
    mul_le_mul hC₁C' (rpow_neg_mono hε0 hε1 hK₁K') (Real.rpow_nonneg hε0.le _) hC'nonneg
  refine ⟨q, hq1, ?_, m, ?_⟩
  · exact le_trans hqC hnum
  · refine le_trans hm ?_
    exact div_le_div_of_nonneg_right hnum (pow_nonneg hLpos.le (d + 1))

end Work.KMTAreas.A4
