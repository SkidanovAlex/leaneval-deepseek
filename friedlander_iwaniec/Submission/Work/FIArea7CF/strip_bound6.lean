/-
# `Submission.Work.FIArea7.strip_bound6` — the elementary bound for the small-moduli strip

`Work.FIArea7.Area7Strip6` is the second of the two inputs of
`Work.FIArea7.area7_6_of_uniform_of_strip` (see `Submission/Work/FIArea7/UniCut6.lean`): the
paper's `W` cut minus the uniform cut is the *small-moduli strip* `Strip6`, and the strip is
elementary.  This file proves it.

The pairs `(z₁,z₂)` of the strip satisfy `|Δ(z₁,z₂)| ≤ 4X²`, each such pair carries at most `X`
moduli `d ≤ X`, and the mass of `β` is bounded by `Work.FIArea6.strip_vsq_polar`; the pair count
is `Work.FIArea7.card_pairs_gBox_absDelta_lt` (with its constant `40` made explicit below as
`card_pairs_strip_le`).  The three delegated lemmas are
`Work.FIArea7.pair_sum_le_card_sqrt` (the two-level Cauchy–Schwarz),
`Work.FIArea7.stripLogFac_le` (the size of the (7.10) logarithm on the box) and
`Work.FIArea7.strip_numeric` (the closing numerical inequality).

`Work.FIArea6.PolarCoeff` (and hence `Work.FIArea6.vsq_polar`) is *not* imported: at the time of
writing it did not compile, because the round-6.1 insertion of `IsAxisFree` into
`Work.FITop4.IsBetaCoeff6` invalidated its `toIsPolarCoeff`.  `Submission.Work.FIArea7.StripMass`
is the self-contained renamed copy of that module (see its header).
-/
import Mathlib
import Submission.Work.FIArea7.UniCut6
import Submission.Work.FIArea7CF.card_pairs_gBox_absDelta_lt
import Submission.Work.FIArea7.StripMass
import Submission.Work.FIArea7.pair_sum_le_card_sqrt
import Submission.Work.FIArea7.strip_numeric
import Submission.Work.FIArea7.stripLogFac_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## dev placeholders for the delegated lemmas -/


/-! ## 0. The inner `d`-sum of the strip -/

/-- `|jacobiSym a b| ≤ 1`. -/
private lemma abs_jacobiSym_le_one' (a : ℤ) (b : ℕ) : |jacobiSym a b| ≤ 1 := by
  by_cases hb : b = 0
  · subst hb; rw [jacobiSym.zero_right]; norm_num
  · by_cases h : jacobiSym a b = 0
    · rw [h]; norm_num
    · have hg : a.gcd (b : ℤ) = 1 := by
        by_contra hg
        exact h ((jacobiSym.eq_zero_iff).mpr ⟨hb, hg⟩)
      rcases jacobiSym.eq_one_or_neg_one hg with h1 | h1 <;> rw [h1] <;> norm_num

/-- **The strip's inner sum is `≤ X·L` on the pairs that can contribute, and `0` otherwise.**  Each
summand is bounded by `|logFac6| ≤ L`, only the moduli `d ≤ X` survive the cut, and there are at
most `X` such `d`; if `|Δ| > 4X²` the cut is empty for every `d`. -/
private theorem stripInner_aux (X : ℕ) (z1 z2 : GaussianInt) {L : ℝ} (hL : 0 ≤ L)
    (hlog : |Work.FITop4.logFac6 z1 z2| ≤ L) :
    ‖((∑ d ∈ Work.FITop4.Sset z1 z2, ((Nat.totient d : ℝ) / (d : ℝ))
          * (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)‖
      ≤ (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2 then (X : ℝ) * L else 0) := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hM : Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2
  · rw [if_pos hM]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hb : ∀ d ∈ Work.FITop4.Sset z1 z2,
        |((Nat.totient d : ℝ) / (d : ℝ))
          * (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2|
        ≤ L * (if d ≤ X then (1 : ℝ) else 0) := by
      intro d hd
      by_cases hdX : d ≤ X
      · rw [if_pos hdX, mul_one]
        have hmem : d ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1) :=
          (Finset.mem_filter.mp hd).1
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hmem).1
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
        have htot1 : ((Nat.totient d : ℝ) / (d : ℝ)) ≤ 1 := by
          rw [div_le_one hd0]
          exact_mod_cast Nat.totient_le d
        have htot0 : (0 : ℝ) ≤ (Nat.totient d : ℝ) / (d : ℝ) := by positivity
        have h1 : |(Nat.totient d : ℝ) / (d : ℝ)| ≤ 1 := by
          rw [abs_of_nonneg htot0]; exact htot1
        have h2 : |(if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)|
            ≤ 1 := by split_ifs <;> norm_num
        have h3 : |(Work.FITop4.ratioSym z1 z2 d : ℝ)| ≤ 1 := by
          have h := abs_jacobiSym_le_one'
            ((((star z1 * z2).re : ZMod d)
              * ((((Work.FIPlan.gnorm z1 : ℕ)) : ZMod d))⁻¹).val : ℤ) d
          rw [← Int.cast_abs]
          exact_mod_cast h
        have h4 : |Work.FITop4.logFac6 z1 z2| ≤ L := hlog
        rw [abs_mul, abs_mul, abs_mul]
        have s1 : |(Nat.totient d : ℝ) / (d : ℝ)|
            * |(if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)|
            ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
        have s2 : |(Nat.totient d : ℝ) / (d : ℝ)|
              * |(if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)|
              * |(Work.FITop4.ratioSym z1 z2 d : ℝ)| ≤ 1 * 1 * 1 :=
          mul_le_mul s1 h3 (abs_nonneg _) (by norm_num)
        exact le_trans (mul_le_mul s2 h4 (abs_nonneg _) (by norm_num)) (le_of_eq (by ring))
      · rw [if_neg hdX, if_neg (by rintro ⟨h, _⟩; exact hdX h)]
        simp
    refine le_trans (Finset.sum_le_sum hb) ?_
    have hcard1 : (∑ d ∈ Work.FITop4.Sset z1 z2, (if d ≤ X then (1 : ℝ) else 0))
        = ∑ d ∈ (Work.FITop4.Sset z1 z2).filter (fun d => d ≤ X), (1 : ℝ) := by
      rw [← Finset.sum_filter]
    have hcard2 : (∑ d ∈ (Work.FITop4.Sset z1 z2).filter (fun d => d ≤ X), (1 : ℝ))
        = ((((Work.FITop4.Sset z1 z2).filter (fun d => d ≤ X)).card : ℕ) : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcle : (((((Work.FITop4.Sset z1 z2).filter (fun d => d ≤ X)).card : ℕ)) : ℝ)
        ≤ (X : ℝ) := by
      have hsub : ((Work.FITop4.Sset z1 z2).filter (fun d => d ≤ X)) ⊆ Finset.Icc 1 X := by
        intro d hd
        rw [Finset.mem_filter] at hd
        exact Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd.1).1).1, hd.2⟩
      have h1 : ((Work.FITop4.Sset z1 z2).filter (fun d => d ≤ X)).card ≤ X := by
        refine le_trans (Finset.card_le_card hsub) ?_
        rw [Nat.card_Icc]
        omega
      exact_mod_cast h1
    calc (∑ d ∈ Work.FITop4.Sset z1 z2, L * (if d ≤ X then (1 : ℝ) else 0))
        = L * ∑ d ∈ Work.FITop4.Sset z1 z2, (if d ≤ X then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
      _ = L * (((((Work.FITop4.Sset z1 z2).filter (fun d => d ≤ X)).card : ℕ)) : ℝ) := by
          rw [hcard1, hcard2]
      _ ≤ L * X := mul_le_mul_of_nonneg_left hcle hL
      _ = (X : ℝ) * L := by ring
  · rw [if_neg hM]
    have hzero : ∀ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ))
          * (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
          * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 = 0 := by
      intro d _
      have hM' : 4 * X ^ 2 < Work.FIPlan.absDelta z1 z2 := not_le.mp hM
      rw [if_neg (by
        rintro ⟨hdX, hle⟩
        have h1 : 4 * d * X ≤ 4 * X ^ 2 := by nlinarith [hdX]
        omega)]
      ring
    rw [Finset.sum_eq_zero hzero, abs_zero]

/-! ## 1. The near-diagonal pair count with an explicit constant -/

private theorem card_pairs_strip_le : ∀ (R : ℤ) (M : ℕ),
    ((((Work.FIPlan.gBox R) ×ˢ (Work.FIPlan.gBox R)).filter
        (fun p => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
      ≤ 40 * ((M : ℝ) + 1) * (((2 * R + 1).toNat : ℝ) ^ 2)
        + 40 * (((2 * R + 1).toNat : ℝ) ^ 3) := by
  intro R M
  rcases lt_or_ge R 0 with hneg | hR
  · have hIcc : Finset.Icc (-R) R = (∅ : Finset ℤ) := by
      rw [Finset.Icc_eq_empty_iff]
      omega
    have hempty : Work.FIPlan.gBox R = ∅ := by
      rw [Work.FIPlan.gBox, hIcc]; simp
    have hN0 : (2 * R + 1).toNat = 0 := Int.toNat_of_nonpos (by omega)
    rw [hempty, hN0]
    simp
  · set n : ℕ := R.toNat with hn
    set N : ℝ := ((2 * R + 1).toNat : ℝ) with hNdef
    have hRn : ((n : ℕ) : ℤ) = R := Int.toNat_of_nonneg hR
    have hNR : (2 * R + 1).toNat = 2 * n + 1 := by
      have h : 2 * R + 1 = (((2 * n + 1 : ℕ)) : ℤ) := by rw [← hRn]; omega
      rw [h, Int.toNat_natCast]
    have hNval : N = (((2 * n + 1 : ℕ)) : ℝ) := by rw [hNdef, hNR]
    have hNnn : (0 : ℝ) ≤ N := by rw [hNval]; positivity
    have hNR2 : (((2 * R + 1).toNat : ℕ) : ℝ) = N := hNdef.symm
    -- decomposition of the pair count as a sum over `z₂`
    have hdecompN : ((Work.FIPlan.gBox R ×ˢ Work.FIPlan.gBox R).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 < M)).card
        = ∑ z2 ∈ Work.FIPlan.gBox R,
            ((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card := by
      rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun z2 _ => ?_)
      rw [Finset.card_filter]
    have hdecomp : (((Work.FIPlan.gBox R ×ˢ Work.FIPlan.gBox R).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
        = ∑ z2 ∈ Work.FIPlan.gBox R,
            (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ) := by
      rw [hdecompN, Nat.cast_sum]
    -- split off the `z₂ = 0` fibre
    have h0mem : (0 : GaussianInt) ∈ Work.FIPlan.gBox R := by
      rw [mem_gBox_iff_gRadius hR]
      simp [gRadius]
    have hsplit : ∑ z2 ∈ Work.FIPlan.gBox R,
            (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
        = (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card : ℝ)
          + ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
              (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ) := by
      have hs := Finset.sum_erase_add (Work.FIPlan.gBox R)
        (fun z2 => (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ))
        h0mem
      rw [add_comm] at hs
      exact hs.symm
    -- the `z₂ = 0` fibre costs at most `N²`
    have hC0 : (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card : ℝ)
        ≤ N ^ 2 := by
      have hcf : ((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card
          ≤ (Work.FIPlan.gBox R).card := Finset.card_filter_le _ _
      have h2 : ((Work.FIPlan.gBox R).card : ℝ) = N ^ 2 := by
        rw [card_gBox_eq, hNdef]
        push_cast
        ring
      calc (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 0 < M)).card : ℝ)
          ≤ ((Work.FIPlan.gBox R).card : ℝ) := by exact_mod_cast hcf
        _ = N ^ 2 := h2
    -- every nonzero `z₂` contributes at most `N·(2M/‖z₂‖ + 1)`
    have hCne : ∀ z2 ∈ (Work.FIPlan.gBox R).erase 0,
        (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
          ≤ N * (2 * (M : ℝ) / (gRadius z2 : ℝ) + 1) := by
      intro z2 hz2
      rw [Finset.mem_erase] at hz2
      have h := card_z1_absDelta_le R M z2 hz2.1
      have step : (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
          ≤ (((2 * R + 1).toNat * (2 * M / gRadius z2 + 1) : ℕ) : ℝ) := by exact_mod_cast h
      refine step.trans ?_
      push_cast
      rw [hNR2]
      apply mul_le_mul_of_nonneg_left _ hNnn
      have hdiv : (((2 * M / gRadius z2 : ℕ)) : ℝ) ≤ 2 * (M : ℝ) / (gRadius z2 : ℝ) := by
        have h0 := natCast_div_le (2 * M) (gRadius z2)
        simpa using h0
      linarith
    -- the harmonic sum and the cardinality of the punctured box
    have hsumS : ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0, (1 : ℝ) / (gRadius z2 : ℝ)
        ≤ 8 * (n : ℝ) := by
      rw [show Work.FIPlan.gBox R = Work.FIPlan.gBox ((n : ℤ)) from by rw [← hRn]]
      exact sum_gRadius_inv_le n
    have herasecard : (((Work.FIPlan.gBox R).erase 0).card : ℝ) ≤ N ^ 2 := by
      have h1 : ((Work.FIPlan.gBox R).erase 0).card ≤ (Work.FIPlan.gBox R).card :=
        Finset.card_le_card (Finset.erase_subset _ _)
      calc (((Work.FIPlan.gBox R).erase 0).card : ℝ) ≤ ((Work.FIPlan.gBox R).card : ℝ) := by
            exact_mod_cast h1
        _ = N ^ 2 := by rw [card_gBox_eq, hNdef]; push_cast; ring
    have hSbound : ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
            (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
        ≤ N * (2 * (M : ℝ) * (8 * (n : ℝ)) + N ^ 2) := by
      have h1 : ∀ z2 ∈ (Work.FIPlan.gBox R).erase 0,
          (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
            ≤ N * (2 * (M : ℝ) * (1 / (gRadius z2 : ℝ)) + 1) := by
        intro z2 hz2
        refine (hCne z2 hz2).trans (le_of_eq ?_)
        ring
      calc ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
              (((Work.FIPlan.gBox R).filter (fun z1 => Work.FIPlan.absDelta z1 z2 < M)).card : ℝ)
          ≤ ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
              N * (2 * (M : ℝ) * (1 / (gRadius z2 : ℝ)) + 1) := Finset.sum_le_sum h1
        _ = N * (2 * (M : ℝ) * (∑ z2 ∈ (Work.FIPlan.gBox R).erase 0, 1 / (gRadius z2 : ℝ))
              + (((Work.FIPlan.gBox R).erase 0).card : ℝ)) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
              nsmul_eq_mul, mul_one]
        _ ≤ N * (2 * (M : ℝ) * (8 * (n : ℝ)) + N ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hNnn
            have hSnn : (0 : ℝ) ≤ ∑ z2 ∈ (Work.FIPlan.gBox R).erase 0,
                1 / (gRadius z2 : ℝ) := by positivity
            nlinarith [hsumS, herasecard, hSnn, show (0 : ℝ) ≤ (M : ℝ) by positivity,
              show (0 : ℝ) ≤ (n : ℝ) by positivity]
    -- assemble
    have hfinal : ((((Work.FIPlan.gBox R) ×ˢ (Work.FIPlan.gBox R)).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
        ≤ N ^ 2 + N * (2 * (M : ℝ) * (8 * (n : ℝ)) + N ^ 2) := by
      rw [hdecomp, hsplit]
      linarith [hC0, hSbound]
    have hnle : (n : ℝ) ≤ N := by
      rw [hNval]
      push_cast
      linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
    have hN1 : (1 : ℝ) ≤ N := by
      rw [hNval]
      push_cast
      linarith [show (0:ℝ) ≤ (n:ℝ) by positivity]
    calc ((((Work.FIPlan.gBox R) ×ˢ Work.FIPlan.gBox R).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 < M)).card : ℝ)
        ≤ N ^ 2 + N * (2 * (M : ℝ) * (8 * (n : ℝ)) + N ^ 2) := hfinal
      _ = N ^ 2 + 16 * (M : ℝ) * (n : ℝ) * N + N ^ 3 := by ring
      _ ≤ 40 * ((M : ℝ) + 1) * N ^ 2 + 40 * N ^ 3 := by
          have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
          have key : 16 * (M : ℝ) * (n : ℝ) * N ≤ 16 * (M : ℝ) * N ^ 2 := by
            have hb : (0 : ℝ) ≤ 16 * (M : ℝ) * N := by positivity
            calc 16 * (M : ℝ) * (n : ℝ) * N = (16 * (M : ℝ) * N) * (n : ℝ) := by ring
              _ ≤ (16 * (M : ℝ) * N) * N := mul_le_mul_of_nonneg_left hnle hb
              _ = 16 * (M : ℝ) * N ^ 2 := by ring
          nlinarith [key, hN1, hM0, sq_nonneg N, mul_nonneg hM0 (sq_nonneg N)]
/-! ## 2. The Chebyshev radius of the inner box -/

private lemma radN_toNat_le (Pa : Work.FITop.Params) (hN1 : (1 : ℝ) ≤ Pa.N) :
    (((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ) ≤ 7 * Real.sqrt Pa.N := by
  have hRt : (Work.FITop.radN Pa).toNat = ⌈Real.sqrt (4 * Pa.N)⌉₊ := by
    rw [Work.FITop.radN, Int.toNat_natCast]
  have htoNat : (2 * Work.FITop.radN Pa + 1).toNat = 2 * ⌈Real.sqrt (4 * Pa.N)⌉₊ + 1 := by
    have hcast : 2 * Work.FITop.radN Pa + 1 = ↑(2 * ⌈Real.sqrt (4 * Pa.N)⌉₊ + 1 : ℕ) := by
      rw [Work.FITop.radN]
      push_cast
      ring
    rw [hcast, Int.toNat_natCast]
  rw [htoNat]
  have hceil : ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) < Real.sqrt (4 * Pa.N) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hs4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs1 : (1 : ℝ) ≤ Real.sqrt Pa.N := by rw [Real.one_le_sqrt]; exact hN1
  push_cast
  rw [hs4] at hceil ⊢
  linarith

/-! ## 3. The pair count at the strip's condition -/

private lemma strip_pair_count (Pa : Work.FITop.Params) (X : ℕ)
    (hX1 : (1 : ℝ) ≤ (X : ℝ)) (hN1 : (1 : ℝ) ≤ Pa.N) (hX9 : (X : ℝ) ^ 9 ≤ Pa.N) :
    ((((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
        (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
        (fun p => Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2)).card : ℝ)
      ≤ 25480 * Pa.N * Real.sqrt Pa.N := by
  have hset : ((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
        (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
        (fun p => Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2)
      = ((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
        (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
        (fun p => Work.FIPlan.absDelta p.1 p.2 < 4 * X ^ 2 + 1) := by
    ext p
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
  rw [hset]
  have hcount := card_pairs_strip_le (Work.FITop.radN Pa) (4 * X ^ 2 + 1)
  have hM : (((4 * X ^ 2 + 1 : ℕ)) : ℝ) + 1 = 4 * (X : ℝ) ^ 2 + 2 := by push_cast; ring
  rw [hM] at hcount
  let x : ℝ := (((2 * Work.FITop.radN Pa + 1).toNat : ℕ) : ℝ)
  have hxnn : 0 ≤ x := by dsimp only [x]; positivity
  have hxle : x ≤ 7 * Real.sqrt Pa.N := by dsimp only [x]; exact radN_toNat_le Pa hN1
  have hsN0 : (0 : ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hsNsq : (Real.sqrt Pa.N) ^ 2 = Pa.N := Real.sq_sqrt (by linarith)
  have hX2 : (X : ℝ) ^ 2 ≤ Real.sqrt Pa.N := by
    have hX4 : (X : ℝ) ^ 4 ≤ Pa.N :=
      le_trans (pow_le_pow_right₀ hX1 (by norm_num : 4 ≤ 9)) hX9
    have hsq : ((X : ℝ) ^ 2) ^ 2 ≤ Pa.N := by
      rw [show ((X : ℝ) ^ 2) ^ 2 = (X : ℝ) ^ 4 by ring]
      exact hX4
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity)] at h
  have hxsq : x ^ 2 ≤ 49 * Pa.N := by
    calc x ^ 2 ≤ (7 * Real.sqrt Pa.N) ^ 2 := pow_le_pow_left₀ hxnn hxle 2
      _ = 49 * Pa.N := by rw [mul_pow, hsNsq]; norm_num
  have hbr : 40 * (4 * (X : ℝ) ^ 2 + 2) + 40 * x ≤ 520 * Real.sqrt Pa.N := by
    have hA : 4 * (X : ℝ) ^ 2 + 2 ≤ 6 * Real.sqrt Pa.N := by nlinarith [hX2, hsN0]
    nlinarith [hA, hxle, hsN0]
  calc (((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
        (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
        (fun p => Work.FIPlan.absDelta p.1 p.2 < 4 * X ^ 2 + 1)).card
      ≤ 40 * (4 * (X : ℝ) ^ 2 + 2) * x ^ 2 + 40 * x ^ 3 := hcount
    _ = (40 * (4 * (X : ℝ) ^ 2 + 2) + 40 * x) * x ^ 2 := by ring
    _ ≤ (520 * Real.sqrt Pa.N) * (49 * Pa.N) := by
        exact mul_le_mul hbr hxsq (sq_nonneg x) (by positivity)
    _ = 25480 * Pa.N * Real.sqrt Pa.N := by ring

/-! ## 4. The mass of `β` -/

private lemma strip_mass_le (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
      ≤ 3000 * Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by
  have hpolar : Work.FIArea6.StripPolar Pa φ β := Work.FIArea6.IsBetaCoeff6.toStripPolar hβ
  have h := Work.FIArea6.strip_vsq_polar Pa φ β hpolar
  rw [show Work.FITop.boxN Pa = Work.FIPlan.gBox (Work.FITop.radN Pa) from rfl] at h
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hθ1 : Pa.θ ≤ 1 := Work.FIArea6.theta_le_one_of_params Pa
  have hsN : Real.sqrt Pa.N ≤ Pa.N := by
    calc Real.sqrt Pa.N ≤ Real.sqrt (Pa.N * Pa.N) := Real.sqrt_le_sqrt (by nlinarith)
      _ = Pa.N := Real.sqrt_mul_self hNpos.le
  have hkey : Pa.θ * Pa.N + Real.sqrt Pa.N + 1 ≤ 3 * Pa.N := by
    have h1 : Pa.θ * Pa.N ≤ Pa.N := by nlinarith [hθ1, hNpos.le]
    linarith [h1, hsN, hN1]
  have hlog3 : (0 : ℝ) ≤ (Real.log (2 + Pa.N)) ^ 3 :=
    pow_nonneg (Real.log_nonneg (by linarith)) 3
  calc (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
      ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 := h
    _ ≤ 1000 * (3 * Pa.N) * (Real.log (2 + Pa.N)) ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ hlog3
        exact mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ = 3000 * Pa.N * (Real.log (2 + Pa.N)) ^ 3 := by ring

/-! ## 5. The strip bound -/

theorem strip_bound6 : Work.FIArea7.Area7Strip6 := by
  refine ⟨100000000000000, Real.exp 1000, by norm_num, ?_⟩
  intro Pa hx X φ z0 β hβ hX hX9
  classical
  have hN1 : (1 : ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hNpos : (0 : ℝ) < Pa.N := by linarith
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hLnn : (0 : ℝ) ≤ 2 * Real.log (2 + Pa.N) := by
    have : (0 : ℝ) ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith)
    linarith
  have hXLnn : (0 : ℝ) ≤ (X : ℝ) * (2 * Real.log (2 + Pa.N)) := mul_nonneg (by positivity) hLnn
  -- `N ≥ exp 250`
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hxe : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [Pa.hη])
  have hexp250 : Real.exp 250 ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (Real.exp 1000 : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (Real.exp_pos 1000).le hx (by norm_num)
    have h2 : (Real.exp 1000 : ℝ) ^ ((1 : ℝ) / 4) = Real.exp 250 := by
      rw [Real.rpow_def_of_pos (Real.exp_pos 1000), Real.log_exp]
      norm_num
    rwa [h2] at h1
  have hH : Real.exp 250 ≤ Pa.N := le_trans hexp250 (le_of_lt (lt_of_le_of_lt hxe Pa.hNlo))
  have hE10 : Real.exp 10 ≤ Pa.N :=
    le_trans (Real.exp_le_exp.mpr (by norm_num)) hH
  have hNgt1 : (1 : ℝ) < Pa.N := by
    have h1 : (1 : ℝ) < Real.exp 250 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    linarith [hH]
  -- ### per-pair bound
  have hper : ∀ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      ∀ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      ‖(β z1 * star (β z2)) *
          (((∑ d ∈ Work.FITop4.Sset z1 z2, ((Nat.totient d : ℝ) / (d : ℝ))
            * (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
            * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℝ) : ℂ)‖
        ≤ ‖β z1‖ * ‖β z2‖ *
          (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2
            then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0) := by
    intro z1 h1 z2 h2
    have hlog : |Work.FITop4.logFac6 z1 z2| ≤ 2 * Real.log (2 + Pa.N) :=
      stripLogFac_le Pa hE10 h1 h2
    have hinner := stripInner_aux X z1 z2 hLnn hlog
    rw [norm_mul, norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  -- ### step 1: norm of the strip sum
  have hstep1 : ‖Strip6 Pa X β‖ ≤ 2 * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      ‖β z1‖ * ‖β z2‖ *
        (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2
          then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0) := by
    rw [Strip6, Tcut6_eq_sum_ofReal, norm_mul]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc ‖∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)) *
              (((∑ d ∈ Work.FITop4.Sset z1 z2, ((Nat.totient d : ℝ) / (d : ℝ))
                * (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
                * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℝ) : ℂ)
           else 0)‖
        ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ‖∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              (if Work.FIPlan.GaussCoprime z1 z2 then
                (β z1 * star (β z2)) *
                  (((∑ d ∈ Work.FITop4.Sset z1 z2, ((Nat.totient d : ℝ) / (d : ℝ))
                    * (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
                    * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℝ) : ℂ)
               else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ‖(if Work.FIPlan.GaussCoprime z1 z2 then
                (β z1 * star (β z2)) *
                  (((∑ d ∈ Work.FITop4.Sset z1 z2, ((Nat.totient d : ℝ) / (d : ℝ))
                    * (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
                    * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2) : ℝ) : ℂ)
               else 0)‖ := by
          apply Finset.sum_le_sum; intro z1 _
          exact norm_sum_le _ _
      _ ≤ ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
            ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
              ‖β z1‖ * ‖β z2‖ *
                (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2
                  then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0) := by
          apply Finset.sum_le_sum; intro z1 h1
          apply Finset.sum_le_sum; intro z2 h2
          by_cases hc : Work.FIPlan.GaussCoprime z1 z2
          · rw [if_pos hc]; exact hper z1 h1 z2 h2
          · rw [if_neg hc]
            have h0 : (0 : ℝ) ≤ ‖β z1‖ * ‖β z2‖ *
                (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2
                  then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0) := by
              by_cases hcc : Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2
              · rw [if_pos hcc]; positivity
              · rw [if_neg hcc]; simp
            simpa only [norm_zero] using h0
  -- ### step 2: the pair sum
  have hstep2 : (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      ‖β z1‖ * ‖β z2‖ *
        (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2
          then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0))
      = ((X : ℝ) * (2 * Real.log (2 + Pa.N))) *
        ∑ p ∈ ((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
              (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
              (fun p => Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2),
          ‖β p.1‖ * ‖β p.2‖ := by
    have hprod : (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ‖β z1‖ * ‖β z2‖ *
          (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2
            then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0))
        = ∑ p ∈ ((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
              (Work.FIPlan.gBox (Work.FITop.radN Pa))),
            ‖β p.1‖ * ‖β p.2‖ *
              (if Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2
                then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0) :=
      (Finset.sum_product _ _
        (fun p : GaussianInt × GaussianInt => ‖β p.1‖ * ‖β p.2‖ *
          (if Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2
            then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0))).symm
    rw [hprod]
    have hcongr : ∀ p : GaussianInt × GaussianInt,
        ‖β p.1‖ * ‖β p.2‖ *
          (if Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2
            then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0)
        = (if Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2
            then ‖β p.1‖ * ‖β p.2‖ else 0) * ((X : ℝ) * (2 * Real.log (2 + Pa.N))) := by
      intro p
      by_cases h : Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2 <;> simp [h]
    rw [Finset.sum_congr rfl (fun p _ => hcongr p)]
    rw [← Finset.sum_mul, ← Finset.sum_filter]
    ring
  -- ### step 3: Cauchy-Schwarz
  have hpairs := pair_sum_le_card_sqrt (Work.FIPlan.gBox (Work.FITop.radN Pa))
      (fun z => ‖β z‖) (fun z _ => norm_nonneg (β z))
      (fun z1 z2 : GaussianInt => Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2)
  have hmass := strip_mass_le Pa φ z0 β hβ
  have hcount := strip_pair_count Pa X hX1 hN1 hX9
  have hcount' : Real.sqrt ((((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
        (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
        (fun p => Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2)).card : ℝ)
      ≤ 160 * Pa.N ^ ((3 : ℝ) / 4) := by
    have h34 : (Pa.N ^ ((3 : ℝ) / 4)) ^ (2 : ℕ) = Pa.N * Real.sqrt Pa.N := by
      have h1 : (Pa.N ^ ((3 : ℝ) / 4)) ^ (2 : ℕ) = Pa.N ^ ((3 : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
        congr 1
        norm_num
      have h2 : Pa.N * Real.sqrt Pa.N = Pa.N ^ ((3 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
        nth_rewrite 1 [← Real.rpow_one Pa.N]
        rw [← Real.rpow_add hNpos]
        congr 1
        norm_num
      rw [h1, h2]
    have hP : (((((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
          (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2)).card : ℕ) : ℝ)
        ≤ 25480 * (Pa.N ^ ((3 : ℝ) / 4)) ^ (2 : ℕ) := by
      rw [h34]
      linarith [hcount]
    calc Real.sqrt (((((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
          (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
          (fun p => Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2)).card : ℕ) : ℝ)
        ≤ Real.sqrt (25480 * (Pa.N ^ ((3 : ℝ) / 4)) ^ (2 : ℕ)) := Real.sqrt_le_sqrt hP
      _ = Real.sqrt 25480 * Pa.N ^ ((3 : ℝ) / 4) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 25480),
            Real.sqrt_sq (by positivity)]
      _ ≤ 160 * Pa.N ^ ((3 : ℝ) / 4) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hS2 : (∑ p ∈ ((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
        (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
        (fun p => Work.FIPlan.absDelta p.1 p.2 ≤ 4 * X ^ 2),
        ‖β p.1‖ * ‖β p.2‖)
      ≤ (3000 * Pa.N * (Real.log (2 + Pa.N)) ^ 3) * (160 * Pa.N ^ ((3 : ℝ) / 4)) := by
    refine le_trans hpairs ?_
    have hA' : (0 : ℝ) ≤ 3000 * Pa.N * (Real.log (2 + Pa.N)) ^ 3 :=
      mul_nonneg (mul_nonneg (by norm_num) hNpos.le)
        (pow_nonneg (Real.log_nonneg (by linarith)) 3)
    exact mul_le_mul hmass hcount' (Real.sqrt_nonneg _) hA'
  -- ### step 4: the numeric inequality
  have hNpow : Pa.N ^ ((7 : ℝ) / 4) = Pa.N * Pa.N ^ ((3 : ℝ) / 4) := by
    rw [show (7 : ℝ) / 4 = 1 + 3 / 4 by norm_num, Real.rpow_add hNpos, Real.rpow_one]
  have h3 : 2 * ((X : ℝ) * (2 * Real.log (2 + Pa.N)) *
        (3000 * Pa.N * (Real.log (2 + Pa.N)) ^ 3 * (160 * Pa.N ^ ((3 : ℝ) / 4))))
      = 1920000 * (X : ℝ) * Pa.N ^ ((7 : ℝ) / 4) * (Real.log (2 + Pa.N)) ^ 4 := by
    rw [hNpow]
    ring
  have h4 : 1920000 * (X : ℝ) * Pa.N ^ ((7 : ℝ) / 4) * (Real.log (2 + Pa.N)) ^ 4
      ≤ 100000000000000 * (X : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N :=
    strip_numeric Pa.N (X : ℝ) hH hX1 hX9
  have h5 : 100000000000000 * (X : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N
      ≤ 100000000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
    have hPz : (0 : ℝ) ≤ (Pa.Pz : ℝ)⁻¹ := by
      apply inv_nonneg.mpr
      exact Nat.cast_nonneg _
    have h1 : 100000000000000 * (X : ℝ)⁻¹
        ≤ 100000000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith
    have h2 : (0 : ℝ) ≤ Pa.N ^ 2 * Real.log Pa.N :=
      mul_nonneg (sq_nonneg _) (le_of_lt (Real.log_pos (by linarith)))
    calc 100000000000000 * (X : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N
        = (100000000000000 * (X : ℝ)⁻¹) * (Pa.N ^ 2 * Real.log Pa.N) := by ring
      _ ≤ (100000000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹)) *
            (Pa.N ^ 2 * Real.log Pa.N) := mul_le_mul_of_nonneg_right h1 h2
      _ = 100000000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
          ring
  -- ### assembly
  have hlink : 2 * (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
      ‖β z1‖ * ‖β z2‖ *
        (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2
          then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0))
      ≤ 2 * ((X : ℝ) * (2 * Real.log (2 + Pa.N)) *
        (3000 * Pa.N * (Real.log (2 + Pa.N)) ^ 3 * (160 * Pa.N ^ ((3 : ℝ) / 4)))) := by
    rw [hstep2]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul_of_nonneg_left hS2 hXLnn
  calc ‖Strip6 Pa X β‖
      ≤ 2 * (∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          ‖β z1‖ * ‖β z2‖ *
            (if Work.FIPlan.absDelta z1 z2 ≤ 4 * X ^ 2
              then (X : ℝ) * (2 * Real.log (2 + Pa.N)) else 0)) := hstep1
    _ ≤ 2 * ((X : ℝ) * (2 * Real.log (2 + Pa.N)) *
        (3000 * Pa.N * (Real.log (2 + Pa.N)) ^ 3 * (160 * Pa.N ^ ((3 : ℝ) / 4)))) := hlink
    _ = 1920000 * (X : ℝ) * Pa.N ^ ((7 : ℝ) / 4) * (Real.log (2 + Pa.N)) ^ 4 := h3
    _ ≤ 100000000000000 * (X : ℝ)⁻¹ * Pa.N ^ 2 * Real.log Pa.N := h4
    _ ≤ 100000000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := h5

end

end Work.FIArea7
