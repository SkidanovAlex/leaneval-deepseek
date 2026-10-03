import Mathlib
import Submission.Work.FITop4.Areas6f
import Submission.Work.FIArea4.A4c.Defs
import Submission.Work.FIArea4.A4c.card_dvd_finset_le
import Submission.Work.FIArea4.A4c.expBound6T
import Submission.Work.FIArea4.A4c.A6RedT_of_expBound6T
import Submission.Work.FIArea4.A4c.Vcut_eq_A4c
import Submission.Work.FIArea4.A4c.junk_le
import Submission.Work.FIArea4.A4c.pieceSum_le
import Submission.Work.FIArea4.A4c.rem_le
import Submission.Work.FIArea7.area7_6b

/-! Guidance from the project lead (the requester):

LEAD DESIGN: read `Submission/Work/FIArea4/AREA4_ENGINES_LEAD.md` (§3, the route) FIRST. Contract: `Work.FITop4.Area4_6c` (frozen, `FITop4/Areas6f.lean`, lead-built). The old engines A6PieceBound/A6RemBound are over-strong; do NOT use them. Route (namespace `Work.FIArea4.A4c`, directory `Submission/Work/FIArea4/A4c/`; exact statements in §3.3):
N1 clean copy of the proved Möbius core (from `removal6.lean` / `mobiusData6`/`moebiusSplit6`); N2 divisor-count lemma (≤ 4τ(|z|²)); N3 `ExpBound6T` (proved `ExpBound6ng` per restricted array, no decay in w); N4 `A6RedT` (template: `A6Red.lean`); N5 piece-sum arithmetic (with both pins τ = θ⁻¹, θ·(log N+1)^{2^20−20} ≤ 1 once log x ≥ 2); N6 the new split identity with uA(t) = S15u(3t/2) (remainder = (W+B)(X) minus a convex combination of (W+B)(m), m < X, plus |Δ| < 4X² junk); N7 junk bound; N8 remainder bound via the PROVED `Area7_6b` (needs X ≥ (log N)², loglog x ≥ nuU/3+1); N9 assembly. Wave 1 in parallel: N1, N2, N6, N7 (N3/N8 can start against stated hypotheses); wave 2: N4, N5, N8, then N9. Dispatch the nodes via request_lemma at NEW paths under FIArea4/A4c/. Proved pieces to reuse (axiom-clean): pD6ngStratumBound, strUvarSum6, ExpBound6ng, sepBound6, expLogBound6, psiSumEqTcut6, A6Close, A6Crude, A6Light, A6Ener3_le, mobiusData6/moebiusSplit6, StrUVarBody (fixed). Never write the words "theorem area4_6c" in comments/docstrings.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The amended area 4 contract `Work.FITop4.Area4_6c`.**

Assembly (design §3.3, node N9).  The exact splitting `A4c.Vcut_eq_A4c` writes `Vcut` as

* the sum of the `J ≤ 12(log N+1)²` smooth pieces `Tcut (A6cut psiA X j) β`, bounded by
  `A4c.pieceSum_le` (which consumes the §15 reduction `A4c.A6RedT_of_expBound6T A4c.expBound6T`,
  hence the Möbius split `A4c.expBound6T` with the divisor count `A4c.card_dvd_finset_le`);
* minus the remainder `(W+B)(X) - Σ_{m<X} wA X m ((W+B)(m) - junk)`, bounded by `A4c.rem_le`
  (the PROVED area 7 `Work.FIArea7.area7_6b` plus the crude junk bound `A4c.junk_le`).

Both bounds are of the form `c X^{-1/3} N²`, and `X^{-1/3} ≤ P^{-1} + X^{-1/3}`, so the two
constants add.  `J := Nat.log2 ((radN Pa).toNat ^ 2) + 2` and its range condition are as in
`Work.FIArea4.area4_6_of_engines` (`J_le_log_sq`). -/
theorem area4_6c : Work.FITop4.Area4_6c := by
  intro η hη0 hη3
  -- the smooth pieces (`psiA` is the bump of the route: smooth, in `[0,1]`, supported in `(1/2,5/2)`)
  obtain ⟨K, xK, hKpos, hpiece⟩ :=
    A4c.pieceSum_le (A4c.A6RedT_of_expBound6T A4c.expBound6T) A4c.card_dvd_finset_le
      A4c.psiA A4c.psiA_contDiff A4c.psiA_nonneg A4c.psiA_le_one A4c.psiA_support_half
  -- the remainder (area 7 + the crude junk bound)
  obtain ⟨c, xc, hcpos, hrem⟩ :=
    A4c.rem_le Work.FIArea7.area7_6b A4c.junk_le η hη0 hη3
  refine ⟨K + c, max xK (max xc 4096), by positivity, ?_⟩
  intro Pa hx hPa hθ hτ X φ z0 β hβ haxis hX1 hlog2 hX9 hXν
  have hxK : xK ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
  have hxmax : max xc 4096 ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx
  have hxc : xc ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hxmax
  have hx4096 : (4096 : ℝ) ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hxmax
  -- `N ≥ 8`, so that `(log N)² ≥ 2` and hence `X ≥ 2` (needed by the splitting)
  have hN8 : (8 : ℝ) ≤ Pa.N := by
    have h1 : ((4096 : ℝ)) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by norm_num) hx4096 (by norm_num)
    have h2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [Pa.hη])
    have h3 : ((4096 : ℝ)) ^ ((1 : ℝ) / 4) = 8 := by
      rw [show ((4096 : ℝ)) = (8 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (8 : ℝ) 4,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    linarith [Pa.hNlo]
  have hX2 : 2 ≤ X := by
    have hlog8 : (2 : ℝ) ≤ Real.log Pa.N := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 8) hN8
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, Real.log_pow] at h
      have hd9 := Real.log_two_gt_d9
      push_cast at h
      linarith
    have hsq : (2 : ℝ) ≤ (Real.log Pa.N) ^ 2 := by
      have h0 : (0 : ℝ) ≤ Real.log Pa.N := by linarith
      nlinarith
    have : (2 : ℝ) ≤ (X : ℝ) := le_trans hsq hlog2
    exact_mod_cast this
  -- the number of pieces and its range condition (verbatim from `area4_6_of_engines`)
  set J : ℕ := Nat.log2 ((Work.FITop.radN Pa).toNat ^ 2) + 2 with hJdef
  have hncast : ((((Work.FITop.radN Pa).toNat : ℕ) : ℝ)) = (Work.FITop.radN Pa : ℝ) := by
    exact_mod_cast (radN_cast_toNat Pa)
  have hRr : (Work.FITop.radN Pa : ℝ) = ((Work.FITop.radN Pa).toNat : ℝ) := hncast.symm
  have hJ : ∀ z1 z2 d, z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa) →
      z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa) →
      d ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1) →
      2 * ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ))) ≤ (2 : ℝ) ^ J := by
    intro z1 z2 d h1 h2 hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hΔ : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 2 * (Work.FITop.radN Pa : ℝ) ^ 2 := by
      have h := absDelta_le_two_mul_sq (R := Work.FITop.radN Pa) (by
        unfold Work.FITop.radN; exact Int.natCast_nonneg _) h1 h2
      have h' : ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
          ≤ ((2 * (Work.FITop.radN Pa) ^ 2 : ℤ) : ℝ) := by exact_mod_cast h
      simpa using h'
    have h2J : ((Work.FITop.radN Pa).toNat : ℝ) ^ 2 ≤ (2 : ℝ) ^ J := by
      have hm1 : 1 ≤ (Work.FITop.radN Pa).toNat ^ 2 := by
        have h2 : 2 ≤ (Work.FITop.radN Pa).toNat := two_le_radN_toNat Pa
        nlinarith
      have hlt := Nat.lt_log2_self (n := (Work.FITop.radN Pa).toNat ^ 2)
      have hle : 2 ^ (Nat.log2 ((Work.FITop.radN Pa).toNat ^ 2) + 1) ≤ 2 ^ J := by
        rw [hJdef]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      have hcast : ((Work.FITop.radN Pa).toNat : ℝ) ^ 2 < (2 : ℝ) ^ J := by
        have h1' : ((((Work.FITop.radN Pa).toNat ^ 2 : ℕ)) : ℝ)
            < (((2 ^ (Nat.log2 ((Work.FITop.radN Pa).toNat ^ 2) + 1) : ℕ)) : ℝ) := by
          exact_mod_cast hlt
        have h2' : ((((2 ^ (Nat.log2 ((Work.FITop.radN Pa).toNat ^ 2) + 1) : ℕ)) : ℝ))
            ≤ (((2 ^ J : ℕ)) : ℝ) := by exact_mod_cast hle
        push_cast at h1' h2' ⊢
        linarith
      exact le_of_lt hcast
    have hstep : 2 * ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ)))
        ≤ ((Work.FITop.radN Pa).toNat : ℝ) ^ 2 := by
      have hAnn : 0 ≤ (Work.FIPlan.absDelta z1 z2 : ℝ) := Nat.cast_nonneg _
      have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
      have hdr : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
      have heq : 2 * ((Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (d : ℝ)))
          = (Work.FIPlan.absDelta z1 z2 : ℝ) / (2 * (X : ℝ) * (d : ℝ)) := by
        field_simp; ring
      rw [heq]
      have hden2 : 2 ≤ 2 * (X : ℝ) * (d : ℝ) := by nlinarith
      have hM2 : (Work.FIPlan.absDelta z1 z2 : ℝ) / (2 * (X : ℝ) * (d : ℝ))
          ≤ (Work.FIPlan.absDelta z1 z2 : ℝ) / 2 :=
        div_le_div_of_nonneg_left hAnn (by norm_num) hden2
      have hM4 : (Work.FIPlan.absDelta z1 z2 : ℝ) / 2 ≤ ((Work.FITop.radN Pa).toNat : ℝ) ^ 2 := by
        rw [hRr] at hΔ
        linarith
      linarith
    linarith
  -- the exact splitting of `Vcut`
  have hsplit := A4c.Vcut_eq_A4c (Rz := Work.FITop.radN Pa) (X := X) hX2 β J hJ
  set A : ℂ := ∑ j ∈ Finset.range J,
    Work.FITop4.Tcut (Work.FITop.radN Pa) (A6cut A4c.psiA X j) β with hAdef
  set B : ℂ := Work.FITop4.Wcut (Work.FITop.radN Pa) X β
    + Work.FITop4.Bcut (Work.FITop.radN Pa) X β with hBdef
  set C : ℂ := ∑ m ∈ Finset.Ico 1 X, ((A4c.wA X m : ℝ) : ℂ) *
    (Work.FITop4.Wcut (Work.FITop.radN Pa) m β + Work.FITop4.Bcut (Work.FITop.radN Pa) m β
      - Work.FITop4.Tcut (Work.FITop.radN Pa) (A4c.junkCut X m) β) with hCdef
  -- the piece bound (N5)
  have hA : ‖A‖ ≤ K * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
    rw [hAdef]
    refine le_trans (norm_sum_le _ _) ?_
    have hJb : (J : ℝ) ≤ 12 * (Real.log Pa.N + 1) ^ 2 := by
      rw [hJdef]; exact J_le_log_sq Pa
    exact hpiece Pa hxK hθ hτ X φ z0 β J hβ hX1 hX9 hJb
  -- the remainder bound (N8)
  have hBC : ‖B - C‖ ≤ c * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
    rw [hBdef, hCdef]
    exact hrem Pa hxc hPa hτ X φ z0 β hβ haxis hlog2 hXν
  -- assemble
  have hcongr : Work.FITop4.Vcut (Work.FITop.radN Pa) X β = A - (B - C) := by
    rw [hsplit]
    ring
  have hmain : ‖Work.FITop4.Vcut (Work.FITop.radN Pa) X β‖
      ≤ (K + c) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by
    rw [hcongr]
    refine le_trans (norm_sub_le A (B - C)) ?_
    refine le_trans (add_le_add hA hBC) ?_
    have heq : K * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2
        + c * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2
        = (K + c) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := by ring
    rw [heq]
  -- absorb into the target's right-hand side
  calc ‖Work.FITop4.Vcut (Work.FITop.radN Pa) X β‖
      ≤ (K + c) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ 2 := hmain
    _ ≤ (K + c) * (((Pa.Pz : ℝ))⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3)) * Pa.N ^ 2 := by
        have hKc : (0 : ℝ) ≤ K + c := by linarith
        have hrp : (0 : ℝ) ≤ (X : ℝ) ^ (-(1 : ℝ) / 3) :=
          Real.rpow_nonneg (Nat.cast_nonneg X) _
        have hinv : (0 : ℝ) ≤ (((Pa.Pz : ℝ)))⁻¹ := by positivity
        have h1 : (X : ℝ) ^ (-(1 : ℝ) / 3)
            ≤ (((Pa.Pz : ℝ)))⁻¹ + (X : ℝ) ^ (-(1 : ℝ) / 3) := by linarith
        have h2 := mul_le_mul_of_nonneg_left h1 hKc
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg Pa.N)

end

end Work.FIArea4
