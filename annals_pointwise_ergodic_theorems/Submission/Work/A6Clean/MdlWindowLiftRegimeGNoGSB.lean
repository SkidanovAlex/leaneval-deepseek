import Mathlib
import Submission.Work.KMTPlan.A6Clean.MdlLiftRegimeDefs
import Submission.Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large
import Submission.Work.A7Hi.fiberBumpPositivity

namespace Work.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

/-! ## The `g`-side regime conditions, no good-scale hypothesis, `ρ`-**only** threshold

`Work.A6Clean.MdlWindowLiftRegimeGNoGS` (PROVED) derives the five numerical conditions
(`hN`, `hrad`, `hnA`, `hΦ`, `hsepU`) of the frozen slice `mdlWindowLiftG` from the model data
`mdlCore` alone, but the threshold `B` it produces is allowed to depend on the datum
(`C₀, a, Λ, ha, ha1, l₁, …, t`): its statement is

  `∀ (datum), ∃ B, ∀ n, mdlCore … n → l₂ ≠ 0 → B ≤ lcL … → (the five conditions)`.

A consumer that fixes its case threshold *before* the datum (which is what the constant
bookkeeping of the §8 assembly needs, cf. the `∃ B, ∀ (all the data)` shape of
`Work.A6Clean.MdlWindowLiftRegimeNoGSB`, the `f`-side twin) requires the `∃ B` **outside** every
parameter.  This file provides that form.

The point is that nothing in the proof of `MdlWindowLiftRegimeG` uses the datum to *choose* a
constant: the witnesses extracted are

* `B₀` from `uScale_regimeG` (an explicit function of `ρ` alone),
* `Cρ₁` from `exists_goodMajorArcs_nonAliasing`, and `B₁` from `goodMajorArcs_uScale_of_large`
  (`ρ` and `Cρ₁` alone),
* `C₂` from `iw_height_separated`, and `B₂` from `goodMajorArcs_uScale_of_large`
  (`ρ` and `C₂` alone),

and the hypotheses `l₂ ≤ U`, `k₂ ≤ U` used against them are consequences of
`U = lcL l₁ l₂ k₁ k₂` itself, never of the threshold.  Hence `max B₀ (max B₁ B₂)` works
uniformly.

The proof is that of `Work.A6Clean.MdlWindowLiftRegimeG` transported verbatim, with the
quantifier over the datum pulled inside; the numeric helpers of that file are `private`, so they
are restated here (as in `MdlWindowLiftRegimeNoGSB`).  Note `hρ1` and `ht` are unused, as in the
`f`-side twin. -/

/-- `(n+1)^2 ≤ 2 ^ (2^n - 1)` for `n ≥ 3`. -/
private lemma two_pow_pred_ge_sqGNoGSB (n : ℕ) (hn : 3 ≤ n) : (n+1)^2 ≤ 2^(2^n - 1) := by
  revert n
  refine Nat.le_induction ?base ?step
  · norm_num
  · intro n hn ih
    have hpow : 2^(2^(n+1) - 1) = 2^(2^n - 1) * 2^(2^n) := by
      have h1 : 2^(n+1) - 1 = (2^n - 1) + 2^n := by
        have : 2^(n+1) = 2 * 2^n := by ring
        omega
      rw [h1, pow_add]
    have h8 : 8 ≤ 2^(2^n) := by
      have h2n : 3 ≤ 2^n := le_trans hn (Nat.lt_two_pow_self.le)
      calc (8:ℕ) = 2^3 := by norm_num
        _ ≤ 2^(2^n) := Nat.pow_le_pow_right (by norm_num) h2n
    rw [hpow]
    calc (n+2)^2 ≤ 8 * (n+1)^2 := by nlinarith
      _ ≤ 2^(2^n) * 2^(2^n - 1) := by
          have := Nat.mul_le_mul h8 ih
          linarith
      _ = 2^(2^n - 1) * 2^(2^n) := by ring

/-- `8·2^n + 2 ≤ 2 ^ (2^n - 1)` for `n ≥ 3`. -/
private lemma two_pow_pred_ge_linGNoGSB (n : ℕ) (hn : 3 ≤ n) : 8*2^n + 2 ≤ 2^(2^n - 1) := by
  revert n
  refine Nat.le_induction ?base ?step
  · norm_num
  · intro n hn ih
    have hpow : 2^(2^(n+1) - 1) = 2^(2^n - 1) * 2^(2^n) := by
      have h1 : 2^(n+1) - 1 = (2^n - 1) + 2^n := by
        have : 2^(n+1) = 2 * 2^n := by ring
        omega
      rw [h1, pow_add]
    have h8 : 8 ≤ 2^(2^n) := by
      have h2n : 3 ≤ 2^n := le_trans hn (Nat.lt_two_pow_self.le)
      calc (8:ℕ) = 2^3 := by norm_num
        _ ≤ 2^(2^n) := Nat.pow_le_pow_right (by norm_num) h2n
    rw [hpow]
    have h16 : 8 * 2^(n+1) + 2 = 16 * 2^n + 2 := by
      have : 2^(n+1) = 2 * 2^n := by ring
      rw [this]; ring
    rw [h16]
    calc 16 * 2^n + 2 ≤ 8 * (8*2^n + 2) := by omega
      _ ≤ 2^(2^n) * 2^(2^n - 1) := by
          have := Nat.mul_le_mul h8 ih
          linarith
      _ = 2^(2^n - 1) * 2^(2^n) := by ring

/-- `s^2 ≤ 2 ^ (2^s - 1)` for real `s ≥ 3`. -/
private lemma real_sq_le_two_powGNoGSB (s : ℝ) (hs : 3 ≤ s) :
    s^2 ≤ (2:ℝ)^((2:ℝ)^s - 1) := by
  set n : ℕ := ⌊s⌋₊ with hn
  have hn3 : 3 ≤ n := Nat.le_floor hs
  have hslt : s < (n:ℝ) + 1 := Nat.lt_floor_add_one s
  have h1 : s^2 ≤ ((n:ℝ)+1)^2 := by nlinarith
  have h2a : ((n:ℝ)+1)^2 ≤ (2:ℝ)^(2^n - 1) := by
    have h := two_pow_pred_ge_sqGNoGSB n hn3
    exact_mod_cast h
  have h2b : (2:ℝ)^(2^n - 1) = (2:ℝ)^((2:ℝ)^n - 1) := by
    rw [← Real.rpow_natCast, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
    norm_num
  have h3 : (2:ℝ)^((2:ℝ)^n - 1) ≤ (2:ℝ)^((2:ℝ)^s - 1) := by
    apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr
    have hns : (n:ℝ) ≤ s := Nat.floor_le (by linarith)
    have h2n : (2:ℝ)^n ≤ (2:ℝ)^s := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr hns
    linarith
  linarith

/-- `4·2^s + 2 ≤ 2 ^ (2^s - 1)` for real `s ≥ 3`. -/
private lemma real_lin_le_two_powGNoGSB (s : ℝ) (hs : 3 ≤ s) :
    4*(2:ℝ)^s + 2 ≤ (2:ℝ)^((2:ℝ)^s - 1) := by
  set n : ℕ := ⌊s⌋₊ with hn
  have hn3 : 3 ≤ n := Nat.le_floor hs
  have hslt : s < (n:ℝ) + 1 := Nat.lt_floor_add_one s
  have h2s : (2:ℝ)^s < (2:ℝ)^(n+1) := by
    rw [← Real.rpow_natCast]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr (by exact_mod_cast hslt)
  have hnn : (2:ℝ)^(n+1) = 2 * (2:ℝ)^n := by rw [pow_succ]; ring
  have h4 : 4*(2:ℝ)^s + 2 ≤ 8*(2:ℝ)^n + 2 := by
    have := h2s; rw [hnn] at this; linarith
  have h2a : 8*(2:ℝ)^n + 2 ≤ (2:ℝ)^(2^n - 1) := by
    have h := two_pow_pred_ge_linGNoGSB n hn3
    exact_mod_cast h
  have h2b : (2:ℝ)^(2^n - 1) = (2:ℝ)^((2:ℝ)^n - 1) := by
    rw [← Real.rpow_natCast, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow]
    norm_num
  have h3 : (2:ℝ)^((2:ℝ)^n - 1) ≤ (2:ℝ)^((2:ℝ)^s - 1) := by
    apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr
    have hns : (n:ℝ) ≤ s := Nat.floor_le (by linarith)
    have h2n : (2:ℝ)^n ≤ (2:ℝ)^s := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr hns
    linarith
  linarith

/-- **The scale count dominates `U + 2·uScale ρ U + 1` exponentially, with a `ρ`-only
threshold.**  There is `B`, a function of `ρ > 0` alone (the explicit
`⌈3/(2ρ)⌉ + ⌈1/(2ρ²)⌉ + 8` used in the proof), such that for every `U ≥ B`,
`U + 2·uScale ρ U + 1 ≤ 2 ^ uScale ρ U`. -/
private theorem uScale_regimeGNoGSB (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, ∀ U : ℕ, B ≤ U →
      U + 2 * Work.KMTAreas.A7.uScale ρ U + 1 ≤ 2 ^ Work.KMTAreas.A7.uScale ρ U := by
  refine ⟨⌈(3:ℝ)/(2*ρ)⌉₊ + (⌈1/(2*ρ^2)⌉₊ + 8), ?_⟩
  intro U hU
  have hU1 : (⌈(3:ℝ)/(2*ρ)⌉₊ : ℕ) ≤ U := by omega
  have hU2 : (⌈1/(2*ρ^2)⌉₊ : ℕ) ≤ U := by omega
  set s : ℝ := 2 * ρ * (U:ℝ) with hsdef
  have hm_eq : Work.KMTAreas.A7.uScale ρ U = ⌊(2:ℝ)^s⌋₊ := by
    rw [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Int.floor_toNat]
    simp only [Nat.cast_one, one_mul]
    rw [hsdef]
  have hs3 : 3 ≤ s := by
    have h1 : (3:ℝ)/(2*ρ) ≤ (⌈(3:ℝ)/(2*ρ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈(3:ℝ)/(2*ρ)⌉₊ : ℕ) : ℝ) ≤ (U:ℝ) := by exact_mod_cast hU1
    have h3 : (3:ℝ)/(2*ρ) ≤ (U:ℝ) := le_trans h1 h2
    have h4 : (0:ℝ) < 2*ρ := by linarith
    rw [div_le_iff₀ h4] at h3
    rw [hsdef]; linarith
  have hone : (1:ℝ) ≤ 2*ρ^2*(U:ℝ) := by
    have h1 : (1:ℝ)/(2*ρ^2) ≤ (⌈1/(2*ρ^2)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1/(2*ρ^2)⌉₊ : ℕ) : ℝ) ≤ (U:ℝ) := by exact_mod_cast hU2
    have h3 : (1:ℝ)/(2*ρ^2) ≤ (U:ℝ) := le_trans h1 h2
    have h4 : (0:ℝ) < 2*ρ^2 := by positivity
    rw [div_le_iff₀ h4] at h3
    linarith
  have hUpos : (0:ℝ) < (U:ℝ) := by
    have : (8:ℕ) ≤ U := by omega
    exact_mod_cast (by omega : 0 < U)
  have hm_le : ((Work.KMTAreas.A7.uScale ρ U : ℕ) : ℝ) ≤ (2:ℝ)^s := by
    rw [hm_eq]; exact Nat.floor_le (by positivity)
  have hm_ge : (2:ℝ)^s - 1 ≤ ((Work.KMTAreas.A7.uScale ρ U : ℕ) : ℝ) := by
    rw [hm_eq]
    have := Nat.lt_floor_add_one ((2:ℝ)^s)
    linarith
  have hA : (2:ℝ)^((2:ℝ)^s - 1) ≤ (2:ℝ)^(Work.KMTAreas.A7.uScale ρ U) := by
    have h := hm_ge
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr h
  have hsq := real_sq_le_two_powGNoGSB s hs3
  have hlin := real_lin_le_two_powGNoGSB s hs3
  have hUsq : (U:ℝ) ≤ s^2/2 := by
    rw [hsdef]
    nlinarith [hone, hUpos, sq_nonneg ρ, sq_nonneg (U:ℝ)]
  have key : (U:ℝ) + 2*((Work.KMTAreas.A7.uScale ρ U : ℕ):ℝ) + 1
      ≤ (2:ℝ)^(Work.KMTAreas.A7.uScale ρ U) := by
    have h1 : (U:ℝ) + 2*((Work.KMTAreas.A7.uScale ρ U : ℕ):ℝ) + 1
        ≤ (U:ℝ) + 2*(2:ℝ)^s + 1 := by linarith
    have h2 : (U:ℝ) + 2*(2:ℝ)^s + 1 ≤ s^2/2 + (4*(2:ℝ)^s + 2)/2 := by linarith
    have h3 : s^2/2 + (4*(2:ℝ)^s + 2)/2 ≤ (2:ℝ)^((2:ℝ)^s - 1) := by linarith
    linarith
  have key2 : ((U : ℕ) : ℝ) + 2*((Work.KMTAreas.A7.uScale ρ U : ℕ):ℝ) + 1
      ≤ ((2 ^ Work.KMTAreas.A7.uScale ρ U : ℕ) : ℝ) := by
    rw [Nat.cast_pow]
    exact key
  exact_mod_cast key2

/-- **The separation arithmetic.**  If `(c/2+2)·S ≤ m` with `S ≥ 1`, `m ≥ 1` and `d ≥ 2`, then
`c·S ≤ 2·d·m - 1`.  (From the hypothesis `c·S/2 + 2·S ≤ m`, hence `c·S ≤ 2m - 4S ≤ 2m - 4`, and
`2m - 4 ≤ 2dm - 1` because `2m(d-1) ≥ -3`.) -/
private lemma sep_arithGNoGSB {c d m S : ℝ} (hd : 2 ≤ d) (hm : 1 ≤ m) (hS : 1 ≤ S)
    (h : (c / 2 + 2) * S ≤ m) : c * S ≤ 2 * d * m - 1 := by
  nlinarith

/-- **(A6 §8 adelic producer, Case G) the g-side regime conditions of the model window-piece
lift on the large-`lcL` data, with a `ρ`-only threshold.**

This is the g-side twin of the PROVED `Work.A6Clean.MdlWindowLiftRegimeNoGSB`
(`Submission/Work/A6Clean/MdlWindowLiftRegimeNoGSB.lean`): same statement shape, `l₂` in place of
`l₁`, `d = P.natDegree`-scaled quantities, and the conclusion packaged as the named predicate
`Work.KMTPlan.A6Clean.MdlLiftRegimeG` (which is *verbatim* the five-hypothesis list of
`Work.KMTPlan.A6Clean.mdlWindowLiftG`).  Route: transplant the proof of the PROVED
`Work.A6Clean.MdlWindowLiftRegimeGNoGS` (`Submission/Work/A6Clean/MdlWindowLiftRegimeGNoGS.lean`,
0 `sorry`) and pull the `∃ B` outside the data, exactly as `MdlWindowLiftRegimeNoGSB` was obtained
from `MdlWindowLiftRegimeNoGS`; all witnesses (`uScale_regimeG`, `goodMajorArcs_uScale_of_large`,
`iw_height_separated`) are `ρ`-only.  Note `hρ1` and `ht` are unused (as in the f-side twin). -/
theorem MdlWindowLiftRegimeGNoGSB (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ B : ℕ, ∀ (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal) (hΛ : 1 < Λ)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
      (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
      (hk₂ : k₂ = 0 → j₂ ≠ -1) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (n : ℕ),
      Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → l₂ ≠ 0 → B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ →
      Work.KMTPlan.A6Clean.MdlLiftRegimeG ρ P a l₁ l₂ k₁ k₂ j₂ t n := by
  -- the `ρ`-only witnesses, extracted **before** the datum
  obtain ⟨B₀, hB₀⟩ := uScale_regimeGNoGSB ρ hρ
  obtain ⟨Cρ₁, hCρ₁, hNA⟩ :=
    Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing hρ
  obtain ⟨B₁, hB₁⟩ := Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large ρ hρ Cρ₁ hCρ₁
  obtain ⟨C₂, hC₂, hsep⟩ := Work.Analysis.IonescuWainger.iw_height_separated hρ
  obtain ⟨B₂, hB₂⟩ :=
    Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large ρ hρ (C₂ / 2 + 2) (by linarith)
  refine ⟨max B₀ (max B₁ B₂), ?_⟩
  intro C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ j₂ hj₂ hk₂ t ht n hcore hl₂ hB
  rw [Work.KMTPlan.A6Clean.MdlLiftRegimeG]
  set U : ℕ := Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ with hUdef
  set N : ℕ := Nat.floor (a n) with hNdef
  have hB0 : B₀ ≤ U := le_trans (le_max_left _ _) hB
  have hB1' : B₁ ≤ U := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB2' : B₂ ≤ U := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  obtain ⟨hin, hcut, hmain⟩ :=
    (Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hcore
  have hk₂U : k₂ ≤ U := by
    rw [hUdef, Work.KMTPlan.A6.lcL]
    exact le_trans (le_max_right k₁ k₂) (le_max_right (max l₁ l₂) (max k₁ k₂))
  have hl₂U : l₂ ≤ U := by
    rw [hUdef, Work.KMTPlan.A6.lcL]
    exact le_trans (le_max_right l₁ l₂) (le_max_left (max l₁ l₂) (max k₁ k₂))
  -- (1) `1 ≤ N`
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    exact Nat.le_floor (by exact_mod_cast ha1 n)
  -- the numerical regime of the scale count
  have hnum : U + 2 * Work.KMTAreas.A7.uScale ρ U + 1
      ≤ 2 ^ Work.KMTAreas.A7.uScale ρ U := hB₀ U hB0
  have hcut2 : 2 ^ (2 ^ Work.KMTAreas.A7.uScale ρ U) < N := by
    have hsplit : Work.KMTAreas.A7.splitCut ρ U
        = 2 ^ (2 ^ Work.KMTAreas.A7.uScale ρ U) := rfl
    rwa [hsplit] at hcut
  have hlog : (2 ^ Work.KMTAreas.A7.uScale ρ U : ℤ) ≤ Work.Analysis.EndVar.logN N := by
    have h2le : 2 ≤ N := by
      have : 1 ≤ 2 ^ (2 ^ Work.KMTAreas.A7.uScale ρ U) := Nat.one_le_two_pow
      omega
    have hlogeq : Work.Analysis.EndVar.logN N = (Nat.log 2 N : ℤ) := by
      simp only [Work.Analysis.EndVar.logN]
      rw [Nat.max_eq_left h2le]
    rw [hlogeq]
    have hN0 : N ≠ 0 := by omega
    have h := (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) hN0).mpr hcut2.le
    exact_mod_cast h
  have hexp : (k₂ : ℤ) + 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ) + 1
      ≤ Work.Analysis.EndVar.logN N := by
    have h1 : (k₂ : ℤ) ≤ (U : ℤ) := by exact_mod_cast hk₂U
    have h2 : ((U : ℤ) + 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ) + 1)
        ≤ (2 ^ Work.KMTAreas.A7.uScale ρ U : ℤ) := by exact_mod_cast hnum
    linarith
  -- (2) the narrow band inequality
  have hrad : (2 : ℝ) ^ ((P.natDegree : ℝ) *
        ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
      ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) := by
    rw [← Real.rpow_intCast]
    apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr
    have h : (k₂ : ℝ) + 2 * (Work.KMTAreas.A7.uScale ρ U : ℝ) + 1
        ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by exact_mod_cast hexp
    have hd1 : (1:ℝ) ≤ (P.natDegree : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ P.natDegree)
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ (P.natDegree : ℝ)), hd1]
  -- (3) the non-aliasing
  have hnA : Work.Analysis.IonescuWainger.NonAliasing
      (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ U : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) := by
    refine hNA l₂ _ ?_
    rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
    have hgm := (hB₁ l₂ U hl₂U hB1').1
    rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at hgm
    push_cast at hgm ⊢
    have hd1 : (1:ℝ) ≤ (P.natDegree : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ P.natDegree)
    have hm0 : (0:ℝ) ≤ (Work.KMTAreas.A7.uScale ρ U : ℝ) := by positivity
    nlinarith [le_mul_of_one_le_left hm0 hd1]
  -- (4) the arc support
  have hΦ : Work.Analysis.IonescuWainger.SupportedInArc
      (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1)
      (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphitildeNtj P N k₂ j₂ t)) := by
    obtain ⟨_, _, _, _, harc⟩ :=
      Work.KMTPlan.A6.VarphitildeNtjPeriodizeAux P N k₂ j₂ t hj₂ hk₂ hN1
    intro ξ hξ
    obtain ⟨θ, hθabs, hθeq⟩ := harc ξ hξ
    refine ⟨θ, ?_, ?_⟩
    · have hstep : (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1)
          ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) := by
        rw [zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)]
        have h0 : (0:ℤ) ≤ (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ U : ℤ) :=
          mul_nonneg (by positivity) (by positivity)
        have heq : (P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)
            = 2 * ((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ U : ℤ)) := by ring
        rw [heq]; omega
      have habs : |θ| ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) :=
        le_trans (le_trans hθabs hrad) hstep
      rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc, ← abs_le]
      exact habs
    · simpa using hθeq.symm
  -- (5) the separation
  have hsepU : ∀ ⦃α β : Work.Analysis.IonescuWainger.Circle⦄,
      α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ →
      β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ → α ≠ β →
      (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)))
        + (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
        < ‖α - β‖ := by
    intro α β hα hβ hne
    have hgm := (hB₂ l₂ U hl₂U hB2').1
    -- the good-major-arcs condition at `-(uScale ρ U)` gives `C₂ · 2^{ρ l₂} ≤ 2·d·uScale - 1`
    have hCl : C₂ * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
        ≤ (P.natDegree : ℝ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℝ) - 1 := by
      rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at hgm
      push_cast at hgm
      have hpow1 : (1:ℝ) ≤ (2:ℝ) ^ (ρ * (l₂ : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have hd2 : (2:ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
      have hm1 : (1:ℝ) ≤ (Work.KMTAreas.A7.uScale ρ U : ℝ) := by
        exact_mod_cast Work.KMTAreas.A7.one_le_uScale ρ hρ.le U
      have hkey := sep_arithGNoGSB hd2 hm1 hpow1
        (by linarith : (C₂ / 2 + 2) * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
          ≤ (Work.KMTAreas.A7.uScale ρ U : ℝ))
      linarith
    have hpowpos : (0:ℝ) < (2:ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) :=
      zpow_pos (by norm_num) _
    have hz1 : (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)))
        = 2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) := by
      rw [show (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) : ℤ)
            = (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) + 1 by ring,
        zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]
      ring
    have h4 : (4 : ℝ) * (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1)
        = (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) + 1) := by
      rw [show (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) + 1 : ℤ)
            = (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) + 2 by ring,
        zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      norm_num
      ring
    have hlt : (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)))
          + (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)))
        < (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) + 1) := by
      rw [← h4, hz1]
      linarith
    have hle : (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) + 1)
        ≤ (2 : ℝ) ^ (-(C₂ * (2 : ℝ) ^ (ρ * (l₂ : ℝ)))) := by
      rw [← Real.rpow_intCast]
      apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr
      push_cast
      linarith
    have hsepl := hsep l₂ hα hβ hne
    linarith
  exact ⟨hN1, hrad, hnA, hΦ, hsepU⟩

end Work.A6Clean
