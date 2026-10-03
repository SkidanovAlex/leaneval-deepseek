import Mathlib
import Submission.Work.A7Hi.fiberBumpPositivity
import Submission.Work.KMTPlan.A6Clean.MdlWindowLiftF
import Submission.Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large

namespace Work.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal NNReal


/-! ## The regime hypotheses of the model window-piece lift, *without* the good-scale hypothesis
## and with a **`ρ`-only** threshold `B`

`Work.A6Clean.MdlWindowLiftRegime` (PROVED) derives the five regime hypotheses `hN`, `hrad`,
`hnA`, `hΦ`, `hsepU` of `Work.KMTPlan.A6Clean.mdlWindowLiftF` from the model data
`mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n` **and** the good-scale hypothesis
`goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) ⌊a n⌋`.

Inspection of that proof shows the good-scale hypothesis is *never used*: only the scale cut
`splitCut ρ U < ⌊a n⌋` (a conjunct of `mdlCore`) enters the narrow-band inequality `hrad`, and the
good-major-arcs conditions behind `hnA`, `hΦ`, `hsepU` come from
`exists_goodMajorArcs_nonAliasing` and `iw_height_separated` applied at the scale count
`uScale ρ U` itself.  So the same five conclusions hold from `mdlCore` alone.

Moreover the threshold `B` of the regime may be taken to depend on `ρ` **only**: the numerical
input `uScale_regimeNoGSB` and the two good-major-arcs thresholds `B₁`, `B₂` are `ρ`-only, and the
hypotheses `l₁ ≤ U`, `k₁ ≤ U` used against them are consequences of `U = lcL l₁ l₂ k₁ k₂` itself,
never of the threshold.  Hence `∃ B, ∀ (all the data), …` — which is what the constant bookkeeping
of a consumer needs: the case threshold `B` enters `Cin` *before* the datum is fixed.

The proof is that of `Work.A6Clean.MdlWindowLiftRegimeNoGS` transported verbatim, with the
quantifier over the datum pulled inside (the helper lemmas being `private`, they are restated
here). -/

/-- `(n+1)^2 ≤ 2 ^ (2^n - 1)` for `n ≥ 3`. -/
private lemma two_pow_pred_ge_sqNoGSB (n : ℕ) (hn : 3 ≤ n) : (n+1)^2 ≤ 2^(2^n - 1) := by
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
private lemma two_pow_pred_ge_linNoGSB (n : ℕ) (hn : 3 ≤ n) : 8*2^n + 2 ≤ 2^(2^n - 1) := by
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
private lemma real_sq_le_two_powNoGSB (s : ℝ) (hs : 3 ≤ s) :
    s^2 ≤ (2:ℝ)^((2:ℝ)^s - 1) := by
  set n : ℕ := ⌊s⌋₊ with hn
  have hn3 : 3 ≤ n := Nat.le_floor hs
  have hslt : s < (n:ℝ) + 1 := Nat.lt_floor_add_one s
  have h1 : s^2 ≤ ((n:ℝ)+1)^2 := by nlinarith
  have h2a : ((n:ℝ)+1)^2 ≤ (2:ℝ)^(2^n - 1) := by
    have h := two_pow_pred_ge_sqNoGSB n hn3
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
private lemma real_lin_le_two_powNoGSB (s : ℝ) (hs : 3 ≤ s) :
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
    have h := two_pow_pred_ge_linNoGSB n hn3
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

/-- **The scale count dominates `U + 2·uScale ρ U + 1` exponentially.**  There is a constant `B`
depending only on `ρ > 0` such that for every `U ≥ B`,
`U + 2·uScale ρ U + 1 ≤ 2 ^ uScale ρ U`. -/
private theorem uScale_regimeNoGSB (ρ : ℝ) (hρ : 0 < ρ) :
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
  have hsq := real_sq_le_two_powNoGSB s hs3
  have hlin := real_lin_le_two_powNoGSB s hs3
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

/-- **The regime hypotheses of the model window-piece lift, with no good-scale hypothesis.**

`Work.KMTPlan.A6Clean.mdlWindowLiftF` needs, at every scale `n` with
`mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n`, the five conditions

  `hN : 1 ≤ ⌊a n⌋`,
  `hrad : 2 ^ (k₁ - logN ⌊a n⌋) ≤ 2 ^ (-(2 * uScale ρ U) - 1)`,
  `hnA : NonAliasing (-(uScale ρ U : ℤ)) (iwArithFreqs ρ l₁)`,
  `hΦ : SupportedInArc (-(uScale ρ U : ℤ) - 1) (periodize (varphiNtj ⌊a n⌋ k₁ j₁ t))`,
  `hsepU : ∀ α ≠ β ∈ iwArithFreqs ρ l₁, 2 ^ (-(2 * uScale ρ U)) + 2 ^ (k₁ - logN ⌊a n⌋) < ‖α - β‖`

(`U = lcL l₁ l₂ k₁ k₂`, `logN = Work.Analysis.EndVar.logN`), with a constant `B` depending on `ρ`
only, away from the finitely many small scales `lcL l₁ l₂ k₁ k₂ < B`.  This is
`Work.A6Clean.MdlWindowLiftRegime` with the (superfluous) good-scale hypothesis removed and the
threshold made `ρ`-only: the scale cut `splitCut ρ U < ⌊a n⌋` inside `mdlCore` alone gives `hrad`,
and the good-major-arcs conditions behind `hnA`, `hΦ`, `hsepU` are those at the scale count
`uScale ρ U`. -/
theorem MdlWindowLiftRegimeNoGSB (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) : ∃ B : ℕ, ∀ (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal) (hΛ : 1 < Λ) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1) (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (n : ℕ), Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → l₁ ≠ 0 → B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ → (1 ≤ Nat.floor (a n)) ∧ ((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) ≤ (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) - 1)) ∧ Work.Analysis.IonescuWainger.NonAliasing (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)) (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) ∧ Work.Analysis.IonescuWainger.SupportedInArc (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ) - 1) (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)) ∧ (∀ ⦃α β : Work.Analysis.IonescuWainger.Circle⦄, α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ → β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ → α ≠ β → (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))) + (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) < ‖α - β‖) := by
  obtain ⟨B₀, hB₀⟩ := uScale_regimeNoGSB ρ hρ
  obtain ⟨Cρ₁, hCρ₁, hNA⟩ :=
    Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing hρ
  obtain ⟨B₁, hB₁⟩ := Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large ρ hρ Cρ₁ hCρ₁
  obtain ⟨C₂, hC₂, hsep⟩ := Work.Analysis.IonescuWainger.iw_height_separated hρ
  obtain ⟨B₂, hB₂⟩ := Work.KMTPlan.A6Clean.goodMajorArcs_uScale_of_large ρ hρ (C₂ / 2 + 2) (by linarith)
  refine ⟨max B₀ (max B₁ B₂), ?_⟩
  intro C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ j₁ hj₁ hk₁ t ht n hcore hl₁ hB
  set U : ℕ := Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ with hUdef
  set N : ℕ := Nat.floor (a n) with hNdef
  have hB0 : B₀ ≤ U := le_trans (le_max_left _ _) hB
  have hB1' : B₁ ≤ U := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB2' : B₂ ≤ U := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  obtain ⟨hin, hcut, hmain⟩ :=
    (Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hcore
  have hk₁U : k₁ ≤ U := by
    rw [hUdef, Work.KMTPlan.A6.lcL]
    exact le_trans (le_max_left k₁ k₂) (le_max_right (max l₁ l₂) (max k₁ k₂))
  have hl₁U : l₁ ≤ U := by
    rw [hUdef, Work.KMTPlan.A6.lcL]
    exact le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max k₁ k₂))
  -- (1) `1 ≤ N`
  have hN1 : 1 ≤ N := by
    rw [hNdef]
    exact Nat.le_floor (by exact_mod_cast ha1 n)
  -- (2) the narrow band inequality
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
  have hexp : (k₁ : ℤ) + 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ) + 1
      ≤ Work.Analysis.EndVar.logN N := by
    have h1 : (k₁ : ℤ) ≤ (U : ℤ) := by exact_mod_cast hk₁U
    have h2 : ((U : ℤ) + 2 * (Work.KMTAreas.A7.uScale ρ U : ℤ) + 1)
        ≤ (2 ^ Work.KMTAreas.A7.uScale ρ U : ℤ) := by exact_mod_cast hnum
    linarith
  have hrad : (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
      ≤ (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) := by
    rw [← Real.rpow_intCast]
    apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr
    have h : (k₁ : ℝ) + 2 * (Work.KMTAreas.A7.uScale ρ U : ℝ) + 1
        ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by
      exact_mod_cast hexp
    push_cast
    linarith
  -- (3) the non-aliasing
  have hnA : Work.Analysis.IonescuWainger.NonAliasing
      (-(Work.KMTAreas.A7.uScale ρ U : ℤ))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) :=
    hNA l₁ (-(Work.KMTAreas.A7.uScale ρ U : ℤ)) (hB₁ l₁ U hl₁U hB1').1
  -- (4) the arc support
  have hΦ : Work.Analysis.IonescuWainger.SupportedInArc
      (-(Work.KMTAreas.A7.uScale ρ U : ℤ) - 1)
      (Work.Analysis.IonescuWainger.periodize (Work.KMTPlan.A6.varphiNtj N k₁ j₁ t)) := by
    obtain ⟨_, _, _, _, harc⟩ :=
      Work.KMTPlan.A6.varphiNtjPeriodize_aux N k₁ j₁ t hj₁ hk₁ hN1
    intro ξ hξ
    obtain ⟨θ, hθabs, hθeq⟩ := harc ξ hξ
    refine ⟨θ, ?_, ?_⟩
    · have hstep : (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1)
          ≤ (2 : ℝ) ^ (-(Work.KMTAreas.A7.uScale ρ U : ℤ) - 1) := by
        rw [zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)]
        omega
      have habs : |θ| ≤ (2 : ℝ) ^ (-(Work.KMTAreas.A7.uScale ρ U : ℤ) - 1) :=
        le_trans (le_trans hθabs hrad) hstep
      rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc, ← abs_le]
      exact habs
    · simpa using hθeq.symm
  -- (5) the separation
  have hsepU : ∀ ⦃α β : Work.Analysis.IonescuWainger.Circle⦄,
      α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ →
      β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ → α ≠ β →
      (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)))
        + (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
        < ‖α - β‖ := by
    intro α β hα hβ hne
    have hgm := (hB₂ l₁ U hl₁U hB2').1
    have hCl : C₂ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))
        ≤ 2 * (Work.KMTAreas.A7.uScale ρ U : ℝ) - 1 := by
      rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at hgm
      push_cast at hgm
      have hpow1 : (1:ℝ) ≤ (2:ℝ) ^ (ρ * (l₁ : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      nlinarith [hgm, hpow1]
    have hsepl := hsep l₁ hα hβ hne
    have hpowpos : (0:ℝ) < (2:ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) :=
      zpow_pos (by norm_num) _
    have hz1 : (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)))
        = 2 * (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) := by
      rw [show (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) : ℤ)
            = (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) + 1 by ring,
        zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one]
      ring
    have h4 : (4 : ℝ) * (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1)
        = (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) + 1) := by
      rw [show (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) + 1 : ℤ)
            = (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) - 1) + 2 by ring,
        zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
      norm_num
      ring
    have hlt : (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)))
          + (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN N : ℤ) : ℝ))
        < (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) + 1) := by
      rw [← h4, hz1]
      linarith
    have hle : (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ U : ℤ)) + 1)
        ≤ (2 : ℝ) ^ (-(C₂ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))) := by
      rw [← Real.rpow_intCast]
      apply (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr
      push_cast
      linarith
    linarith
  exact ⟨hN1, hrad, hnA, hΦ, hsepU⟩

end Work.A6Clean
