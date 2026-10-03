/-
# Non-aliasing of the exact-height arithmetic frequencies at the scale `uScale ρ L`

This module proves that the exact-height Ionescu--Wainger frequency set
`diffFreqs ρ l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}` is non-aliasing at the (very small) arc
radius `2^{-3·uScale ρ L}`, uniformly in `l ≤ L` and for all `L` beyond a
`ρ`-dependent threshold.

The mathematics is the "good major arcs are non-aliasing" half of Theorem `thm:iw`
(`Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing`): non-aliasing holds
whenever the arc radius `2^k` is smaller than the separation `2^{-C_ρ 2^{ρl}}` of the
arithmetic frequencies, i.e. whenever `k ≤ -C_ρ 2^{ρl}`.  Since the scale
`uScale ρ L = ⌊2^{2ρL}⌋` dominates `2^{2ρL}/2`, the threshold `k = -3 uScale ρ L` is
small enough as soon as `C_ρ 2^{ρl} ≤ uScale ρ L`, which for `l ≤ L` follows from
`C_ρ < 2^{ρL}`, true for `L ≥ ⌈log₂(2 C_ρ)/ρ⌉ + 1`.

Note that `diffFreqs ρ l ⊆ (ℚ/ℤ)_{≤l}` *by definition* (no monotonicity of the
`iwArithFreqs` family in `ρ` is needed), so the restriction to the exact height level is
immediate and the argument applies for every `ρ > 0`, with no upper bound on `ρ`.

## Main result

* `Work.KMTPlan.A6.nonAliasing_diffFreqs`
-/
import Mathlib
import Submission.Work.KMTPlan.A6.iwArithFreqs_separated
import Submission.Work.KMTPlan.A6.two_mul_uScale_ge_rpow

namespace Work.KMTPlan.A6

/-- **A power of two eventually dominates any positive constant.**  For `ρ > 0` and `C > 0`
there is a threshold `B` with `C < 2^{ρL}` for every `L ≥ B`.  Explicitly
`B = ⌈log₂ C / ρ⌉ + 1`. -/
private lemma exists_rpow_gt (ρ : ℝ) (hρ : 0 < ρ) (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, ∀ L : ℕ, B ≤ L → C < (2 : ℝ) ^ (ρ * (L : ℝ)) := by
  refine ⟨⌈Real.logb 2 C / ρ⌉₊ + 1, ?_⟩
  intro L hL
  have hLe : ((⌈Real.logb 2 C / ρ⌉₊ : ℕ) : ℝ) < (L : ℝ) := by
    have h1 : ⌈Real.logb 2 C / ρ⌉₊ + 1 ≤ L := hL
    have h2 : ((⌈Real.logb 2 C / ρ⌉₊ + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast h1
    push_cast at h2
    linarith
  have hx : Real.logb 2 C / ρ < (L : ℝ) := lt_of_le_of_lt (Nat.le_ceil _) hLe
  have hlt : Real.logb 2 C < ρ * (L : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hx hρ
    rwa [mul_div_cancel₀ (Real.logb 2 C) (ne_of_gt hρ)] at hmul
  rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hC]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hlt

theorem nonAliasing_diffFreqs (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, ∀ L l : ℕ, B ≤ L → l ≤ L →
      Work.Analysis.IonescuWainger.NonAliasing (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)))
        (Work.KMTAreas.A7.diffFreqs ρ l) := by
  obtain ⟨Cρ, hCρpos, hNA⟩ :=
    Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing hρ
  obtain ⟨B, hB⟩ := exists_rpow_gt ρ hρ (2 * Cρ) (by linarith)
  refine ⟨B, ?_⟩
  intro L l hBL hlL
  -- the exact-height level sits inside the height-`≤ l` set, by definition
  have hsub : Work.KMTAreas.A7.diffFreqs ρ l
      ⊆ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
    by_cases h0 : l = 0
    · rw [Work.KMTAreas.A7.diffFreqs, if_pos h0, h0]
    · rw [Work.KMTAreas.A7.diffFreqs, if_neg h0]
      exact Finset.sdiff_subset
  refine fun α hα β hβ θ hθ θ' hθ' heq =>
    hNA l (-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ))) ?_
      α (hsub hα) β (hsub hβ) θ hθ θ' hθ' heq
  -- the good-major-arcs condition `-3 uScale ρ L ≤ -Cρ 2^{ρl}`
  rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
  have hApos : (0 : ℝ) < (2 : ℝ) ^ (ρ * (L : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hlL' : (l : ℝ) ≤ (L : ℝ) := by exact_mod_cast hlL
  have hexp : ρ * (l : ℝ) ≤ ρ * (L : ℝ) := by nlinarith [hρ.le]
  have hpow : (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have h2C : 2 * Cρ < (2 : ℝ) ^ (ρ * (L : ℝ)) := hB L hBL
  have hsq : (2 : ℝ) ^ (ρ * (L : ℝ)) * (2 : ℝ) ^ (ρ * (L : ℝ))
      = (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hucount : (2 : ℝ) ^ (2 * ρ * (L : ℝ))
      ≤ 2 * (Work.KMTAreas.A7.uScale ρ L : ℝ) :=
    two_mul_uScale_ge_rpow ρ hρ.le L
  have hkey : Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) < (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
    have hstep : Cρ * (2 : ℝ) ^ (ρ * (L : ℝ))
        < (2 : ℝ) ^ (ρ * (L : ℝ)) * (2 : ℝ) ^ (ρ * (L : ℝ)) / 2 := by
      have hneg : (2 * Cρ - (2 : ℝ) ^ (ρ * (L : ℝ))) * (2 : ℝ) ^ (ρ * (L : ℝ)) < 0 :=
        mul_neg_of_neg_of_pos (by linarith) hApos
      linarith
    have hstep' : Cρ * (2 : ℝ) ^ (ρ * (l : ℝ))
        ≤ Cρ * (2 : ℝ) ^ (ρ * (L : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow hCρpos.le
    rw [hsq] at hstep
    linarith
  have hcast : ((-(3 * (Work.KMTAreas.A7.uScale ρ L : ℤ)) : ℤ) : ℝ)
      = -(3 * (Work.KMTAreas.A7.uScale ρ L : ℝ)) := by
    push_cast
    ring
  rw [hcast]
  have husnn : (0 : ℝ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := Nat.cast_nonneg _
  linarith

end Work.KMTPlan.A6
