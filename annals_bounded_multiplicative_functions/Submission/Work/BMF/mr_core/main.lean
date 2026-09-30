import Mathlib
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_core.goodPart_le
import Submission.Work.BMF.mr_core.badPart_le2
import Submission.Work.BMF.mr_core.smallT_le
import Submission.Work.BMF.mr_core.invPrimes_coarse_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.CoreInput` — assembly of the critical regime

This module proves `Work.BMF.CoreInput θ C₀`, the Matomäki–Radziwiłł input in the critical range
`Y/H ≤ T ≤ (2C₀/ε)·Y/H`, by assembling

* `Work.BMF.mr_core.goodPart_le` — the integral over the good set `𝒯₁` (fine Buchstab system /
  MR §8.1),
* `Work.BMF.mr_core.badPart_le` — the integral over the bad set `𝓤` (coarse Buchstab system /
  Halász + large values),
* `Work.BMF.mr_core.smallT_le` — the case `T ≤ 3`,
* `Work.BMF.mr_core.invPrimes_coarse_le` — the Mertens estimate for the coarse sieve loss,

together with the elementary splitting identity
`∫_{-2T}^{2T} = ∫_{goodSet} + ∫_{badSet}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.BMF

open MeasureTheory intervalIntegral Filter
open scoped BigOperators
open BoundedMultiplicativeFunctions

noncomputable section

/-- `dirPolyD a Y` is continuous in `t` (for `Y ≥ 1`, so that every `n ∈ natIcc Y (3Y)` is `≥ 1`). -/
lemma continuous_dirPolyD (a : ℕ → ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    Continuous fun t : ℝ => dirPolyD a Y t := by
  unfold dirPolyD
  refine continuous_finsetSum _ fun n hn => ?_
  have hn1 : 1 ≤ n := by
    rw [natIcc, Finset.mem_Icc] at hn
    have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
    have h1 : 1 ≤ ⌈Y⌉₊ := Nat.ceil_pos.mpr hY0
    omega
  exact continuous_const.mul (mr_direct.continuous_cpow_neg_one_sub hn1)

/-- **Splitting identity.**  `[-S,S]` is the disjoint union of the good set `𝒯₁` and the bad set
`𝓤`, so the integral of a continuous function splits accordingly. -/
lemma integral_Icc_eq_good_add_bad (ε : ℝ) (g : ℕ → ℂ) (Y S : ℝ) (hY : 1 ≤ Y) :
    (∫ t in Set.Icc (-S) S, ‖dirPolyD g Y t‖ ^ 2)
      = (∫ t in mrCore.goodSet ε g Y S, ‖dirPolyD g Y t‖ ^ 2)
        + (∫ t in mrCore.badSet ε g Y S, ‖dirPolyD g Y t‖ ^ 2) := by
  have hcont : Continuous fun t : ℝ => ‖dirPolyD g Y t‖ ^ 2 :=
    (continuous_dirPolyD g hY).norm.pow 2
  have hint : IntegrableOn (fun t : ℝ => ‖dirPolyD g Y t‖ ^ 2) (Set.Icc (-S) S) :=
    hcont.integrableOn_Icc
  have hsub : mrCore.goodSet ε g Y S ⊆ Set.Icc (-S) S := fun t ht => ht.1
  have hbad : mrCore.badSet ε g Y S = Set.Icc (-S) S \ mrCore.goodSet ε g Y S := by
    ext t
    simp [mrCore.badSet, Set.mem_sdiff]
  have hsd := MeasureTheory.setIntegral_sdiff (mrCore.measurableSet_goodSet ε g Y S) hint hsub
  have h2 : (∫ t in mrCore.badSet ε g Y S, ‖dirPolyD g Y t‖ ^ 2)
      = (∫ t in Set.Icc (-S) S, ‖dirPolyD g Y t‖ ^ 2)
        - (∫ t in mrCore.goodSet ε g Y S, ‖dirPolyD g Y t‖ ^ 2) := by
    rw [hbad]
    exact hsd
  rw [h2]
  ring

/-- The interval integral is the set integral over `Set.Icc`. -/
lemma intervalIntegral_eq_setIntegral_Icc (F : ℝ → ℝ) {a b : ℝ} (h : a ≤ b) :
    (∫ t in a..b, F t) = ∫ t in Set.Icc a b, F t := by
  rw [intervalIntegral.integral_of_le h, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **Assembly of the critical regime.** -/
theorem coreInput (θ C₀ : ℝ) (hC₀ : 0 < C₀) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    CoreInput θ C₀ := by
  intro ε hε
  set ε₁ : ℝ := min ε 1 with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε one_pos
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁le : ε₁ ≤ ε := min_le_left _ _
  ---- the three pieces
  have hgood_ev : ∀ᶠ Y in Filter.atTop, ∀ (g : ℕ → ℂ) (H T : ℝ),
      g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      Y ^ θ ≤ H → H ≤ Y → 3 ≤ T → Y / H ≤ T → T ≤ 2 * C₀ / ε₁ * (Y / H) →
      (Y / H) / T * (∫ t in mrCore.goodSet ε₁ g Y (2 * T), ‖dirPolyD g Y t‖ ^ 2)
        ≤ ε₁ / 8 :=
    mr_core.goodPart_le ε₁ C₀ θ hε₁ hε₁1 hC₀ hθ₀ hθ₁
  obtain ⟨Ygood, hYgood⟩ := Filter.eventually_atTop.1 hgood_ev
  obtain ⟨B₀, hB₀pos, hbad_ev⟩ := mr_core.badPart_le2 ε₁ C₀ θ hε₁ hε₁1 hC₀ hθ₀ hθ₁
  obtain ⟨Bs, Cs, Xs, hBs, hCs, hXs, hsmall⟩ := mr_core.smallT_le ε₁ hε₁
  ---- the constants
  set B : ℝ := max (max B₀ (1000 / ε₁)) (max Bs 5) with hBdef
  have hB_B₀ : B₀ ≤ B := le_trans (le_max_left _ _) (le_max_left _ _)
  have hB_1000 : 1000 / ε₁ ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
  have hB_Bs : Bs ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
  have hB5 : 5 ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
  have hBpos : 0 < B := by linarith
  have hBmax : max B₀ (1000 / ε₁) ≤ B := max_le hB_B₀ hB_1000
  -- the window constant `W` for the bad part (must dominate `W₀`, `8C₀/ε₁` and `Cs`)
  obtain ⟨W₀, hW₀pos, hbad_ev2⟩ := hbad_ev B hBmax
  set C : ℝ := max (max (8 * C₀ / ε₁ + 1) W₀) Cs with hCdef
  have hC_bad : 8 * C₀ / ε₁ + 1 ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC_W₀ : W₀ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC_small : Cs ≤ C := le_max_right _ _
  have hCpos : 0 < C := by
    have : (0 : ℝ) < 8 * C₀ / ε₁ + 1 := by positivity
    linarith
  -- the eventual bad-set statement for the chosen `B` and `W = C`
  have hbad_evB : ∀ᶠ Y in Filter.atTop, ∀ (g : ℕ → ℂ) (H T : ℝ),
      g 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
      Y ^ θ ≤ H → H ≤ Y → 3 ≤ T → Y / H ≤ T → T ≤ 2 * C₀ / ε₁ * (Y / H) →
      (∑ p ∈ primesIn (mrCore.Pc Y) (mrCore.Qc B Y), 1 / (p : ℝ)) ≤ B ^ 2 / 16 →
      (∀ u : ℝ, |u| ≤ C * Y / H →
        B ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
      (Y / H) / T * (∫ t in mrCore.badSet ε₁ g Y (2 * T), ‖dirPolyD g Y t‖ ^ 2)
        ≤ ε₁ / 8 :=
    hbad_ev2 C hC_W₀
  obtain ⟨Ybad, hYbad⟩ := Filter.eventually_atTop.1 hbad_evB
  ---- the threshold
  refine ⟨B, C, max 1 (max Ygood (max Ybad (max Xs (Real.exp (Real.exp (7 * B ^ 2)))))), hBpos,
    hCpos, le_max_left _ _, ?_⟩
  intro g hg1 hgmul hgb Y H T hY hYθ hHY hhyp hYT hTup
  have hY1 : 1 ≤ Y := le_trans (le_max_left _ _) hY
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY1
  have hYgood' : Ygood ≤ Y :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY
  have hYbad' : Ybad ≤ Y :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hY
  have hXs' : Xs ≤ Y :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hY
  have hexpB : Real.exp (Real.exp (7 * B ^ 2)) ≤ Y :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))) hY
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hYpos θ) hYθ
  have hH1 : 1 ≤ H := le_trans (Real.one_le_rpow hY1 (le_of_lt hθ₀)) hYθ
  have hρ1 : 1 ≤ Y / H := (one_le_div hHpos).mpr hHY
  have hρ0 : 0 ≤ Y / H := le_trans zero_le_one hρ1
  -- the distance hypothesis in the two windows used below
  have hhypCs : ∀ u : ℝ, |u| ≤ Cs * Y / H →
      Bs ≤ 𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y := by
    intro u hu
    refine le_trans hB_Bs (hhyp u (le_trans hu (div_le_div_of_nonneg_right ?_ hHpos.le)))
    exact mul_le_mul_of_nonneg_right hC_small hYpos.le
  have hTup' : T ≤ 2 * C₀ / ε₁ * (Y / H) := by
    refine le_trans hTup (mul_le_mul_of_nonneg_right ?_ hρ0)
    exact div_le_div_of_nonneg_left (by positivity) hε₁ hε₁le
  by_cases hT3 : T ≤ 3
  · have h := hsmall g Y H T hXs' hg1 hgmul hgb hρ1 hHY hhypCs hYT hT3
    linarith
  · push_neg at hT3
    have hgp := hYgood Y hYgood' g H T hg1 hgmul hgb hYθ hHY hT3.le hYT hTup'
    have hsieve : (∑ p ∈ primesIn (mrCore.Pc Y) (mrCore.Qc B Y), 1 / (p : ℝ))
        ≤ B ^ 2 / 16 := mr_core.invPrimes_coarse_le B Y hB5 hexpB
    have hbp := hYbad Y hYbad' g H T hg1 hgmul hgb hYθ hHY hT3.le hYT hTup'
      hsieve hhyp
    have hTpos : 0 < T := by linarith
    have hsplit : (∫ t in -(2 * T)..(2 * T), ‖dirPolyD g Y t‖ ^ 2)
        = (∫ t in mrCore.goodSet ε₁ g Y (2 * T), ‖dirPolyD g Y t‖ ^ 2)
          + (∫ t in mrCore.badSet ε₁ g Y (2 * T), ‖dirPolyD g Y t‖ ^ 2) := by
      rw [intervalIntegral_eq_setIntegral_Icc _ (by linarith : -(2 * T) ≤ 2 * T)]
      exact integral_Icc_eq_good_add_bad ε₁ g Y (2 * T) hY1
    have hlin : (Y / H) / T * (∫ t in -(2 * T)..(2 * T), ‖dirPolyD g Y t‖ ^ 2)
        = (Y / H) / T * (∫ t in mrCore.goodSet ε₁ g Y (2 * T), ‖dirPolyD g Y t‖ ^ 2)
          + (Y / H) / T * (∫ t in mrCore.badSet ε₁ g Y (2 * T), ‖dirPolyD g Y t‖ ^ 2) := by
      rw [hsplit]; ring
    rw [hlin]
    linarith

end

end Work.BMF
