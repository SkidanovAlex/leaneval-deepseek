/-
# `Work.KMTPlan.A6.slicesTwoLe` — the `ℓ²` bounds for the two frozen slices

This module proves the `ℓ²` bounds for the two packet families of the frozen-`t` slice

  `mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n`
     `= if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then T^{l₁}_{φ_{N,t,j₁}} (Π_{l₁,≤-u} f) else 0`,
  `mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n`
     `= if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then T^{l₂}_{φ̃_{N,t,j₂}} (Π_{l₂,≤-du} g) else 0`

(`N = ⌊a n⌋`, `u = uScale ρ (lcL l₁ l₂ k₁ k₂)`) with a constant `C` depending only on
`(P, ρ, B)`: for all `l₁ l₂ k₁ k₂` with `lcL l₁ l₂ k₁ k₂ ≤ B`,

  `‖mdlSliceF … n‖_{ℓ²(ℤ)} ≤ C ‖f‖_{ℓ²(ℤ)}`,  `‖mdlSliceG … n‖_{ℓ²(ℤ)} ≤ C ‖g‖_{ℓ²(ℤ)}`.

This is step 4 of the plan of `MdlSliceBadPart`; its inputs are all already in the tree:

* `tleTwoLeOfPeriodizeBound` (the `ℓ²` bound of the IW multiplier `T^l_φ` by the sup norm of the
  periodisation of `φ` times the cardinality of `iwArithFreqs ρ l`),
* `mdlF_two_le` / `mdlG_two_le_uniform` (the `ℓ²` bounds of the two model inputs `Π_{l,≤-u} f`,
  `Π_{l,≤-du} g`, uniform in the scale),
* `varphiNtj_arc_ssu` / `varphitildeNtj_arc_ssu` (`mainRegime` forces `k ≤ Log N`, so the bumps are
  supported in an arc of length `≤ 1`),
* `norm_varphiNtj_le_eight` / `varphitildeNtjPointwise` (the pointwise bounds `8`, `Cb`).

The one elementary observation which makes the periodisation bounds cheap is
`norm_periodize_le_three_mul`: a function supported in `|ξ| ≤ 1` has periodisation bounded by
`3 ‖φ‖_∞`, because at most the three shifts `-1, 0, 1` can contribute.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs
import Submission.Work.KMTPlan.A6.MdlSliceSsuGain
import Submission.Work.KMTPlan.A6.mdlF_two_le
import Submission.Work.KMTPlan.A6.mdlG_two_le_uniform
import Submission.Work.KMTPlan.A6.tleTwoLeOfPeriodizeBound
import Submission.Work.KMTPlan.A6.periodizeVarphitildeNtjBound

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

noncomputable section

/-! ## Unfoldings of the two slices -/

/-- Unfolding of the `f`-side slice at a fixed index `n`. -/
lemma mdlSliceF_apply (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ)
    (f : ℤ → ℂ) (n : ℕ) :
    mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n =
      if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
        Work.KMTAreas.A7.Tle ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t)
          (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f)
      else 0 := rfl

/-- Unfolding of the `g`-side slice at a fixed index `n`. -/
lemma mdlSliceG_apply (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (g : ℤ → ℂ) (n : ℕ) :
    mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n =
      if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
        Work.KMTAreas.A7.Tle ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
          (mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)
      else 0 := rfl

/-! ## The periodisation of a function supported in the unit ball -/

/-- **A function supported in the closed unit ball and bounded by `C` has periodisation bounded by
`3 C`.**  For the representative `x ∈ [0,1)` of a point of the circle, a shift `k` can only
contribute if `|x + k| ≤ 1`, which forces `k ∈ {-1, 0, 1}`: for `k ≥ 2` we have
`x + k ≥ 2 > 1`, and for `k ≤ -2` we have `|x + k| = -(x + k) ≥ 2 - x > 1`. -/
lemma norm_periodize_le_three_mul {φ : ℝ → ℂ} {C : ℝ}
    (hsupp : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ 1) (hC : ∀ ξ : ℝ, ‖φ ξ‖ ≤ C)
    (y : Circle) : ‖periodize φ y‖ ≤ 3 * C := by
  have hzero : ∀ k : ℤ, k ∉ ({-1, 0, 1} : Finset ℤ) →
      φ (circleRep y + (k : ℝ)) = 0 := by
    intro k hk
    by_contra hne
    have hgt : 1 < |circleRep y + (k : ℝ)| := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      have hx0 : 0 ≤ circleRep y := circleRep_nonneg y
      have hx1 : circleRep y < 1 := circleRep_lt_one y
      by_cases hk2 : 2 ≤ k
      · have hk2' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
        rw [abs_of_nonneg (by linarith)]
        linarith
      · have h2 : k ≤ -2 := by omega
        have h2' : (k : ℝ) ≤ -2 := by exact_mod_cast h2
        rw [abs_of_nonpos (by linarith)]
        linarith
    exact absurd (hsupp _ hne) (not_le.mpr hgt)
  rw [periodize]
  change ‖∑' k : ℤ, φ (circleRep y + (k : ℝ))‖ ≤ 3 * C
  rw [tsum_eq_sum (s := ({-1, 0, 1} : Finset ℤ)) hzero]
  calc ‖∑ k ∈ ({-1, 0, 1} : Finset ℤ), φ (circleRep y + (k : ℝ))‖
      ≤ ∑ k ∈ ({-1, 0, 1} : Finset ℤ), ‖φ (circleRep y + (k : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ ({-1, 0, 1} : Finset ℤ), C := Finset.sum_le_sum fun k _ => hC _
    _ = 3 * C := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : (({-1, 0, 1} : Finset ℤ).card : ℝ) = 3 := by
          have h3 : ({-1, 0, 1} : Finset ℤ).card = 3 := by decide
          rw [h3]; norm_num
        rw [hc]

/-! ## The main regime bounds the height by `Log N` -/

/-- **In the main regime the continuous height is at most `Log N`.**  Indeed
`mainRegime ρ k₁ k₂ N` gives `k + 2 uScale ρ (max k₁ k₂) ≤ (Log N).toNat` and
`1 ≤ uScale ρ (max k₁ k₂)`, so `k + 2 ≤ (Log N).toNat ≤ Log N`. -/
lemma le_logN_of_mainRegime {ρ : ℝ} (hρ : 0 ≤ ρ) {k₁ k₂ N : ℕ}
    (h : Work.KMTAreas.A7.mainRegime ρ k₁ k₂ N) :
    (k₁ : ℤ) ≤ logN N ∧ (k₂ : ℤ) ≤ logN N := by
  have h2 : ((logN N).toNat : ℤ) ≤ logN N := by
    have h0 : (0 : ℤ) ≤ logN N := by rw [logN]; exact Int.natCast_nonneg _
    calc ((logN N).toNat : ℤ) = logN N := Int.toNat_of_nonneg h0
      _ ≤ logN N := le_rfl
  have key : ∀ k : ℕ, k + 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂)
      ≤ (logN N).toNat → (k : ℤ) ≤ logN N := by
    intro k hk
    have hu : 1 ≤ Work.KMTAreas.A7.uScale ρ (max k₁ k₂) := one_le_uScale_ssu ρ hρ _
    have h1 : k + 2 ≤ (logN N).toNat := by omega
    have h3 : (k : ℤ) + 2 ≤ ((logN N).toNat : ℤ) := by exact_mod_cast h1
    linarith
  exact ⟨key k₁ h.1, key k₂ h.2⟩

/-! ## The periodisation bounds for the two modified bumps -/

/-- **The periodisation of the modified `f`-side bump is bounded by `24`.**  By `mainRegime`
(`k ≤ Log N`) the bump is supported in `|ξ| ≤ 1` (`varphiNtj_arc_ssu` at `K = 0`) and it is
pointwise bounded by `8` (`norm_varphiNtj_le_eight`), so `norm_periodize_le_three_mul` gives
`3 · 8 = 24`. -/
lemma periodize_varphiNtj_le (N k : ℕ) (j : ℤ) (t : ℝ)
    (hj : j ∈ ({-1, 0, 1} : Finset ℤ)) (hk : k ≠ 0 ∨ 0 ≤ j) (hN : 1 ≤ N)
    (hlog : (k : ℤ) ≤ logN N) :
    ∀ y : Circle, ‖periodize (varphiNtj N k j t) y‖ ≤ 24 := by
  intro y
  refine le_trans (norm_periodize_le_three_mul (C := 8) ?_
    (fun ξ => norm_varphiNtj_le_eight N k j hj hk hN t ξ) y) ?_
  · intro ξ hξ
    have h := varphiNtj_arc_ssu N k j t 0 (by omega) ξ hξ
    simpa using h
  · norm_num

/-- **The periodisation of the modified `g`-side bump is bounded by `3 Cb`**, with `Cb` the
uniform pointwise bound of `varphitildeNtjPointwise`.  Same argument as for the `f`-side, with
`varphitildeNtj_arc_ssu` at `K = 0`. -/
lemma periodize_varphitildeNtj_le (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {Cb : ℝ}
    (hCb : ∀ (N k : ℕ) (j : ℤ) (t : ℝ), j ∈ ({-1, 0, 1} : Finset ℤ) →
      ¬ (k = 0 ∧ j = -1) → 1 ≤ N → ∀ ξ : ℝ,
        ‖varphitildeNtj P N k j t ξ‖ ≤ Cb)
    (N k : ℕ) (j : ℤ) (t : ℝ) (hj : j ∈ ({-1, 0, 1} : Finset ℤ))
    (hkj : ¬ (k = 0 ∧ j = -1)) (hN : 1 ≤ N) (hlog : (k : ℤ) ≤ logN N) :
    ∀ y : Circle, ‖periodize (varphitildeNtj P N k j t) y‖ ≤ 3 * Cb := by
  intro y
  refine norm_periodize_le_three_mul (C := Cb)
    (fun ξ hξ => ?_) (fun ξ => hCb N k j t hj hkj hN ξ) y
  have h := varphitildeNtj_arc_ssu P (by omega) N k j t 0 ?_ ξ hξ
  · simpa using h
  · have hd0 : (0 : ℤ) ≤ (P.natDegree : ℤ) := Int.natCast_nonneg _
    have hsub : (k : ℤ) - logN N ≤ 0 := by omega
    exact mul_nonpos_of_nonneg_of_nonpos hd0 hsub

/-! ## The two `ℓ²` bounds -/

theorem slicesTwoLe (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (C₀ : ℕ) (a : ℕ → NNReal) (ha1 : ∀ n, 1 ≤ a n)
      (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ))
      (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1) (hk₂ : k₂ = 0 → j₂ ≠ -1)
      (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f g : ℤ → ℂ) (n : ℕ),
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B →
      (MeasureTheory.eLpNorm (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) 2
          MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ∧
      (MeasureTheory.eLpNorm (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) 2
          MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
  obtain ⟨Cb, hCb0, hCb⟩ := (varphitildeNtjPointwise P hd).1
  obtain ⟨Cg, hCg0, hCg⟩ := mdlG_two_le_uniform P hd ρ hρ hρ1
  set Q : ℕ := Work.KMTAreas.A7.arithQ ρ B with hQeq
  set Cf : ℝ := 2 * (1 + 2 * (Q : ℝ) ^ 2) with hCfeq
  set ncd : ℝ := ((iwArithFreqs ρ B).card : ℝ) with hnCdeq
  set Cmax : ℝ :=
    max 1 (max (ncd * 24 * Cf) (ncd * (3 * Cb) * (Cg * (1 + (B : ℝ))))) with hCmaxeq
  have hCmaxpos : 0 < Cmax := by
    rw [hCmaxeq]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCf0 : 0 ≤ Cf := by rw [hCfeq]; positivity
  have hncd0 : 0 ≤ ncd := by rw [hnCdeq]; positivity
  refine ⟨Cmax, hCmaxpos, ?_⟩
  intro C₀ a ha1 l₁ l₂ k₁ k₂ j₁ j₂ hj₁ hj₂ hk₁ hk₂ t ht f g n hlcL
  have hl₁B : l₁ ≤ B := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hlcL
  have hl₂B : l₂ ≤ B := le_trans (le_trans (le_max_right l₁ l₂) (le_max_left _ _)) hlcL
  have hLle : max (max l₁ l₂) (max k₁ k₂) ≤ B := hlcL
  -- the denominator bounds of `mdlF_two_le`
  have hQle : ∀ l' : ℕ, l' ≤ B → ∀ q ∈ iwP ρ l', q ≤ Q := by
    intro l' hl' q hq
    rw [hQeq]
    have hmem : q ∈ iwP ρ B := iwP_mono hρ hρ1 hl' hq
    have hpos : 0 < (iwP ρ B).lcm id := by
      rw [pos_iff_ne_zero]
      intro h0
      obtain ⟨x, hx, hx0⟩ := Finset.lcm_eq_zero_iff.mp h0
      exact (pos_of_mem_iwP hx).ne' hx0
    exact le_trans (Nat.le_of_dvd hpos (Finset.dvd_lcm hmem)) (le_max_right _ _)
  constructor
  · -- ## the `f`-side
    by_cases hcore : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · rw [mdlSliceF_apply, if_pos hcore]
      set N : ℕ := Nat.floor (a n) with hNeq
      set u : ℕ := Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) with hueq
      obtain ⟨-, -, hmain⟩ := (mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hcore
      rw [← hNeq] at hmain
      have hN1 : 1 ≤ N := by
        rw [hNeq]; exact (Nat.one_le_floor_iff (a n)).mpr (ha1 n)
      obtain ⟨hlog₁, -⟩ := le_logN_of_mainRegime hρ.le hmain
      have hper₁ : ∀ y : Circle, ‖periodize (varphiNtj N k₁ j₁ t) y‖ ≤ 24 :=
        periodize_varphiNtj_le N k₁ j₁ t hj₁ (ne_zero_or_nonneg_ssu hj₁ hk₁) hN1 hlog₁
      have hu1 : (2 : ℝ) ^ (-(u : ℤ)) ≤ 1 := by
        calc (2 : ℝ) ^ (-(u : ℤ)) ≤ (2 : ℝ) ^ (0 : ℤ) :=
              zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
          _ = 1 := zpow_zero 2
      have hcard0₁ : (0 : ℝ) < ((iwArithFreqs ρ l₁).card : ℝ) := by
        have hmem0 : (0 : Circle) ∈ iwArithFreqs ρ l₁ :=
          mem_iwArithFreqs.mpr ⟨1, one_mem_iwP ρ l₁, by simp⟩
        exact_mod_cast Finset.card_pos.mpr ⟨0, hmem0⟩
      by_cases hftop : eLpNorm f 2 Measure.count = ⊤
      · rw [hftop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hCmaxpos))]
        exact le_top
      · have hmem₁ : MemLp (periodize (varphiNtj N k₁ j₁ t)) ⊤ circleMeasure :=
          memLp_periodize_varphiNtj N k₁ j₁ t hj₁ (ne_zero_or_nonneg_ssu hj₁ hk₁) hN1 ht
        have hT : eLpNorm (Work.KMTAreas.A7.Tle ρ l₁ (varphiNtj N k₁ j₁ t)
              (mdlF ρ u l₁ f)) 2 Measure.count
            ≤ ENNReal.ofReal (((iwArithFreqs ρ l₁).card : ℝ) * 24)
              * eLpNorm (mdlF ρ u l₁ f) 2 Measure.count := by
          by_cases hFtop : eLpNorm (mdlF ρ u l₁ f) 2 Measure.count = ⊤
          · have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (((iwArithFreqs ρ l₁).card : ℝ) * 24) := by
              rw [ENNReal.ofReal_pos]
              exact mul_pos hcard0₁ (by norm_num)
            rw [hFtop, ENNReal.mul_top (ne_of_gt hpos)]
            exact le_top
          · have hFmem : MemLp (mdlF ρ u l₁ f) 2 Measure.count :=
              MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hFtop)
            exact tleTwoLeOfPeriodizeBound ρ l₁ (varphiNtj N k₁ j₁ t) 24 (by norm_num)
              hper₁ hmem₁ (mdlF ρ u l₁ f) hFmem
        have hF := mdlF_two_le ρ u l₁ Q (hQle l₁ hl₁B)
          (hQle (l₁ - 1) (le_trans (Nat.sub_le l₁ 1) hl₁B)) f
        have hcard₁ : ((iwArithFreqs ρ l₁).card : ℝ) ≤ ncd := by
          rw [hnCdeq]
          exact_mod_cast Finset.card_le_card (iwArithFreqs_mono hρ hρ1 hl₁B)
        have hA₁ : ((iwArithFreqs ρ l₁).card : ℝ) * 24 ≤ ncd * 24 :=
          mul_le_mul_of_nonneg_right hcard₁ (by norm_num)
        have hF' : eLpNorm (mdlF ρ u l₁ f) 2 Measure.count
            ≤ ENNReal.ofReal Cf * eLpNorm f 2 Measure.count := by
          refine le_trans hF (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
          rw [hCfeq]
          have hQ2 : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := sq_nonneg _
          nlinarith [hu1, hQ2]
        have hconst₁ : ((iwArithFreqs ρ l₁).card : ℝ) * 24 * Cf ≤ Cmax := by
          rw [hCmaxeq]
          refine le_trans (le_trans ?_ (le_max_left _ _)) (le_max_right 1 _)
          exact mul_le_mul_of_nonneg_right hA₁ hCf0
        refine le_trans hT ?_
        refine le_trans (mul_le_mul_right hF'
          (ENNReal.ofReal (((iwArithFreqs ρ l₁).card : ℝ) * 24))) ?_
        rw [← mul_assoc,
          ← ENNReal.ofReal_mul (p := ((iwArithFreqs ρ l₁).card : ℝ) * 24) (by positivity)]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hconst₁) _
    · rw [mdlSliceF_apply, if_neg hcore, eLpNorm_zero]
      exact bot_le
  · -- ## the `g`-side
    by_cases hcore : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
    · rw [mdlSliceG_apply, if_pos hcore]
      set N : ℕ := Nat.floor (a n) with hNeq
      set u : ℕ := Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) with hueq
      obtain ⟨-, -, hmain⟩ := (mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hcore
      rw [← hNeq] at hmain
      have hN1 : 1 ≤ N := by
        rw [hNeq]; exact (Nat.one_le_floor_iff (a n)).mpr (ha1 n)
      obtain ⟨-, hlog₂⟩ := le_logN_of_mainRegime hρ.le hmain
      have hkj₂ : ¬ (k₂ = 0 ∧ j₂ = -1) := fun h => hk₂ h.1 h.2
      have hper₂ : ∀ y : Circle, ‖periodize (varphitildeNtj P N k₂ j₂ t) y‖ ≤ 3 * Cb :=
        periodize_varphitildeNtj_le P hd hCb N k₂ j₂ t hj₂ hkj₂ hN1 hlog₂
      have hcard0₂ : (0 : ℝ) < ((iwArithFreqs ρ l₂).card : ℝ) := by
        have hmem0 : (0 : Circle) ∈ iwArithFreqs ρ l₂ :=
          mem_iwArithFreqs.mpr ⟨1, one_mem_iwP ρ l₂, by simp⟩
        exact_mod_cast Finset.card_pos.mpr ⟨0, hmem0⟩
      by_cases hgtop : eLpNorm g 2 Measure.count = ⊤
      · rw [hgtop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hCmaxpos))]
        exact le_top
      · have hmem₂ : MemLp (periodize (varphitildeNtj P N k₂ j₂ t)) ⊤ circleMeasure :=
          memLp_periodize_varphitildeNtj_ssu P hd N k₂ j₂ t
            (ne_zero_or_nonneg_ssu hj₂ hk₂) hN1 ht hj₂
        have hT : eLpNorm (Work.KMTAreas.A7.Tle ρ l₂ (varphitildeNtj P N k₂ j₂ t)
              (mdlG ρ P u l₂ g)) 2 Measure.count
            ≤ ENNReal.ofReal (((iwArithFreqs ρ l₂).card : ℝ) * (3 * Cb))
              * eLpNorm (mdlG ρ P u l₂ g) 2 Measure.count := by
          by_cases hGtop : eLpNorm (mdlG ρ P u l₂ g) 2 Measure.count = ⊤
          · have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (((iwArithFreqs ρ l₂).card : ℝ) * (3 * Cb)) := by
              rw [ENNReal.ofReal_pos]
              exact mul_pos hcard0₂ (by nlinarith [hCb0])
            rw [hGtop, ENNReal.mul_top (ne_of_gt hpos)]
            exact le_top
          · have hGmem : MemLp (mdlG ρ P u l₂ g) 2 Measure.count :=
              MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hGtop)
            exact tleTwoLeOfPeriodizeBound ρ l₂ (varphitildeNtj P N k₂ j₂ t) (3 * Cb)
              (by positivity) hper₂ hmem₂ (mdlG ρ P u l₂ g) hGmem
        have hG := hCg (max (max l₁ l₂) (max k₁ k₂)) l₂
          (le_trans (le_max_right l₁ l₂) (le_max_left _ _)) g
        have hcard₂ : ((iwArithFreqs ρ l₂).card : ℝ) ≤ ncd := by
          rw [hnCdeq]
          exact_mod_cast Finset.card_le_card (iwArithFreqs_mono hρ hρ1 hl₂B)
        have hA₂ : ((iwArithFreqs ρ l₂).card : ℝ) * (3 * Cb) ≤ ncd * (3 * Cb) :=
          mul_le_mul_of_nonneg_right hcard₂ (by nlinarith [hCb0])
        have hG' : eLpNorm (mdlG ρ P u l₂ g) 2 Measure.count
            ≤ ENNReal.ofReal (Cg * (1 + (B : ℝ))) * eLpNorm g 2 Measure.count := by
          refine le_trans hG (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
          have hl₂B' : (l₂ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hl₂B
          nlinarith [hCg0]
        have hconst₂ : ((iwArithFreqs ρ l₂).card : ℝ) * (3 * Cb) * (Cg * (1 + (B : ℝ))) ≤ Cmax := by
          rw [hCmaxeq]
          refine le_trans (le_trans ?_ (le_max_right _ _)) (le_max_right 1 _)
          exact mul_le_mul_of_nonneg_right hA₂ (by nlinarith [hCg0])
        refine le_trans hT ?_
        refine le_trans (mul_le_mul_right hG'
          (ENNReal.ofReal (((iwArithFreqs ρ l₂).card : ℝ) * (3 * Cb)))) ?_
        rw [← mul_assoc,
          ← ENNReal.ofReal_mul (p := ((iwArithFreqs ρ l₂).card : ℝ) * (3 * Cb))
            (by nlinarith [hCb0])]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hconst₂) _
    · rw [mdlSliceG_apply, if_neg hcore, eLpNorm_zero]
      exact bot_le

end

end Work.KMTPlan.A6
