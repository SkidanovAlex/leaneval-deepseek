import Mathlib
import Submission.Work.KMTPlan.A6.LowpassVarOnCore
import Submission.Work.KMTPlan.A6.iwQl_mul_le_splitCut
import Submission.Work.Analysis.Lp.summableNormRpowOfLtTop
import Submission.Work.KMTPlan.A6.lowpassSmallHeightShiftG
import Submission.Work.KMTPlan.A6.gclVarEstimateOfClip
import Submission.Port.Aesm

set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-! ## The clipped `g`-side low-pass estimate from its two regimes

The `g`-side low-pass family of the model slice is `n ↦ Tle ρ l (varphitildeN d ⌊a n⌋ 0) g`, which
by `Work.KMTAreas.A7Hi2.Tle_varphitildeN_zero` and `Work.KMTAreas.A7.lpf` is the *monotone
re-indexing* of the Ionescu--Wainger walk `m ↦ lpf ρ l M m g = kmtProj ρ l (-(M+m)) g` at the
levels `d · logN ⌊a n⌋` (whose *level* spacing is `d·(logN ⌊a n⌋ - logN ⌊a m⌋)`, so repetitions are
harmless: the re-indexing is only required to be monotone).

The A6 core clip `1_{core ∧ Farey}` removes the whole *shallow* part of that walk: at the first
core-and-Farey index `n₀`,

* either `L₁(ρ) ≤ l`, and then `24 · iwQl ρ l ≤ splitCut ρ L < ⌊a n₀⌋`
  (`Work.KMTPlan.A6.iwQl_mul_le_splitCut`), which puts **every** level of the clipped walk in the
  *decimation* regime (`Work.KMTPlan.A6.walkDecimVarBound`, the `l`-free bound of the deep walk);
* or `l < L₁(ρ)`, and the height is *bounded*, so the elementary supremum + chain-part route
  applies with a constant depending only on `(ρ, L₁(ρ))`.

Both regimes are taken here as hypotheses (`hdec`, `hsh`), so this lemma is the *assembly* only and
carries no deep input.  The same dichotomy is what closed the `f`-side low-pass case in
`Submission/Work/KMTPlan/A6/MdlLowpassCaseHighOfDecim.lean`. -/
/-- The clipping set `core ∧ Farey(·,0)` of the *unmodulated* `g`-side family is a tail. -/
private theorem coreFareyZero_iff_le_zero {ρ Cρc : ℝ} {C₀ l₁ l₂ k₁ k₂ : ℕ} {a : ℕ → NNReal}
    (hamono : Monotone a)
    (h : ∃ n, Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
      Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n) :
    ∃ n₀, ∀ n, (Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
      Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n) ↔ n₀ ≤ n := by
  classical
  refine ⟨Nat.find h, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · by_contra hcon
    rw [not_le] at hcon
    exact Nat.find_min h hcon hn
  · exact ⟨Work.KMTAreas.A7.core_mono hamono hn (Nat.find_spec h).1,
      Work.KMTAreas.A7.farey_mono hamono hn (Nat.find_spec h).2⟩

theorem lowpassVarGClipBound_of_inputs (d : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))) (Λ : NNReal) (hΛ : 1 < Λ)
    (r : NNReal) (hr : 2 < r) (pR : ℝ) (hpR : 1 < pR)
    (hsumm : ∀ g : ℤ → ℂ, MeasureTheory.eLpNorm g (ENNReal.ofReal pR)
        MeasureTheory.Measure.count < ⊤ → Summable (fun k : ℤ => ‖g k‖ ^ pR))
    (L₁p : ℕ)
    (harith : ∀ (L l : ℕ), L₁p ≤ L → l ≤ L →
      24 * Work.Analysis.IonescuWainger.iwQl ρ l ≤ Work.KMTAreas.A7.splitCut ρ L)
    (hdec : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (m l : ℕ) (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) → ∀ g : ℤ → ℂ,
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
        (-(Work.Analysis.EndVar.logN (Nat.floor (a m)))) →
      24 * Work.Analysis.IonescuWainger.iwQl ρ l ≤ Nat.floor (a m) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l
            (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (n + m))) 0) g x))
          (ENNReal.ofReal pR) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm g (ENNReal.ofReal pR) MeasureTheory.Measure.count)
    (hsh : ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ K : ℝ, 0 < K ∧ ∀ (m l : ℕ) (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) → l ≤ L₁p → ∀ g : ℤ → ℂ,
      Summable (fun k : ℤ => ‖g k‖ ^ pR) →
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
        (-(Work.Analysis.EndVar.logN (Nat.floor (a m)))) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l
            (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (n + m))) 0) g x))
          (ENNReal.ofReal pR) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm g (ENNReal.ofReal pR)
            MeasureTheory.Measure.count) :
    ∃ CρcLow : ℝ, 0 < CρcLow ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (Cρc : ℝ), CρcLow ≤ Cρc →
        ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
          (l l₁ l₂ k₁ k₂ : ℕ) (hl : l ≤ l₂) (g : ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
              then Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0))
            (ENNReal.ofReal pR) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (3 * C * (1 + (l₂ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm g (ENNReal.ofReal pR) MeasureTheory.Measure.count := by
  classical
  obtain ⟨Cρ₁, hCρ₁pos, C₁, hC₁pos, hDec⟩ := hdec
  obtain ⟨Cρ₂, hCρ₂pos, K₂, hK₂pos, hSh⟩ := hsh
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp0 : (ENNReal.ofReal pR) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (lt_trans zero_lt_one hpR)
  have hpT : (ENNReal.ofReal pR) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨max Cρ₁ Cρ₂, lt_max_of_lt_left hCρ₁pos, max C₁ K₂, lt_max_of_lt_left hC₁pos, ?_⟩
  intro Cρc hCρc a ha ha1 l l₁ l₂ k₁ k₂ hl g
  have hCρ₁le : Cρ₁ ≤ Cρc := le_trans (le_max_left _ _) hCρc
  have hCρ₂le : Cρ₂ ≤ Cρc := le_trans (le_max_right _ _) hCρc
  by_cases htop : MeasureTheory.eLpNorm g (ENNReal.ofReal pR) MeasureTheory.Measure.count = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))]
    exact le_top
  · have hmem : Summable (fun k : ℤ => ‖g k‖ ^ pR) :=
      hsumm g (lt_top_iff_ne_top.mpr htop)
    by_cases hne : ∃ n : ℕ, Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
        Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
    · -- ## the clipped index set is a tail, from `n₀` on
      have hamono : Monotone a := monotone_of_lacunary hΛ ha ha1
      obtain ⟨n₀, hn₀⟩ := coreFareyZero_iff_le_zero hamono hne
      have hFarey₀ : Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n₀ := ((hn₀ n₀).mpr le_rfl).2
      have hcore₀ : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n₀ := ((hn₀ n₀).mpr le_rfl).1
      -- narrowness at the base gives good major arcs there, for both branch constants
      have hlogle : (-(Work.Analysis.EndVar.logN (Nat.floor (a n₀))) : ℤ)
          ≤ Work.KMTAreas.A7.fareyK Cρc ρ l₂ := by
        have h := hFarey₀
        simp only [Work.KMTAreas.A7.Farey] at h
        simpa using h
      have hgood₁ : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₁ l
          (-(Work.Analysis.EndVar.logN (Nat.floor (a n₀)))) := by
        have hK : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₁ l
            (Work.KMTAreas.A7.fareyK Cρc ρ l₂) :=
          Work.KMTAreas.A7.goodMajorArcs_fareyK hCρ₁le hCρ₁pos.le hρ.le hl
        simp only [Work.Analysis.IonescuWainger.GoodMajorArcs] at hK ⊢
        have h2 : ((-(Work.Analysis.EndVar.logN (Nat.floor (a n₀))) : ℤ) : ℝ)
            ≤ ((Work.KMTAreas.A7.fareyK Cρc ρ l₂ : ℤ) : ℝ) := by exact_mod_cast hlogle
        linarith
      have hgood₂ : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₂ l
          (-(Work.Analysis.EndVar.logN (Nat.floor (a n₀)))) := by
        have hK : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₂ l
            (Work.KMTAreas.A7.fareyK Cρc ρ l₂) :=
          Work.KMTAreas.A7.goodMajorArcs_fareyK hCρ₂le hCρ₂pos.le hρ.le hl
        simp only [Work.Analysis.IonescuWainger.GoodMajorArcs] at hK ⊢
        have h2 : ((-(Work.Analysis.EndVar.logN (Nat.floor (a n₀))) : ℤ) : ℝ)
            ≤ ((Work.KMTAreas.A7.fareyK Cρc ρ l₂ : ℤ) : ℝ) := by exact_mod_cast hlogle
        linarith
      -- the pointwise domination by the shifted family
      have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
              then Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0)
          ≤ 3 * PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x) := by
        intro x
        have hrewrite : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
              then Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0)
            = fun n : ℕ => if n < n₀ then 0
                else Work.KMTAreas.A7.Tle ρ l
                  (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (n - n₀ + n₀))) 0) g x := by
          funext n
          by_cases hn : n < n₀
          · have hnf : ¬ (Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n) :=
              fun hcon => absurd ((hn₀ n).mp hcon) (not_le.mpr hn)
            rw [if_neg hnf, if_pos hn]
          · have hle : n₀ ≤ n := le_of_not_gt hn
            have hf : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n := (hn₀ n).mpr hle
            rw [if_pos hf, if_neg hn, Nat.sub_add_cancel hle]
        rw [hrewrite]
        exact Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le hr1 n₀
          (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
            (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x)
      -- the bound for the shifted family, in the two regimes
      have hshbound : MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x))
            (ENNReal.ofReal pR) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((max C₁ K₂) * (1 + (l : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm g (ENNReal.ofReal pR) MeasureTheory.Measure.count := by
        rcases le_total L₁p l with hbig | hsl
        · -- the *decimation* regime: the base scale exceeds the lattice of the height
          have hL₁p_le_L : L₁p ≤ max (max l₁ l₂) (max k₁ k₂) :=
            le_trans (le_trans hbig hl) (le_trans (le_max_right _ _) (le_max_left _ _))
          have hl_le_L : l ≤ max (max l₁ l₂) (max k₁ k₂) :=
            le_trans hl (le_trans (le_max_right _ _) (le_max_left _ _))
          have hlarge : 24 * Work.Analysis.IonescuWainger.iwQl ρ l ≤ Nat.floor (a n₀) :=
            le_of_lt (lt_of_le_of_lt (harith _ _ hL₁p_le_L hl_le_L) hcore₀.2.1)
          refine (hDec n₀ l a ha ha1 g hgood₁ hlarge).trans ?_
          have hconstle : ENNReal.ofReal (C₁ * (1 + (l : ℝ)) ^ 2)
              ≤ ENNReal.ofReal ((max C₁ K₂) * (1 + (l : ℝ)) ^ 2) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left C₁ K₂) (by positivity))
          exact mul_le_mul' hconstle le_rfl
        · -- the *bounded height* regime
          have hsl' : l ≤ L₁p := hsl
          refine (hSh n₀ l a ha ha1 hsl' g hmem hgood₂).trans ?_
          have hconstle : ENNReal.ofReal K₂
              ≤ ENNReal.ofReal ((max C₁ K₂) * (1 + (l : ℝ)) ^ 2) :=
            ENNReal.ofReal_le_ofReal (by
              have h1 : (1 : ℝ) ≤ (1 + (l : ℝ)) ^ 2 := by
                nlinarith [Nat.cast_nonneg (α := ℝ) l]
              calc K₂ ≤ max C₁ K₂ := le_max_right C₁ K₂
                _ = max C₁ K₂ * 1 := (mul_one _).symm
                _ ≤ max C₁ K₂ * (1 + (l : ℝ)) ^ 2 :=
                    mul_le_mul_of_nonneg_left h1 (le_trans hK₂pos.le (le_max_right C₁ K₂)))
          exact mul_le_mul' hconstle le_rfl
      -- assemble the clipping constant
      have hstep1 : MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                  Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
                then Work.KMTAreas.A7.Tle ρ l
                  (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0))
            (ENNReal.ofReal pR) MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm (fun x : ℤ => (3 : ENNReal) *
              PointwiseErgodicTheorems.variationalNorm r
                (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                  (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x))
            (ENNReal.ofReal pR) MeasureTheory.Measure.count :=
        MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (μ := MeasureTheory.Measure.count)
          (p := ENNReal.ofReal pR) hpt
      have hstep2 : MeasureTheory.eLpNorm (fun x : ℤ => (3 : ENNReal) *
              PointwiseErgodicTheorems.variationalNorm r
                (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                  (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x))
            (ENNReal.ofReal pR) MeasureTheory.Measure.count
          = 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                  (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x))
            (ENNReal.ofReal pR) MeasureTheory.Measure.count :=
        Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
          (V := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
              (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x))
          (μ := MeasureTheory.Measure.count) (c := (3 : ENNReal))
          (p := ENNReal.ofReal pR) (by norm_num) hp0 hpT
      have h3mul : (3 : ENNReal) * (ENNReal.ofReal ((max C₁ K₂) * (1 + (l : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm g (ENNReal.ofReal pR) MeasureTheory.Measure.count)
          = ENNReal.ofReal (3 * ((max C₁ K₂) * (1 + (l : ℝ)) ^ 2)) *
              MeasureTheory.eLpNorm g (ENNReal.ofReal pR) MeasureTheory.Measure.count := by
        rw [show (3 : ENNReal) = ENNReal.ofReal (3 : ℝ) by norm_num, ← mul_assoc,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      have hArith : 3 * ((max C₁ K₂) * (1 + (l : ℝ)) ^ 2)
          ≤ 3 * (max C₁ K₂) * (1 + (l₂ : ℝ)) ^ 2 := by
        have hl' : (l : ℝ) ≤ (l₂ : ℝ) := by exact_mod_cast hl
        have hsq : (1 + (l : ℝ)) ^ 2 ≤ (1 + (l₂ : ℝ)) ^ 2 := by nlinarith
        have hCpos : (0 : ℝ) < max C₁ K₂ := lt_max_of_lt_left hC₁pos
        nlinarith [hsq, hCpos.le]
      calc MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                    Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
                  then Work.KMTAreas.A7.Tle ρ l
                    (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0))
              (ENNReal.ofReal pR) MeasureTheory.Measure.count
          ≤ MeasureTheory.eLpNorm (fun x : ℤ => (3 : ENNReal) *
              PointwiseErgodicTheorems.variationalNorm r
                (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                  (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x))
              (ENNReal.ofReal pR) MeasureTheory.Measure.count := hstep1
        _ = 3 * MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm r
                (fun m : ℕ => Work.KMTAreas.A7.Tle ρ l
                  (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (m + n₀))) 0) g x))
              (ENNReal.ofReal pR) MeasureTheory.Measure.count := hstep2
        _ ≤ 3 * (ENNReal.ofReal ((max C₁ K₂) * (1 + (l : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm g (ENNReal.ofReal pR) MeasureTheory.Measure.count) :=
              mul_le_mul_of_nonneg_left hshbound zero_le
        _ = ENNReal.ofReal (3 * ((max C₁ K₂) * (1 + (l : ℝ)) ^ 2)) *
              MeasureTheory.eLpNorm g (ENNReal.ofReal pR) MeasureTheory.Measure.count := h3mul
        _ ≤ ENNReal.ofReal (3 * (max C₁ K₂) * (1 + (l₂ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm g (ENNReal.ofReal pR) MeasureTheory.Measure.count :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal hArith) le_rfl
    · -- ## no core-and-Farey index: the clipped family vanishes
      have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
              then Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0)) = 0 := by
        funext x
        have hfam : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
              then Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0)
            = (0 : ℕ → ℂ) := by
          funext n
          rw [if_neg (fun hcon => hne ⟨n, hcon⟩)]
          rfl
        have h0 : PointwiseErgodicTheorems.variationalNorm r (0 : ℕ → ℂ) = 0 := by
          have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul
            (r := r) hr1 (0 : ℂ) (0 : ℕ → ℂ)
          simpa using h
        rw [hfam, h0]
        rfl
      rw [hzero, MeasureTheory.eLpNorm_zero]
      exact zero_le


/-! ## The deep-walk reindexing at a general exponent, and the `g`-side decimation regime -/

/-- **The monotone reindexing of the deep walk preserves the unconditional variational bound**, at a
general real exponent `p > 1` (the `p = 2` case is `Work.KMTPlan.A6.walkVarOfMonotoneReindex`). -/
private theorem walkVarOfMonotoneReindexG (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (R : NNReal)
    (hR : 2 < R) (p : ℝ) (hp : 1 < p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l C₀ : ℕ) (σ : ℕ → ℕ), Monotone σ → (∀ n : ℕ, 1 ≤ σ n) → ∀ f : ℤ → ℂ,
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(C₀ : ℤ)) →
        3 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ C₀ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (σ n) f x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count := by
  obtain ⟨Cρ, hCρpos, C, hCpos, hwalk⟩ := walkDecimVarBound ρ hρ hρ1 R hR p hp
  refine ⟨Cρ, hCρpos, C, hCpos, ?_⟩
  intro l C₀ σ hσmono hσ1 f hgood hnarrow
  have hid : ∀ n : ℕ, 1 + (σ n - 1) = σ n := fun n => by have h1 := hσ1 n; omega
  have hfun : ∀ x : ℤ, (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (σ n) f x)
      = (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + (σ n - 1)) f x) := by
    intro x; funext n; rw [hid n]
  have hcomp : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + (σ n - 1)) f x)
      ≤ PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x) := by
    intro x
    exact Work.KMTAreas.A7.variationalNorm_comp_mono_le (r := R)
      (u := fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x)
      (φ := fun n : ℕ => σ n - 1) (fun i j hij => Nat.sub_le_sub_right (hσmono hij) 1)
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (σ n) f x)
      ≤ PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (1 + n) f x) := by
    intro x
    exact (congrArg (fun w : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm R w)
      (hfun x)).le.trans (hcomp x)
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (μ := MeasureTheory.Measure.count)
    (p := ENNReal.ofReal p) (fun x => hpt x)).trans (hwalk l C₀ hgood hnarrow f)

/-- The `g`-side low-pass family at a base scale dominating the Ionescu--Wainger lattice is deep,
so the whole walk is bounded by `Work.KMTPlan.A6.walkDecimVarBound`. -/
private theorem lowpassVarDecimShiftAux (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d : ℕ) (hd : 1 ≤ d)
    (R : NNReal) (hR : 2 < R) (p : ℝ) (hp : 1 < p) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (m l : ℕ) (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) → ∀ g : ℤ → ℂ,
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l
        (-(Work.Analysis.EndVar.logN (Nat.floor (a m)))) →
      24 * Work.Analysis.IonescuWainger.iwQl ρ l ≤ Nat.floor (a m) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l
            (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (n + m))) 0) g x))
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨Cρw, hCρwpos, Cw, hCwpos, hwalk⟩ := walkVarOfMonotoneReindexG ρ hρ hρ1 R hR p hp
  refine ⟨Cρw + 1, by linarith, Cw, hCwpos, ?_⟩
  intro m l a ha ha1 g hgood hbig
  have hmono : Monotone a := monotone_of_lacunary hΛ ha ha1
  have hfloor : Monotone (fun n : ℕ => Nat.floor (a n)) :=
    fun n m' hnm => Nat.floor_mono (hmono hnm)
  have hlogmono : Monotone (fun n : ℕ => Work.Analysis.EndVar.logN (Nat.floor (a n))) :=
    fun n m' hnm => Work.Analysis.EndVar.logN_mono (hfloor hnm)
  set L : ℕ := (Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat with hLdef
  have hLcoe : ((L : ℕ) : ℤ) = Work.Analysis.EndVar.logN (Nat.floor (a m)) :=
    Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
  have hlt : Nat.floor (a m) < 2 ^ (L + 1) := by
    have h1 : max (Nat.floor (a m)) 2 < 2 ^ (Nat.log 2 (max (Nat.floor (a m)) 2) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num) _
    have h2 : L = Nat.log 2 (max (Nat.floor (a m)) 2) := by
      rw [hLdef, Work.Analysis.EndVar.logN]
      exact Int.toNat_natCast _
    rw [h2]
    exact lt_of_le_of_lt (le_max_left _ _) h1
  have hQ1 : 1 ≤ Work.Analysis.IonescuWainger.iwQl ρ l := by
    have h := Work.Analysis.IonescuWainger.iwQl_pos (ρ := ρ) (l := l); omega
  have h12 : 12 * Work.Analysis.IonescuWainger.iwQl ρ l ≤ 2 ^ L := by
    have h1 : 24 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ (L + 1) := lt_of_le_of_lt hbig hlt
    rw [pow_succ] at h1
    omega
  have hL1 : 1 ≤ L := by
    have h12' : 12 ≤ 2 ^ L := le_trans (by omega) h12
    by_contra hcon
    have h0 : L = 0 := by omega
    rw [h0] at h12'
    norm_num at h12'
  set C₀ : ℕ := d * L - 1 with hC₀def
  have hdL : L ≤ d * L := by
    have := Nat.mul_le_mul_right L hd
    simpa using this
  have hC₀ge : L - 1 ≤ C₀ := by omega
  have hC₀eq : C₀ + 1 = d * L := by omega
  have hgood' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρw l (-(C₀ : ℤ)) := by
    have hle : (-(C₀ : ℤ) : ℤ) ≤ -((L : ℕ) : ℤ) + 1 := by omega
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hgoodR : -((L : ℕ) : ℝ) ≤ -(Cρw + 1) * (2 : ℝ) ^ (ρ * (l : ℝ)) := by
      have h := hgood
      simp only [Work.Analysis.IonescuWainger.GoodMajorArcs] at h
      rw [← hLcoe] at h
      push_cast at h
      exact h
    have h3 : -((C₀ : ℕ) : ℝ) ≤ -((L : ℕ) : ℝ) + 1 := by
      have h := hle
      push_cast at h
      exact_mod_cast h
    simp only [Work.Analysis.IonescuWainger.GoodMajorArcs]
    push_cast
    nlinarith [hgoodR, h3, h1]
  have hnarrow : 3 * Work.Analysis.IonescuWainger.iwQl ρ l < 2 ^ C₀ := by
    have hpow : 2 ^ (L - 1) ≤ 2 ^ C₀ := Nat.pow_le_pow_right (by norm_num) hC₀ge
    have h6 : 6 * Work.Analysis.IonescuWainger.iwQl ρ l ≤ 2 ^ (L - 1) := by
      have h2 : 2 ^ L = 2 ^ (L - 1) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      have h12' : 12 * Work.Analysis.IonescuWainger.iwQl ρ l ≤ 2 ^ (L - 1) * 2 := by
        rw [← h2]
        exact h12
      have h12'' : (6 * Work.Analysis.IonescuWainger.iwQl ρ l) * 2
          ≤ (2 ^ (L - 1)) * 2 := by
        rw [show (6 * Work.Analysis.IonescuWainger.iwQl ρ l) * 2
          = 12 * Work.Analysis.IonescuWainger.iwQl ρ l by ring]
        exact h12'
      omega
    have hpos := Work.Analysis.IonescuWainger.iwQl_pos (ρ := ρ) (l := l)
    omega
  -- ## the reindexing of the `d`-scaled levels into the walk
  set σ : ℕ → ℕ :=
    fun n => d * (Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))).toNat - C₀ with hσdef
  have hσmono : Monotone σ := by
    intro n n' hnn'
    have h1 : Nat.floor (a (n + m)) ≤ Nat.floor (a (n' + m)) := hfloor (by omega)
    have h2 : Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a (n' + m))) :=
      Work.Analysis.EndVar.logN_mono h1
    have h3 : (Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))).toNat
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a (n' + m)))).toNat :=
      Int.toNat_le_toNat h2
    simp only [hσdef]
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_left d h3) C₀
  have hσ1 : ∀ n : ℕ, 1 ≤ σ n := by
    intro n
    have h1 : Nat.floor (a m) ≤ Nat.floor (a (n + m)) := hfloor (Nat.le_add_left m n)
    have h2 : L ≤ (Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))).toNat := by
      rw [hLdef]
      exact Int.toNat_le_toNat (Work.Analysis.EndVar.logN_mono h1)
    simp only [hσdef]
    have h3 : d * L ≤ d * (Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))).toNat :=
      Nat.mul_le_mul_left d h2
    omega
  -- the family identity
  have hfam : ∀ x : ℤ, (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l
        (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (n + m))) 0) g x)
      = (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (σ n) g x) := by
    intro x
    funext n
    rw [Work.KMTAreas.A7Hi2.Tle_varphitildeN_zero]
    show Work.KMTContract.kmtProj ρ l (-((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (n + m))))) g x
      = Work.KMTContract.kmtProj ρ l (-(((C₀ : ℤ)) + (σ n : ℤ))) g x
    have hL'coe : (((Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))).toNat : ℕ) : ℤ)
        = Work.Analysis.EndVar.logN (Nat.floor (a (n + m))) :=
      Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
    have hle' : C₀ ≤ d * (Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))).toNat := by
      have h1 : Nat.floor (a m) ≤ Nat.floor (a (n + m)) := hfloor (Nat.le_add_left m n)
      have h2 : L ≤ (Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))).toNat := by
        rw [hLdef]
        exact Int.toNat_le_toNat (Work.Analysis.EndVar.logN_mono h1)
      have h3 : d * L ≤ d * (Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))).toNat :=
        Nat.mul_le_mul_left d h2
      have h4 : C₀ < d * L := by omega
      omega
    have harg : (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a (n + m)))
        = (C₀ : ℤ) + (σ n : ℤ) := by
      simp only [hσdef]
      rw [Nat.cast_sub hle', Nat.cast_mul]
      rw [hL'coe]
      ring
    rw [harg]
  have hμ : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l
          (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a (n + m))) 0) g x))
      = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7Hi.lpf ρ l C₀ (σ n) g x) := by
    funext x
    exact congrArg (fun w : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm R w) (hfam x)
  rw [hμ]
  refine (hwalk l C₀ σ hσmono hσ1 g hgood' hnarrow).trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have h1 : (1 : ℝ) ≤ (1 + (l : ℝ)) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) l]
  calc Cw = Cw * 1 := (mul_one _).symm
    _ ≤ Cw * (1 + (l : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left h1 hCwpos.le

/-! ## The clipped `g`-side low-pass estimate, crux-free

Assembling `lowpassVarGClipBound_of_inputs` with the two proved regime bounds — the *decimation*
regime `lowpassVarDecimShiftAux` above (equivalently the delegated
`Work.KMTPlan.A6.lowpassVarDecimShiftG`) and the bounded-height regime
`Work.KMTPlan.A6.lowpassSmallHeightShiftG` — and the `ℓᵖ`-summability transfer
`Work.Analysis.Lp.summableNormRpowOfLtTop`. -/
theorem lowpassVarGClipDecim (d : ℕ) (hd : 1 ≤ d) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))) (Λ : NNReal) (hΛ : 1 < Λ)
    (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ CρcLow : ℝ, 0 < CρcLow ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (Cρc : ℝ), CρcLow ≤ Cρc →
        ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
          (l l₁ l₂ k₁ k₂ : ℕ) (hl : l ≤ l₂) (g : ℤ → ℂ),
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n ∧
                Work.KMTAreas.A7.Farey Cρc ρ l₂ 0 a n
              then Work.KMTAreas.A7.Tle ρ l
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) g x else 0))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (3 * C * (1 + (l₂ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  have hpR0 : (0 : ℝ) < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one hp)) (ne_of_lt hptop)
  have hpR : 1 < p.toReal := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  have hpeq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal (ne_of_lt hptop)
  obtain ⟨L₁p, harith⟩ := iwQl_mul_le_splitCut ρ hρ hρ1
  obtain ⟨Cρ₁, hCρ₁pos, C₁, hC₁pos, hDec⟩ :=
    lowpassVarDecimShiftAux ρ hρ hρ1 d hd r hr p.toReal hpR Λ hΛ
  obtain ⟨Cρ₂, hCρ₂pos, K₂, hK₂pos, hSh⟩ :=
    lowpassSmallHeightShiftG ρ hρ hρ1 d hd r hr p.toReal hpR Λ hΛ L₁p
  obtain ⟨CρcLow, hCρcLowpos, C, hCpos, hmain⟩ :=
    lowpassVarGClipBound_of_inputs d ρ hρ hρ1 C₀ hC₀ hρC Λ hΛ r hr p.toReal hpR
      (fun g hg => Work.Analysis.Lp.summableNormRpowOfLtTop g p.toReal hpR hg)
      L₁p harith ⟨Cρ₁, hCρ₁pos, C₁, hC₁pos, hDec⟩
      ⟨Cρ₂, hCρ₂pos, K₂, hK₂pos, hSh⟩
  refine ⟨CρcLow, hCρcLowpos, C, hCpos, fun Cρc hCρc a ha ha1 l l₁ l₂ k₁ k₂ hl g => ?_⟩
  have h := hmain Cρc hCρc a ha ha1 l l₁ l₂ k₁ k₂ hl g
  simpa only [hpeq] using h

theorem MdlSliceLowpassGDecim (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (R : NNReal) (hR : 2 < R) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ (Λ : NNReal) (hΛ : 1 < Λ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
        (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ))),
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ : ℕ) (t : ℝ) (g : ℤ → ℂ),
            PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            t ∈ Set.Icc (1 / 2 : ℝ) 1 →
            MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
                (fun n : ℕ =>
                  if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ 0 n then
                    Work.KMTAreas.A7.Tle ρ l₂
                      (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t)
                      (Work.KMTPlan.A6.mdlG ρ P
                        (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ 0))) l₂ g) x
                  else 0)) 2 MeasureTheory.Measure.count
              ≤ ENNReal.ofReal C * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ 0) *
                  MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  MdlSliceLowpassG_of_gcl
    (fun P hd => gclVarEstimateOfClip P hd
      (fun ρ hρ hρ1 C₀ hC₀ hρC Λ hΛ r hr p hp hptop =>
        lowpassVarGClipDecim P.natDegree (by omega) ρ hρ hρ1 C₀ hC₀ hρC Λ hΛ r hr p hp hptop))
    P hd C₀ hC₀ R hR

end Work.KMTPlan.A6
