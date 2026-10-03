/-
# The defect case of the low-case model approximation, *narrow-window* variant (area A6)

This module works on the target

`Work.KMTPlan.A6.LowModApproxNoAliasingCaseU`,

the `-uScale`-window version of `Work.KMTPlan.A6.LowModApproxNoAliasingCase`: the defect
hypothesis uses non-aliasing at the *window* scale `-(uScale ρ L)` (the scale that the functional
calculus `bn-ident` and the fibre collapse of §6 actually need) instead of `-(2 · uScale ρ L)`.

## Structure of the proof

The proof follows the sibling `LowModApproxNoAliasingCase`, with the arithmetic adapted:

* **The arithmetic part** (`lcL_le_of_not_nonAliasingU`).  `¬ NonAliasing (-(uScale ρ L))`
  forces the height `L = lcL l₁ l₂ k₁ k₂` to be bounded by a constant depending only on `ρ`.
  The new ingredient with respect to the `-2·uScale` sibling is the *linear* count: the size
  test of the good-major-arcs theorem is `uScale ρ L ≥ Cna · 2^{ρ L}`, and since
  `2 · uScale ρ L ≥ 2^{2ρL}` (`rpow_le_two_mul_uScale`) it is enough to know
  `2 Cna < 2^{ρL}`, i.e. `L > logb 2 (2 Cna) / ρ`.
* **The plateau branch** (`lcL_le_of_plateauFail`, proved in the sibling module): the failure of
  the strict plateau at a core scale forces `lcL ≤ B(ρ)`.

Once the height is bounded, the estimate is the *bounded-height* variational bound for the two
operators of the model approximation, `Work.KMTAreas.A7.mainPartTuple` (concrete §5 column) and
`Work.KMTPlan.A6.mdlPart` (§6 model operator); the weight `lcWeight c l₁ l₂ k₁ k₂ ≥ 2^{-cB(ρ)}`
is then a constant and is absorbed into `K(Λ)`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.PieceLocal.ModelPiece
import Submission.Work.KMTPlan.A6.LowFix.mainPiece
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6.LowFix

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger

/-! ## The arithmetic of the first branch: non-aliasing at the *window* scale `-uScale ρ L`

The size test of the Ionescu--Wainger theorem `thm:iw` is
`(K : ℝ) + Cna · 2^{ρ l} < 0` (`K` the arc level, `l` the arithmetic height).  At the window
scale `K = -(uScale ρ L)` and the height `l = max l₁ l₂ ≤ L` this test is
`Cna · 2^{ρ max l₁ l₂} < uScale ρ L`, and since `2^{2ρL} ≤ 2 · uScale ρ L`, the *linear* bound
`2 Cna < 2^{ρL}` suffices.  This is strictly weaker than the estimate used for the
`-2 · uScale` sibling (where `Cna < 2^{ρL}` was needed for the *quadratic* comparison
`Cna · 2^{ρ max l} < 2^{ρL} · 2^{ρL} ≤ 2 uScale`). -/

/-- **Non-aliasing at the window scale forces a bounded height.**  If the good-major-arcs size
test `(K : ℝ) + Cna · 2^{ρl} < 0 → NonAliasing K ((ℚ/ℤ)_{≤l})` is available (a corollary of the
Ionescu--Wainger theorem `thm:iw`), then failure of non-aliasing at the *window* scale
`-(uScale ρ (lcL l₁ l₂ k₁ k₂))` of the union `(ℚ/ℤ)_{≤l₁} ∪ (ℚ/ℤ)_{≤l₂}` forces
`L = lcL l₁ l₂ k₁ k₂ ≤ ⌈logb 2 (2 Cna)/ρ⌉₊ + 1`. -/
theorem lcL_le_of_not_nonAliasingU (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (Cna : ℝ) (hCna : 0 < Cna)
    (hsize : ∀ (l : ℕ) (K : ℤ),
      (K : ℝ) + Cna * (2 : ℝ) ^ (ρ * (l : ℝ)) < 0 →
        Work.Analysis.IonescuWainger.NonAliasing K (Work.Analysis.IonescuWainger.iwArithFreqs ρ l))
    (l₁ l₂ k₁ k₂ : ℕ)
    (hna : ¬ Work.Analysis.IonescuWainger.NonAliasing
      (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)) :
    Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ ⌈Real.logb 2 (2 * Cna) / ρ⌉₊ + 1 := by
  by_contra h
  rw [not_le] at h
  set L : ℕ := Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ with hL
  -- `L ≥ ⌈logb 2 (2 Cna)/ρ⌉₊ + 2`
  have hceil : ((⌈Real.logb 2 (2 * Cna) / ρ⌉₊ : ℕ) : ℝ) < (L : ℝ) := by
    have h1 : ((⌈Real.logb 2 (2 * Cna) / ρ⌉₊ + 1 : ℕ) : ℝ) < ((L : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at h1
    linarith
  -- hence `logb 2 (2 Cna) < ρ L`
  have hlog : Real.logb 2 (2 * Cna) < ρ * (L : ℝ) := by
    have h1 : Real.logb 2 (2 * Cna) / ρ ≤ ((⌈Real.logb 2 (2 * Cna) / ρ⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h3 : Real.logb 2 (2 * Cna) / ρ < (L : ℝ) := lt_of_le_of_lt h1 hceil
    have h4 : ρ * (Real.logb 2 (2 * Cna) / ρ) < ρ * (L : ℝ) :=
      mul_lt_mul_of_pos_left h3 hρ
    rwa [mul_div_cancel₀ (Real.logb 2 (2 * Cna)) (ne_of_gt hρ)] at h4
  -- hence `2 Cna < 2^{ρL}`
  have hCna2 : 0 < 2 * Cna := by linarith
  have h2Cna : 2 * Cna < (2 : ℝ) ^ (ρ * (L : ℝ)) := by
    have hlogeq : (2 : ℝ) ^ Real.logb 2 (2 * Cna) = 2 * Cna :=
      Real.rpow_logb (by norm_num) (by norm_num) hCna2
    rw [← hlogeq]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hlog
  -- hence `Cna · 2^{ρ·max l₁ l₂} < uScale ρ L`
  have hMle : max l₁ l₂ ≤ L := by rw [hL]; exact le_max_left _ _
  have hMcast : max (l₁ : ℝ) (l₂ : ℝ) ≤ (L : ℝ) := by
    have h : ((max l₁ l₂ : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hMle
    rwa [Nat.cast_max] at h
  have hpowM : (2 : ℝ) ^ (ρ * max (l₁ : ℝ) (l₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by nlinarith [hρ.le, hMcast])
  have hprod : Cna * (2 : ℝ) ^ (ρ * max (l₁ : ℝ) (l₂ : ℝ))
      < (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
    have hposL : (0 : ℝ) < (2 : ℝ) ^ (ρ * (L : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hposM : (0 : ℝ) < (2 : ℝ) ^ (ρ * max (l₁ : ℝ) (l₂ : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hhalf : Cna < (2 : ℝ) ^ (ρ * (L : ℝ)) / 2 := by linarith
    have step1 : Cna * (2 : ℝ) ^ (ρ * max (l₁ : ℝ) (l₂ : ℝ))
        < ((2 : ℝ) ^ (ρ * (L : ℝ)) / 2) * (2 : ℝ) ^ (ρ * max (l₁ : ℝ) (l₂ : ℝ)) :=
      mul_lt_mul_of_pos_right hhalf hposM
    have step2 : ((2 : ℝ) ^ (ρ * (L : ℝ)) / 2) * (2 : ℝ) ^ (ρ * max (l₁ : ℝ) (l₂ : ℝ))
        ≤ ((2 : ℝ) ^ (ρ * (L : ℝ)) / 2) * (2 : ℝ) ^ (ρ * (L : ℝ)) :=
      mul_le_mul_of_nonneg_left hpowM (by positivity)
    have step : Cna * (2 : ℝ) ^ (ρ * max (l₁ : ℝ) (l₂ : ℝ))
        < ((2 : ℝ) ^ (ρ * (L : ℝ)) / 2) * (2 : ℝ) ^ (ρ * (L : ℝ)) :=
      lt_of_lt_of_le step1 step2
    -- `(2^{ρL}/2)·2^{ρL} = 2^{2ρL}/2`
    have hsq2 : (2 : ℝ) ^ (ρ * (L : ℝ)) * (2 : ℝ) ^ (ρ * (L : ℝ))
        = (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hsq : ((2 : ℝ) ^ (ρ * (L : ℝ)) / 2) * (2 : ℝ) ^ (ρ * (L : ℝ))
        = (2 : ℝ) ^ (2 * ρ * (L : ℝ)) / 2 := by
      calc ((2 : ℝ) ^ (ρ * (L : ℝ)) / 2) * (2 : ℝ) ^ (ρ * (L : ℝ))
          = ((2 : ℝ) ^ (ρ * (L : ℝ)) * (2 : ℝ) ^ (ρ * (L : ℝ))) / 2 := by ring
        _ = (2 : ℝ) ^ (2 * ρ * (L : ℝ)) / 2 := by rw [hsq2]
    rw [hsq] at step
    have hucount := rpow_le_two_mul_uScale ρ hρ.le L
    linarith [step, hucount]
  have hunion := iwArithFreqs_union_max hρ hρ1 l₁ l₂
  refine hna ?_
  rw [hunion]
  refine hsize (max l₁ l₂) (-(Work.KMTAreas.A7.uScale ρ L : ℤ)) ?_
  push_cast
  linarith [hprod]

/-! ## The reduction of the target to the two bounded-height estimates

Both branches of the defect hypothesis force the height `L = lcL l₁ l₂ k₁ k₂` to be bounded by a
constant depending only on `ρ`:

* the first branch is `lcL_le_of_not_nonAliasingU` above;
* the second branch is `Work.KMTPlan.A6.lcL_le_of_plateauFail` (proved in the sibling module).

Hence the estimate follows from the two *bounded-height* variational bounds
`MainPieceBoundedH` (the concrete §5 column `mainPartTuple`) and `ModelPieceBoundedH` (the §6 model
`mdlPart`), with the weight `lcWeight c` absorbed into `K(Λ)` because on the bounded range of
heights `lcWeight c l₁ l₂ k₁ k₂ ≥ 2^{-c·B(ρ)}`.

We take `c = 1` and `ρ₀ = 1`; the constants of the two bounded-height inputs at
`B(ρ) = max (⌈logb 2 (2 Cna)/ρ⌉₊ + 1) B₂(ρ)` are then absorbed with the factor `2^B`. -/

/-- **The target follows from the two bounded-height variational bounds.**  This is the sibling
`lowModApproxNoAliasingCase_of_boundedH` with the arithmetic of the *window* scale
(`lcL_le_of_not_nonAliasingU` in place of `lcL_le_of_not_nonAliasing`); the rest of the argument
(subadditivity of `variationalNorm`, the `ℒ¹` triangle inequality, the absorption of the weight
`2^{-L}` into `K(Λ)` on the bounded range of heights) is insensitive to the window. -/
theorem lowModApproxNoAliasingCaseU_of_boundedH (P : Polynomial ℤ) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ)
    (hmain : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ B : ℕ, MainPieceBoundedH P r C₀ ρ B)
    (hmdl : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ B : ℕ, ModelPieceBoundedH P r C₀ ρ B) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        (k₁ = 0 ∨ k₂ = 0) →
        (¬ (Work.Analysis.IonescuWainger.NonAliasing
              (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
                ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
          ∨ ∃ n : ℕ,
              Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
                  (Nat.floor (a n)) ∧
              Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) ∧
              Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) ∧
              ¬ (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
                  ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat)) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTPlan.A6.modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (Work.KMTPlan.A6.lcWeight c l₁ l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  refine ⟨1, one_pos, 1, one_pos, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨Cna, hCnaps, hna0⟩ := exists_goodMajorArcs_nonAliasing hρ
  have hsize : ∀ (l : ℕ) (K : ℤ),
      (K : ℝ) + Cna * (2 : ℝ) ^ (ρ * (l : ℝ)) < 0 → NonAliasing K (iwArithFreqs ρ l) := by
    intro l K hK
    refine hna0 l K ?_
    show (K : ℝ) ≤ -Cna * (2 : ℝ) ^ (ρ * (l : ℝ))
    linarith
  obtain ⟨B₂, hB₂⟩ := lcL_le_of_plateauFail ρ hρ
  set B : ℕ := max (⌈Real.logb 2 (2 * Cna) / ρ⌉₊ + 1) B₂ with hBdef
  obtain ⟨K₁, hK₁⟩ := hmain ρ hρ hρ1 B
  obtain ⟨K₂, hK₂⟩ := hmdl ρ hρ hρ1 B
  refine ⟨fun Λ => (K₁ Λ + K₂ Λ) * (2 : NNReal) ^ B, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ hdef
  have hLB : lcL l₁ l₂ k₁ k₂ ≤ B := by
    rcases hdef with hna | ⟨n, _hidx, hcut, _hreg, hfail⟩
    · refine le_trans (lcL_le_of_not_nonAliasingU ρ hρ hρ1 Cna hCnaps hsize l₁ l₂ k₁ k₂ hna) ?_
      rw [hBdef]; exact le_max_left _ _
    · refine le_trans (hB₂ C₀ a l₁ l₂ k₁ k₂ n hcut hfail) ?_
      rw [hBdef]; exact le_max_right _ _
  have e₁ := hK₁ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ
  have e₂ := hK₂ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ
  set Fm : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFm
  set Fd : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFd
  set Fe : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFe
  have hpt : ∀ x : ℤ, Fe x ≤ Fm x + Fd x := by
    intro x
    have hsub : (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          - (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
      funext n
      rfl
    simp only [hFe, hFm, hFd]
    rw [hsub]
    exact variationalNorm_sub_le' hr1 _ _
  have hmono : eLpNorm (fun x : ℤ => Fe x) 1 Measure.count
      ≤ eLpNorm (fun x : ℤ => Fm x + Fd x) 1 Measure.count :=
    eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
  have hadd : eLpNorm (fun x : ℤ => Fm x + Fd x) 1 Measure.count
      ≤ eLpNorm Fm 1 Measure.count + eLpNorm Fd 1 Measure.count :=
    eLpNorm_add_le le_rfl
  have hgain : (1 : ENNReal) ≤ ENNReal.ofReal ((2 : ℝ) ^ (B : ℝ))
      * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) := by
    rw [lcWeight_one_eq_lcL, ← ENNReal.ofReal_one, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (one_le_two_pow_mul B (lcL l₁ l₂ k₁ k₂) hLB)
  have h2B : (((2 : NNReal) ^ B : NNReal) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ (B : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast
    rw [Real.rpow_natCast]
  have hcoef : ((K₁ Λ + K₂ Λ : NNReal) : ENNReal)
      ≤ (((K₁ Λ + K₂ Λ) * (2 : NNReal) ^ B : NNReal) : ENNReal)
          * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) := by
    rw [ENNReal.coe_mul, h2B, mul_assoc]
    calc ((K₁ Λ + K₂ Λ : NNReal) : ENNReal)
        = ((K₁ Λ + K₂ Λ : NNReal) : ENNReal) * 1 := (mul_one _).symm
      _ ≤ ((K₁ Λ + K₂ Λ : NNReal) : ENNReal)
            * (ENNReal.ofReal ((2 : ℝ) ^ (B : ℝ))
              * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)) := mul_le_mul' le_rfl hgain
      _ = ((K₁ Λ + K₂ Λ : NNReal) : ENNReal)
            * (ENNReal.ofReal ((2 : ℝ) ^ (B : ℝ))
              * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)) := by ring
  calc eLpNorm (fun x : ℤ => Fe x) 1 Measure.count
      ≤ eLpNorm (fun x : ℤ => Fm x + Fd x) 1 Measure.count := hmono
    _ ≤ eLpNorm Fm 1 Measure.count + eLpNorm Fd 1 Measure.count := hadd
    _ ≤ (K₁ Λ : ENNReal) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
        + (K₂ Λ : ENNReal) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count :=
        add_le_add (by simpa only [hFm] using e₁) (by simpa only [hFd] using e₂)
    _ = ((K₁ Λ + K₂ Λ : NNReal) : ENNReal)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
        push_cast
        ring
    _ ≤ ((((K₁ Λ + K₂ Λ) * (2 : NNReal) ^ B : NNReal)) : ENNReal)
          * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
        exact mul_le_mul' (mul_le_mul' hcoef le_rfl) le_rfl

/-- **The defect case of the low-case model approximation (narrow window).** -/
theorem LowModApproxNoAliasingCaseU (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        (k₁ = 0 ∨ k₂ = 0) →
        (¬ (Work.Analysis.IonescuWainger.NonAliasing
              (-(Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ))
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
                ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
          ∨ ∃ n : ℕ,
              Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
                  (Nat.floor (a n)) ∧
              Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) ∧
              Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) ∧
              ¬ (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
                  ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat)) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTPlan.A6.modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (Work.KMTPlan.A6.lcWeight c l₁ l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
  lowModApproxNoAliasingCaseU_of_boundedH P r hr C₀
    (fun ρ hρ hρ1 B =>
      Work.KMTPlan.A6.LowFix.mainPiece P hd r hr C₀ hC₀ hA1 ρ hρ hρ1 B)
    (fun ρ hρ hρ1 B =>
      Work.KMTPlan.A6.PieceLocal.modelPiece P hd r hr C₀ hC₀ hA1 ρ hρ hρ1 B)

end

end Work.KMTPlan.A6.LowFix
