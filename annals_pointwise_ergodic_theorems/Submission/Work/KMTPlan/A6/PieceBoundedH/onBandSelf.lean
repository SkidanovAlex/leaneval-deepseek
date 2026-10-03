/-
# Fallback proof of the on-band half of `Work.KMTPlan.A6.PieceBoundedH.errorBound`

The delegated module `Submission/Work/KMTPlan/A6/PieceBoundedH/errorBoundOnBand.lean` states the
on-band half; this module contains an independent proof of the *same* statement (under the name
`onBandSelf`, so that the two can coexist).  It is used by `errorBound.lean` only if the delegated
statement turns out to be unavailable.

The proof runs entirely through the proved, `AreaA1`-free machinery:

* `Work.KMTAreas.A7.RepMassBound` — the `ℓ¹(ℤ²)`-mass of the §6 kernel difference, available for
  `0 < ρ ≤ 1` (no `ρ ≤ 1/(4C₀)` and no `AreaA1`);
* `Work.KMTAreas.A7.repSingleScale` — the single-scale bound on the band (exponent
  `(2⁻¹+2⁻¹)⁻¹ = 1` at `p₁ = p₂ = 2`);
* the height bound `lcL ≤ B` makes the weight uniform (`Work.KMTPlan.A6.PieceBoundedH.lmaxR_le_of_lcL_le`
  and `Work.KMTAreas.A7.repWeight`);
* `Work.KMTAreas.A7.invFloor_tsum_le` — the lacunary reciprocal sum.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.PieceBoundedH.errorBoundAux

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.PieceBoundedH

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- **The main (finite-norm) case of the on-band bound.** -/
private theorem onBandBound_main (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) (A D : ℝ) (hD : 0 < D)
    (hmassHyp : Work.KMTAreas.A7.RepMassHyp P A ρ D) (W : ℝ) (hW0 : 0 ≤ W)
    (hWbound : ∀ l₁ l₂ k₁ k₂ : ℕ, lcL l₁ l₂ k₁ k₂ ≤ B →
      Work.KMTAreas.A7.repWeight A ρ l₁ l₂ k₁ k₂ ≤ W)
    (Dts : NNReal → ℝ) (hDtsb : ∀ (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      Summable (fun n : ℕ => (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) ∧
        (∑' n : ℕ, (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) ≤ Dts Λ)
    (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ m, 1 ≤ a m)
    (l₁ l₂ k₁ k₂ : ℕ) (hLB : lcL l₁ l₂ k₁ k₂ ≤ B) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (f g : ℤ → ℂ) (hfmem : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hgmem : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
            ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
          Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          else 0))
      1 MeasureTheory.Measure.count
      ≤ (((⌈4 * (4 * D * W) * Dts Λ⌉₊ + 1 : NNReal)) : ENNReal)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hfBd : Work.KMTAreas.A5.BoundedZ f :=
    Work.KMTAreas.A5.boundedZ_of_memLp (p := 2) (by norm_num) hfmem
  have hgBd : Work.KMTAreas.A5.BoundedZ g :=
    Work.KMTAreas.A5.boundedZ_of_memLp (p := 2) (by norm_num) hgmem
  set A2 : ENNReal := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count with hA2
  set A2' : ENNReal := MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hA2'
  set Z : ℕ → ENNReal := (fun n : ℕ =>
      if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
          ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
        ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0) with hZ
  set uOn : ℕ → ℤ → ℂ := (fun n x =>
      if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
          ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
        Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
          - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      else 0) with huOn
  -- the per-scale bound on the band
  have hper : ∀ n : ℕ, MeasureTheory.eLpNorm (uOn n) 1 MeasureTheory.Measure.count
      ≤ (ENNReal.ofReal (4 * D * W) * Z n) * (A2 * A2') := by
    intro n
    rw [hZ]
    simp only []
    by_cases hc : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
        ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
    · rw [if_pos hc]
      have huu : uOn n = fun x : ℤ =>
          Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x := by
        funext x
        rw [huOn]
        simp only []
        rw [if_pos hc]
      rw [huu]
      have hss := Work.KMTAreas.A7.repSingleScale P 2 2 hd (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (le_of_eq ENNReal.inv_two_add_inv_two)
        A ρ hρ hρ1 D hD hmassHyp C₀ a l₁ l₂ k₁ k₂ n f g hl₁ hl₂ hfBd hgBd hc.1 hc.2
      rw [inv_two_add_inv_two_inv] at hss
      refine hss.trans ?_
      refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
      rw [← ENNReal.ofReal_mul (p := D) (le_of_lt hD)]
      exact ENNReal.ofReal_le_ofReal
        (by nlinarith [hWbound l₁ l₂ k₁ k₂ hLB, hD.le, hW0])
    · rw [if_neg hc]
      have hz : uOn n = 0 := by
        funext x
        rw [huOn]
        simp only []
        rw [if_neg hc, Pi.zero_apply]
      rw [hz, MeasureTheory.eLpNorm_zero]
      simp
  -- the lacunary reciprocal-sum bound
  have hZnonneg : ∀ n : ℕ, 0 ≤ (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ :=
    fun n => inv_nonneg.mpr (Nat.cast_nonneg _)
  have hZs : Summable (fun n : ℕ => (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) := (hDtsb Λ hΛ a ha ha1).1
  have hZsle : (∑' n : ℕ, (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) ≤ Dts Λ := (hDtsb Λ hΛ a ha ha1).2
  have hZle : (∑' n : ℕ, Z n) ≤ ENNReal.ofReal (Dts Λ) := by
    have h1 : ∀ n : ℕ, Z n ≤ ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by
      intro n
      rw [hZ]
      simp only []
      by_cases hc : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
          ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
      · rw [if_pos hc]
      · rw [if_neg hc]
        exact bot_le
    calc (∑' n : ℕ, Z n)
        ≤ ∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := ENNReal.tsum_le_tsum h1
      _ = ENNReal.ofReal (∑' n : ℕ, (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) :=
          (ENNReal.ofReal_tsum_of_nonneg hZnonneg hZs).symm
      _ ≤ ENNReal.ofReal (Dts Λ) := ENNReal.ofReal_le_ofReal hZsle
  -- the summation
  have hstep1 : (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (uOn n) 1 MeasureTheory.Measure.count)
      ≤ (4 * ENNReal.ofReal (4 * D * W)) * ((∑' n : ℕ, Z n) * (A2 * A2')) := by
    refine (ENNReal.tsum_le_tsum (f := fun n : ℕ =>
        4 * MeasureTheory.eLpNorm (uOn n) 1 MeasureTheory.Measure.count)
      (g := fun n : ℕ => 4 * ((ENNReal.ofReal (4 * D * W) * Z n) * (A2 * A2')))
      (fun n : ℕ => mul_le_mul' le_rfl (hper n))).trans (le_of_eq ?_)
    rw [show (fun n : ℕ => 4 * ((ENNReal.ofReal (4 * D * W) * Z n) * (A2 * A2')))
        = (fun n : ℕ => (4 * ENNReal.ofReal (4 * D * W)) * (Z n * (A2 * A2'))) from by
      funext n
      ring]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  have hsum : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => uOn n x)) 1 MeasureTheory.Measure.count
      ≤ (4 * ENNReal.ofReal (4 * D * W)) * ((∑' n : ℕ, Z n) * (A2 * A2')) :=
    (Work.KMTAreas.A7.VarNormTsumLp (r := r) (p := 1) hr1 le_rfl uOn).trans hstep1
  -- combine the constants
  have h4 : (4 * ENNReal.ofReal (4 * D * W)) * ENNReal.ofReal (Dts Λ)
      = ENNReal.ofReal (4 * (4 * D * W) * Dts Λ) := by
    rw [show (4 : ENNReal) = ENNReal.ofReal 4 from (ENNReal.ofReal_ofNat 4).symm]
    rw [← ENNReal.ofReal_mul (p := 4) (show (0 : ℝ) ≤ 4 by norm_num),
      ← ENNReal.ofReal_mul (p := 4 * (4 * D * W))
        (show (0 : ℝ) ≤ 4 * (4 * D * W) by nlinarith [hD.le, hW0])]
  have hKbound : ENNReal.ofReal (4 * (4 * D * W) * Dts Λ)
      ≤ (((⌈4 * (4 * D * W) * Dts Λ⌉₊ + 1 : NNReal)) : ENNReal) := by
    have h1 : ENNReal.ofReal (4 * (4 * D * W) * Dts Λ)
        ≤ ((⌈4 * (4 * D * W) * Dts Λ⌉₊ : ℕ) : ENNReal) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
    refine h1.trans ?_
    rw [ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one]
    exact le_add_right le_rfl
  have hstep3 : (4 * ENNReal.ofReal (4 * D * W)) * (ENNReal.ofReal (Dts Λ) * (A2 * A2'))
      ≤ ENNReal.ofReal (4 * (4 * D * W) * Dts Λ) * (A2 * A2') :=
    (le_of_eq (mul_assoc (4 * ENNReal.ofReal (4 * D * W))
      (ENNReal.ofReal (Dts Λ)) (A2 * A2')).symm).trans
      (mul_le_mul' (le_of_eq h4) le_rfl)
  have hgoal : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => uOn n x)) 1 MeasureTheory.Measure.count
      ≤ (((⌈4 * (4 * D * W) * Dts Λ⌉₊ + 1 : NNReal)) : ENNReal) * (A2 * A2') :=
    hsum.trans ((mul_le_mul' le_rfl (mul_le_mul' hZle le_rfl)).trans
      (hstep3.trans (mul_le_mul' hKbound le_rfl)))
  exact hgoal.trans (le_of_eq (mul_assoc _ _ _).symm)

/-- **The on-band half of `errorBound`, proved here directly.** -/
theorem onBandSelf (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        lcL l₁ l₂ k₁ k₂ ≤ B → 1 ≤ l₁ → 1 ≤ l₂ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
              Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              else 0))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  obtain ⟨A, hA, hmassAll⟩ := Work.KMTAreas.A7.RepMassBound P hd
  obtain ⟨D, hD, hmassρ⟩ := hmassAll ρ hρ hρ1
  have hmassHyp : Work.KMTAreas.A7.RepMassHyp P A ρ D := by
    intro N l₁ l₂ k₁ k₂ hN hl₁ hl₂ hb₁ hb₂ h2₁ h2₂ hna₁ hna₂
    obtain ⟨h1, h2⟩ := hmassρ N l₁ l₂ k₁ k₂ hN hl₁ hl₂ hb₁ hb₂ h2₁ h2₂ hna₁ hna₂
    exact ⟨h1, by rw [Work.KMTAreas.A7.repWeight]; exact h2⟩
  -- the height bound makes the weight uniform
  set W : ℝ := (2 : ℝ) ^ (A * ((2 : ℝ) ^ (ρ * (B : ℝ)) + (B : ℝ))) with hW
  have hW0 : 0 ≤ W := by rw [hW]; positivity
  have hWbound : ∀ l₁ l₂ k₁ k₂ : ℕ, lcL l₁ l₂ k₁ k₂ ≤ B →
      Work.KMTAreas.A7.repWeight A ρ l₁ l₂ k₁ k₂ ≤ W := by
    intro l₁ l₂ k₁ k₂ hLB
    have hL : Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ ≤ (B : ℝ) := lmaxR_le_of_lcL_le hLB
    have hp : (2 : ℝ) ^ (ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
        ≤ (2 : ℝ) ^ (ρ * (B : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ])
    have hexp : A * ((2 : ℝ) ^ (ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
          + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ≤ A * ((2 : ℝ) ^ (ρ * (B : ℝ)) + (B : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hA
    rw [Work.KMTAreas.A7.repWeight, hW]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  -- the lacunary reciprocal-sum constant
  set Dts : NNReal → ℝ := fun Λ =>
    if h : 1 < Λ then Classical.choose (Work.KMTAreas.A7.invFloor_tsum_le Λ h) else 0 with hDts
  have hDtsb : ∀ (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      Summable (fun n : ℕ => (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) ∧
        (∑' n : ℕ, (((Nat.floor (a n) : ℕ) : ℝ))⁻¹) ≤ Dts Λ := by
    intro Λ hΛ a ha ha1
    rw [hDts]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (Work.KMTAreas.A7.invFloor_tsum_le Λ hΛ)).2 a ha ha1
  refine ⟨fun Λ => ⌈4 * (4 * D * W) * Dts Λ⌉₊ + 1, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hl₁ hl₂
  have hK1 : (1 : NNReal) ≤ ⌈4 * (4 * D * W) * Dts Λ⌉₊ + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact_mod_cast Nat.le_add_left 1 ⌈4 * (4 * D * W) * Dts Λ⌉₊
  have hKne : (((⌈4 * (4 * D * W) * Dts Λ⌉₊ + 1 : NNReal)) : ENNReal) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1)
      (by rw [← ENNReal.coe_one, ENNReal.coe_le_coe]; exact hK1))
  by_cases hf0 : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = 0
  · have hfz : f = 0 :=
      Work.KMTAreas.A7.rep_eq_zero_of_eLpNorm_count_eq_zero (p := 2) (by norm_num) hf0
    subst hfz
    have hsub : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
            ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
          Work.KMTAreas.A7.mainPartTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x
            - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x
          else 0)) = 0 := by
      funext x
      have h0 : (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x
            - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x) = 0 := by
        funext n
        rw [Work.KMTAreas.A7.repMainPartTuple_zero_left ρ P C₀ a g l₁ l₂ k₁ k₂ n x,
          Work.KMTAreas.A7.repModelTupleRep_zero_left ρ P C₀ a g l₁ l₂ k₁ k₂ n x, sub_zero,
          Pi.zero_apply]
      have hnn : (fun n : ℕ => if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
              ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
            Work.KMTAreas.A7.mainPartTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x
              - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x
            else 0) = 0 := by
        funext n
        by_cases hc : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
            ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
        · rw [if_pos hc]
          exact congrFun h0 n
        · rw [if_neg hc, Pi.zero_apply]
      rw [hnn]
      exact Work.KMTAreas.A7.variationalNorm_zero r hr1
    rw [hsub, MeasureTheory.eLpNorm_zero]
    exact bot_le
  · by_cases hg0 : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = 0
    · have hgz : g = 0 :=
        Work.KMTAreas.A7.rep_eq_zero_of_eLpNorm_count_eq_zero (p := 2) (by norm_num) hg0
      subst hgz
      have hsub : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
              ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
            Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x
              - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x
            else 0)) = 0 := by
        funext x
        have h0 : (fun n : ℕ => Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x
              - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x) = 0 := by
          funext n
          rw [Work.KMTAreas.A7.repMainPartTuple_zero_right ρ P C₀ a f l₁ l₂ k₁ k₂ n x,
            Work.KMTAreas.A7.repModelTupleRep_zero_right ρ P C₀ a f l₁ l₂ k₁ k₂ n x, sub_zero,
            Pi.zero_apply]
        have hnn : (fun n : ℕ => if Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
              Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x
                - Work.KMTAreas.A7.modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x
              else 0) = 0 := by
          funext n
          by_cases hc : Work.KMTAreas.A7.hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
              ∧ Work.KMTAreas.A7.bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
          · rw [if_pos hc]
            exact congrFun h0 n
          · rw [if_neg hc, Pi.zero_apply]
        rw [hnn]
        exact Work.KMTAreas.A7.variationalNorm_zero r hr1
      rw [hsub, MeasureTheory.eLpNorm_zero]
      exact bot_le
    · by_cases hfT : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ⊤
      · have htop : (((⌈4 * (4 * D * W) * Dts Λ⌉₊ + 1 : NNReal)) : ENNReal)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤ := by
          rw [hfT, ENNReal.mul_top hKne, ENNReal.top_mul hg0]
        rw [htop]
        exact le_top
      · by_cases hgT : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
        · have htop : (((⌈4 * (4 * D * W) * Dts Λ⌉₊ + 1 : NNReal)) : ENNReal)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤ := by
            rw [hgT, ENNReal.mul_top (mul_ne_zero hKne hf0)]
          rw [htop]
          exact le_top
        · -- the finite-norm case
          have hfmem : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count :=
            MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hfT)
          have hgmem : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count :=
            MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hgT)
          exact onBandBound_main P hd r hr C₀ ρ hρ hρ1 B A D hD hmassHyp W hW0 hWbound Dts hDtsb
            Λ hΛ a ha ha1 l₁ l₂ k₁ k₂ hLB hl₁ hl₂ f g hfmem hgmem

end

end Work.KMTPlan.A6.PieceBoundedH
