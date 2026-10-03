/-
# The main assembly of `Work.KMTAreas.A7.ModelApproxHiRep`

This module proves the target `Work.KMTAreas.A7.ModelApproxHiRep` (in the form
`Work.KMTAreas.A7.repMain`) from the three inputs of the repaired §6 analysis:

* `Work.KMTAreas.A7.RepMassBound` — the `ℓ¹(ℤ²)` mass bound of the kernel difference
  `hiKconcN − hiKmodNRep` on the band (the analytic core of §6);
* `Work.KMTAreas.A7.hiModelTupleRep_eq_bilinOp` — the model tuple is the bilinear convolution with
  `hiKmodNRep`;
* `Work.KMTAreas.A7.RepOffBandRegime` + `Work.KMTAreas.A7.RepOffBandCrude` — the off-band scales
  (handled in `RepAux.lean`).

The variational estimate is assembled from the single-scale bounds by
`Work.KMTAreas.A7.VarNormTsumLp` (the `ℓ¹`-of-`ℓ^p` spike bound) and the lacunary summation
`Work.KMTAreas.A7.tsum_ite_floor_le_indexSet` (`∑_n ⌊a n⌋⁻¹ ≲ 2^{-2^{L/C₀}}`), with the
absorption `Work.KMTAreas.A7.RepAbsorb`.  Since the lacunary gain kills both the exponential factor
`2^{A 2^{ρL}}` of the single-scale weight and the factor `2^{A L}`, the loss weight of the
conclusion can be taken to be `1` (`c = 0`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.RepAux
import Submission.Work.KMTAreas.A7.RepAbsorb
import Submission.Work.KMTAreas.A7.RepMassBound
import Submission.Work.KMTAreas.A7.RepOffBandRegime
import Submission.Work.KMTAreas.A7.RepOffBandCrude
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar Work.KMTContract

/-- **The main theorem**: `Work.KMTAreas.A7.ModelApproxHiRep`, in the form used by the target
file. -/
theorem repMain (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            1 ≤ l₁ → 1 ≤ l₂ →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  classical
  intro C₀ r hC₀ hr
  obtain ⟨A, hA, hmassAll⟩ := RepMassBound P hdeg
  have hC0R : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  -- the off-band ingredients
  have hreg : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / (4 * (C₀ : ℝ)) →
      ∃ B : ℕ, 1 ≤ B ∧ ∀ (l₁ l₂ k₁ k₂ N : ℕ),
        inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) N →
        splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < N →
        mainRegime ρ k₁ k₂ N →
        ¬ bandCond ρ l₁ l₂ k₁ k₂ N →
        l₁ ≤ B ∧ l₂ ≤ B ∧ k₁ ≤ B ∧ k₂ ≤ B ∧ (Work.Analysis.EndVar.logN N).toNat ≤ B
          ∧ N ≤ 2 ^ B :=
    fun ρ hρ hρ4 => RepOffBandRegime P C₀ hC₀ ρ hρ hρ4
  have hρ4le1 : 1 / (4 * (C₀ : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hcrude : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / (4 * (C₀ : ℝ)) → ∀ B : ℕ,
      ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ k₁ k₂ N : ℕ) (f g : ℤ → ℂ),
        l₁ ≤ B → l₂ ≤ B → k₁ ≤ B → k₂ ≤ B → N ≤ 2 ^ B →
        MeasureTheory.eLpNorm (varpPiece (kmtPj ρ) P P.natDegree (N : NNReal) f g l₁ l₂ k₁ k₂)
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) :=
    fun ρ hρ hρ4 B => RepOffBandCrude P p₁ p₂ hp₁ htp₁ hp₂ htp₂ hsum ρ hρ
      (le_trans hρ4 hρ4le1) B
  have hoffAll := repOffBand_of_ingredients P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum C₀ hC₀ r hr
    hreg hcrude
  refine ⟨0, le_rfl, 1 / (4 * (C₀ : ℝ)), by positivity, ?_⟩
  intro ρ hρ hρ4
  have hρ1 : ρ ≤ 1 := le_trans hρ4 hρ4le1
  obtain ⟨D, hD, hmassρ⟩ := hmassAll ρ hρ hρ1
  obtain ⟨Koffρ, hKoffρ⟩ := hoffAll ρ hρ hρ4
  obtain ⟨Kabs, hKabs1, hKabs⟩ := RepAbsorb A hA C₀ hC₀ ρ hρ hρ4
  have hDr : 0 ≤ D := le_of_lt hD
  -- the mass hypothesis for the single-scale estimate
  have hmassHyp : RepMassHyp P A ρ D := by
    intro N l₁ l₂ k₁ k₂ hN hl₁ hl₂ hb₁ hb₂ h2₁ h2₂ hna₁ hna₂
    obtain ⟨h1, h2⟩ := hmassρ N l₁ l₂ k₁ k₂ hN hl₁ hl₂ hb₁ hb₂ h2₁ h2₂ hna₁ hna₂
    refine ⟨h1, ?_⟩
    rw [repWeight]
    exact h2
  -- the lacunary summation constants
  set Dinv : NNReal → ℝ := fun Λ =>
    if h : 1 < Λ then Classical.choose (invFloorSum_le C₀ hC₀ Λ h) else 0 with hDinv
  have hDinv0 : ∀ Λ : NNReal, 0 ≤ Dinv Λ := by
    intro Λ
    by_cases h : 1 < Λ
    · rw [hDinv]; simp only [dif_pos h]
      exact (Classical.choose_spec (invFloorSum_le C₀ hC₀ Λ h)).1
    · rw [hDinv]; simp [h]
  have hDinvb : ∀ (Λ : NNReal) (hΛ : 1 < Λ) (L : ℕ), 1 ≤ L → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        ≤ Dinv Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) := by
    intro Λ hΛ L hL a ha ha1
    rw [hDinv]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (invFloorSum_le C₀ hC₀ Λ hΛ)).2 L hL a ha ha1
  -- the constant of the on-band part (made nonnegative by the outer `max · 0`)
  set Kcf : NNReal → NNReal := fun Λ =>
    Real.toNNReal (4 * D * Kabs * max (max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (Dinv Λ)) 0)
    with hKcf
  -- the final constant
  refine ⟨fun Λ => 1 + 2 * max (Kcf Λ) (Koffρ Λ), ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hl₁ hl₂
  have hq : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hp₁0 : p₁ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp₁)
  have hp₂0 : p₂ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp₂)
  set AB : ENNReal := MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
    * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hAB
  have hKne : ((1 + 2 * max (Kcf Λ) (Koffρ Λ) : NNReal) : ENNReal) ≠ 0 := by
    have h1 : ((1 : NNReal) : ENNReal) ≤ ((1 + 2 * max (Kcf Λ) (Koffρ Λ) : NNReal) : ENNReal) := by
      rw [ENNReal.coe_le_coe]
      exact le_add_right le_rfl
    refine ne_of_gt (lt_of_lt_of_le zero_lt_one ?_)
    simpa using h1
  -- the degenerate cases
  by_cases hf0 : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = 0
  · have hfz : f = 0 := rep_eq_zero_of_eLpNorm_count_eq_zero hp₁0 hf0
    subst hfz
    have hz : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
        mainPartTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x
          - modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x)) = 0 := by
      funext x
      have h0 : (fun n : ℕ => mainPartTuple ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x
          - modelTupleRep ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x) = 0 := by
        funext n
        rw [repMainPartTuple_zero_left ρ P C₀ a g l₁ l₂ k₁ k₂ n x,
          repModelTupleRep_zero_left ρ P C₀ a g l₁ l₂ k₁ k₂ n x, sub_zero,
          Pi.zero_apply]
      rw [h0]
      exact variationalNorm_zero r hr1
    rw [hz, MeasureTheory.eLpNorm_zero]
    exact bot_le
  · by_cases hg0 : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = 0
    · have hgz : g = 0 := rep_eq_zero_of_eLpNorm_count_eq_zero hp₂0 hg0
      subst hgz
      have hz : (fun x : ℤ => variationalNorm r (fun n : ℕ =>
          mainPartTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x
            - modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x)) = 0 := by
        funext x
        have h0 : (fun n : ℕ => mainPartTuple ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x
            - modelTupleRep ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x) = 0 := by
          funext n
          rw [repMainPartTuple_zero_right ρ P C₀ a f l₁ l₂ k₁ k₂ n x,
            repModelTupleRep_zero_right ρ P C₀ a f l₁ l₂ k₁ k₂ n x, sub_zero,
            Pi.zero_apply]
        rw [h0]
        exact variationalNorm_zero r hr1
      rw [hz, MeasureTheory.eLpNorm_zero]
      exact bot_le
    · -- if one of the two norms is infinite, the right-hand side is infinite
      by_cases hfT : MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count = ⊤
      · rw [hfT, lossWeight]
        simp only [zero_mul, Real.rpow_zero, mul_one, ENNReal.ofReal_one]
        rw [ENNReal.mul_top hKne, ENNReal.top_mul hg0]
        exact le_top
      · by_cases hgT : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤
        · rw [hgT, lossWeight]
          simp only [zero_mul, Real.rpow_zero, mul_one, ENNReal.ofReal_one]
          rw [ENNReal.mul_top (mul_ne_zero hKne hf0)]
          exact le_top
        · -- the main case
          have hfBd : Work.KMTAreas.A5.BoundedZ f :=
            Work.KMTAreas.A5.boundedZ_of_memLp hp₁
              (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hfT))
          have hgBd : Work.KMTAreas.A5.BoundedZ g :=
            Work.KMTAreas.A5.boundedZ_of_memLp hp₂
              (MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hgT))
          set u : ℕ → ℤ → ℂ := fun n x => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x with hu
          set uOn : ℕ → ℤ → ℂ := fun n x =>
              if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                  ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
                mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                  - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              else 0 with huOn
          set uOff : ℕ → ℤ → ℂ := fun n x =>
              if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                  ∧ ¬ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
                mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                  - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
              else 0 with huOff
          have hdecomp : ∀ n : ℕ, u n = uOn n + uOff n := by
            intro n
            funext x
            by_cases hg' : hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
            · simp only [hu, huOn, huOff]
              split_ifs <;> simp_all
            · have hconj : ¬ (inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
                  (Nat.floor (a n))
                  ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
                  ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n))) := hg'
              have h1 : mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n = 0 := by
                funext y
                simp only [mainPartTuple, if_neg hconj, Pi.zero_apply]
              have hconj2 : ¬ (inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
                  (Nat.floor (a n))
                  ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
                  ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n))
                  ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) :=
                fun h => hg' ⟨h.1, h.2.1, h.2.2.1⟩
              have h2 : modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n = 0 := by
                funext y
                simp only [modelTupleRep, if_neg hconj2, Pi.zero_apply]
              simp only [hu, huOn, huOff, h1, h2]
              split_ifs <;> simp_all
          -- the off-band bound
          have hOff : MeasureTheory.eLpNorm (fun x : ℤ =>
                variationalNorm r (fun n : ℕ => uOff n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count ≤ (Koffρ Λ : ENNReal) * AB := by
            have h := hKoffρ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
            simpa only [huOff, hAB] using h
          -- the on-band bound
          have hOn : MeasureTheory.eLpNorm (fun x : ℤ =>
                variationalNorm r (fun n : ℕ => uOn n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count ≤ (Kcf Λ : ENNReal) * AB := by
            have hper : ∀ n : ℕ,
                MeasureTheory.eLpNorm (uOn n) (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
                  ≤ if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                      ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
                      ENNReal.ofReal D * ENNReal.ofReal (repWeight A ρ l₁ l₂ k₁ k₂)
                        * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) * AB
                    else 0 := by
              intro n
              by_cases hc : hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                  ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
              · rw [if_pos hc]
                have huu : uOn n = fun x : ℤ =>
                    mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                      - modelTupleRep ρ P C₀ a f g l₁ l₂ k₁ k₂ n x := by
                  funext x; simp only [huOn, if_pos hc]
                rw [huu]
                refine (repSingleScale P p₁ p₂ hdeg hp₁ htp₁ hp₂ htp₂ hsum A ρ hρ hρ1 D hD
                  hmassHyp C₀ a l₁ l₂ k₁ k₂ n f g hl₁ hl₂ hfBd hgBd hc.1 hc.2).trans (le_of_eq ?_)
                rw [hAB]
              · rw [if_neg hc]
                have hz : uOn n = 0 := by
                  funext x; simp only [huOn, if_neg hc, Pi.zero_apply]
                rw [hz, MeasureTheory.eLpNorm_zero]
            set Xe : ENNReal := ENNReal.ofReal D * ENNReal.ofReal (repWeight A ρ l₁ l₂ k₁ k₂) * AB
              with hXe
            have hper'' : ∀ n : ℕ,
                MeasureTheory.eLpNorm (uOn n) (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
                  ≤ if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                      ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n)) then
                      Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0 := by
              intro n
              have h := hper n
              by_cases hc : hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                  ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
              · rw [if_pos hc] at h ⊢
                refine h.trans (le_of_eq ?_)
                rw [hXe]; ring
              · rw [if_neg hc] at h ⊢
                exact h
            refine (VarNormTsumLp (r := r) hr1 hq uOn).trans ?_
            have hstep : (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (uOn n) (p₁⁻¹ + p₂⁻¹)⁻¹
                  MeasureTheory.Measure.count)
                ≤ 4 * Xe * (∑' n : ℕ, (if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                    ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
                    then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := by
              calc (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (uOn n) (p₁⁻¹ + p₂⁻¹)⁻¹
                    MeasureTheory.Measure.count)
                  ≤ ∑' n : ℕ, 4 * (if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                      ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
                      then Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0) :=
                    ENNReal.tsum_le_tsum (fun n => mul_le_mul' le_rfl (hper'' n))
                _ = ∑' n : ℕ, (4 * Xe) * (if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                      ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
                      then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0) := by
                    refine tsum_congr (fun n => ?_)
                    by_cases hc : hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                        ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
                    · rw [if_pos hc, if_pos hc]; ring
                    · rw [if_neg hc, if_neg hc]; ring
                _ = 4 * Xe * (∑' n : ℕ, (if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                      ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
                      then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) :=
                    ENNReal.tsum_mul_left
            have hcond : ∀ n : ℕ, (hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))) →
                max (max l₁ l₂) (max k₁ k₂) ≤ heightScale C₀ (Nat.floor (a n)) := by
              intro n hc
              have h1 : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
                  (Nat.floor (a n)) := hc.1.1
              rw [inIndexSet] at h1
              have h2 : max (l₁ : ℤ) (l₂ : ℤ) ≤
                  ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.1
              have h3 : (k₁ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.2.1
              have h4 : (k₂ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.2.2
              omega
            set E : ℝ := max (max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (Dinv Λ)) 0 with hE
            set Lr : ℝ := ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) with hLr
            have hE0 : 0 ≤ E := by rw [hE]; exact le_max_right _ _
            set SS : ℝ := E * (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2) with hSS
            have hstep4 : (∑' n : ℕ, (if hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n
                  ∧ bandCond ρ l₁ l₂ k₁ k₂ (Nat.floor (a n))
                  then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
                ≤ ENNReal.ofReal SS := by
              rw [hSS, hLr]
              refine tsum_ite_floor_le_indexSet C₀ hC₀ Λ hΛ (Dinv Λ) (hDinv0 Λ) (hDinvb Λ hΛ)
                (max (max l₁ l₂) (max k₁ k₂)) E ?_ a ha ha1 _ hcond
              rw [hE]
              exact le_max_left _ _
            refine (hstep.trans (mul_le_mul' le_rfl hstep4)).trans ?_
            have hLrEq : lmaxR l₁ l₂ k₁ k₂ = Lr := by
              rw [hLr, lmaxR, Work.Analysis.EndVar.lmax]
              congr 1
              rw [Nat.cast_max, Nat.cast_max]
              push_cast
              rfl
            have hkey : repWeight A ρ l₁ l₂ k₁ k₂ * SS ≤ Kabs * E := by
              have hKabs' : repWeight A ρ l₁ l₂ k₁ k₂
                    * (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2) ≤ Kabs := by
                rw [repWeight, hLrEq, hLr]
                exact hKabs _
              calc repWeight A ρ l₁ l₂ k₁ k₂ * SS
                  = (repWeight A ρ l₁ l₂ k₁ k₂
                      * (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2)) * E := by
                    rw [hSS]; ring
                _ ≤ Kabs * E := mul_le_mul_of_nonneg_right hKabs' hE0
            have hKE0 : (0 : ℝ) ≤ Kabs * E :=
              mul_nonneg (le_trans zero_le_one hKabs1) hE0
            have h4D : (0 : ℝ) ≤ 4 * D := by positivity
            have hkeyE : (4 : ENNReal) * ENNReal.ofReal D * ENNReal.ofReal (Kabs * E)
                = ENNReal.ofReal (4 * D * Kabs * E) := by
              have h1 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := (ENNReal.ofReal_ofNat 4).symm
              rw [h1, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
                ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * D)]
              congr 1
              ring
            calc 4 * Xe * ENNReal.ofReal SS
                = 4 * ENNReal.ofReal D * ENNReal.ofReal (repWeight A ρ l₁ l₂ k₁ k₂)
                    * ENNReal.ofReal SS * AB := by
                  rw [hXe]; ring
              _ = 4 * ENNReal.ofReal D * (ENNReal.ofReal (repWeight A ρ l₁ l₂ k₁ k₂)
                    * ENNReal.ofReal SS) * AB := by ring
              _ = 4 * ENNReal.ofReal D * ENNReal.ofReal (repWeight A ρ l₁ l₂ k₁ k₂ * SS) * AB := by
                  rw [ENNReal.ofReal_mul (repWeight_nonneg A ρ l₁ l₂ k₁ k₂)]
              _ ≤ 4 * ENNReal.ofReal D * ENNReal.ofReal (Kabs * E) * AB := by
                  refine mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl
                  exact ENNReal.ofReal_le_ofReal hkey
              _ = (Kcf Λ : ENNReal) * AB := by
                  have hKcfval : ((Kcf Λ : NNReal) : ℝ) = 4 * D * Kabs * E := by
                    rw [hKcf, hE]
                    exact Real.coe_toNNReal _ (by positivity)
                  have hKcfEq : (Kcf Λ : ENNReal) = ENNReal.ofReal (4 * D * Kabs * E) := by
                    rw [← ENNReal.ofReal_coe_nnreal, hKcfval]
                  rw [hkeyE, hKcfEq]
          -- assemble
          have hpt : ∀ x : ℤ, variationalNorm r (fun n : ℕ => u n x)
              ≤ variationalNorm r (fun n : ℕ => uOn n x)
                + variationalNorm r (fun n : ℕ => uOff n x) := by
            intro x
            have heq : (fun n : ℕ => u n x)
                = (fun n : ℕ => uOn n x) + (fun n : ℕ => uOff n x) := by
              funext n
              rw [hdecomp n]
              rfl
            rw [heq]
            exact variationalNorm_add_le hr1 _ _
          have hsub : MeasureTheory.eLpNorm (fun x : ℤ =>
                variationalNorm r (fun n : ℕ => uOn n x)
                  + variationalNorm r (fun n : ℕ => uOff n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
              ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
                  variationalNorm r (fun n : ℕ => uOn n x)) (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
                + MeasureTheory.eLpNorm (fun x : ℤ =>
                  variationalNorm r (fun n : ℕ => uOff n x)) (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count :=
            MeasureTheory.eLpNorm_add_le hq
          have hmain : MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ Measure.count
              ≤ (Kcf Λ : ENNReal) * AB + (Koffρ Λ : ENNReal) * AB :=
            (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
              (f := fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
              (g := fun x : ℤ => variationalNorm r (fun n : ℕ => uOn n x)
                + variationalNorm r (fun n : ℕ => uOff n x))
              (fun x => by simpa only [enorm_eq_self] using hpt x)).trans
              (hsub.trans (add_le_add hOn hOff))
          refine hmain.trans ?_
          have hloss : ENNReal.ofReal (lossWeight 0 ρ l₁ l₂ k₁ k₂) = 1 := by
            rw [lossWeight]
            simp only [zero_mul, Real.rpow_zero, mul_one, ENNReal.ofReal_one]
          rw [hloss]
          have hle : (Kcf Λ : ENNReal) + (Koffρ Λ : ENNReal)
              ≤ ((1 + 2 * max (Kcf Λ) (Koffρ Λ) : NNReal) : ENNReal) := by
            rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
            have h1 : Kcf Λ ≤ max (Kcf Λ) (Koffρ Λ) := le_max_left _ _
            have h2 : Koffρ Λ ≤ max (Kcf Λ) (Koffρ Λ) := le_max_right _ _
            linarith
          calc (Kcf Λ) * AB + (Koffρ Λ) * AB
              = ((Kcf Λ) + (Koffρ Λ)) * AB := (add_mul _ _ _).symm
            _ ≤ ((1 + 2 * max (Kcf Λ) (Koffρ Λ) : NNReal) : ENNReal) * AB :=
                mul_le_mul' hle le_rfl
            _ = ((1 + 2 * max (Kcf Λ) (Koffρ Λ) : NNReal) : ENNReal) * 1
                  * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
                  * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
                rw [hAB]; ring

end

end Work.KMTAreas.A7
