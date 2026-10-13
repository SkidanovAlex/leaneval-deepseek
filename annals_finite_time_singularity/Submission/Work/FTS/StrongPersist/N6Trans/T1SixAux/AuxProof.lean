/-
Auxiliary proof module: the generic-exponent estimate `slotT1SixAux` for
`Submission/Work/FTS/StrongPersist/N6Trans/slotT1Six.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.SlicePrep
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Asm
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.t1TermSix
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_zero_z)
open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- **The generic level-six `D_θ`-transport slot bound.**  For every admissible exponent
`q ∈ [0,γ]` (`q ≤ η` when `a = 0`) the canonical-weight slot pairing of `(f·D_θ g, g)` is
bounded by `C α^{-1/2}|f|_{ℋ⁶}|g|²_{ℋ⁶}`, uniformly in `α ∈ (0,1]`. -/
theorem slotT1SixAux : ∃ K : ℝ, 0 < K ∧
    ∀ (α q : ℝ) (f g : ℝ → ℝ → ℝ) (a b : ℕ),
      0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → HkMem α 6 f →
      Work.FTS.EllipticEst.SmoothOpen g → HkMem α 6 g →
      a + b ≤ 6 → 0 ≤ q → q ≤ gam α → (a = 0 → q ≤ eta) →
      |Work.FTS.TransportS.slotPairing (canonW q) a b
          (fun z θ => f z θ * Dth g z θ) g|
        ≤ K * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f * HkSq α 6 g := by
  obtain ⟨Kt, hKt0, hterm6⟩ := T1SixAux.t1TermSix
  have hleib : ∀ (f g : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen f →
      Work.FTS.EllipticEst.SmoothOpen g → ∀ (a b : ℕ) (z θ : ℝ), 0 < z → 0 < θ →
      θ < π / 2 →
      mixed b a (fun z θ => f z θ * Dth g z θ) z θ - f z θ * Dth (mixed b a g) z θ
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0
            else (a.choose i : ℝ) * (b.choose j : ℝ)
              * (mixed j i f z θ * mixed (b - j) (a - i + 1) g z θ)) :=
    fun f g hF hG a b => T1SixAux.leibnizRem6 hF hG a b
  obtain ⟨Ch, hCh0, hhard⟩ := T1SixAux.hardSlotSliceSixZero
  obtain ⟨Cs, hCs0, hsup⟩ := T1SixAux.supSix
  refine ⟨64 * Kt + Ch * Cs, by positivity, ?_⟩
  intro α q f g a b hα hα1 hF hmF hG hmG hab hq0 hqγ hqη
  have hq2 : q ≤ 2 := by
    have h1 : gam α ≤ 2 := by rw [gam]; linarith
    linarith
  have hαnn : 0 ≤ α := hα.le
  have hKfnn : 0 ≤ Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f :=
    mul_nonneg (mul_nonneg hCs0.le (Real.rpow_nonneg hαnn _))
      (HkNorm_nonneg α 6 f)
  have hBBnn : 0 ≤ α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f
      * HkSq α 6 g :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hαnn _)
      (HkNorm_nonneg α 6 f)) (HkSq_nonneg α 6 g)
  have hKtBB : 0 ≤ Kt * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f
      * HkSq α 6 g :=
    mul_nonneg (mul_nonneg (mul_nonneg hKt0.le (Real.rpow_nonneg hαnn _))
      (HkNorm_nonneg α 6 f)) (HkSq_nonneg α 6 g)
  have hb0 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |f z θ| ≤ Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f := by
    intro z θ hz hθ hθ2
    exact hsup α f hα hα1 hF hmF 0 0 (by norm_num) z θ hz hθ hθ2
  have hb1 : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Dth f z θ| ≤ Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f := by
    intro z θ hz hθ hθ2
    have h := hsup α f hα hα1 hF hmF 0 1 (by norm_num) z θ hz hθ hθ2
    simpa only [mixed_zero_left, DthIter_succ,
      DthIter_zero] using h
  have hYint : ∀ z ∈ Iz, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      canonW q z θ * (mixed b a g z θ) ^ 2) Iθ :=
    fun z hz => T1SixAux.slotSliceIntegrable α q hG hmG
      hqγ hqη hab hz
  obtain ⟨hYmarg, hYen⟩ :=
    T1SixAux.slotEnergyZOuter α q hG hmG hq0 hqγ hqη hab
  have hYnn : ∀ z ∈ Iz, 0 ≤ ∫ θ in Iθ,
      canonW q z θ * (mixed b a g z θ) ^ 2 :=
    fun z _ => MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => mul_nonneg (canonW_nonneg hθ) (sq_nonneg _))
  let Trm : ℕ → ℕ → ℝ → ℝ → ℝ := fun i j z θ => canonW q z θ
      * |mixed j i f z θ| * |mixed (b - j) (a - i + 1) g z θ|
      * |mixed b a g z θ|
  let cff : ℕ → ℕ → ℝ := fun i j => (a.choose i : ℝ) * (b.choose j : ℝ)
  have hcff0 : ∀ i j, 0 ≤ cff i j := by
    intro i j
    show 0 ≤ (a.choose i : ℝ) * (b.choose j : ℝ)
    positivity
  have hcff : ∀ i j z θ, |cff i j| * (|mixed j i f z θ|
        * |mixed (b - j) (a - i + 1) g z θ|)
      = cff i j * (|mixed j i f z θ|
        * |mixed (b - j) (a - i + 1) g z θ|) := by
    intro i j z θ
    rw [abs_of_nonneg (hcff0 i j)]
  have hTrmnn : ∀ i j z θ, θ ∈ Iθ → 0 ≤ Trm i j z θ := by
    intro i j z θ hθ
    exact mul_nonneg (mul_nonneg (mul_nonneg (canonW_nonneg hθ) (abs_nonneg _))
      (abs_nonneg _)) (abs_nonneg _)
  let Tsl : ℝ → ℝ → ℝ := fun z θ => ∑ i ∈ Finset.range (a + 1),
      ∑ j ∈ Finset.range (b + 1),
        (if i = 0 ∧ j = 0 then 0 else cff i j * Trm i j z θ)
  let Mz : ℝ → ℝ := fun z => ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
      (if i = 0 ∧ j = 0 then 0 else cff i j * ∫ θ in Iθ, Trm i j z θ)
  have hTrmSlice : ∀ (i j : ℕ), i ∈ Finset.range (a + 1) → j ∈ Finset.range (b + 1) →
      ¬(i = 0 ∧ j = 0) →
      ∀ z ∈ Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => Trm i j z θ)
        Iθ := by
    intro i j hi hj hij z hz
    have hi' : i ≤ a := by have := Finset.mem_range.mp hi; omega
    have hj' : j ≤ b := by have := Finset.mem_range.mp hj; omega
    exact (hterm6 α q f g a b i j hα hα1 hF hmF hG hmG hi' hj' hab
      (fun hc => hij ⟨hc.1, hc.2.1⟩) hq0 hqγ hqη).1 z hz
  have hTrmMarg : ∀ (i j : ℕ), i ∈ Finset.range (a + 1) → j ∈ Finset.range (b + 1) →
      ¬(i = 0 ∧ j = 0) →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Iθ, Trm i j z θ)
        Iz := by
    intro i j hi hj hij
    have hi' : i ≤ a := by have := Finset.mem_range.mp hi; omega
    have hj' : j ≤ b := by have := Finset.mem_range.mp hj; omega
    exact (hterm6 α q f g a b i j hα hα1 hF hmF hG hmG hi' hj' hab
      (fun hc => hij ⟨hc.1, hc.2.1⟩) hq0 hqγ hqη).2.1
  have hTrmLe : ∀ (i j : ℕ), i ∈ Finset.range (a + 1) → j ∈ Finset.range (b + 1) →
      ¬(i = 0 ∧ j = 0) →
      (∫ z in Iz, ∫ θ in Iθ, Trm i j z θ)
        ≤ Kt * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f * HkSq α 6 g := by
    intro i j hi hj hij
    have hi' : i ≤ a := by have := Finset.mem_range.mp hi; omega
    have hj' : j ≤ b := by have := Finset.mem_range.mp hj; omega
    exact (hterm6 α q f g a b i j hα hα1 hF hmF hG hmG hi' hj' hab
      (fun hc => hij ⟨hc.1, hc.2.1⟩) hq0 hqγ hqη).2.2
  have hTslInt : ∀ z ∈ Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => Tsl z θ)
      Iθ := by
    intro z hz
    refine MeasureTheory.integrable_finsetSum _ fun i hi =>
      MeasureTheory.integrable_finsetSum _ fun j hj => ?_
    by_cases hij : i = 0 ∧ j = 0
    · simp only [if_pos hij]; exact integrableOn_zero
    · simp only [if_neg hij]
      exact (hTrmSlice i j hi hj hij z hz).const_mul _
  have hTslVal : ∀ z ∈ Iz, (∫ θ in Iθ, Tsl z θ) = Mz z := by
    intro z hz
    have hint : ∀ i ∈ Finset.range (a + 1), MeasureTheory.Integrable (fun θ : ℝ =>
        (∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0 else cff i j * Trm i j z θ)))
        (MeasureTheory.volume.restrict Iθ) := by
      intro i hi
      exact MeasureTheory.integrable_finsetSum _ fun j hj => by
        by_cases hij : i = 0 ∧ j = 0
        · simp only [if_pos hij]; exact integrableOn_zero
        · simp only [if_neg hij]
          exact (hTrmSlice i j hi hj hij z hz).const_mul _
    have hint2 : ∀ i ∈ Finset.range (a + 1), ∀ j ∈ Finset.range (b + 1),
        MeasureTheory.Integrable (fun θ : ℝ =>
          (if i = 0 ∧ j = 0 then 0 else cff i j * Trm i j z θ))
        (MeasureTheory.volume.restrict Iθ) := by
      intro i hi j hj
      by_cases hij : i = 0 ∧ j = 0
      · simp only [if_pos hij]; exact integrableOn_zero
      · simp only [if_neg hij]
        exact (hTrmSlice i j hi hj hij z hz).const_mul _
    rw [MeasureTheory.integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => hint2 i hi j hj)]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hij : i = 0 ∧ j = 0
    · simp only [if_pos hij, MeasureTheory.integral_zero]
    · simp only [if_neg hij, MeasureTheory.integral_const_mul]
  have hMzInt : MeasureTheory.IntegrableOn Mz Iz := by
    refine MeasureTheory.integrable_finsetSum _ fun i hi =>
      MeasureTheory.integrable_finsetSum _ fun j hj => ?_
    by_cases hij : i = 0 ∧ j = 0
    · simp only [if_pos hij]; exact integrableOn_zero
    · simp only [if_neg hij]
      exact (hTrmMarg i j hi hj hij).const_mul _
  have hMzEval : (∫ z in Iz, Mz z)
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0 else cff i j
            * ∫ z in Iz, ∫ θ in Iθ, Trm i j z θ) := by
    have hint : ∀ i ∈ Finset.range (a + 1), MeasureTheory.Integrable (fun z : ℝ =>
        (∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0 else cff i j * ∫ θ in Iθ, Trm i j z θ)))
        (MeasureTheory.volume.restrict Iz) := by
      intro i hi
      exact MeasureTheory.integrable_finsetSum _ fun j hj => by
        by_cases hij : i = 0 ∧ j = 0
        · simp only [if_pos hij]; exact integrableOn_zero
        · simp only [if_neg hij]
          exact (hTrmMarg i j hi hj hij).const_mul _
    have hint2 : ∀ i ∈ Finset.range (a + 1), ∀ j ∈ Finset.range (b + 1),
        MeasureTheory.Integrable (fun z : ℝ =>
          (if i = 0 ∧ j = 0 then 0 else cff i j * ∫ θ in Iθ, Trm i j z θ))
        (MeasureTheory.volume.restrict Iz) := by
      intro i hi j hj
      by_cases hij : i = 0 ∧ j = 0
      · simp only [if_pos hij]; exact integrableOn_zero
      · simp only [if_neg hij]
        exact (hTrmMarg i j hi hj hij).const_mul _
    rw [MeasureTheory.integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => hint2 i hi j hj)]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hij : i = 0 ∧ j = 0
    · simp only [if_pos hij, MeasureTheory.integral_zero]
    · simp only [if_neg hij, MeasureTheory.integral_const_mul]
  have hchooseSum : ∀ n : ℕ, (∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ℝ))
      = (2 : ℝ) ^ n := by
    intro n
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  have hpowSum : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), cff i j)
      = (2 : ℝ) ^ (a + b) := by
    have hc : ∀ i j, cff i j = (a.choose i : ℝ) * (b.choose j : ℝ) := fun i j => rfl
    simp only [hc]
    rw [← Finset.sum_mul_sum, hchooseSum a, hchooseSum b, ← pow_add]
  have hpow : (2 : ℝ) ^ (a + b) ≤ 64 := by
    calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 :=
          pow_le_pow_right₀ (by norm_num) hab
      _ = 64 := by norm_num
  have hMzLe : (∫ z in Iz, Mz z)
      ≤ 64 * (Kt * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f
          * HkSq α 6 g) := by
    rw [hMzEval]
    calc (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then 0 else cff i j
              * ∫ z in Iz, ∫ θ in Iθ, Trm i j z θ))
        ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (cff i j * (Kt * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f
              * HkSq α 6 g)) := by
          refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
          by_cases hij : i = 0 ∧ j = 0
          · simp only [if_pos hij]
            exact mul_nonneg (hcff0 i j) hKtBB
          · simp only [if_neg hij]
            exact mul_le_mul_of_nonneg_left (hTrmLe i j hi hj hij) (hcff0 i j)
      _ = (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1), cff i j)
            * (Kt * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f
                * HkSq α 6 g) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.sum_mul]
      _ ≤ 64 * (Kt * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f
            * HkSq α 6 g) := by
          rw [hpowSum]
          exact mul_le_mul_of_nonneg_right hpow hKtBB
  have hMzNN : ∀ z ∈ Iz, 0 ≤ Mz z := by
    intro z hz
    refine Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => ?_
    by_cases hij : i = 0 ∧ j = 0
    · simp only [if_pos hij]
      exact le_refl 0
    · simp only [if_neg hij]
      exact mul_nonneg (hcff0 i j) (MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ hθ => hTrmnn i j z θ hθ))
  have hdom : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |canonW q z θ * (mixed b a (fun z θ => f z θ * Dth g z θ) z θ
          - f z θ * Dth (mixed b a g) z θ) * mixed b a g z θ|
        ≤ Tsl z θ := by
    intro z θ hz hθ0 hθ1
    have hθI : θ ∈ Iθ := ⟨hθ0.le, hθ1.le⟩
    have hCW : 0 ≤ canonW q z θ := canonW_nonneg hθI
    have hkey := hleib f g hF hG a b z θ hz hθ0 hθ1
    have habs : |mixed b a (fun z θ => f z θ * Dth g z θ) z θ
          - f z θ * Dth (mixed b a g) z θ|
        ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then 0 else |cff i j|
              * (|mixed j i f z θ|
                  * |mixed (b - j) (a - i + 1) g z θ|)) := by
      rw [hkey]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i hi => ?_)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j hj => ?_)
      by_cases hij : i = 0 ∧ j = 0
      · simp only [if_pos hij, abs_zero]
        exact le_refl 0
      · simp only [if_neg hij]
        rw [abs_mul, abs_mul, abs_mul]
    have hstep : canonW q z θ * |mixed b a
          (fun z θ => f z θ * Dth g z θ) z θ
          - f z θ * Dth (mixed b a g) z θ|
          * |mixed b a g z θ| ≤ Tsl z θ := by
      refine le_trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left habs hCW) (abs_nonneg _)) ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      show canonW q z θ * ((if i = 0 ∧ j = 0 then 0 else |cff i j|
            * (|mixed j i f z θ|
              * |mixed (b - j) (a - i + 1) g z θ|)))
            * |mixed b a g z θ|
          ≤ (if i = 0 ∧ j = 0 then 0 else cff i j * (canonW q z θ
              * |mixed j i f z θ|
              * |mixed (b - j) (a - i + 1) g z θ|
              * |mixed b a g z θ|))
      by_cases hij : i = 0 ∧ j = 0
      · rw [if_pos hij, if_pos hij]
        simp
      · rw [if_neg hij, if_neg hij]
        rw [hcff i j z θ]
        exact le_of_eq (by ring)
    calc |canonW q z θ * (mixed b a
            (fun z θ => f z θ * Dth g z θ) z θ
            - f z θ * Dth (mixed b a g) z θ) * mixed b a g z θ|
        = canonW q z θ * |mixed b a
            (fun z θ => f z θ * Dth g z θ) z θ
            - f z θ * Dth (mixed b a g) z θ|
          * |mixed b a g z θ| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hCW]
      _ ≤ Tsl z θ := hstep
  have hAesm : ∀ z : ℝ, 0 < z → MeasureTheory.AEStronglyMeasurable (fun θ : ℝ =>
      canonW q z θ * (mixed b a (fun z θ => f z θ * Dth g z θ) z θ
        - f z θ * Dth (mixed b a g) z θ) * mixed b a g z θ)
      (MeasureTheory.volume.restrict Iθ) := by
    intro z hz0
    refine aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => canonW q p.1 p.2
      * (mixed b a (fun z θ => f z θ * Dth g z θ) p.1 p.2
          - f p.1 p.2 * Dth (mixed b a g) p.1 p.2)
      * mixed b a g p.1 p.2) ?_ hz0
    have hcw : ContinuousOn (fun p : ℝ × ℝ => canonW q p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
      Work.FTS.TransportS.SlotT2.continuousOn_canonW q
    have h1 : ContinuousOn (fun p : ℝ × ℝ => mixed b a
        (fun z θ => f z θ * Dth g z θ) p.1 p.2
          - f p.1 p.2 * Dth (mixed b a g) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      have hmix : Work.FTS.EllipticEst.SmoothOpen (mixed b a
          (fun z θ => f z θ * Dth g z θ)) :=
        (T1SixAux.SmoothOpenMul hF hG.Dth).mixed b a
      exact (hmix.continuousOn.sub (hF.continuousOn.mul (hG.mixed b a).Dth.continuousOn))
    have h2 : ContinuousOn (fun p : ℝ × ℝ => mixed b a g p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := (hG.mixed b a).continuousOn
    exact (hcw.mul h1).mul h2
  have hLoInt : ∀ z ∈ Iz, MeasureTheory.IntegrableOn (fun θ : ℝ =>
      canonW q z θ * (mixed b a (fun z θ => f z θ * Dth g z θ) z θ
        - f z θ * Dth (mixed b a g) z θ) * mixed b a g z θ)
      Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ : ℝ => canonW q 0 θ
          * (mixed b a (fun z θ => f z θ * Dth g z θ) 0 θ
              - f 0 θ * Dth (mixed b a g) 0 θ)
          * mixed b a g 0 θ) = fun _ => (0 : ℝ) from by
        funext θ; rw [canonW_zero_z]; ring]
      exact integrableOn_zero
    · refine MeasureTheory.Integrable.mono' (hTslInt z hz) (hAesm z hz0) ?_
      filter_upwards [Work.FTS.TransportS.ae_mem_Ioo_Iθ] with θ hθ
      rw [Real.norm_eq_abs]
      exact hdom z θ hz0 hθ.1 hθ.2
  have hLoBound : ∀ z ∈ Iz, (∫ θ in Iθ,
      |canonW q z θ * (mixed b a (fun z θ => f z θ * Dth g z θ) z θ
        - f z θ * Dth (mixed b a g) z θ) * mixed b a g z θ|)
      ≤ Mz z := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ : ℝ => |canonW q 0 θ
          * (mixed b a (fun z θ => f z θ * Dth g z θ) 0 θ
              - f 0 θ * Dth (mixed b a g) 0 θ)
          * mixed b a g 0 θ|) = fun _ => (0 : ℝ) from by
        funext θ; simp only [canonW_zero_z, zero_mul, abs_zero]]
      rw [MeasureTheory.integral_zero]
      exact hMzNN 0 hz
    · have h1 : (∫ θ in Iθ,
          |canonW q z θ * (mixed b a (fun z θ => f z θ * Dth g z θ) z θ
            - f z θ * Dth (mixed b a g) z θ)
            * mixed b a g z θ|) ≤ ∫ θ in Iθ, Tsl z θ := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (hTslInt z hz) ?_
        · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ _ => abs_nonneg _)
        · filter_upwards [Work.FTS.TransportS.ae_mem_Ioo_Iθ] with θ hθ
          exact hdom z θ hz0 hθ.1 hθ.2
      exact le_trans h1 (le_of_eq (hTslVal z hz))
  have hHard : ∀ z ∈ Iz,
      |∫ θ in Iθ, canonW q z θ * f z θ
          * Dth (mixed b a g) z θ * mixed b a g z θ|
        ≤ Ch * (Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f)
          * ∫ θ in Iθ, canonW q z θ * (mixed b a g z θ) ^ 2 := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [show (fun θ : ℝ => canonW q 0 θ * f 0 θ
          * Dth (mixed b a g) 0 θ * mixed b a g 0 θ)
          = fun _ => (0 : ℝ) from by funext θ; rw [canonW_zero_z]; ring,
        show (fun θ : ℝ => canonW q 0 θ * (mixed b a g 0 θ) ^ 2)
          = fun _ => (0 : ℝ) from by funext θ; rw [canonW_zero_z]; ring]
      simp only [MeasureTheory.integral_zero, abs_zero, mul_zero]
      exact le_refl 0
    · exact hhard q (Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f) z f
        (mixed b a g) hq0 hq2 hKfnn hz hF (hG.mixed b a)
        (fun θ hθ hθ2 => hb0 z θ hz0 hθ hθ2)
        (fun θ hθ hθ2 => hb1 z θ hz0 hθ hθ2)
        (hYint z hz)
  have hSlice : ∀ z ∈ Iz,
      |∫ θ in Iθ, canonW q z θ
          * mixed b a (fun z θ => f z θ * Dth g z θ) z θ
          * mixed b a g z θ|
        ≤ Ch * (Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f)
            * (∫ θ in Iθ, canonW q z θ * (mixed b a g z θ) ^ 2)
          + Mz z := by
    intro z hz
    by_cases hInt : MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ
        * mixed b a (fun z θ => f z θ * Dth g z θ) z θ
        * mixed b a g z θ) Iθ
    · have hLo := hLoInt z hz
      have hHi : MeasureTheory.IntegrableOn (fun θ : ℝ => canonW q z θ * f z θ
          * Dth (mixed b a g) z θ * mixed b a g z θ)
          Iθ := by
        have hsub : (fun θ : ℝ => canonW q z θ
              * mixed b a (fun z θ => f z θ * Dth g z θ) z θ
              * mixed b a g z θ)
            - (fun θ : ℝ => canonW q z θ * (mixed b a
                (fun z θ => f z θ * Dth g z θ) z θ
                - f z θ * Dth (mixed b a g) z θ)
                * mixed b a g z θ)
            = fun θ : ℝ => canonW q z θ * f z θ
                * Dth (mixed b a g) z θ
                * mixed b a g z θ := by
          funext θ
          simp only [Pi.sub_apply]
          ring
        rw [← hsub]
        exact hInt.sub hLo
      have hsplit : (∫ θ in Iθ, canonW q z θ
            * mixed b a (fun z θ => f z θ * Dth g z θ) z θ
            * mixed b a g z θ)
          = (∫ θ in Iθ, canonW q z θ * f z θ
              * Dth (mixed b a g) z θ
              * mixed b a g z θ)
            + (∫ θ in Iθ, canonW q z θ * (mixed b a
                (fun z θ => f z θ * Dth g z θ) z θ
                - f z θ * Dth (mixed b a g) z θ)
                * mixed b a g z θ) := by
        rw [show (fun θ : ℝ => canonW q z θ
              * mixed b a (fun z θ => f z θ * Dth g z θ) z θ
              * mixed b a g z θ)
            = fun θ : ℝ => canonW q z θ * f z θ
                * Dth (mixed b a g) z θ
                * mixed b a g z θ
              + canonW q z θ * (mixed b a
                  (fun z θ => f z θ * Dth g z θ) z θ
                  - f z θ * Dth (mixed b a g) z θ)
                * mixed b a g z θ
            from by funext θ; ring]
        exact MeasureTheory.integral_add hHi hLo
      rw [hsplit]
      calc |(∫ θ in Iθ, canonW q z θ * f z θ
                * Dth (mixed b a g) z θ
                * mixed b a g z θ)
              + (∫ θ in Iθ, canonW q z θ * (mixed b a
                  (fun z θ => f z θ * Dth g z θ) z θ
                  - f z θ * Dth (mixed b a g) z θ)
                  * mixed b a g z θ)|
          ≤ |∫ θ in Iθ, canonW q z θ * f z θ
                * Dth (mixed b a g) z θ
                * mixed b a g z θ|
              + |∫ θ in Iθ, canonW q z θ * (mixed b a
                  (fun z θ => f z θ * Dth g z θ) z θ
                  - f z θ * Dth (mixed b a g) z θ)
                  * mixed b a g z θ| :=
            abs_add_le _ _
        _ ≤ Ch * (Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f)
              * (∫ θ in Iθ, canonW q z θ * (mixed b a g z θ) ^ 2)
              + ∫ θ in Iθ, |canonW q z θ * (mixed b a
                  (fun z θ => f z θ * Dth g z θ) z θ
                  - f z θ * Dth (mixed b a g) z θ)
                  * mixed b a g z θ| :=
            add_le_add (hHard z hz) MeasureTheory.abs_integral_le_integral_abs
        _ ≤ Ch * (Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f)
              * (∫ θ in Iθ, canonW q z θ * (mixed b a g z θ) ^ 2)
              + Mz z :=
            add_le_add le_rfl (hLoBound z hz)
    · rw [MeasureTheory.integral_undef hInt, abs_zero]
      refine add_nonneg (mul_nonneg (mul_nonneg hCh0.le hKfnn) (hYnn z hz)) (hMzNN z hz)
  have hRhsInt : MeasureTheory.IntegrableOn (fun z : ℝ =>
      Ch * (Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f)
          * (∫ θ in Iθ, canonW q z θ * (mixed b a g z θ) ^ 2)
        + Mz z) Iz := (hYmarg.const_mul _).add hMzInt
  have hmain : |Work.FTS.TransportS.slotPairing (canonW q) a b
        (fun z θ => f z θ * Dth g z θ) g|
      ≤ (64 * Kt + Ch * Cs) * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f
          * HkSq α 6 g := by
    rw [Work.FTS.TransportS.slotPairing]
    refine le_trans MeasureTheory.abs_integral_le_integral_abs ?_
    refine le_trans (MeasureTheory.setIntegral_mono_of_nonneg (fun z _ => abs_nonneg _)
      (fun z hz => hSlice z hz) hRhsInt) ?_
    rw [MeasureTheory.integral_add (hYmarg.const_mul _) hMzInt,
      MeasureTheory.integral_const_mul]
    have h1 : Ch * (Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f)
          * (∫ z in Iz, ∫ θ in Iθ,
              canonW q z θ * (mixed b a g z θ) ^ 2)
        ≤ Ch * (Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f)
            * HkSq α 6 g :=
      mul_le_mul_of_nonneg_left hYen (mul_nonneg hCh0.le hKfnn)
    have h3 : Ch * (Cs * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f)
          * HkSq α 6 g
        + 64 * (Kt * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f
            * HkSq α 6 g)
        = (64 * Kt + Ch * Cs) * α ^ (-(1 / 2 : ℝ)) * HkNorm α 6 f
            * HkSq α 6 g := by
      ring
    linarith [h1, hMzLe, h3]
  exact hmain

end Work.FTS.StrongPersist.N6Trans
