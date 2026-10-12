import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB2.DvApriori.integrable_uncurry_of_radial_bound
import Submission.Work.BoseFixB2.DvApriori.tBamp_pair_decay_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori

open MeasureTheory Filter
open scoped ContDiff Topology Real BigOperators ENNReal

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-! ## Auxiliary facts about the box indicator `indU ℓ 0` -/

/-- The moving box at `u = 0` is the centred cube. -/
private lemma lamBox_zero_eq_acube {ℓ : ℝ} :
    Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext y; simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- The slot evaluation `x ↦ indU ℓ 0 (x j)` is measurable. -/
private lemma measurable_indU_zero_slot {n : ℕ} {ℓ : ℝ} (j : Fin n) :
    Measurable (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j)) := by
  have h : Work.BoseKinLoc.indU ℓ (0 : R3)
      = (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) := by
    rw [show Work.BoseKinLoc.indU ℓ (0 : R3)
        = (Work.BoseKinLoc.lamBox ℓ 0).indicator (fun _ => (1 : ℝ)) from rfl,
      lamBox_zero_eq_acube]
  rw [h]
  exact ((measurable_const : Measurable fun _ : R3 => (1 : ℝ)).indicator
    (Submission.BoseGases.acube_measurable ℓ)).comp (continuous_apply j).measurable

/-! ## The Fubini exchange for an abstract window -/

/-- The `p ↔ abox` Fubini exchange for an abstract smooth compactly supported window. -/
private theorem swap_p_abox_tBamp_pair_gen {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {F : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hFm : Measurable F)
    (hFbd : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ 2)
    {χ : R3 → ℝ} (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    {W V : Submission.BoseGases.X n → ℝ} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : R3, F ‖p‖ *
            (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
              Work.SmallBoxTBWord.tBamp χ p V j x).re))
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : R3, F ‖p‖ *
            (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
              (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
                Work.SmallBoxTBWord.tBamp χ p V j x).re) := by
  classical
  have hχc : Continuous χ := hχcd.continuous
  obtain ⟨CW, hCW0, hCW⟩ := Work.SmallBoxTBWord.tBamp_decay (N := n) hℓ hχcd hχcs hW
  obtain ⟨CV, hCV0, hCV⟩ := Work.SmallBoxTBWord.tBamp_decay (N := n) hℓ hχcd hχcs hV
  let f : R3 → Submission.BoseGases.X n → ℝ := fun p x =>
    Work.BoseKinLoc.indU ℓ 0 (x j) * (F ‖p‖ *
      (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
        Work.SmallBoxTBWord.tBamp χ p V j x).re)
  let ν : Measure (Submission.BoseGases.X n) :=
    (volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)
  -- ## the pointwise bound (delegated: `tBamp_pair_decay_bound`)
  have hbound : ∀ x ∈ Submission.BoseGases.abox n ℓ, ∀ p : R3,
      ‖f p x‖ ≤ K * CW * CV / (1 + ‖p‖) ^ 4 :=
    fun x hx p => tBamp_pair_decay_bound j hK hCW0 hCV0 hFbd
      (fun x hx p => hCW x hx j p) (fun x hx p => hCV x hx j p) x hx p
  -- ## joint measurability
  have hGc : Continuous (fun q : R3 × Submission.BoseGases.X n =>
      (star (Work.SmallBoxTBWord.tBamp χ q.1 W j q.2) *
        Work.SmallBoxTBWord.tBamp χ q.1 V j q.2).re) :=
    Complex.continuous_re.comp
      ((continuous_star.comp
          (Work.SmallBoxTBWord.continuous_tBamp_pair hχc hχcs hW.continuous j)).mul
        (Work.SmallBoxTBWord.continuous_tBamp_pair hχc hχcs hV.continuous j))
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (volume.prod ν) := by
    have h1 : Measurable (fun q : R3 × Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (q.2 j)) :=
      (measurable_indU_zero_slot (ℓ := ℓ) j).comp measurable_snd
    have h2 : Measurable (fun q : R3 × Submission.BoseGases.X n => F ‖q.1‖) :=
      hFm.comp (continuous_norm.comp continuous_fst).measurable
    have h3 : Measurable (Function.uncurry f) := by
      show Measurable (fun q : R3 × Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (q.2 j) * (F ‖q.1‖ *
          (star (Work.SmallBoxTBWord.tBamp χ q.1 W j q.2) *
            Work.SmallBoxTBWord.tBamp χ q.1 V j q.2).re))
      exact h1.mul (h2.mul hGc.measurable)
    exact h3.aestronglyMeasurable
  -- ## the a.e. domination along the fibres
  have hbd : ∀ᵐ x ∂ν, ∀ p : R3, ‖f p x‖ ≤ K * CW * CV / (1 + ‖p‖) ^ 4 := by
    rw [show ν = (volume : Measure (Submission.BoseGases.X n)).restrict
        (Submission.BoseGases.abox n ℓ) from rfl,
      ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
    filter_upwards with x hx
    exact hbound x hx
  -- ## joint integrability and Fubini
  have hAfin : (volume : Measure (Submission.BoseGases.X n))
      (Submission.BoseGases.abox n ℓ) ≠ ⊤ :=
    (Submission.BoseGases.abox_lt_top n ℓ hℓ.le).ne
  have hKmul : (0 : ℝ) ≤ K * CW * CV := by positivity
  have hInt : Integrable (Function.uncurry f) (volume.prod ν) :=
    integrable_uncurry_of_radial_bound hAfin hmeas hKmul hbd
  have hswap : (∫ x in Submission.BoseGases.abox n ℓ, ∫ p : R3, f p x)
      = (∫ p : R3, ∫ x in Submission.BoseGases.abox n ℓ, f p x) :=
    (MeasureTheory.integral_integral_swap (μ := (volume : Measure R3)) (ν := ν) hInt).symm
  -- ## the algebraic steps
  have hstep1 : (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : R3, F ‖p‖ *
            (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
              Work.SmallBoxTBWord.tBamp χ p V j x).re))
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j) * (∫ p : R3, F ‖p‖ *
            (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
              Work.SmallBoxTBWord.tBamp χ p V j x).re)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  have hstep2 : (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * (∫ p : R3, F ‖p‖ *
            (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
              Work.SmallBoxTBWord.tBamp χ p V j x).re))
      = (∫ x in Submission.BoseGases.abox n ℓ, ∫ p : R3, f p x) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact (MeasureTheory.integral_const_mul (Work.BoseKinLoc.indU ℓ 0 (x j))
      (fun p : R3 => F ‖p‖ *
        (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
          Work.SmallBoxTBWord.tBamp χ p V j x).re)).symm
  have hstep4 : ∀ p : R3,
      (∫ x in Submission.BoseGases.abox n ℓ, f p x)
      = F ‖p‖ * (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j) *
            (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
              Work.SmallBoxTBWord.tBamp χ p V j x).re) := by
    intro p
    have key : (∫ x in Submission.BoseGases.abox n ℓ, f p x)
        = (∫ x in Submission.BoseGases.abox n ℓ,
            F ‖p‖ * (Work.BoseKinLoc.indU ℓ 0 (x j) *
              (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
                Work.SmallBoxTBWord.tBamp χ p V j x).re)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      show f p x = F ‖p‖ * (Work.BoseKinLoc.indU ℓ 0 (x j) *
        (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
          Work.SmallBoxTBWord.tBamp χ p V j x).re)
      dsimp only [f]
      ring
    rw [key]
    exact MeasureTheory.integral_const_mul (F ‖p‖) _
  have hfinal : (∫ p : R3, ∫ x in Submission.BoseGases.abox n ℓ, f p x)
      = (∫ p : R3, F ‖p‖ *
          (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
            (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
              Work.SmallBoxTBWord.tBamp χ p V j x).re)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    exact hstep4 p
  calc (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : R3, F ‖p‖ *
            (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
              Work.SmallBoxTBWord.tBamp χ p V j x).re))
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x j) * (∫ p : R3, F ‖p‖ *
            (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
              Work.SmallBoxTBWord.tBamp χ p V j x).re)) := hstep1
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ x in Submission.BoseGases.abox n ℓ, ∫ p : R3, f p x) := by rw [hstep2]
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ p : R3, ∫ x in Submission.BoseGases.abox n ℓ, f p x) := by rw [hswap]
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (∫ p : R3, F ‖p‖ *
            (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
              (star (Work.SmallBoxTBWord.tBamp χ p W j x) *
                Work.SmallBoxTBWord.tBamp χ p V j x).re)) := by rw [hfinal]

/-- Fubini exchange of the momentum integral with the configuration-box integral for the
windowed `tBamp` pairing of two smooth slot states.  The exchange is justified by the uniform
decay `‖tBamp χ₀ p W j x‖ ≤ C/(1+‖p‖)³` on the box (`tBamp_decay`, for `W` and `V`) together
with the measurability of `F` and the polynomial growth bound `|F r| ≤ K(1+r)²`, which make the
`(x,p)`-integrand jointly integrable. -/
theorem swap_p_abox_tBamp_pair {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n)
    {F : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hFm : Measurable F)
    (hFbd : ∀ r : ℝ, 0 ≤ r → |F r| ≤ K * (1 + r) ^ 2)
    {W V : Submission.BoseGases.X n → ℝ} (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j) * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
            (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
              Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re))
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : EuclideanSpace ℝ (Fin 3), F ‖p‖ *
            (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
              (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
                Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re) := by
  have hχcd : ContDiff ℝ (⊤ : ℕ∞) (Work.BSKinetic.bsWin ℓ (0 : R3)) := by
    have h' : Work.BSKinetic.bsWin ℓ (0 : R3)
        = fun z : R3 => Submission.BoseGases.chiScale ℓ (z - ℓ • (0 : R3)) := rfl
    rw [h']
    exact (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).comp
      (contDiff_id.sub contDiff_const)
  have hχcs : HasCompactSupport (Work.BSKinetic.bsWin ℓ (0 : R3)) :=
    Work.BSKinetic.SwapTBAmp.hasCompactSupport_chiBig (ne_of_gt hℓ) 0
  exact swap_p_abox_tBamp_pair_gen hℓ j hK hFm hFbd hχcd hχcs hW hV

end Work.BoseFixB2.DvApriori
