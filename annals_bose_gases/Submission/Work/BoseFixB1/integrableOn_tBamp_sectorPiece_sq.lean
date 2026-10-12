import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.integrable_sbKin
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal
open Submission.BoseGases
open Work.UBBInputs8
open Work.SmallBoxSliding

-- NB: `ℝ³` is the *global* notation `EuclideanSpace ℝ (Fin 3)` of
-- `Submission/Work/BoseKinLoc/Defs.lean`, already in this file's import cone (a local
-- re-declaration would be ambiguous).

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. Auxiliary lemmas

Both are the generic versions of the private lemmas of
`Work.SlotWord.integrableOn_tBamp_slotPiece_ampSq`, with the slot piece replaced by the sector
piece (the proof does not use anything about the state except its sup bound on the box). -/

/-- The sliding cutoff `χ_B = chiB ℓ d u` is continuous. -/
private lemma continuous_chiB_aux (ℓ d : ℝ) (u : ℝ³) : Continuous (chiB ℓ d u) := by
  unfold chiB
  exact (chiScale_continuous ℓ).mul
    ((chiScale_continuous (ℓ * d)).comp (continuous_id.sub continuous_const))

/-- **The windowed amplitude is bounded by the window mass times the sup.**  If `χ` is continuous
with compact support and vanishes off `acube L`, and `Ψ` is bounded by `B` on `abox N L`, then
for `x ∈ abox N L`, `‖tBamp χ p Ψ i x‖ ≤ B · ∫|χ|`: outside `tsupport χ` the integrand vanishes,
and inside `tsupport χ ⊆ acube L` the updated configuration stays in the box. -/
private theorem norm_tBamp_le_aux {N : ℕ} {L : ℝ} {χ : ℝ³ → ℝ} (hχc : Continuous χ)
    (hχcs : HasCompactSupport χ) (hχsupp : ∀ z : ℝ³, χ z ≠ 0 → z ∈ acube L)
    {Ψ : X N → ℝ} {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y ∈ abox N L, |Ψ y| ≤ B)
    (i : Fin N) (p : ℝ³) {x : X N} (hx : x ∈ abox N L) :
    ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖ ≤ B * ∫ z : ℝ³, |χ z| := by
  have hχint : Integrable χ := hχc.integrable_of_hasCompactSupport hχcs
  have hint : Integrable (fun z : ℝ³ => |χ z| * B) := (hχint.abs).mul_const B
  have hexp : ∀ z : ℝ³, ‖Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))‖ = 1 := by
    intro z
    rw [Complex.norm_exp]
    simp
  have hpt : ∀ z : ℝ³,
      ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Ψ (Function.update x i z) : ℂ)‖ ≤ |χ z| * B := by
    intro z
    have hnorm1 : ‖(χ z : ℂ)‖ = |χ z| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have hnorm2 : ‖(Ψ (Function.update x i z) : ℂ)‖ = |Ψ (Function.update x i z)| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [norm_mul, hexp z, mul_one, hnorm1, hnorm2]
    by_cases hz : χ z = 0
    · rw [hz]; simp
    · have hzA : z ∈ acube L := hχsupp z hz
      have hmem : Function.update x i z ∈ abox N L := by
        rw [mem_abox_iff] at hx ⊢
        intro j
        rw [Function.update_apply]
        by_cases hj : j = i
        · rw [if_pos hj]; exact hzA
        · rw [if_neg hj]; exact hx j
      exact mul_le_mul_of_nonneg_left (hb _ hmem) (abs_nonneg _)
  calc ‖Work.SmallBoxTBWord.tBamp χ p Ψ i x‖
      = ‖∫ z, (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Ψ (Function.update x i z) : ℂ)‖ := by simp only [Work.SmallBoxTBWord.tBamp]
    _ ≤ ∫ z, ‖(χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Ψ (Function.update x i z) : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, |χ z| * B :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hint
          (Eventually.of_forall hpt)
    _ = B * ∫ z, |χ z| := by rw [integral_mul_const]; ring

/-- The amplitude `x ↦ tBamp χ p Ψ i x` is measurable for measurable `χ` and `Ψ`.  The integrand
`(x,z) ↦ χ z · e^{−i⟪p,z⟫} · Ψ (x_{i←z})` is jointly measurable, so the parametric Bochner
integral is strongly measurable (`StronglyMeasurable.integral_prod_right'`). -/
private theorem measurable_tBamp_aux {N : ℕ} {χ : ℝ³ → ℝ} (hχ : Measurable χ)
    (p : ℝ³) {Ψ : X N → ℝ} (hΨ : Measurable Ψ) (i : Fin N) :
    Measurable (fun x : X N => Work.SmallBoxTBWord.tBamp χ p Ψ i x) := by
  have hprod : Continuous (fun q : X N × ℝ³ => (p, q.2)) :=
    continuous_const.prodMk continuous_snd
  have hinner_c : Continuous (fun q : X N × ℝ³ => (inner ℝ p q.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_inner.comp hprod)
  have hexp_meas : Measurable (fun q : X N × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ)))) :=
    (Complex.continuous_exp.comp ((continuous_const.mul hinner_c).neg)).measurable
  have hJ : Measurable (fun q : X N × ℝ³ =>
      (χ q.2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) *
        (Ψ (Function.update q.1 i q.2) : ℂ)) := by
    refine Measurable.mul (Measurable.mul ?_ hexp_meas) ?_
    · exact Complex.continuous_ofReal.measurable.comp (hχ.comp measurable_snd)
    · exact Complex.continuous_ofReal.measurable.comp (hΨ.comp measurable_update')
  have hSM := hJ.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ³))
  simpa only [Work.SmallBoxTBWord.tBamp] using hSM.measurable

/-! ## 2. The target -/

theorem integrableOn_tBamp_sectorPiece_sq {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (i : Fin n) (p : EuclideanSpace ℝ (Fin 3)) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB ℓ d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) i
          (Work.FockBridge.sectorPiece (Submission.BoseGases.dlBox ℓ d u) k Φ)) i x‖ ^ 2)
      (Submission.BoseGases.abox n ℓ) := by
  classical
  -- ## Facts about the sliding box
  have hAmeas : MeasurableSet (dlBox ℓ d u) := measurableSet_dlBox ℓ d u
  have hAa : dlBox ℓ d u ⊆ acube ℓ := dlBox_subset_acube ℓ d u
  have hfin : (volume : Measure ℝ³) (dlBox ℓ d u) < ⊤ := volume_dlBox_lt_top hℓ d u
  have hvol : boxMass ℓ d u = (volume : Measure ℝ³).real (dlBox ℓ d u) :=
    boxMass_eq_measureReal ℓ d u
  -- ## A sup bound for `Φ` on the compact box
  obtain ⟨C, hC⟩ := (abox_compact n hℓ).exists_bound_of_continuousOn hΦ.continuousOn
  let B : ℝ := max C 0
  have hB0 : 0 ≤ B := le_max_right _ _
  have hbΦ : ∀ y ∈ abox n ℓ, |Φ y| ≤ B := by
    intro y hy
    have h1 : ‖Φ y‖ ≤ C := hC y hy
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  -- ## The sector piece inherits the sup bound
  have hΨ0b : ∀ y : X n, (∀ j : Fin n, y j ∈ acube ℓ) →
      |Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ y| ≤ B := by
    intro y hy
    have h1 : ‖Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ y‖ ≤ ‖Φ y‖ := by
      simpa only [Work.FockBridge.sectorPiece] using
        (norm_indicator_le_norm_self (s := Work.FockBridge.sectorSet (dlBox ℓ d u) k)
          (f := Φ) (a := y))
    have h1' : |Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ y| ≤ |Φ y| := by
      simpa [Real.norm_eq_abs] using h1
    exact le_trans h1' (hbΦ y ((mem_abox_iff n ℓ y).mpr hy))
  -- ## The projection is bounded on the box
  let M : ℝ := B + |boxMass ℓ d u|⁻¹ * (B * (volume : Measure ℝ³).real (dlBox ℓ d u))
  have hM0 : 0 ≤ M := by
    refine add_nonneg hB0 ?_
    refine mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (mul_nonneg hB0 ?_)
    exact measureReal_nonneg
  have hΨb : ∀ y ∈ abox n ℓ,
      |Work.UBBInputs8.boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i
        (Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ) y| ≤ M :=
    fun y hy => Work.SlotWord.abs_boxQInd_le_of_bound (N := n) ℓ (A := dlBox ℓ d u) hAa
      (volA := boxMass ℓ d u) (C := B) hB0 hfin hΨ0b i y ((mem_abox_iff n ℓ y).mp hy)
  -- ## The amplitude is bounded
  have hBamp : ∀ x ∈ abox n ℓ,
      ‖Work.SmallBoxTBWord.tBamp (chiB ℓ d u) p
        (Work.UBBInputs8.boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i
          (Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ)) i x‖
        ≤ M * ∫ z : ℝ³, |chiB ℓ d u z| :=
    fun _ hx => norm_tBamp_le_aux (continuous_chiB_aux ℓ d u)
      (Work.SmallBoxTBWord.hasCompactSupport_chiB hℓ hd u)
      (fun z hz => (chiB_support_mem hℓ hd u z hz).1) hM0 hΨb i p hx
  -- ## Measurability of the squared amplitude
  have hΨ0m : Measurable (Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ) := by
    simpa only [Work.FockBridge.sectorPiece] using
      hΦ.measurable.indicator
        (Work.FockBridge.sectorSet_measurable (dlBox ℓ d u) hAmeas k)
  have hΨm : Measurable (fun x : X n => Work.UBBInputs8.boxQInd (boxMass ℓ d u)
      (dlBox ℓ d u) i (Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ) x) :=
    Work.SlotWord.measurable_boxQInd (boxMass ℓ d u) (dlBox ℓ d u) hAmeas i hΨ0m
  have hχm : Measurable (chiB ℓ d u) := (continuous_chiB_aux ℓ d u).measurable
  have hampm : Measurable (fun x : X n => Work.SmallBoxTBWord.tBamp (chiB ℓ d u) p
      (Work.UBBInputs8.boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i
        (Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ)) i x) :=
    measurable_tBamp_aux hχm p hΨm i
  have hsqm : Measurable (fun x : X n => ‖Work.SmallBoxTBWord.tBamp (chiB ℓ d u) p
      (Work.UBBInputs8.boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i
        (Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ)) i x‖ ^ 2) :=
    hampm.norm.pow_const 2
  -- ## Integrability from the bound
  refine MeasureTheory.IntegrableOn.of_bound (abox_lt_top n ℓ hℓ.le)
    hsqm.aestronglyMeasurable ((M * ∫ z : ℝ³, |chiB ℓ d u z|) ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (abox_measurable n ℓ)] with x hx
  have hb1 : ‖Work.SmallBoxTBWord.tBamp (chiB ℓ d u) p
      (Work.UBBInputs8.boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i
        (Work.FockBridge.sectorPiece (dlBox ℓ d u) k Φ)) i x‖
      ≤ M * ∫ z : ℝ³, |chiB ℓ d u z| := hBamp x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) hb1 2

end

end Work.BoseFixB1
