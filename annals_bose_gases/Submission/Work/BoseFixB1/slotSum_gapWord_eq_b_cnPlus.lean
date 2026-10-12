import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.slotSum_gapWord_eq_b_cnPlus`

The gap word of the localised kinetic operator, summed over the particle slots against the
box indicator, is exactly the large-box excited count:

`ℓ⁻³ Σᵢ ∫_{abox (n+1) ℓ} 1_{Λ}(xᵢ) · (bℓ⁻² ∫_{Λ} (Q_{Λ} fibreᵢ Φ(x))²) dx = b ℓ⁻² n₊(Φ)`,
`n₊ = cnPlus ℓ Φ`.

The proof is bookkeeping around three pointwise facts and one measure-theoretic identity:

* `indU ℓ 0 (xᵢ) = 1` on the centred box (`abox_measurable`, `Set.indicator_of_mem`);
* `gapWord ℓ b 0 ψ = b ℓ⁻² ∫_{acube ℓ} (bsQ ℓ 0 ψ)²` (the anchored box `Λ(0)` is `acube ℓ`);
* `bsQ ℓ 0 (fibre (n+1) i Φ x) z = aQ ℓ i Φ (Function.update x i z)`
  (the box mean of the `i`-th fibre is the condensate mean `aP`);
* **slot duplication**: for continuous `F`,
  `∫_{abox (n+1) ℓ} ∫_{acube ℓ} F (Function.update x i z) dz dx = ℓ³ ∫_{abox (n+1) ℓ} F x dx`
  — the map `x ↦ Function.update x i z` forgets the `i`-th coordinate, so integrating the
  extra coordinate `z` over the box costs the box volume `ℓ³`.

Since `cnPlus ℓ Φ = Σᵢ ∫_{abox (n+1) ℓ} (aQ ℓ i Φ x)²`, the sum over the slots together with
`ℓ⁻³·ℓ³ = 1` gives the claim.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real Topology

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Pointwise helpers -/

/-- The anchored moving box `Λ(0)` is the centred cube `acube ℓ`. -/
private theorem lamBox_zero_slotSum (ℓ : ℝ) :
    Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
  ext x
  simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]

/-- The box indicator is `1` on the centred cube. -/
private theorem indU_zero_eq_one_slotSum {ℓ : ℝ} {y : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ Submission.BoseGases.acube ℓ) : Work.BoseKinLoc.indU ℓ 0 y = 1 := by
  rw [Work.BoseKinLoc.indU, lamBox_zero_slotSum]
  exact Set.indicator_of_mem hy _

/-- The gap word is `bℓ⁻²` times the mean-free box mass of the state over the anchored box. -/
private theorem gapWord_zero_eq_slotSum (ℓ b : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.gapWord ℓ b 0 ψ
      = b * ℓ ^ (-2 : ℤ) * ∫ z in Submission.BoseGases.acube ℓ,
          (Work.BSKinetic.bsQ ℓ 0 ψ z) ^ 2 := by
  simp only [Work.BoseKinLoc.gapWord, Work.BoseKinLoc.gapBare, Work.BoseKinLoc.Qfree,
    lamBox_zero_slotSum]

/-- The mean-free projection travels to the fibre: the box mean of the `i`-th fibre is the
condensate mean `aP`, so the anchored `bsQ` of the fibre is `aQ` of the flattened state. -/
private theorem bsQ_fibre_eq_slotSum {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (x : Submission.BoseGases.X (n + 1))
    (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BSKinetic.bsQ ℓ 0 (Work.BoseKinLoc.fibre (n + 1) i Φ x) z
      = Submission.BoseGases.aQ ℓ i Φ (Function.update x i z) := by
  simp only [Work.BSKinetic.bsQ, Work.BSKinetic.bsMean, Work.BoseKinLoc.fibre,
    Submission.BoseGases.aQ, Submission.BoseGases.aP, smul_zero, zero_add, one_div,
    Function.update_idem]

/-! ## The slot-duplication identity

For a continuous `F`, integrating the extra coordinate `z` of `Function.update x i z` over the
box costs the volume `ℓ³` of the forgotten coordinate.  The proof peels the `i`-th slot with
`Submission.BoseGases.abox_integral_peel_gen`: after the peel the integrand `G (kcInsN n i (y,r))`
is independent of `y`, so the `y`-integral is `ℓ³` times the remaining integral; comparing with
the peel of `F` itself gives the claim.  (`IntegrableOn` of the peeled function `G` is obtained
from the bound `M·ℓ³`, `M` a bound of `F` on the compact box.) -/

private theorem update_slot_abox_integral_slotSum {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i : Fin (n + 1)) {F : Submission.BoseGases.X (n + 1) → ℝ} (hF : Continuous F) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        ∫ z in Submission.BoseGases.acube ℓ, F (Function.update x i z))
      = ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x := by
  have hFint : IntegrableOn F (Submission.BoseGases.abox (n + 1) ℓ) volume :=
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ hF
  obtain ⟨M, hM⟩ := (Submission.BoseGases.abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
    hF.continuousOn
  have hreal : (volume : Measure (EuclideanSpace ℝ (Fin 3))).real
      (Submission.BoseGases.acube ℓ) = ℓ ^ 3 := by
    rw [MeasureTheory.Measure.real, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  have hvol_lt : volume (Submission.BoseGases.acube ℓ) < ⊤ := by
    rw [Submission.BoseGases.acube_volume ℓ hℓ.le]
    exact ENNReal.ofReal_lt_top
  set G : Submission.BoseGases.X (n + 1) → ℝ :=
    fun x => ∫ z in Submission.BoseGases.acube ℓ, F (Function.update x i z) with hGdef
  have hGmeas : AEStronglyMeasurable G
      (volume.restrict (Submission.BoseGases.abox (n + 1) ℓ)) := by
    have hjoint : StronglyMeasurable
        (Function.uncurry (fun x : Submission.BoseGases.X (n + 1) =>
          fun z : EuclideanSpace ℝ (Fin 3) => F (Function.update x i z))) :=
      hF.stronglyMeasurable.comp_measurable (measurable_update' (a := i))
    have h := MeasureTheory.StronglyMeasurable.integral_prod_right
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)) hjoint
    rw [hGdef]
    exact h.aestronglyMeasurable
  have hGbound : ∀ x ∈ Submission.BoseGases.abox (n + 1) ℓ, ‖G x‖ ≤ M * ℓ ^ 3 := by
    intro x hx
    rw [hGdef]
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
      (s := Submission.BoseGases.acube ℓ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (f := fun z => F (Function.update x i z)) (C := M) hvol_lt
      (fun z hz => hM _ (Submission.BoseGases.update_mem_abox i hx hz))
    rwa [hreal] at h
  have hGint : IntegrableOn G (Submission.BoseGases.abox (n + 1) ℓ) volume := by
    refine MeasureTheory.IntegrableOn.of_bound ?_ hGmeas (M * ℓ ^ 3) ?_
    · rw [Submission.BoseGases.abox_volume (n + 1) ℓ hℓ.le]
      exact ENNReal.ofReal_lt_top
    · filter_upwards [MeasureTheory.ae_restrict_mem
        (Submission.BoseGases.abox_measurable (n + 1) ℓ)] with x hx
      exact hGbound x hx
  have hpeelG := Submission.BoseGases.abox_integral_peel_gen (ℓ := ℓ) i G hGint
  have hpeelF := Submission.BoseGases.abox_integral_peel_gen (ℓ := ℓ) i F hFint
  have hinner : ∀ r : Submission.BoseGases.X n,
      (∫ y in Submission.BoseGases.acube ℓ, G ((Submission.BoseGases.kcInsN n i) (y, r)))
        = ℓ ^ 3 * (∫ z in Submission.BoseGases.acube ℓ,
            F ((Submission.BoseGases.kcInsN n i) (z, r))) := by
    intro r
    have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
        G ((Submission.BoseGases.kcInsN n i) (y, r))
          = (∫ z in Submission.BoseGases.acube ℓ,
              F ((Submission.BoseGases.kcInsN n i) (z, r))) := by
      intro y
      rw [hGdef]
      refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) ?_
      intro z hz
      simp only [Submission.BoseGases.update_kcInsN]
    rw [show (∫ y in Submission.BoseGases.acube ℓ,
          G ((Submission.BoseGases.kcInsN n i) (y, r)))
        = ∫ y in Submission.BoseGases.acube ℓ,
            (∫ z in Submission.BoseGases.acube ℓ,
              F ((Submission.BoseGases.kcInsN n i) (z, r))) from
      MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
        (fun y _ => hpt y)]
    rw [MeasureTheory.setIntegral_const, hreal]
    simp
  calc (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        ∫ z in Submission.BoseGases.acube ℓ, F (Function.update x i z))
      = ∫ x in Submission.BoseGases.abox (n + 1) ℓ, G x := by simp only [hGdef]
    _ = ∫ r in Submission.BoseGases.abox n ℓ,
          ∫ y in Submission.BoseGases.acube ℓ,
            G ((Submission.BoseGases.kcInsN n i) (y, r)) := hpeelG
    _ = ∫ r in Submission.BoseGases.abox n ℓ, ℓ ^ 3 *
          (∫ z in Submission.BoseGases.acube ℓ,
            F ((Submission.BoseGases.kcInsN n i) (z, r))) := by
        exact MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
          (fun r _ => hinner r)
    _ = ℓ ^ 3 * ∫ r in Submission.BoseGases.abox n ℓ,
          ∫ z in Submission.BoseGases.acube ℓ,
            F ((Submission.BoseGases.kcInsN n i) (z, r)) := by
        rw [MeasureTheory.integral_const_mul]
    _ = ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x := by rw [hpeelF]

/-! ## The main identity -/

theorem slotSum_gapWord_eq_b_cnPlus {n : ℕ} {ℓ b : ℝ} (hℓ : 0 < ℓ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) :
    ℓ ^ (-3 : ℤ) * (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (n + 1) i Φ x))
      = b * ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ Φ := by
  have hcont : Continuous Φ := hΦ.continuous
  -- ## Per-slot value
  have hterm : ∀ i : Fin (n + 1),
      (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (n + 1) i Φ x))
        = b * ℓ ^ (-2 : ℤ) * ℓ ^ 3
            * ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
                (Submission.BoseGases.aQ ℓ i Φ x) ^ 2 := by
    intro i
    -- drop the box indicator (it is `1` on the box)
    have h1 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          Work.BoseKinLoc.indU ℓ 0 (x i)
            * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (n + 1) i Φ x))
        = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (n + 1) i Φ x) := by
      refine MeasureTheory.setIntegral_congr_fun
        (Submission.BoseGases.abox_measurable (n + 1) ℓ) ?_
      intro x hx
      simp only [indU_zero_eq_one_slotSum (hx i), one_mul]
    rw [h1]
    -- unfold `gapWord` and identify `bsQ` of the fibre with `aQ` of the flattened state
    have h2 : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (n + 1) i Φ x))
        = ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            b * ℓ ^ (-2 : ℤ) * ∫ z in Submission.BoseGases.acube ℓ,
                (Submission.BoseGases.aQ ℓ i Φ (Function.update x i z)) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun
        (Submission.BoseGases.abox_measurable (n + 1) ℓ) ?_
      intro x hx
      simp only [gapWord_zero_eq_slotSum]
      congr 1
      refine MeasureTheory.setIntegral_congr_fun
        (Submission.BoseGases.acube_measurable ℓ) ?_
      intro z hz
      simp only [bsQ_fibre_eq_slotSum i Φ x z]
    rw [h2, MeasureTheory.integral_const_mul]
    -- the slot-duplication identity, with `F = (QᵢΦ)²`
    have key : (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          ∫ z in Submission.BoseGases.acube ℓ,
            (Submission.BoseGases.aQ ℓ i Φ (Function.update x i z)) ^ 2)
        = ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
            (Submission.BoseGases.aQ ℓ i Φ x) ^ 2 := by
      simpa only [] using update_slot_abox_integral_slotSum hℓ i
        (F := fun x => (Submission.BoseGases.aQ ℓ i Φ x) ^ 2)
        ((Submission.BoseGases.aQ_continuous hℓ i hcont).pow 2)
    rw [key]
    ring
  -- ## Sum over the slots: `Σᵢ ∫ (QᵢΦ)² = cnPlus ℓ Φ`
  have hsum : (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i)
          * Work.BoseKinLoc.gapWord ℓ b 0 (Work.BoseKinLoc.fibre (n + 1) i Φ x))
      = b * ℓ ^ (-2 : ℤ) * ℓ ^ 3 * Submission.BoseGases.cnPlus ℓ Φ := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
    congr 1
  rw [hsum]
  -- ## The `ℓ⁻³` prefactor cancels the volume factor
  have h3 : ℓ ^ (-3 : ℤ) * ℓ ^ 3 = 1 := by
    rw [← zpow_natCast ℓ 3, ← zpow_add₀ (ne_of_gt hℓ)]
    norm_num
  rw [show ℓ ^ (-3 : ℤ) * (b * ℓ ^ (-2 : ℤ) * ℓ ^ 3 * Submission.BoseGases.cnPlus ℓ Φ)
      = (ℓ ^ (-3 : ℤ) * ℓ ^ 3) * (b * ℓ ^ (-2 : ℤ) * Submission.BoseGases.cnPlus ℓ Φ) by ring,
    h3, one_mul]

end Work.BoseFixB1
