import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.PB3Aux3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## 1. The diagonal of the slot projection -/

/-- **The slot projection kills its own complement**: `P_j (Q_j Φ) = 0` pointwise.  The mean of
`Q_j Φ` over the `j`-th slot vanishes because `P_j Φ` is constant in that slot. -/
theorem pb3_aP_aQ_self {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) {Φ : Xn n → ℝ}
    (hΦc : Continuous Φ) (x : Xn n) :
    Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ j Φ) x = 0 := by
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
  have hmem : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  have hpt : ∀ y : E3, Submission.BoseGases.aQ ℓ j Φ (Function.update x j y)
      = Φ (Function.update x j y) - Submission.BoseGases.aP ℓ j Φ x := by
    intro y
    rw [Submission.BoseGases.aQ, Submission.BoseGases.aP_const_in_coord hℓ j hΦc x y]
  have hInt1 : Integrable (fun y : E3 => Φ (Function.update x j y))
      ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    Submission.BoseGases.integrableOn_acube_of_continuous hℓ (hΦc.comp (by fun_prop))
  have hInt2 : Integrable (fun _ : E3 => Submission.BoseGases.aP ℓ j Φ x)
      ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
    MeasureTheory.Integrable.of_bound
      (aestronglyMeasurable_const : AEStronglyMeasurable
        (fun _ : E3 => Submission.BoseGases.aP ℓ j Φ x)
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
      ‖Submission.BoseGases.aP ℓ j Φ x‖
      (Filter.Eventually.of_forall (fun _ => le_refl _))
  have hB : (∫ y in Submission.BoseGases.acube ℓ, Φ (Function.update x j y))
      = ℓ ^ 3 * Submission.BoseGases.aP ℓ j Φ x := by
    have h3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    rw [show Submission.BoseGases.aP ℓ j Φ x = (1 / ℓ ^ 3) *
        (∫ y in Submission.BoseGases.acube ℓ, Φ (Function.update x j y)) from rfl]
    rw [one_div, ← mul_assoc, mul_inv_cancel₀ h3, one_mul]
  rw [show Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ j Φ) x
      = (1 / ℓ ^ 3) * (∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.aQ ℓ j Φ (Function.update x j y)) from rfl]
  rw [MeasureTheory.setIntegral_congr_fun hmem (fun y _ => hpt y)]
  rw [integral_sub hInt1 hInt2,
    Submission.BoseGases.integral_const_acube ℓ hℓ (Submission.BoseGases.aP ℓ j Φ x), hB,
    mul_comm (ℓ ^ 3) (Submission.BoseGases.aP ℓ j Φ x), sub_self, mul_zero]

/-! ## 2. The pair-set reindexing -/

/-- The `pairSet n`-sum of a matrix factorises as the full double sum, provided the diagonal
vanishes. -/
theorem pb3_pairSet_sum_eq {n : ℕ} (G : Fin n → Fin n → ℝ) (hdiag : ∀ j : Fin n, G j j = 0) :
    (∑ p ∈ Submission.BoseGases.pairSet n, G p.1 p.2)
      = ∑ j : Fin n, ∑ i : Fin n, G i j := by
  have h4 : ∀ j : Fin n, (∑ i : Fin n, (if i ≠ j then G i j else 0))
      = ∑ i : Fin n, G i j := by
    intro j
    rw [← Finset.sum_filter, Finset.filter_ne']
    have h := Finset.sum_erase_add Finset.univ (fun i : Fin n => G i j) (Finset.mem_univ j)
    rw [hdiag j, add_zero] at h
    exact h
  calc (∑ p ∈ Submission.BoseGases.pairSet n, G p.1 p.2)
      = ∑ p : Fin n × Fin n, (if p.1 = p.2 then 0 else G p.1 p.2) := by
        rw [Submission.BoseGases.pairSet, Finset.sum_filter]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases h : p.1 = p.2 <;> simp [h]
    _ = ∑ i : Fin n, ∑ j : Fin n, (if i = j then 0 else G i j) :=
        Fintype.sum_prod_type _
    _ = ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then G i j else 0) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        by_cases h : i = j <;> simp [h]
    _ = ∑ j : Fin n, ∑ i : Fin n, (if i ≠ j then G i j else 0) := Finset.sum_comm
    _ = ∑ j : Fin n, ∑ i : Fin n, G i j := by
        refine Finset.sum_congr rfl (fun j _ => h4 j)

/-! ## 3. The mass word as a double sum -/

/-- **`n0MassWord` factorises**: the `j`-slot mass word is the double sum over the two slot
projections. -/
theorem pb3_n0MassWord_eq {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Φ : Xn n → ℝ} (hΦc : Continuous Φ) :
    n0MassWord ℓ Φ
      = ∑ j : Fin n, ∑ i : Fin n,
          ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.chiScale ℓ (x j)) ^ 2
              * Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x
              * Submission.BoseGases.aQ ℓ j Φ x := by
  unfold n0MassWord
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hcont : ∀ i : Fin n, Continuous (fun x : Xn n =>
      Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x
        * Submission.BoseGases.aQ ℓ j Φ x
        * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2) := by
    intro i
    exact ((Submission.BoseGases.aP_continuous hℓ i
        (Submission.BoseGases.aQ_continuous hℓ j hΦc)).mul
        (Submission.BoseGases.aQ_continuous hℓ j hΦc)).mul
      (((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply j)).pow 2)
  rw [show (∫ x in Submission.BoseGases.abox n ℓ,
        (∑ i : Fin n, Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x)
          * (Submission.BoseGases.aQ ℓ j Φ x)
          * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ∑ i : Fin n, (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aQ ℓ j Φ) x
            * Submission.BoseGases.aQ ℓ j Φ x
            * (Submission.BoseGases.chiScale ℓ (x j)) ^ 2) from by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Finset.sum_mul]]
  rw [integral_finsetSum _ (fun i _ =>
    Submission.BoseGases.integrableOn_abox_of_continuous hℓ (hcont i))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  ring

/-! ## 4. The pair-set sum is the mass word -/

/-- **The `pairSet` sum of the `(i,j)`-terms of the mass word is the whole mass word.**  The
diagonal `i = j` contributes `0` by `pb3_aP_aQ_self`. -/
theorem pb3_pairSet_eq_n0MassWord {n : ℕ} {v : E3 → ℝ} {μ : ℝ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))} :
    (∑ p ∈ Submission.BoseGases.pairSet n,
      ∫ x in Submission.BoseGases.abox n (ellH v μ),
        (Submission.BoseGases.chiScale (ellH v μ) (x p.2)) ^ 2
          * Submission.BoseGases.aP (ellH v μ) p.1
              (Submission.BoseGases.aQ (ellH v μ) p.2 Φ) x
          * Submission.BoseGases.aQ (ellH v μ) p.2 Φ x)
      = n0MassWord (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  rw [pb3_pairSet_sum_eq (n := n)
    (G := fun i j => ∫ x in Submission.BoseGases.abox n (ellH v μ),
        (Submission.BoseGases.chiScale (ellH v μ) (x j)) ^ 2
          * Submission.BoseGases.aP (ellH v μ) i
              (Submission.BoseGases.aQ (ellH v μ) j Φ) x
          * Submission.BoseGases.aQ (ellH v μ) j Φ x)
    (fun j => by
      rw [show (fun x : Xn n => (Submission.BoseGases.chiScale (ellH v μ) (x j)) ^ 2
          * Submission.BoseGases.aP (ellH v μ) j
              (Submission.BoseGases.aQ (ellH v μ) j Φ) x
          * Submission.BoseGases.aQ (ellH v μ) j Φ x) = fun _ => (0 : ℝ) from
        funext (fun x => by rw [pb3_aP_aQ_self hℓ j hΦc x, mul_zero, zero_mul])]
      simp)]
  exact (pb3_n0MassWord_eq hℓ hΦc).symm

end

end Work.BoseBoxFock
