import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseB4.BoxChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.exists_boxData` — a `BoxData` whose cell is the unit cube `[-1/2,1/2]³`

FS's localization data `Work.BoseB4.BoxData` asks for a continuous, nonnegative, even
localization function `χ` supported in a unit cell `cell ⊆ ℝ³` of volume `1`, normalised
by `∫χ² = 1`.  This module produces an explicit instance with

  `cell = {x : ℝ³ | ∀ i, |x i| ≤ 1/2}`   (the cube of side `1`),

so that the corpus can use *concrete* localization data (the cube, with a bump `χ` built
from `max 0 (1/4 - t²)`, normalised by `(∫F²)^{-1/2}` with `F = ⊗ᵢ bump1(xᵢ)`).

Everything is stated over `ℝ³ = EuclideanSpace ℝ (Fin 3)` with the Lebesgue/`addHaar`
measure; `y.ofLp` is the underlying function of `y : ℝ³`, and `y i = y.ofLp i` holds
definitionally.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical Filter

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The unit cube `[-1/2,1/2]³` and its measure theory -/

/-- FS's unit cell: the cube `[-1/2,1/2]³` of side `1`. -/
def unitCell : Set ℝ³ := {x | ∀ i, |x i| ≤ (1 / 2 : ℝ)}

/-- The cube written in `ofLp` coordinates, as a product of intervals. -/
lemma unitCell_eq_coordBox :
    unitCell = {x : ℝ³ | ∀ i, x.ofLp i ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)} := by
  ext x
  simp only [unitCell, Set.mem_ofPred_eq, Set.mem_Icc]
  exact ⟨fun h i => abs_le.mp (h i), fun h i => abs_le.mpr (h i)⟩

/-- **The unit cube has volume `1`.**  Written as a product of three intervals of length
`1` through the volume-preserving identification `ℝ³ ≃ (Fin 3 → ℝ)`. -/
lemma volume_unitCell : volume unitCell = 1 := by
  let C : Set (Fin 3 → ℝ) := {f | ∀ k, f k ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)}
  have hcell : unitCell = (WithLp.ofLp : ℝ³ → (Fin 3 → ℝ)) ⁻¹' C := by
    ext y
    simp only [unitCell, Set.mem_ofPred_eq, Set.mem_preimage, C, Set.mem_Icc]
    exact ⟨fun h k => abs_le.mp (h k), fun h k => abs_le.mpr (h k)⟩
  rw [hcell]
  have hCpi : C =
      (Set.univ : Set (Fin 3)).pi (fun _ : Fin 3 => (Set.Icc (-(1 / 2) : ℝ) (1 / 2) : Set ℝ)) := by
    ext f
    simp only [C, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
  have hCmeas : MeasurableSet C := by
    rw [hCpi]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
  rw [MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    hCmeas.nullMeasurableSet]
  rw [hCpi, MeasureTheory.volume_pi,
    MeasureTheory.Measure.pi_pi (μ := fun _ : Fin 3 => (volume : Measure ℝ))
      (s := fun _ : Fin 3 => (Set.Icc (-(1 / 2) : ℝ) (1 / 2) : Set ℝ))]
  simp only [Real.volume_Icc, Finset.prod_const]
  norm_num

lemma isClosed_unitCell : IsClosed unitCell := by
  have h : unitCell = ⋂ i : Fin 3, {x : ℝ³ | |x i| ≤ (1 / 2 : ℝ)} := by
    ext x
    simp only [unitCell, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i))
      continuous_const

lemma isCompact_unitCell : IsCompact unitCell := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ³) 1) isClosed_unitCell ?_
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  have h2 : ‖x‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin 3, ‖x.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, ((1 / 2 : ℝ)) ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi : ‖x.ofLp i‖ ≤ (1 / 2 : ℝ) := by simpa [Real.norm_eq_abs] using hx i
          exact pow_le_pow_left₀ (norm_nonneg _) hi 2
      _ = 3 / 4 := by simp [Finset.sum_const, Fintype.card_fin]; norm_num
      _ ≤ (1 : ℝ) ^ 2 := by norm_num
  nlinarith [h2, norm_nonneg x]

/-! ## The bump function `F = ⊗ᵢ max 0 (1/4 - xᵢ²)` -/

/-- The one-dimensional bump `t ↦ max 0 (1/4 - t²)`: continuous, nonnegative, even,
vanishing off `[-1/2,1/2]`. -/
def bump1 (t : ℝ) : ℝ := max 0 ((1 / 4 : ℝ) - t ^ 2)

lemma continuous_bump1 : Continuous bump1 :=
  continuous_const.max (continuous_const.sub (continuous_id.pow 2))

lemma bump1_nonneg (t : ℝ) : 0 ≤ bump1 t := le_max_left _ _

lemma bump1_even (t : ℝ) : bump1 (-t) = bump1 t := by simp only [bump1, neg_sq]

/-- `bump1 t ≠ 0` forces `|t| < 1/2` — the support condition for `χ`. -/
lemma abs_lt_half_of_bump1_ne_zero {t : ℝ} (h : bump1 t ≠ 0) : |t| < 1 / 2 := by
  have hlt : 0 < (1 / 4 : ℝ) - t ^ 2 := by
    by_contra hc
    exact h (max_eq_left (not_lt.mp hc))
  have hsq : t ^ 2 < (1 / 2 : ℝ) ^ 2 := by norm_num at hlt ⊢; linarith
  rw [sq_lt_sq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hsq
  exact hsq

/-- The product bump on the cube. -/
def bumpF (x : ℝ³) : ℝ := ∏ i : Fin 3, bump1 (x i)

lemma continuous_bumpF : Continuous bumpF := by
  unfold bumpF
  exact continuous_finsetProd _
    (fun i _ => continuous_bump1.comp (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i))

lemma bumpF_nonneg (x : ℝ³) : 0 ≤ bumpF x := by
  unfold bumpF
  exact Finset.prod_nonneg (fun i _ => bump1_nonneg (x i))

lemma bumpF_even (x : ℝ³) : bumpF (-x) = bumpF x := by
  unfold bumpF
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [PiLp.neg_apply, bump1_even]

lemma bumpF_zero : bumpF (0 : ℝ³) = (1 / 4 : ℝ) ^ 3 := by
  simp [bumpF, bump1]

lemma bumpF_zero_ne : bumpF (0 : ℝ³) ≠ 0 := by
  rw [bumpF_zero]; norm_num

lemma bumpF_supp_subset : Function.support bumpF ⊆ unitCell := by
  intro x hx
  simp only [unitCell, Set.mem_ofPred_eq]
  intro i
  have hi : bump1 (x i) ≠ 0 :=
    fun hzero => hx (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
  exact le_of_lt (abs_lt_half_of_bump1_ne_zero hi)

lemma hasCompactSupport_bumpF : HasCompactSupport bumpF :=
  isCompact_unitCell.of_isClosed_subset (isClosed_tsupport bumpF)
    (closure_minimal bumpF_supp_subset isCompact_unitCell.isClosed)

lemma integrable_bumpF_sq : Integrable (fun x : ℝ³ => (bumpF x) ^ 2) := by
  have hcs : HasCompactSupport (bumpF * bumpF) := hasCompactSupport_bumpF.mul_right (f' := bumpF)
  have hcont : Continuous (bumpF * bumpF) := continuous_bumpF.mul continuous_bumpF
  refine (hcont.integrable_of_hasCompactSupport hcs).congr (Eventually.of_forall fun x => ?_)
  simp [Pi.mul_apply, pow_two]

/-- `∫F² > 0`: `F` is continuous and does not vanish at the origin. -/
lemma integral_bumpF_sq_pos : 0 < ∫ y : ℝ³, (bumpF y) ^ 2 := by
  rw [integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun y => by positivity) integrable_bumpF_sq]
  exact (continuous_bumpF.pow 2).isOpen_support.measure_pos volume
    ⟨0, by rw [Function.mem_support]; exact pow_ne_zero 2 bumpF_zero_ne⟩

/-! ## The normalised localization function -/

/-- `χ = (∫F²)^{-1/2} F`: the bump normalised so that `∫χ² = 1`. -/
def unitChi (x : ℝ³) : ℝ := ((Real.sqrt (∫ y : ℝ³, (bumpF y) ^ 2))⁻¹) * bumpF x

lemma continuous_unitChi : Continuous unitChi := continuous_const.mul continuous_bumpF

lemma unitChi_nonneg (x : ℝ³) : 0 ≤ unitChi x :=
  mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (bumpF_nonneg x)

lemma unitChi_even (x : ℝ³) : unitChi (-x) = unitChi x := by
  unfold unitChi
  rw [bumpF_even]

lemma unitChi_supp_subset : Function.support unitChi ⊆ unitCell := by
  intro x hx
  refine bumpF_supp_subset ?_
  intro hb
  exact hx (by unfold unitChi; rw [hb, mul_zero])

/-- **The normalisation `∫χ² = 1`.** -/
lemma integral_unitChi_sq : ∫ x : ℝ³, (unitChi x) ^ 2 = 1 := by
  have hIpos : 0 < ∫ y : ℝ³, (bumpF y) ^ 2 := integral_bumpF_sq_pos
  have hIne : (∫ y : ℝ³, (bumpF y) ^ 2) ≠ 0 := ne_of_gt hIpos
  have hcongr : ∀ x : ℝ³,
      (unitChi x) ^ 2 = (((Real.sqrt (∫ y : ℝ³, (bumpF y) ^ 2))⁻¹) ^ 2) * (bumpF x) ^ 2 := by
    intro x
    unfold unitChi
    rw [mul_pow]
  calc ∫ x : ℝ³, (unitChi x) ^ 2
      = ∫ x : ℝ³, (((Real.sqrt (∫ y : ℝ³, (bumpF y) ^ 2))⁻¹) ^ 2) * (bumpF x) ^ 2 :=
        integral_congr_ae (Eventually.of_forall hcongr)
    _ = (((Real.sqrt (∫ y : ℝ³, (bumpF y) ^ 2))⁻¹) ^ 2) * ∫ x : ℝ³, (bumpF x) ^ 2 := by
        rw [integral_const_mul]
    _ = (((Real.sqrt (∫ y : ℝ³, (bumpF y) ^ 2)) ^ 2)⁻¹) * (∫ y : ℝ³, (bumpF y) ^ 2) := by
        rw [inv_pow]
    _ = ((∫ y : ℝ³, (bumpF y) ^ 2)⁻¹) * (∫ y : ℝ³, (bumpF y) ^ 2) := by
        rw [Real.sq_sqrt (le_of_lt hIpos)]
    _ = 1 := inv_mul_cancel₀ hIne

/-! ## The localization data -/

theorem exists_boxData :
    ∃ B : Work.BoseB4.BoxData,
      B.cell = {x : EuclideanSpace ℝ (Fin 3) | ∀ i, |x i| ≤ (1 / 2 : ℝ)} :=
  ⟨{ chi := unitChi
     chi_cont := continuous_unitChi
     chi_nonneg := unitChi_nonneg
     chi_even := unitChi_even
     cell := unitCell
     cell_meas := isClosed_unitCell.measurableSet
     cell_compact := isCompact_unitCell
     cell_vol := volume_unitCell
     chi_supp := unitChi_supp_subset
     chi_int := integral_unitChi_sq }, rfl⟩

end Work.BoseB4
