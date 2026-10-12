import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1P.AcubeSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1P

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Real
open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- **Sharp mean-free Poincare inequality on an axis-parallel box of `R^3`** whose sides are all
`<= a`: for smooth mean-free `u`, `pi^2/a^2 * int_B u^2 <= int_B sum_k (partial_k u)^2`.  The
constant `pi^2/a^2` is the sharp cube constant and must not be weakened.

Route. (1) The cube `Box3 (-a/2) (a/2) = acube a` (see `Work.BoseFixB1P.Box3_cube`): combine the two
PROVED Neumann Parseval identities `Work.SmallBoxModeParseval.acube_parseval_boxNeumann3`
(Continuous input; gives `int_{acube a} u^2 = sum'_k c_k` with
`c_k = (int u * boxNeumann3 a k)^2 / prod_j (if k_j = 0 then a else a/2)`) and
`Work.SmallBoxA0.boxNeumann3_deriv_parseval` (ContDiff 2 input; gives
`int sum_k (partial_k u)^2 = sum'_k lam_k c_k` with `lam_k = sum_j (pi k_j/a)^2`).  For `k = 0` the
coefficient vanishes by the mean-free hypothesis (`boxNeumann3_zero_eq_one`) and
`lam_k >= pi^2/a^2` for `k != 0`; compare the two series termwise.
(2) A general box with corners `p q : Fin 3 -> R` and sides `L_j = q_j - p_j <= a` is the image of
the cube `acube a` under the diagonal affine map `Psi y = p + ((y_j + a/2) * (L_j/a))_j`, which is
a diagonal linear map `A` (with `|det A| = prod_j L_j/a`) followed by a translation.  With
`v = u o Psi`, the change of variables for `A` (`MeasureTheory.map_linearMap_addHaar_eq_smul_addHaar`
/ `MeasureTheory.Measure.addHaar_image_linearMap`, plus translation invariance) gives
`int_{acube a} v^2 = (prod_j L_j/a)^{-1} int_B u^2` and
`int_{acube a} (partial_j v)^2 = (prod_j L_j/a)^{-1} (L_j/a)^{-2} int_B (partial_j u)^2`, so the cube
inequality yields `pi^2/a^2 int_B u^2 <= sum_j (L_j/a)^2 int_B (partial_j u)^2 <= sum_j int_B
(partial_j u)^2`.  (Degenerate boxes are null sets, where both sides vanish.) -/
theorem boxPoincareSharp {a : ℝ} (ha : 0 < a) (p q : Fin 3 → ℝ)
    (hpq : ∀ j : Fin 3, q j - p j ≤ a) (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu : ContDiff ℝ (⊤ : ENat) u) (hmean : (∫ x in Work.BoseFixB1P.Box3 p q, u x) = 0) :
    Real.pi ^ 2 / a ^ 2 * (∫ x in Work.BoseFixB1P.Box3 p q, (u x) ^ 2)
      ≤ ∑ k : Fin 3, ∫ x in Work.BoseFixB1P.Box3 p q,
          (fderiv ℝ u x (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hcont_k : ∀ k : Fin 3, Continuous (fun x : E3 => fderiv ℝ u x (kcStdBasis k)) :=
    fun k => (hu2.continuous_fderiv (by norm_num)).clm_apply continuous_const
  by_cases hemp : ∃ j : Fin 3, q j < p j
  · obtain ⟨j, hj⟩ := hemp
    have hempty : Box3 p q = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have h := hx j
      simp only [Set.mem_Icc] at h
      linarith
    rw [hempty]
    simp
  · have hL : ∀ j : Fin 3, 0 ≤ q j - p j := by
      intro j
      by_contra h
      exact hemp ⟨j, by linarith⟩
    by_cases hdeg : ∃ j : Fin 3, q j - p j = 0
    · obtain ⟨j, hj⟩ := hdeg
      have hnull : (volume : Measure E3) (Box3 p q) = 0 :=
        volume_Box3_eq_zero ⟨j, by linarith [hj]⟩
      have h1 : (∫ x in Box3 p q, (u x) ^ 2) = 0 := setIntegral_measure_zero _ hnull
      have h2 : ∀ k : Fin 3, (∫ x in Box3 p q,
          (fderiv ℝ u x (kcStdBasis k)) ^ 2) = 0 :=
        fun k => setIntegral_measure_zero _ hnull
      rw [h1, Finset.sum_congr rfl (fun k _ => h2 k)]
      simp
    · have hpos : ∀ j : Fin 3, 0 < q j - p j := fun j =>
        lt_of_le_of_ne (hL j) (fun h => hdeg ⟨j, h.symm⟩)
      set C : ℝ := ∏ j : Fin 3, (q j - p j) / a with hC
      set v : E3 → ℝ := fun y => u (boxScale a p q y) with hv
      have hCpos : 0 < C := by
        rw [hC]
        exact Finset.prod_pos (fun j _ => div_pos (hpos j) ha)
      have hCne : C ≠ 0 := ne_of_gt hCpos
      have hv_cd : ContDiff ℝ (⊤ : ENat) v := by
        rw [hv]
        exact contDiff_comp_boxScale hu a p q
      have hmean_box : (∫ x in Box3 p q, u x) = C * ∫ y in acube a, v y := by
        rw [hC]
        exact integralBoxScaleImage ha hL (F := fun x => u x) hu.continuous
      have hmeanv : (∫ y in acube a, v y) = 0 := by
        have h := hmean_box.symm.trans hmean
        exact (mul_eq_zero.mp h).resolve_left hCne
      have hcube := acubeSharp ha hv_cd hmeanv
      have h2L : (∫ x in Box3 p q, (u x) ^ 2) = C * ∫ y in acube a, (v y) ^ 2 := by
        rw [hC]
        exact integralBoxScaleImage ha hL (F := fun x => (u x) ^ 2) (hu.continuous.pow 2)
      have h3L : ∀ k : Fin 3, (∫ x in Box3 p q, (fderiv ℝ u x (kcStdBasis k)) ^ 2)
          = C * ∫ y in acube a, (fderiv ℝ u (boxScale a p q y) (kcStdBasis k)) ^ 2 := by
        intro k
        rw [hC]
        exact integralBoxScaleImage ha hL (F := fun x => (fderiv ℝ u x (kcStdBasis k)) ^ 2)
          ((hcont_k k).pow 2)
      have hderiv : ∀ k : Fin 3, (∫ y in acube a, (fderiv ℝ v y (kcStdBasis k)) ^ 2)
          = ((q k - p k) / a) ^ 2
            * ∫ y in acube a, (fderiv ℝ u (boxScale a p q y) (kcStdBasis k)) ^ 2 := by
        intro k
        have hpt : ∀ y : E3, fderiv ℝ v y (kcStdBasis k)
            = ((q k - p k) / a) * fderiv ℝ u (boxScale a p q y) (kcStdBasis k) := by
          intro y
          rw [hv]
          exact fderiv_boxScale ha p q hu k y
        calc (∫ y in acube a, (fderiv ℝ v y (kcStdBasis k)) ^ 2)
            = ∫ y in acube a,
                (((q k - p k) / a)
                  * fderiv ℝ u (boxScale a p q y) (kcStdBasis k)) ^ 2 := by
              apply setIntegral_congr_fun (acube_measurable a)
              intro y _
              simp only [hpt]
          _ = ((q k - p k) / a) ^ 2
                * ∫ y in acube a,
                    (fderiv ℝ u (boxScale a p q y) (kcStdBasis k)) ^ 2 := by
              rw [show (fun y : E3 => (((q k - p k) / a)
                    * fderiv ℝ u (boxScale a p q y) (kcStdBasis k)) ^ 2)
                  = fun y : E3 => ((q k - p k) / a) ^ 2
                    * (fderiv ℝ u (boxScale a p q y) (kcStdBasis k)) ^ 2 from
                funext (fun y => by ring)]
              rw [integral_const_mul]
      have hstep : Real.pi ^ 2 / a ^ 2 * (∫ x in Box3 p q, (u x) ^ 2)
          ≤ ∑ k : Fin 3, ((q k - p k) / a) ^ 2
              * (∫ x in Box3 p q, (fderiv ℝ u x (kcStdBasis k)) ^ 2) := by
        have hmul : C * (Real.pi ^ 2 / a ^ 2 * (∫ y in acube a, (v y) ^ 2))
            ≤ C * (∑ k : Fin 3, ∫ y in acube a, (fderiv ℝ v y (kcStdBasis k)) ^ 2) :=
          mul_le_mul_of_nonneg_left hcube (le_of_lt hCpos)
        calc Real.pi ^ 2 / a ^ 2 * (∫ x in Box3 p q, (u x) ^ 2)
            = C * (Real.pi ^ 2 / a ^ 2 * (∫ y in acube a, (v y) ^ 2)) := by
              rw [h2L]; ring
          _ ≤ C * (∑ k : Fin 3, ∫ y in acube a, (fderiv ℝ v y (kcStdBasis k)) ^ 2) := hmul
          _ = ∑ k : Fin 3, ((q k - p k) / a) ^ 2
                * (∫ x in Box3 p q, (fderiv ℝ u x (kcStdBasis k)) ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              rw [hderiv k, h3L k]
              ring
      have hfinal : ∑ k : Fin 3, ((q k - p k) / a) ^ 2
            * (∫ x in Box3 p q, (fderiv ℝ u x (kcStdBasis k)) ^ 2)
          ≤ ∑ k : Fin 3, ∫ x in Box3 p q, (fderiv ℝ u x (kcStdBasis k)) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have h0 : 0 ≤ (q k - p k) / a := (div_pos (hpos k) ha).le
        have h1 : (q k - p k) / a ≤ 1 := (div_le_one ha).mpr (hpq k)
        have hck : ((q k - p k) / a) ^ 2 ≤ 1 := by nlinarith [h0, h1]
        have hD : 0 ≤ ∫ x in Box3 p q, (fderiv ℝ u x (kcStdBasis k)) ^ 2 :=
          integral_nonneg (fun x => sq_nonneg _)
        exact mul_le_of_le_one_left hD hck
      exact hstep.trans hfinal

end

end Work.BoseFixB1P
