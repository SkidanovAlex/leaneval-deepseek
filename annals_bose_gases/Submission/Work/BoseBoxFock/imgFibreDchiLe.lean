import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.imagesFibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibreDchiLe`

The `χ`-weighted Dirichlet content of a state (`imgFibreDχ`) is **not increased** by the box
projections `aP ℓ i`, `aQ ℓ i` acting in a slot `i` *different* from the differentiated slot
`p.1`:

    imgFibreDχ ℓ p (aP ℓ i F) ≤ imgFibreDχ ℓ p F ,      imgFibreDχ ℓ p (aQ ℓ i F) ≤ imgFibreDχ ℓ p F .

## The mathematics

Write `c x := chiScale ℓ (x p.1)` for the window in the differentiated slot.  Since `i ≠ p.1`:

* **the window is constant in slot `i`**, so it commutes with the slot-`i` box mean
  (`aP_mul_constIn`, `aQ_mul_constIn`):

      aP ℓ i (c · h) = c · aP ℓ i h ,        aQ ℓ i (c · h) = c · aQ ℓ i h ;

* **the differentiation in slot `p.1` commutes with the slot-`i` mean**
  (`SmallBoxKinBridge.fderiv_aP_kcDir_of_ne`, `fderiv_aQ_kcDir_of_ne`):

      ∂_{p.1,j}(aP ℓ i F) = aP ℓ i (∂_{p.1,j}F) ,     ∂_{p.1,j}(aQ ℓ i F) = aQ ℓ i (∂_{p.1,j}F) ;

* **the slot mean and the mean-subtraction are `L²`-contractions on the centred box**
  (`Q0Sector.aP_sq_le`, `SmallBoxKinBridge.integral_aQ_sq_le`):

      ∫_{abox N ℓ} (aP ℓ i h)² ≤ ∫_{abox N ℓ} h² ,    ∫_{abox N ℓ} (aQ ℓ i h)² ≤ ∫_{abox N ℓ} h² .

Combining them with `h := c·∂_{p.1,j}F` produces the desired contraction in each coordinate
direction `j`, and the three directions are summed.  (The window is *absorbed* into `h`, which is
why the unweighted `L²` contraction suffices and no weighted `L²` theory is needed.)
-/

noncomputable section

set_option linter.unusedVariables false

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X

open Submission.BoseGases

/-! ## 1. A slot-`i`-constant factor commutes with the slot-`i` box mean -/

/-- A factor `c` that is constant in slot `i` pulls out of the slot-`i` box mean. -/
lemma aP_mul_constIn {n : ℕ} {ℓ : ℝ} (i : Fin n) {c g : Xn n → ℝ}
    (hc : ∀ (x : Xn n) (z : E3), c (Function.update x i z) = c x) :
    aP ℓ i (fun x => c x * g x) = fun x => c x * aP ℓ i g x := by
  funext y
  have h1 : (fun z : E3 => c (Function.update y i z) * g (Function.update y i z))
      = fun z : E3 => c y * g (Function.update y i z) := funext (fun z => by rw [hc y z])
  show (1 / ℓ ^ 3) * (∫ z in acube ℓ, c (Function.update y i z) * g (Function.update y i z))
    = c y * ((1 / ℓ ^ 3) * (∫ z in acube ℓ, g (Function.update y i z)))
  rw [h1, MeasureTheory.integral_const_mul]
  ring

/-- The same for the complement projection `Qᵢ = 1 − Pᵢ`. -/
lemma aQ_mul_constIn {n : ℕ} {ℓ : ℝ} (i : Fin n) {c g : Xn n → ℝ}
    (hc : ∀ (x : Xn n) (z : E3), c (Function.update x i z) = c x) :
    aQ ℓ i (fun x => c x * g x) = fun x => c x * aQ ℓ i g x := by
  funext y
  have h : aP ℓ i (fun x => c x * g x) y = c y * aP ℓ i g y :=
    congrFun (aP_mul_constIn (ℓ := ℓ) (i := i) (c := c) (g := g) hc) y
  show c y * g y - aP ℓ i (fun x => c x * g x) y = c y * (g y - aP ℓ i g y)
  rw [h]
  ring

/-- The window `x ↦ chiScale ℓ (x m)` is constant in every slot `i ≠ m`. -/
lemma chiScale_apply_constIn {n : ℕ} {ℓ : ℝ} {i m : Fin n} (him : i ≠ m) :
    ∀ (x : Xn n) (z : E3),
      (fun y : Xn n => chiScale ℓ (y m)) (Function.update x i z)
        = (fun y : Xn n => chiScale ℓ (y m)) x := by
  intro x z
  simp only []
  rw [Function.update_of_ne (show m ≠ i from fun h => him h.symm)]

/-! ## 2. The `χ`-weighted contraction in one coordinate direction -/

/-- **The slot-`i` mean contracts the `χ`-weighted square**: the window is absorbed into the
function to which `aP ℓ i` is applied. -/
lemma aP_chiScale_sq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i m : Fin n} (him : i ≠ m)
    {g : Xn n → ℝ} (hg : Continuous g) :
    (∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * (aP ℓ i g x) ^ 2)
      ≤ ∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * (g x) ^ 2 := by
  have hc := chiScale_apply_constIn (ℓ := ℓ) (i := i) (m := m) him
  have hcongr : (∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * (aP ℓ i g x) ^ 2)
      = ∫ x in abox n ℓ, (aP ℓ i (fun y => chiScale ℓ (y m) * g y) x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    rw [congrFun (aP_mul_constIn (ℓ := ℓ) (i := i)
      (c := fun y => chiScale ℓ (y m)) (g := g) hc) x]
    ring
  rw [hcongr]
  have hcont : Continuous (fun y : Xn n => chiScale ℓ (y m) * g y) :=
    ((chiScale_contDiff (ne_of_gt hℓ)).continuous.comp (continuous_apply m)).mul hg
  refine (aP_sq_le hℓ i hcont).trans_eq ?_
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- **The slot-`i` mean-subtraction contracts the `χ`-weighted square**. -/
lemma aQ_chiScale_sq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i m : Fin n} (him : i ≠ m)
    {g : Xn n → ℝ} (hg : Continuous g) :
    (∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * (aQ ℓ i g x) ^ 2)
      ≤ ∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * (g x) ^ 2 := by
  have hc := chiScale_apply_constIn (ℓ := ℓ) (i := i) (m := m) him
  have hcongr : (∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * (aQ ℓ i g x) ^ 2)
      = ∫ x in abox n ℓ, (aQ ℓ i (fun y => chiScale ℓ (y m) * g y) x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    rw [congrFun (aQ_mul_constIn (ℓ := ℓ) (i := i)
      (c := fun y => chiScale ℓ (y m)) (g := g) hc) x]
    ring
  rw [hcongr]
  have hcont : Continuous (fun y : Xn n => chiScale ℓ (y m) * g y) :=
    ((chiScale_contDiff (ne_of_gt hℓ)).continuous.comp (continuous_apply m)).mul hg
  refine (integral_aQ_sq_le hℓ i hcont).trans_eq ?_
  apply integral_congr_ae
  filter_upwards with x
  ring

/-! ## 3. The three coordinate directions together -/

/-- The sum over the three coordinate directions of the `χ`-weighted squares is contracted by the
slot-`i` mean. -/
lemma aP_chiScale_sum_sq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i m : Fin n} (him : i ≠ m)
    {A : Fin 3 → Xn n → ℝ} (hA : ∀ j : Fin 3, Continuous (A j)) :
    (∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (aP ℓ i (A j) x) ^ 2)
      ≤ ∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (A j x) ^ 2 := by
  have hwcont : Continuous (fun x : Xn n => chiScale ℓ (x m)) :=
    (chiScale_contDiff (ne_of_gt hℓ)).continuous.comp (continuous_apply m)
  have hL : (∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (aP ℓ i (A j) x) ^ 2)
      = ∑ j : Fin 3, ∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * (aP ℓ i (A j) x) ^ 2 := by
    have hpt : ∀ x : Xn n, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (aP ℓ i (A j) x) ^ 2
        = ∑ j : Fin 3, (chiScale ℓ (x m)) ^ 2 * (aP ℓ i (A j) x) ^ 2 :=
      fun x => Finset.mul_sum Finset.univ (fun j : Fin 3 => (aP ℓ i (A j) x) ^ 2)
        ((chiScale ℓ (x m)) ^ 2)
    trans ∫ x in abox n ℓ, ∑ j : Fin 3, (chiScale ℓ (x m)) ^ 2 * (aP ℓ i (A j) x) ^ 2
    · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    · exact MeasureTheory.integral_finsetSum Finset.univ
        (f := fun j x => (chiScale ℓ (x m)) ^ 2 * (aP ℓ i (A j) x) ^ 2)
        (fun j _ => integrableOn_abox_of_continuous hℓ
          ((hwcont.pow 2).mul ((aP_continuous hℓ i (hA j)).pow 2)))
  have hR : (∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (A j x) ^ 2)
      = ∑ j : Fin 3, ∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * (A j x) ^ 2 := by
    have hpt : ∀ x : Xn n, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (A j x) ^ 2
        = ∑ j : Fin 3, (chiScale ℓ (x m)) ^ 2 * (A j x) ^ 2 :=
      fun x => Finset.mul_sum Finset.univ (fun j : Fin 3 => (A j x) ^ 2)
        ((chiScale ℓ (x m)) ^ 2)
    trans ∫ x in abox n ℓ, ∑ j : Fin 3, (chiScale ℓ (x m)) ^ 2 * (A j x) ^ 2
    · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    · exact MeasureTheory.integral_finsetSum Finset.univ
        (f := fun j x => (chiScale ℓ (x m)) ^ 2 * (A j x) ^ 2)
        (fun j _ => integrableOn_abox_of_continuous hℓ ((hwcont.pow 2).mul ((hA j).pow 2)))
  rw [hL, hR]
  exact Finset.sum_le_sum (fun j _ => aP_chiScale_sq_le hℓ him (hA j))

/-- The same for the mean-subtraction `aQ ℓ i`. -/
lemma aQ_chiScale_sum_sq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i m : Fin n} (him : i ≠ m)
    {A : Fin 3 → Xn n → ℝ} (hA : ∀ j : Fin 3, Continuous (A j)) :
    (∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (aQ ℓ i (A j) x) ^ 2)
      ≤ ∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (A j x) ^ 2 := by
  have hwcont : Continuous (fun x : Xn n => chiScale ℓ (x m)) :=
    (chiScale_contDiff (ne_of_gt hℓ)).continuous.comp (continuous_apply m)
  have hL : (∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (aQ ℓ i (A j) x) ^ 2)
      = ∑ j : Fin 3, ∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * (aQ ℓ i (A j) x) ^ 2 := by
    have hpt : ∀ x : Xn n, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (aQ ℓ i (A j) x) ^ 2
        = ∑ j : Fin 3, (chiScale ℓ (x m)) ^ 2 * (aQ ℓ i (A j) x) ^ 2 :=
      fun x => Finset.mul_sum Finset.univ (fun j : Fin 3 => (aQ ℓ i (A j) x) ^ 2)
        ((chiScale ℓ (x m)) ^ 2)
    trans ∫ x in abox n ℓ, ∑ j : Fin 3, (chiScale ℓ (x m)) ^ 2 * (aQ ℓ i (A j) x) ^ 2
    · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    · exact MeasureTheory.integral_finsetSum Finset.univ
        (f := fun j x => (chiScale ℓ (x m)) ^ 2 * (aQ ℓ i (A j) x) ^ 2)
        (fun j _ => integrableOn_abox_of_continuous hℓ
          ((hwcont.pow 2).mul ((aQ_continuous hℓ i (hA j)).pow 2)))
  have hR : (∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (A j x) ^ 2)
      = ∑ j : Fin 3, ∫ x in abox n ℓ, (chiScale ℓ (x m)) ^ 2 * (A j x) ^ 2 := by
    have hpt : ∀ x : Xn n, (chiScale ℓ (x m)) ^ 2 * ∑ j : Fin 3, (A j x) ^ 2
        = ∑ j : Fin 3, (chiScale ℓ (x m)) ^ 2 * (A j x) ^ 2 :=
      fun x => Finset.mul_sum Finset.univ (fun j : Fin 3 => (A j x) ^ 2)
        ((chiScale ℓ (x m)) ^ 2)
    trans ∫ x in abox n ℓ, ∑ j : Fin 3, (chiScale ℓ (x m)) ^ 2 * (A j x) ^ 2
    · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    · exact MeasureTheory.integral_finsetSum Finset.univ
        (f := fun j x => (chiScale ℓ (x m)) ^ 2 * (A j x) ^ 2)
        (fun j _ => integrableOn_abox_of_continuous hℓ ((hwcont.pow 2).mul ((hA j).pow 2)))
  rw [hL, hR]
  exact Finset.sum_le_sum (fun j _ => aQ_chiScale_sq_le hℓ him (hA j))

/-! ## 4. The target -/

theorem imgFibreDchiLe {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {F : Submission.BoseGases.X n → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) {i : Fin n} (hi : i ≠ p.1) :
    (Work.BoseBoxFock.imgFibreDχ ℓ p (Submission.BoseGases.aP ℓ i F)
        ≤ Work.BoseBoxFock.imgFibreDχ ℓ p F) ∧
    (Work.BoseBoxFock.imgFibreDχ ℓ p (Submission.BoseGases.aQ ℓ i F)
        ≤ Work.BoseBoxFock.imgFibreDχ ℓ p F) := by
  have hAcont : ∀ j : Fin 3, Continuous (fun y : Xn n => fderiv ℝ F y (slotDirVec p.1 j)) :=
    fun j => (hF.continuous_fderiv (by decide)).clm_apply continuous_const
  constructor
  · show (∫ x in abox n ℓ, (chiScale ℓ (x p.1)) ^ 2
          * ∑ j : Fin 3, (fderiv ℝ (aP ℓ i F) x (slotDirVec p.1 j)) ^ 2)
        ≤ (∫ x in abox n ℓ, (chiScale ℓ (x p.1)) ^ 2
          * ∑ j : Fin 3, (fderiv ℝ F x (slotDirVec p.1 j)) ^ 2)
    have hderiv : ∀ (x : Xn n) (j : Fin 3),
        fderiv ℝ (aP ℓ i F) x (slotDirVec p.1 j)
          = aP ℓ i (fun y => fderiv ℝ F y (slotDirVec p.1 j)) x :=
      fun x j => fderiv_aP_kcDir_of_ne hℓ (Ne.symm hi) hF x j
    have hcongr : (∫ x in abox n ℓ, (chiScale ℓ (x p.1)) ^ 2
          * ∑ j : Fin 3, (fderiv ℝ (aP ℓ i F) x (slotDirVec p.1 j)) ^ 2)
        = ∫ x in abox n ℓ, (chiScale ℓ (x p.1)) ^ 2
          * ∑ j : Fin 3, (aP ℓ i (fun y => fderiv ℝ F y (slotDirVec p.1 j)) x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by rw [hderiv x j])
    rw [hcongr]
    exact aP_chiScale_sum_sq_le (ℓ := ℓ) (i := i) (m := p.1) hℓ hi
      (A := fun j => fun y => fderiv ℝ F y (slotDirVec p.1 j)) hAcont
  · show (∫ x in abox n ℓ, (chiScale ℓ (x p.1)) ^ 2
          * ∑ j : Fin 3, (fderiv ℝ (aQ ℓ i F) x (slotDirVec p.1 j)) ^ 2)
        ≤ (∫ x in abox n ℓ, (chiScale ℓ (x p.1)) ^ 2
          * ∑ j : Fin 3, (fderiv ℝ F x (slotDirVec p.1 j)) ^ 2)
    have hderiv : ∀ (x : Xn n) (j : Fin 3),
        fderiv ℝ (aQ ℓ i F) x (slotDirVec p.1 j)
          = aQ ℓ i (fun y => fderiv ℝ F y (slotDirVec p.1 j)) x :=
      fun x j => fderiv_aQ_kcDir_of_ne hℓ (Ne.symm hi) hF x j
    have hcongr : (∫ x in abox n ℓ, (chiScale ℓ (x p.1)) ^ 2
          * ∑ j : Fin 3, (fderiv ℝ (aQ ℓ i F) x (slotDirVec p.1 j)) ^ 2)
        = ∫ x in abox n ℓ, (chiScale ℓ (x p.1)) ^ 2
          * ∑ j : Fin 3, (aQ ℓ i (fun y => fderiv ℝ F y (slotDirVec p.1 j)) x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by rw [hderiv x j])
    rw [hcongr]
    exact aQ_chiScale_sum_sq_le (ℓ := ℓ) (i := i) (m := p.1) hℓ hi
      (A := fun j => fun y => fderiv ℝ F y (slotDirVec p.1 j)) hAcont

end Work.BoseBoxFock
