import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Gap.gapBare_eq_expand
import Submission.Work.BoseKinLoc.Gap.integral_lamBox_eq_acube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseKinLoc.Word.integral_prod_erase_mul_indU` — the erase-slot Fubini
identity for the box indicator

The `N`-body localised forms of `Work.BoseKinLoc.Defs` (`slotForm`, `kinForm`,
`boxForm`) integrate a `u`-dependent one-body factor in the slot `i` against a
`u`-independent factor in the other `n - 1` slots.  On a product trial state the
slot-`i` fibre of the one-body factor is the box indicator `indU ℓ u`, and the
remaining slots carry a single one-body function `f`; the whole integral then has
to factorise.  This module supplies that computation:

* `integral_indU_eq` — the one-body normalisation `∫_{ℝ³} indU ℓ u = ℓ³` (the moving
  box `Λ(u)` has volume `ℓ³`);
* `integral_prod_erase_mul_indU` — Fubini over the product measure of
  `X n = (ℝ³)ⁿ` for an integrand that is the product of `indU ℓ u` in slot `i` with
  `f` in every other slot:

      `∫_{X n} indU ℓ u (x i) · ∏_{j ≠ i} f (x j) = ℓ³ · (∫ f)^{n - 1}`.

Both are *unconditional* in `f`: the Bochner-integral form of Fubini
(`MeasureTheory.integral_fintype_prod_volume_eq_prod`) needs neither measurability
nor integrability, and the only normalisation input is the volume of the box.
-/

namespace Work.BoseKinLoc.Word

open MeasureTheory

/-- **Normalisation of the box indicator.**  The integral of the indicator of the moving box
`Λ(u) = ℓu + [−ℓ/2,ℓ/2]³` is its volume `ℓ³`.

The computation is `∫ indU = vol(Λ(u)) = vol(acube ℓ) = ℓ³`: the middle step is the
translation change of variables `Gap.integral_lamBox_eq_acube` (which needs no measurability
of the moving box), and the last is `Submission.BoseGases.acube_volume`. -/
lemma integral_indU_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3)) :
    ∫ z : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.indU ℓ u z = ℓ ^ 3 := by
  have hAc : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  have hLm : MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) := by
    rw [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
    exact hAc.preimage (by fun_prop)
  -- the indicator integrates to the measure of the box
  rw [Work.BoseKinLoc.indU, MeasureTheory.integral_indicator hLm]
  -- translate the moving box back to the centred cube
  rw [Work.BoseKinLoc.Gap.integral_lamBox_eq_acube ℓ hℓ (fun _ => (1 : ℝ)) u]
  -- the centred cube has volume `ℓ³`
  rw [← MeasureTheory.integral_indicator hAc]
  rw [show (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) = 1 from rfl]
  rw [MeasureTheory.integral_indicator_one hAc]
  rw [Measure.real, Submission.BoseGases.acube_volume ℓ hℓ.le]
  simp [ENNReal.toReal_ofReal (pow_nonneg hℓ.le 3)]

/-- **The erase-slot Fubini identity.**  For a function of the `i`-th coordinate `a`, a
function `f` of all the other coordinates, and the product measure on `X n = (ℝ³)ⁿ`,

    `∫_{X n} a (x i) · ∏_{j ∈ univ.erase i} f (x j) = (∫ a) · (∫ f)^{n - 1}`.

The statement is unconditional in `a` and `f`: `MeasureTheory.integral_fintype_prod_volume_eq_prod`
is a Bochner-integral identity with no measurability or integrability hypotheses, and the
`a`-slot contributes its own one-body integral while each of the remaining `n - 1` slots
contributes `∫ f`. -/
theorem integral_prod_erase_mul_indU {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (u : EuclideanSpace ℝ (Fin 3)) (i : Fin n) (f : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ x : Submission.BoseGases.X n,
        Work.BoseKinLoc.indU ℓ u (x i) * (∏ j ∈ Finset.univ.erase i, f (x j)))
      = ℓ ^ 3 * (∫ z : EuclideanSpace ℝ (Fin 3), f z) ^ (n - 1) := by
  -- the one-body normalisation of the box indicator
  have hU : (∫ z : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.indU ℓ u z) = ℓ ^ 3 :=
    integral_indU_eq hℓ u
  -- write the integrand as a product over *all* slots, with the `i`-th slot carrying `indU`
  let g : Fin n → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun j => if j = i then Work.BoseKinLoc.indU ℓ u else f
  have hpoint : ∀ x : Submission.BoseGases.X n,
      (∏ j : Fin n, g j (x j))
        = Work.BoseKinLoc.indU ℓ u (x i) * (∏ j ∈ Finset.univ.erase i, f (x j)) := by
    intro x
    rw [← Finset.prod_erase_mul Finset.univ (fun j : Fin n => g j (x j)) (Finset.mem_univ i)]
    have h1 : (∏ j ∈ Finset.univ.erase i, g j (x j))
        = ∏ j ∈ Finset.univ.erase i, f (x j) := by
      refine Finset.prod_congr rfl (fun j hj => ?_)
      show (if j = i then Work.BoseKinLoc.indU ℓ u else f) (x j) = f (x j)
      rw [if_neg (Finset.mem_erase.mp hj).1]
    have h2 : g i (x i) = Work.BoseKinLoc.indU ℓ u (x i) := by
      show (if i = i then Work.BoseKinLoc.indU ℓ u else f) (x i) = _
      rw [if_pos rfl]
    rw [h1, h2, mul_comm]
  rw [show (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ u (x i) * (∏ j ∈ Finset.univ.erase i, f (x j)))
      = fun x : Submission.BoseGases.X n => ∏ j : Fin n, g j (x j) from
        funext (fun x => (hpoint x).symm)]
  -- Fubini over the finite product measure
  rw [MeasureTheory.integral_fintype_prod_volume_eq_prod g]
  -- every slot contributes its own one-body integral
  have hprod : (∏ j : Fin n, ∫ z : EuclideanSpace ℝ (Fin 3), g j z)
      = (∫ z : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.indU ℓ u z)
          * (∫ z : EuclideanSpace ℝ (Fin 3), f z) ^ (n - 1) := by
    rw [← Finset.prod_erase_mul Finset.univ
      (fun j : Fin n => ∫ z : EuclideanSpace ℝ (Fin 3), g j z) (Finset.mem_univ i)]
    have h1 : (∏ j ∈ Finset.univ.erase i, ∫ z : EuclideanSpace ℝ (Fin 3), g j z)
        = (∫ z : EuclideanSpace ℝ (Fin 3), f z) ^ (n - 1) := by
      have hc : (∏ j ∈ Finset.univ.erase i, ∫ z : EuclideanSpace ℝ (Fin 3), g j z)
          = ∏ j ∈ Finset.univ.erase i, ∫ z : EuclideanSpace ℝ (Fin 3), f z := by
        refine Finset.prod_congr rfl (fun j hj => ?_)
        show (∫ z : EuclideanSpace ℝ (Fin 3), (if j = i then Work.BoseKinLoc.indU ℓ u else f) z)
          = ∫ z : EuclideanSpace ℝ (Fin 3), f z
        rw [if_neg (Finset.mem_erase.mp hj).1]
      rw [hc, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]
    have h2 : (∫ z : EuclideanSpace ℝ (Fin 3), g i z)
        = ∫ z : EuclideanSpace ℝ (Fin 3), Work.BoseKinLoc.indU ℓ u z := by
      show (∫ z : EuclideanSpace ℝ (Fin 3), (if i = i then Work.BoseKinLoc.indU ℓ u else f) z) = _
      rw [if_pos rfl]
    rw [h1, h2]
    exact mul_comm _ _
  rw [hprod, hU]

end Work.BoseKinLoc.Word
