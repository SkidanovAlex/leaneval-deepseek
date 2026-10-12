import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.abox_indicator_peel_split
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.abox_integral_slot_collapse`

The *collapse of a slot* of the box integral, for an integrand which does not depend on one
distinguished slot.

The two-slot peel `PCFU.abox_indicator_peel_split` writes the integral of `f` over the centred
box `abox n ℓ` as the iterated integral over the remaining coordinates `x'` and the two peeled
slots `w, w'`,

    ∫_{x ∈ abox n ℓ} f x
      = ∫_{x'} ∫_w ∫_{w'} 1_Λ(w) · (1_Λ(w') · (1_{ΠΛ}(x') · f (chCcfg i j w w' x'))) ,

with `Λ` the one-particle cube `acube ℓ`.  If now `f x = (F x)^2` where `F` is invariant in the
slot `i` (`F (Function.update x i z) = F x`, the hypothesis `hFi` of the target), then the
integrand of the peel does not depend on the slot variable `w` at all: the `w`-integration
collapses to the volume of the cube, and the *first* slot `w` can be fixed to `0` in the
remaining integral.  The result is

    ∫_{x ∈ abox n ℓ} (F x)^2
      = ℓ³ · ∫_{x'} 1_{ΠΛ}(x') · ∫_{z ∈ Λ} (F (chCcfg i j 0 z x'))^2 .

This is the target `PCFU.abox_integral_slot_collapse`.  The proof is organised as

* `chCcfg_update_slot` : writing `w` into slot `i` of `chCcfg i j 0 w' x'` recovers the full
  `(i,j)`-slot configuration (so `F`'s invariance transfers);
* `cubeInd_integral` : the volume of the cube, `∫_w 1_Λ(w) = ℓ³`;
* `slotIntegral_collapse` : the purely measure-theoretic collapse of the *slugged* triple
  integral, valid for an arbitrary integrand `H` (no integrability needed — it only uses the
  unconditional constant-pull rules `integral_const_mul` / `integral_mul_const` and
  `integral_congr_ae`);
* the target itself, by peeling, replacing the slot-`i` variable using `hFi` and evaluating the
  one-dimensional integral.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)
set_option linter.unusedVariables false

/-- The type of the coordinates other than the two slots `i, j`. -/
abbrev SlotRest {n : ℕ} (i j : Fin n) : Type := {k : Fin n // k ≠ i ∧ k ≠ j} → E3

/-- The real-valued indicator of the centred cube `acube ℓ`. -/
noncomputable abbrev cubeInd (ℓ : ℝ) (z : E3) : ℝ :=
  (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) z

/-- The real-valued indicator of the product of centred cubes `∏_{k ≠ i,j} acube ℓ` on the
remaining coordinates. -/
noncomputable abbrev restInd {n : ℕ} (i j : Fin n) (ℓ : ℝ) (x' : SlotRest i j) : ℝ :=
  (Set.univ.pi (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} =>
    Submission.BoseGases.acube ℓ)).indicator (fun _ => (1 : ℝ)) x'

/-- Writing `z` into the slot `i` of a `(i,j)`-slot configuration amounts to moving the `i`-slot
entry: `update (chCcfg i j w w' x') i z = chCcfg i j z w' x'`. -/
lemma chCcfg_update_slot {n : ℕ} {i j : Fin n} (w w' : E3) (x' : SlotRest i j) (z : E3) :
    Function.update (chCcfg i j w w' x') i z = chCcfg i j z w' x' := by
  funext k
  rw [Function.update_apply]
  by_cases hki : k = i
  · rw [if_pos hki, hki, chCcfg_i]
  · rw [if_neg hki]
    by_cases hkj : k = j
    · have hij : i ≠ j := fun hh => hki (by rw [hkj, hh])
      rw [hkj, chCcfg_j hij, chCcfg_j hij]
    · rw [chCcfg_other w w' x' hki hkj, chCcfg_other z w' x' hki hkj]

/-- The volume of the one-particle cube: `∫_w 1_{acube ℓ}(w) = ℓ³` for `ℓ > 0`. -/
lemma cubeInd_integral {ℓ : ℝ} (hℓ : 0 < ℓ) : (∫ w : E3, cubeInd ℓ w) = ℓ ^ 3 := by
  rw [MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
  rw [MeasureTheory.setIntegral_const]
  rw [MeasureTheory.Measure.real_def, Submission.BoseGases.acube_volume ℓ (le_of_lt hℓ)]
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp

/-- **The measure-theoretic collapse of one slot of the slugged triple integral.**  If the
integrand does not depend on the first slot variable `w`, then

    ∫_{x'} ∫_w ∫_{w'} 1_Λ(w) · (1_Λ(w') · (1_{ΠΛ}(x') · H x' w'))
      = (∫_w 1_Λ(w)) · ∫_{x'} 1_{ΠΛ}(x') · ∫_{z ∈ Λ} H x' z .

No integrability hypothesis is needed: the identity only uses the unconditional constant-pull
rules for the Bochner integral. -/
lemma slotIntegral_collapse {n : ℕ} {i j : Fin n} {ℓ : ℝ} (H : SlotRest i j → E3 → ℝ) :
    (∫ x' : SlotRest i j, ∫ w : E3, ∫ w' : E3,
        cubeInd ℓ w * (cubeInd ℓ w' * (restInd i j ℓ x' * H x' w')))
      = (∫ w : E3, cubeInd ℓ w)
        * ∫ x' : SlotRest i j, restInd i j ℓ x' * ∫ z in Submission.BoseGases.acube ℓ, H x' z := by
  have hstepA : ∀ x' : SlotRest i j,
      (∫ w : E3, ∫ w' : E3, cubeInd ℓ w * (cubeInd ℓ w' * (restInd i j ℓ x' * H x' w')))
        = (∫ w : E3, cubeInd ℓ w) * (∫ w' : E3, cubeInd ℓ w' * (restInd i j ℓ x' * H x' w')) := by
    intro x'
    rw [show (∫ w : E3, ∫ w' : E3, cubeInd ℓ w * (cubeInd ℓ w' * (restInd i j ℓ x' * H x' w')))
        = ∫ w : E3, cubeInd ℓ w * (∫ w' : E3, cubeInd ℓ w' * (restInd i j ℓ x' * H x' w')) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      exact MeasureTheory.integral_const_mul _ _]
    rw [MeasureTheory.integral_mul_const]
  have hstepB : ∀ x' : SlotRest i j,
      (∫ w' : E3, cubeInd ℓ w' * (restInd i j ℓ x' * H x' w'))
        = restInd i j ℓ x' * ∫ z in Submission.BoseGases.acube ℓ, H x' z := by
    intro x'
    rw [show (∫ w' : E3, cubeInd ℓ w' * (restInd i j ℓ x' * H x' w'))
        = ∫ w' : E3, restInd i j ℓ x' * (cubeInd ℓ w' * H x' w') from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w' => by ring)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [← MeasureTheory.integral_indicator (Submission.BoseGases.acube_measurable ℓ)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
    by_cases hw : w' ∈ Submission.BoseGases.acube ℓ
    · simp only [cubeInd, Set.indicator_of_mem hw]; ring
    · simp only [cubeInd, Set.indicator_of_notMem hw]; ring
  calc (∫ x' : SlotRest i j, ∫ w : E3, ∫ w' : E3,
        cubeInd ℓ w * (cubeInd ℓ w' * (restInd i j ℓ x' * H x' w')))
      = ∫ x' : SlotRest i j,
          (∫ w : E3, cubeInd ℓ w) * (∫ w' : E3, cubeInd ℓ w' * (restInd i j ℓ x' * H x' w')) := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
        exact hstepA x'
    _ = (∫ w : E3, cubeInd ℓ w)
        * ∫ x' : SlotRest i j, (∫ w' : E3, cubeInd ℓ w' * (restInd i j ℓ x' * H x' w')) := by
        rw [MeasureTheory.integral_const_mul]
    _ = (∫ w : E3, cubeInd ℓ w)
        * ∫ x' : SlotRest i j, restInd i j ℓ x' * ∫ z in Submission.BoseGases.acube ℓ, H x' z := by
        congr 1
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hstepB)

theorem abox_integral_slot_collapse {n : ℕ} {i j : Fin n} (hij : i ≠ j) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {F : Submission.BoseGases.X n → ℝ} (hFm : Measurable F)
    (hFi : ∀ (x : Submission.BoseGases.X n) (z : EuclideanSpace ℝ (Fin 3)),
        F (Function.update x i z) = F x)
    (hFint : MeasureTheory.Integrable
        (fun x => (Submission.BoseGases.abox n ℓ).indicator (fun x => (F x) ^ 2) x)
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) :
    (∫ x in Submission.BoseGases.abox n ℓ, (F x) ^ 2)
      = ℓ ^ 3 * ∫ x' : ({k : Fin n // k ≠ i ∧ k ≠ j} → EuclideanSpace ℝ (Fin 3)),
          (Set.univ.pi (fun _ : {k : Fin n // k ≠ i ∧ k ≠ j} =>
              Submission.BoseGases.acube ℓ)).indicator (fun _ => (1 : ℝ)) x'
            * ∫ z in Submission.BoseGases.acube ℓ,
                (F (Work.BoseBoxFock.PCFU.chCcfg i j 0 z x')) ^ 2 := by
  classical
  -- `F` sees the `(i,j)`-slot configuration only through the slot `w'`.
  have hinv : ∀ (w w' : E3) (x' : SlotRest i j),
      F (chCcfg i j w w' x') = F (chCcfg i j 0 w' x') := by
    intro w w' x'
    rw [← chCcfg_update_slot (i := i) (j := j) (w := 0) w' x' w]
    exact hFi _ w
  -- the box integral is the integral of the box indicator of `F²`.
  rw [← MeasureTheory.integral_indicator (Submission.BoseGases.abox_measurable n ℓ)]
  -- peel the two slots `i, j`.
  rw [abox_indicator_peel_split hij hFint]
  -- replace the slot-`i` entry using the invariance of `F`.
  rw [show (∫ x' : SlotRest i j, ∫ w : E3, ∫ w' : E3,
        cubeInd ℓ w * (cubeInd ℓ w' * (restInd i j ℓ x' * (F (chCcfg i j w w' x')) ^ 2)))
      = ∫ x' : SlotRest i j, ∫ w : E3, ∫ w' : E3,
        cubeInd ℓ w * (cubeInd ℓ w' * (restInd i j ℓ x' * (F (chCcfg i j 0 w' x')) ^ 2)) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w' => ?_)
      beta_reduce
      rw [hinv w w' x']]
  -- the collapsed slot integral, then the volume of the cube.
  rw [slotIntegral_collapse (i := i) (j := j) (ℓ := ℓ)
    (H := fun x' z => (F (chCcfg i j 0 z x')) ^ 2)]
  rw [cubeInd_integral hℓ]

end Work.BoseBoxFock.PCFU
