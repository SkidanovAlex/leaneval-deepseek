import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotOf_chiMode_eq
import Submission.Work.BoseBoxFock.chiRowDefs
import Submission.Work.BoseBoxFock.chiRow_constPart_vanish
import Submission.Work.BoseBoxFock.chiTail_bound
import Submission.Work.BoseBoxFock.pin_e0_eq
import Submission.Work.BoseBoxFock.potChiLin_eq_summed_good
import Submission.Work.BoseBoxFock.potTruncRepair
import Submission.Work.BoseBoxFock.thetaExp_eq_etaOf_of_pairing
import Submission.Work.BoseBoxFock.thetaTail_bound
import Submission.Work.BoseBoxFock.wLoc_fibre_kernelCompare
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.chiRow_aP_abox_facts`

Three elementary *box-locality* facts for the centred box `abox n ℓ = (Λ(ℓ))ⁿ`
(`Λ(ℓ) = acube ℓ = [−ℓ/2,ℓ/2]³`), used to localise the χ-row:

* the slot projection `aP ℓ i` only sees the values of its argument on `abox n ℓ`
  (hence it annihilates any function vanishing there);
* FS's sharp box indicator `θ_Λ = 1_{Λ(ℓ)}` (`Work.BoseB4.BoxData.thetaFun` for the
  corpus bump) equals `1` on `acube ℓ` — because `acube ℓ ⊆ boxL ℓ = ℓ • unitCell`;
* `aP ℓ i` is compatible with pointwise equality on `abox n ℓ`.

The common input is that updating the `i`-th slot of a box configuration by a point
of `acube ℓ` keeps the configuration in the box.
-/

noncomputable section

open MeasureTheory
open scoped Pointwise

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- **Updating one coordinate of a point of the box by a point of `acube ℓ` keeps it in the
box.** -/
lemma chiRow_update_mem_abox {n : ℕ} {ℓ : ℝ} {x : Submission.BoseGases.X n}
    (hx : x ∈ Submission.BoseGases.abox n ℓ) (i : Fin n) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ Submission.BoseGases.acube ℓ) :
    Function.update x i z ∈ Submission.BoseGases.abox n ℓ := by
  rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
  intro j
  rw [Function.update_apply]
  split
  · exact hz
  · exact hx j

/-- **The centred cube sits inside FS's box**: `acube ℓ ⊆ boxL ℓ = ℓ • unitCell` for `0 < ℓ`.
Since `unitCell = {u | ∀ j, |u j| ≤ 1/2}`, this is `|y j| ≤ ℓ/2` for `y ∈ acube ℓ`. -/
lemma corpusBox_acube_subset_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Submission.BoseGases.acube ℓ ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro y hy
  show y ∈ ℓ • Work.BoseB4.unitCell
  rw [Set.mem_smul_set]
  refine ⟨ℓ⁻¹ • y, ?_, ?_⟩
  · intro m
    have hmem := (Submission.BoseGases.mem_acube_iff ℓ y).mp hy m
    show |(ℓ⁻¹ • y).ofLp m| ≤ 1 / 2
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hℓ)]
    have hz : |y.ofLp m| ≤ ℓ / 2 := abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
    calc ℓ⁻¹ * |y.ofLp m| ≤ ℓ⁻¹ * (ℓ / 2) :=
          mul_le_mul_of_nonneg_left hz (le_of_lt (inv_pos.mpr hℓ))
      _ = 1 / 2 := by rw [← mul_div_assoc, inv_mul_cancel₀ (ne_of_gt hℓ)]
  · rw [smul_inv_smul₀ (ne_of_gt hℓ)]

theorem chiRow_aP_abox_facts {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∀ (i : Fin n) {F : Submission.BoseGases.X n → ℝ},
        (∀ y ∈ Submission.BoseGases.abox n ℓ, F y = 0) →
        ∀ x ∈ Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i F x = 0)
      ∧ (∀ {x : Submission.BoseGases.X n}, x ∈ Submission.BoseGases.abox n ℓ →
          ∀ j : Fin n, Work.BoseK15.corpusBox.thetaFun ℓ (x j) = 1)
      ∧ (∀ (i : Fin n) {F G : Submission.BoseGases.X n → ℝ},
          (∀ y ∈ Submission.BoseGases.abox n ℓ, F y = G y) →
          ∀ x ∈ Submission.BoseGases.abox n ℓ, Submission.BoseGases.aP ℓ i F x = Submission.BoseGases.aP ℓ i G x) := by
  refine ⟨?_, ?_, ?_⟩
  · -- `aP ℓ i F` averages `F` over the fibre, which stays inside the box
    intro i F hF x hx
    have hzero : (∫ y in Submission.BoseGases.acube ℓ, F (Function.update x i y)) = 0 := by
      have h := MeasureTheory.setIntegral_congr_fun (μ := MeasureTheory.volume)
        (s := Submission.BoseGases.acube ℓ)
        (f := fun y => F (Function.update x i y)) (g := fun _ => (0 : ℝ))
        (Submission.BoseGases.acube_measurable ℓ)
        (fun y hy => hF (Function.update x i y) (chiRow_update_mem_abox hx i hy))
      simpa using h
    unfold Submission.BoseGases.aP
    rw [hzero, mul_zero]
  · -- the box indicator is `1` on the centred cube
    intro x hx j
    have hxj : x j ∈ Submission.BoseGases.acube ℓ :=
      (Submission.BoseGases.mem_abox_iff n ℓ x).mp hx j
    rw [Work.BoseB4.BoxData.thetaFun_apply, if_pos (corpusBox_acube_subset_boxL hℓ hxj)]
  · -- pointwise equality on the box passes to the fibre average
    intro i F G hFG x hx
    unfold Submission.BoseGases.aP
    congr 1
    exact MeasureTheory.setIntegral_congr_fun (μ := MeasureTheory.volume)
      (Submission.BoseGases.acube_measurable ℓ)
      (fun y hy => hFG (Function.update x i y) (chiRow_update_mem_abox hx i hy))

end Work.BoseBoxFock
