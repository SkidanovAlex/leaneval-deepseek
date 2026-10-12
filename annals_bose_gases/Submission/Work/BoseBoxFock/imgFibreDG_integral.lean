import Mathlib
import Submission.Work.BoseBoxFock.abox_peel_two
import Submission.Work.BoseBoxFock.imgFibreEnergyDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

/-!
# `Work.BoseBoxFock.imgFibreDG_integral`

The measure-theoretic identity

    ∫_{u ∈ boxL ℓ} χ_ℓ(u)² · imgFibreDG ℓ p G u = imgFibreDχ ℓ p G

for a `C^∞` state `G` and two distinct slots `p.1 ≠ p.2`.

Both sides are integrals of the same function over the *same* set of configurations, read through
the coordinate insertion `Φ ((u,v),x') = insertCoord2 p u v x'`:

* the right-hand side is the χ-weighted `p.1`-slot Dirichlet content of `G` on `abox n ℓ`;
* the left-hand side integrates over the `p.1`-slot value `u` only the χ-weight, the `p.2`-slot
  value `v` and the remaining coordinates being integrated out.

The bridge is the measure-preserving coordinate insertion `sliceIns p hp`
(`Work.BoseBoxFock.sliceIns_measurePreserving`), which identifies the product box measure with the
box measure on `abox n ℓ`; the iterated form of that identification is the corpus lemma
`Work.BoseBoxFock.abox_peel_two`.  Everything else is Fubini (`MeasureTheory.integral_integral_swap`)
plus the two unconditional rewriting rules `MeasureTheory.integral_const_mul` and
`Work.BoseBoxFock.insertCoord2_apply_fst`; the only analytic input is the continuity of the
integrand, which is what makes it integrable on the (compact) box.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- The corpus box `boxL ℓ` is compact. -/
lemma isCompact_corpusBoxBoxL {ℓ : ℝ} (hℓ : 0 < ℓ) : IsCompact (boxL ℓ) := by
  rw [corpusBox_boxL_eq_acube hℓ]
  exact Submission.BoseGases.acube_compact hℓ

/-- **Integrability on the box product `boxL ℓ × π(boxL ℓ)`**: a continuous function is integrable
against the product of the box measure with the product box measure. -/
lemma integrable_boxPi_pair {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {φ : E3 × (ι → E3) → ℝ} (hφ : Continuous φ) :
    Integrable φ ((boxMeas ℓ).prod (Measure.pi (fun _ : ι => boxMeas ℓ))) := by
  have h1 : (Measure.pi (fun _ : ι => boxMeas ℓ))
      = (volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ) :=
    (restrict_boxPiSet_eq (ι := ι) (ℓ := ℓ)).symm
  rw [h1]
  have h2 : ((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ))
      = (volume : Measure (E3 × (ι → E3))).restrict (boxL ℓ ×ˢ boxPiSet ι ℓ) :=
    Measure.prod_restrict _ _
  rw [h2]
  exact ContinuousOn.integrableOn_compact
    ((isCompact_corpusBoxBoxL hℓ).prod (isCompact_boxPiSet hℓ)) hφ.continuousOn

/-- **Integrability on the box triple product `(boxL ℓ × boxL ℓ) × π(boxL ℓ)`**. -/
lemma integrable_box_triple {ι : Type*} [Fintype ι] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : (E3 × E3) × (ι → E3) → ℝ} (hΦ : Continuous Φ) :
    Integrable Φ (((boxMeas ℓ).prod (boxMeas ℓ)).prod (Measure.pi (fun _ : ι => boxMeas ℓ))) := by
  have h1 : (Measure.pi (fun _ : ι => boxMeas ℓ))
      = (volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ) :=
    (restrict_boxPiSet_eq (ι := ι) (ℓ := ℓ)).symm
  rw [h1]
  have h2 : ((volume : Measure E3).restrict (boxL ℓ)).prod
        ((volume : Measure E3).restrict (boxL ℓ))
      = (volume : Measure (E3 × E3)).restrict (boxL ℓ ×ˢ boxL ℓ) :=
    Measure.prod_restrict _ _
  rw [h2]
  have h3 : ((volume : Measure (E3 × E3)).restrict (boxL ℓ ×ˢ boxL ℓ)).prod
        ((volume : Measure (ι → E3)).restrict (boxPiSet ι ℓ))
      = (volume : Measure ((E3 × E3) × (ι → E3))).restrict
          ((boxL ℓ ×ˢ boxL ℓ) ×ˢ boxPiSet ι ℓ) :=
    Measure.prod_restrict _ _
  rw [h3]
  exact ContinuousOn.integrableOn_compact
    (((isCompact_corpusBoxBoxL hℓ).prod (isCompact_corpusBoxBoxL hℓ)).prod
      (isCompact_boxPiSet hℓ)) hΦ.continuousOn

/-- **The measure-theoretic core.**  For *any continuous* `f`, the χ-weighted `p.1`-slot density
integrates to the χ-weighted box content of `f`. -/
theorem imgFibreDG_integral_gen {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {f : Xn n → ℝ} (hf : Continuous f) :
    (∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 *
        (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ, f (insertCoord2 p u s x')))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x p.1)) ^ 2 * f x := by
  classical
  have hχ : Continuous (Submission.BoseGases.chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous
  set F : Xn n → ℝ := fun x => (Submission.BoseGases.chiScale ℓ (x p.1)) ^ 2 * f x with hF
  have hFc : Continuous F := ((hχ.comp (continuous_apply p.1)).pow 2).mul hf
  have hins : Continuous (fun w : (E3 × E3) × (pairFib23 n p → E3) =>
      insertCoord2 p w.1.1 w.1.2 w.2) :=
    (contDiff_insertCoord2_comp (P := (E3 × E3) × (pairFib23 n p → E3)) p
      (contDiff_fst.comp contDiff_fst) (contDiff_snd.comp contDiff_fst) contDiff_snd).continuous
  have hFin : Integrable (fun w : (E3 × E3) × (pairFib23 n p → E3) =>
      F (insertCoord2 p w.1.1 w.1.2 w.2))
      (((boxMeas ℓ).prod (boxMeas ℓ)).prod (Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ))) :=
    integrable_box_triple hℓ (hFc.comp hins)
  -- pull the χ-weight out of the two inner integrals
  have hpull : ∀ u : E3, (∫ v in boxL ℓ, ∫ x' in boxPiSet (pairFib23 n p) ℓ,
        (Submission.BoseGases.chiScale ℓ u) ^ 2 * f (insertCoord2 p u v x'))
      = (Submission.BoseGases.chiScale ℓ u) ^ 2 *
          (∫ v in boxL ℓ, ∫ x' in boxPiSet (pairFib23 n p) ℓ,
            f (insertCoord2 p u v x')) := by
    intro u
    rw [← MeasureTheory.integral_const_mul ((Submission.BoseGases.chiScale ℓ u) ^ 2)
      (fun v : E3 => ∫ x' in boxPiSet (pairFib23 n p) ℓ, f (insertCoord2 p u v x'))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun v =>
      MeasureTheory.integral_const_mul _ _)
  -- Fubini for the two inner integrals
  have hswap : ∀ u : E3,
      (∫ v in boxL ℓ, ∫ x' in boxPiSet (pairFib23 n p) ℓ, f (insertCoord2 p u v x'))
      = (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ v in boxL ℓ,
          f (insertCoord2 p u v x')) := by
    intro u
    have hL : (∫ v in boxL ℓ, ∫ x' in boxPiSet (pairFib23 n p) ℓ, f (insertCoord2 p u v x'))
        = ∫ v : E3, (∫ x' : pairFib23 n p → E3, f (insertCoord2 p u v x')
            ∂(Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ))) ∂(boxMeas ℓ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      exact setIntegral_boxPiSet_eq (fun x' : pairFib23 n p → E3 => f (insertCoord2 p u v x'))
    have hR : (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ v in boxL ℓ, f (insertCoord2 p u v x'))
        = ∫ x' : pairFib23 n p → E3, (∫ v : E3, f (insertCoord2 p u v x') ∂(boxMeas ℓ))
            ∂(Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ)) := by
      exact setIntegral_boxPiSet_eq (fun x' : pairFib23 n p → E3 =>
        ∫ v in boxL ℓ, f (insertCoord2 p u v x'))
    rw [hL, hR]
    refine MeasureTheory.integral_integral_swap ?_
    have hc : Continuous (fun z : E3 × (pairFib23 n p → E3) =>
        f (insertCoord2 p u z.1 z.2)) :=
      hf.comp ((contDiff_insertCoord2_comp (P := E3 × (pairFib23 n p → E3)) p
        contDiff_const contDiff_fst contDiff_snd).continuous)
    exact integrable_boxPi_pair hℓ hc
  -- assemble the iterated identity pointwise in `u`
  have hstep : (∫ u in boxL ℓ, ∫ v in boxL ℓ, ∫ x' in boxPiSet (pairFib23 n p) ℓ,
        F (insertCoord2 p u v x'))
      = ∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 *
          (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
            f (insertCoord2 p u s x')) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show (∫ v in boxL ℓ, ∫ x' in boxPiSet (pairFib23 n p) ℓ, F (insertCoord2 p u v x'))
      = (Submission.BoseGases.chiScale ℓ u) ^ 2 *
          (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
            f (insertCoord2 p u s x'))
    have h1 : (∫ v in boxL ℓ, ∫ x' in boxPiSet (pairFib23 n p) ℓ, F (insertCoord2 p u v x'))
        = ∫ v in boxL ℓ, ∫ x' in boxPiSet (pairFib23 n p) ℓ,
            (Submission.BoseGases.chiScale ℓ u) ^ 2 * f (insertCoord2 p u v x') := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
      show (Submission.BoseGases.chiScale ℓ (insertCoord2 p u v x' p.1)) ^ 2 *
            f (insertCoord2 p u v x')
          = (Submission.BoseGases.chiScale ℓ u) ^ 2 * f (insertCoord2 p u v x')
      rw [show insertCoord2 p u v x' p.1 = u from insertCoord2_apply_fst p ((u, v), x')]
    rw [h1, hpull u, hswap u]
  have hmain : (∫ x in Submission.BoseGases.abox n ℓ, F x)
      = ∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 *
          (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
            f (insertCoord2 p u s x')) :=
    (abox_peel_two hℓ hp hFin).trans hstep
  exact hmain.symm

theorem imgFibreDG_integral {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {G : Submission.BoseGases.X n → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    (∫ u in Work.BoseK15.corpusBox.boxL ℓ,
        (Submission.BoseGases.chiScale ℓ u) ^ 2 * Work.BoseBoxFock.imgFibreDG ℓ p G u)
      = Work.BoseBoxFock.imgFibreDχ ℓ p G := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    rw [show (0 : WithTop ℕ∞) = ((0 : ℕ∞) : WithTop ℕ∞) from rfl]
    exact fun h => ENat.top_ne_zero (WithTop.coe_eq_coe.mp h)
  have hf : Continuous (fun x : Xn n =>
      ∑ j : Fin 3, (fderiv ℝ G x (slotDirVec p.1 j)) ^ 2) := by
    refine continuous_finsetSum (Finset.univ : Finset (Fin 3)) (fun j _ => ?_)
    exact (((hG.continuous_fderiv_apply hne).comp
      (continuous_id.prodMk continuous_const))).pow 2
  have hgen := imgFibreDG_integral_gen (n := n) (ℓ := ℓ) hℓ hp
    (f := fun x : Xn n => ∑ j : Fin 3, (fderiv ℝ G x (slotDirVec p.1 j)) ^ 2) hf
  simpa only [imgFibreDG, imgFibreDχ] using hgen

end Work.BoseBoxFock
