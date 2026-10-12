import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.abox_peel_two
import Submission.Work.BoseBoxFock.integrable_peelIntegrand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibre_peel`

The peel identity for the position-space fibre of the `χχ`-images words
(`Work.BoseBoxFock.imgFibre`, `Work.BoseBoxFock.imagesFibre`):

    ∫_{abox n ℓ} (aP ℓ p.1 F₁ x) · G x · imgKernel ℓ W (x p.1) (x p.2)
      = ∫_{boxL ℓ}∫_{boxL ℓ} imgKernel ℓ W u v · imgFibre ℓ p F₁ G u v ,

i.e. the pairing of the slot-`p.1` mean of `F₁` against `G` with the lattice-images kernel is the
`boxL × boxL`-pairing of the kernel against the fibre in which the two slots `p.1`, `p.2` are
frozen at `u`, `v`, the slot `p.1` is averaged over the box and the remaining coordinates are
integrated out.

Both sides are the same `(ℓ³)⁻¹`-multiple of the iterated integral

    ∫_{u ∈ boxL}∫_{v ∈ boxL}∫_{x' ∈ boxᴺ⁻²}∫_{s ∈ boxL}
        F₁ (insertCoord2 p s v x') · G (insertCoord2 p u v x') · imgKernel ℓ W u v ;

the only non-elementary step is the measure-preserving two-slot peel
(`Work.BoseBoxFock.abox_peel_two`), which rewrites the `abox n ℓ`-integral over the configuration
as the `boxL × boxL × boxᴺ⁻²`-integral over the insertion `insertCoord2 p u v x'`.  Everything
else is the definitional expansion of `aP` (`aP_insertCoord2`, the `p.1`-slot update of the
insertion), together with the (unconditional) linearity of the Bochner integral in a constant
factor moved across the `s`-integral.

The two analytic inputs of the peel are `Work.BoseBoxFock.abox_peel_two` (the change of variables)
and `Work.BoseBoxFock.integrable_peelIntegrand` (integrability of the inserted integrand, which
rests on the `L¹`-bound `Work.BoseBoxFock.uncurry_pairImg_integrable` for the images kernel).

`sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The `p.1`-slot of a two-coordinate insertion is its first argument. -/
lemma insertCoord2_self_fst {n : ℕ} (p : Fin n × Fin n) (u v : E3)
    (x' : pairFib23 n p → E3) : insertCoord2 p u v x' p.1 = u := by
  simp [insertCoord2_eq]

/-- The `p.2`-slot of a two-coordinate insertion is its second argument. -/
lemma insertCoord2_self_snd {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (u v : E3)
    (x' : pairFib23 n p → E3) : insertCoord2 p u v x' p.2 = v := by
  simp [insertCoord2_eq, Ne.symm hp]

/-- Updating the `p.1`-slot of a two-coordinate insertion re-inserts the new value there. -/
lemma update_insertCoord2_fst {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (u v s : E3)
    (x' : pairFib23 n p → E3) :
    Function.update (insertCoord2 p u v x') p.1 s = insertCoord2 p s v x' := by
  funext k
  by_cases h1 : k = p.1
  · subst h1
    simp [Function.update_apply]
  · by_cases h2 : k = p.2
    · subst h2
      simp [Function.update_apply, Ne.symm hp]
    · simp only [insertCoord2_eq, Function.update_apply, h1, h2, dif_neg, not_false_iff]
      simp

/-- **The `aP`-mean at a two-coordinate insertion** is the `p.1`-slot average over the box (the
other inserted value is irrelevant for the mean). -/
lemma aP_insertCoord2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (F₁ : Submission.BoseGases.X n → ℝ) (u v : E3) (x' : pairFib23 n p → E3) :
    Submission.BoseGases.aP ℓ p.1 F₁ (insertCoord2 p u v x')
      = (ℓ ^ 3)⁻¹ * ∫ s in Work.BoseK15.corpusBox.boxL ℓ, F₁ (insertCoord2 p s v x') := by
  rw [Submission.BoseGases.aP, ← corpusBox_boxL_eq_acube hℓ, one_div]
  refine congrArg (fun t => (ℓ ^ 3)⁻¹ * t) ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [update_insertCoord2_fst p hp]

theorem imgFibre_peel {n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hR : 0 ≤ R) (hRℓ : R ≤ ℓ / 2)
    (hWs : ∀ u : EuclideanSpace ℝ (Fin 3), R ≤ ‖u‖ → W u = 0)
    {F₁ G : Submission.BoseGases.X n → ℝ} (hF₁ : Continuous F₁) (hG : Continuous G) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ p.1 F₁ x * G x
          * Work.BoseBoxFock.imgKernel ℓ W (x p.1) (x p.2))
      = ∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseBoxFock.imgKernel ℓ W u v * Work.BoseBoxFock.imgFibre ℓ p F₁ G u v := by
  classical
  -- bounds for the two continuous factors on the box
  obtain ⟨B₁, hB₁⟩ :=
    (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn hF₁.continuousOn
  obtain ⟨B₂, hB₂⟩ :=
    (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn hG.continuousOn
  have hF₁b : ∀ x ∈ Submission.BoseGases.abox n ℓ, |F₁ x| ≤ max B₁ 0 := fun x hx => by
    rw [← Real.norm_eq_abs]
    exact le_trans (hB₁ x hx) (le_max_left _ _)
  have hGb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |G x| ≤ max B₂ 0 := fun x hx => by
    rw [← Real.norm_eq_abs]
    exact le_trans (hB₂ x hx) (le_max_left _ _)
  have haPb : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      |Submission.BoseGases.aP ℓ p.1 F₁ x| ≤ max B₁ 0 :=
    Submission.BoseGases.aP_abs_le hℓ p.1 hF₁ (le_max_right _ _) hF₁b
  -- integrability of the inserted integrand (the two-slot slice of the LHS integrand)
  have hInt₀ : MeasureTheory.Integrable
      (fun w : (E3 × E3) × (pairFib23 n p → E3) =>
        Submission.BoseGases.aP ℓ p.1 F₁ (insertCoord2 p w.1.1 w.1.2 w.2)
          * G (insertCoord2 p w.1.1 w.1.2 w.2)
          * imgKernel ℓ W w.1.1 w.1.2)
      (((boxMeas ℓ).prod (boxMeas ℓ)).prod (Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ))) :=
    integrable_peelIntegrand hℓ hp hWi hR hRℓ hWs
      (Submission.BoseGases.aP_continuous hℓ p.1 hF₁) hG (le_max_right _ _) (le_max_right _ _)
      haPb hGb
  have hInt : MeasureTheory.Integrable
      (fun w : (E3 × E3) × (pairFib23 n p → E3) =>
        (fun x => Submission.BoseGases.aP ℓ p.1 F₁ x * G x
            * imgKernel ℓ W (x p.1) (x p.2)) (insertCoord2 p w.1.1 w.1.2 w.2))
      (((boxMeas ℓ).prod (boxMeas ℓ)).prod (Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ))) :=
    hInt₀.congr (Filter.Eventually.of_forall fun w => by
      simp only [insertCoord2_self_fst, insertCoord2_self_snd p hp])
  -- the measure-preserving two-slot peel
  have hpeel := abox_peel_two (ℓ := ℓ) (p := p) hℓ hp
    (F := fun x => Submission.BoseGases.aP ℓ p.1 F₁ x * G x * imgKernel ℓ W (x p.1) (x p.2)) hInt
  rw [hpeel]
  -- the two kernel slots of the insertion are the two integration variables
  simp only [insertCoord2_self_fst, insertCoord2_self_snd p hp]
  -- expand the `aP`-mean
  simp_rw [aP_insertCoord2 hℓ p hp F₁]
  -- unfold the fibre on the right-hand side
  simp only [imgFibre]
  -- the rest is moving the constant factor across the `s`-integral
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have h1 : ∀ x' : pairFib23 n p → E3,
      ((ℓ ^ 3)⁻¹ * ∫ s in Work.BoseK15.corpusBox.boxL ℓ, F₁ (insertCoord2 p s v x'))
          * G (insertCoord2 p u v x') * imgKernel ℓ W u v
        = (ℓ ^ 3)⁻¹ * (imgKernel ℓ W u v
            * (∫ s in Work.BoseK15.corpusBox.boxL ℓ,
                F₁ (insertCoord2 p s v x') * G (insertCoord2 p u v x'))) := by
    intro x'
    rw [MeasureTheory.integral_mul_const]
    ring
  simp_rw [h1]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  ring

end Work.BoseBoxFock
