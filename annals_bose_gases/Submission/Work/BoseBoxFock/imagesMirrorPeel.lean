import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.imgFibre_peel
import Submission.Work.BoseBoxFock.integrableOn_imgKernel_slots
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imagesMirrorPeel` — a cone-local copy of the `p.2`-slot peel

This is a verbatim copy of `Submission/Work/BoseBoxFock/imgFibre2_peel.lean` in which the auxiliary
lemma `insertCoord2_update_p2` has been renamed to `insertCoord2_update_p2Mirror`.

**Why.**  The module `Work.BoseBoxFock.imgFibreEnergyLe` (a proved sibling) *also* declares
`Work.BoseBoxFock.insertCoord2_update_p2`, so the two modules cannot live in one import cone.  The
assembly `imagesWordLe` needs both the mirror peel and `imgFibreEnergyLe`; this copy provides the
peel under a cone-local renamed auxiliary, so that no duplicate declaration arises.  The renamed
lemma is used only inside this file.

# (original title) `imgFibre2_peel` — the `p.2`-slot peel of the images words

The mirror twin of `Work.BoseBoxFock.imgFibre_peel`: the pair term whose free factor is the
**slot-`p.2` mean** `aP ℓ p.2 F₁` is the `boxL × boxL`-pairing of the kernel against the *mirror*
fibre `imgFibre₂` (whose averaged slot is the **second** coordinate of the two-slot insertion).

    ∫_{x ∈ abox n ℓ} (aP ℓ p.2 F₁ x)·G x·imgKernel ℓ W (x p.1) (x p.2)
      = ∫_{u ∈ boxL ℓ}∫_{v ∈ boxL ℓ} imgKernel ℓ W u v · imgFibre₂ ℓ p F₁ G u v

**Route.**  The two-slot peel `abox_peel_two` (with its integrability hypothesis produced here by
`integrable_pullback_insertCoord2` from the measure-preserving coordinate insertion
`sliceIns_measurePreserving`) rewrites the box integral as the iterated integral over
`boxL × boxL × boxPiSet`; in the peeled configuration the two slots `p.1`, `p.2` of the insertion
are `u`, `v` (`insertCoord2_self_p1`/`insertCoord2_self_p2`), which produces the kernel
`imgKernel ℓ W u v`, and the `p.2`-slot mean `aP ℓ p.2 F₁ (insertCoord2 p u v x')` unfolds — after
updating slot `p.2` (`insertCoord2_update_p2Mirror`) — into `ℓ⁻³ ∫_{s ∈ boxL} F₁ (insertCoord2 p u s
x')`.  What remains is the pointwise identity `(ℓ⁻³ ∫_s F₁(s))·G·K = ℓ⁻³ K·∫_s F₁(s)G`
(`integral_mul_const`) plus pulling the two constants out of the `x'`-integral
(`integral_const_mul`).

Only the *unpushed* integrability of the box integrand is needed (supplied by
`integrableOn_imgKernel_slots` applied to `|aP ℓ p.2 F₁ · G|`), so the assembly is
`abox_peel_two` + elementary unfolding.  `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Coordinate evaluations of the two-slot insertion -/

/-- The `p.1`-slot of `insertCoord2 p u v x'` is the first inserted value. -/
theorem insertCoord2_self_p1 {n : ℕ} (p : Fin n × Fin n) (u v : E3)
    (x' : pairFib23 n p → E3) : insertCoord2 p u v x' p.1 = u := by
  simp [insertCoord2_eq]

/-- The `p.2`-slot of `insertCoord2 p u v x'` is the second inserted value. -/
theorem insertCoord2_self_p2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (u v : E3)
    (x' : pairFib23 n p → E3) : insertCoord2 p u v x' p.2 = v := by
  simp [insertCoord2_eq, Ne.symm hp]

/-- Updating the `p.2`-slot of a two-slot insertion re-inserts the new value there. -/
theorem insertCoord2_update_p2Mirror {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (u v s : E3) (x' : pairFib23 n p → E3) :
    Function.update (insertCoord2 p u v x') p.2 s = insertCoord2 p u s x' := by
  funext k
  by_cases h2 : k = p.2
  · subst h2
    rw [Function.update_self]
    simp [insertCoord2_eq, Ne.symm hp]
  · rw [Function.update_of_ne h2]
    by_cases h1 : k = p.1
    · subst h1
      simp [insertCoord2_eq]
    · simp only [insertCoord2_eq, dif_neg h1, dif_neg h2]

/-- **The `p.2`-slot mean at a two-slot insertion** is the box average of `F₁` over the *second*
inserted coordinate. -/
theorem aP_insertCoord2_p2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    (F₁ : Submission.BoseGases.X n → ℝ) (u v : E3) (x' : pairFib23 n p → E3) :
    Submission.BoseGases.aP ℓ p.2 F₁ (insertCoord2 p u v x')
      = (ℓ ^ 3)⁻¹ * ∫ s in Work.BoseK15.corpusBox.boxL ℓ, F₁ (insertCoord2 p u s x') := by
  have hupd : ∀ s : E3, Function.update (insertCoord2 p u v x') p.2 s
      = insertCoord2 p u s x' := fun s => insertCoord2_update_p2Mirror p hp u v s x'
  simp only [Submission.BoseGases.aP]
  rw [← corpusBox_boxL_eq_acube hℓ, one_div]
  refine congrArg (fun t => (ℓ ^ 3)⁻¹ * t) ?_
  exact integral_congr_ae (Filter.Eventually.of_forall fun s => congrArg F₁ (hupd s))

/-! ## 2. Integrability of the pull-back along the two-slot insertion -/

/-- **The pushed-forward integrability form of the two-slot peel.**  If `F` is integrable on the
box `abox n ℓ`, then the pull-back of `F` along the coordinate insertion is integrable against the
product of the box measures — which is the hypothesis of the two-slot peel
`Work.BoseBoxFock.abox_peel_two` (from `Submission/Work/BoseBoxFock/abox_peel_two.lean`).

The insertion `sliceIns p hp` is a measure-preserving *equivalence* from
`(boxMeas ℓ × boxMeas ℓ) × Measure.pi (fun _ => boxMeas ℓ)` onto `Measure.pi (fun _ => boxMeas ℓ)`
(`sliceIns_measurePreserving`), and the latter is `volume.restrict (abox n ℓ)`
(`restrict_abox_eq`); `MeasurePreserving.integrable_comp` transports integrability backwards. -/
theorem integrable_pullback_insertCoord2 {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    (hp : p.1 ≠ p.2) {F : Submission.BoseGases.X n → ℝ}
    (hF : MeasureTheory.IntegrableOn F (Submission.BoseGases.abox n ℓ)) :
    MeasureTheory.Integrable
      (fun w : (E3 × E3) × (pairFib23 n p → E3) => F (insertCoord2 p w.1.1 w.1.2 w.2))
      (((boxMeas ℓ).prod (boxMeas ℓ)).prod
        (Measure.pi (fun _ : pairFib23 n p => boxMeas ℓ))) := by
  have hμ : (volume : Measure (Fin n → E3)).restrict (Submission.BoseGases.abox n ℓ)
      = Measure.pi (fun _ : Fin n => boxMeas ℓ) := restrict_abox_eq hℓ
  have hF' : MeasureTheory.Integrable F (Measure.pi (fun _ : Fin n => boxMeas ℓ)) := by
    rw [← hμ]; exact hF
  have h := ((sliceIns_measurePreserving (ℓ := ℓ) p hp).integrable_comp
      hF'.aestronglyMeasurable).mpr hF'
  convert h using 2 with w
  rw [Function.comp_apply, sliceIns_apply]

/-! ## 3. The mirror peel identity -/

theorem imgFibre2_peel {n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hR : 0 ≤ R) (hRℓ : R ≤ ℓ / 2)
    (hWs : ∀ u : EuclideanSpace ℝ (Fin 3), R ≤ ‖u‖ → W u = 0)
    {F₁ G : Submission.BoseGases.X n → ℝ} (hF₁ : Continuous F₁) (hG : Continuous G) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        Submission.BoseGases.aP ℓ p.2 F₁ x * G x
          * Work.BoseBoxFock.imgKernel ℓ W (x p.1) (x p.2))
      = ∫ u in Work.BoseK15.corpusBox.boxL ℓ, ∫ v in Work.BoseK15.corpusBox.boxL ℓ,
          Work.BoseBoxFock.imgKernel ℓ W u v * Work.BoseBoxFock.imgFibre₂ ℓ p F₁ G u v := by
  -- integrability of the box integrand
  have hcont : Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.aP ℓ p.2 F₁ x * G x) :=
    (Submission.BoseGases.aP_continuous hℓ p.2 hF₁).mul hG
  have hAbs := integrableOn_imgKernel_slots hℓ hp hWi hR hRℓ hWs
    (fun x : Submission.BoseGases.X n => |Submission.BoseGases.aP ℓ p.2 F₁ x * G x|) hcont.abs
  have hAESM : AEStronglyMeasurable
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ p.2 F₁ x * G x
        * imgKernel ℓ W (x p.1) (x p.2))
      ((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)) :=
    hcont.aestronglyMeasurable.mul (aestronglyMeasurable_imgKernel hℓ hp hWi)
  have hIntOn : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => Submission.BoseGases.aP ℓ p.2 F₁ x * G x
        * imgKernel ℓ W (x p.1) (x p.2))
      (Submission.BoseGases.abox n ℓ) :=
    MeasureTheory.Integrable.mono' hAbs hAESM (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul])
  rw [abox_peel_two (ℓ := ℓ) (p := p) hℓ hp
    (integrable_pullback_insertCoord2 hℓ p hp hIntOn)]
  -- the two inserted slots become the two integration variables
  simp_rw [insertCoord2_self_p1, insertCoord2_self_p2 p hp]
  -- unfold the `p.2`-slot mean into the box average over the second inserted coordinate
  simp_rw [aP_insertCoord2_p2 hℓ p hp F₁]
  -- unfold the mirror fibre
  simp only [imgFibre₂]
  -- the remaining identity is a pointwise constant-pull-out
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  have h1 : ∀ x' : pairFib23 n p → E3,
      ((ℓ ^ 3)⁻¹ * ∫ s in Work.BoseK15.corpusBox.boxL ℓ, F₁ (insertCoord2 p u s x'))
          * G (insertCoord2 p u v x') * imgKernel ℓ W u v
        = (ℓ ^ 3)⁻¹ * (imgKernel ℓ W u v
            * (∫ s in Work.BoseK15.corpusBox.boxL ℓ,
                F₁ (insertCoord2 p u s x') * G (insertCoord2 p u v x'))) := by
    intro x'
    rw [MeasureTheory.integral_mul_const]
    ring
  simp_rw [h1]
  rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
  ring

end Work.BoseBoxFock
