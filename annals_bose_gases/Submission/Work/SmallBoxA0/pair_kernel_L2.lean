import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SboxEB
import Submission.Work.SmallBoxA0.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators
open Submission BoseGases
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Identification of the two-particle box `abox 2 s ⊆ X 2 = Fin 2 → ℝ³` with the
product cube `acube s ×ˢ acube s ⊆ ℝ³ × ℝ³`: the map `(y,z) ↦ ![y,z]` is a
measure-preserving bijection onto `abox 2 s`, so the `L²`-mass of a pair kernel
computed in the two coordinates agrees with the `L²`-mass computed on the
two-particle box.  Also transfers a.e. strong measurability and the
integrability of the square.

Route: use the measurable equivalence `X 2 ≃ᵐ ℝ³ × ℝ³`, `x ↦ (x 0, x 1)`
(`MeasurableEquiv.piFinTwo`), which maps `abox 2 s` onto `acube s ×ˢ acube s`
and pushes `(volume : Measure (X 2)).restrict (abox 2 s)` to
`(volume : Measure (ℝ³ × ℝ³)).restrict (acube s ×ˢ acube s)` (via
`restrict_abox_eq_pi`, `Measure.pi` over `Fin 2` = product, `Measure.prod_restrict`);
transfer `AEStronglyMeasurable` (`MeasurePreserving.ae_strongly_measurable_comp_iff`),
`Integrable` of the square, and the integral (`MeasurePreserving.integral_comp`),
using `memLp_two_iff_integrable_sq` for the `MemLp → Integrable (·²)` step. -/
lemma pair_kernel_L2 {s : ℝ} (hs : 0 < s) {W : ℝ³ → ℝ³ → ℝ}
    (hW : MemLp (fun q : X 2 => W (q 0) (q 1)) 2 (volume.restrict (abox 2 s))) :
    AEStronglyMeasurable (fun q : ℝ³ × ℝ³ => W q.1 q.2) (volume.restrict (acube s ×ˢ acube s))
    ∧ IntegrableOn (fun q : ℝ³ × ℝ³ => (W q.1 q.2) ^ 2) (acube s ×ˢ acube s) volume
    ∧ (∫ q in acube s ×ˢ acube s, (W q.1 q.2) ^ 2)
        = ∫ q in abox 2 s, (W (q 0) (q 1)) ^ 2 := by
  -- The measurable equivalence `X 2 ≃ᵐ ℝ³ × ℝ³`, `x ↦ (x 0, x 1)`.
  let e : X 2 ≃ᵐ ℝ³ × ℝ³ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ³)
  -- It is measure preserving from the two-particle box to the product cube.
  have hmp : MeasurePreserving e (volume.restrict (abox 2 s))
      (volume.restrict (acube s ×ˢ acube s)) := by
    have h := measurePreserving_piFinTwo
        (fun _ : Fin 2 => (volume : Measure ℝ³).restrict (acube s))
    rw [← restrict_abox_eq_pi 2 s] at h
    rw [Measure.prod_restrict] at h
    rw [← MeasureTheory.Measure.volume_eq_prod ℝ³ ℝ³] at h
    exact h
  have he : ⇑e = fun x : X 2 => (x 0, x 1) := by
    rw [MeasurableEquiv.piFinTwo_apply]
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have heq : (fun x : X 2 => W (x 0) (x 1)) = (fun q : ℝ³ × ℝ³ => W q.1 q.2) ∘ e := by
    funext x; simp [he, Function.comp]
  -- A.e. strong measurability transfers.
  have h1 : AEStronglyMeasurable (fun q : ℝ³ × ℝ³ => W q.1 q.2)
      (volume.restrict (acube s ×ˢ acube s)) := by
    rw [← hmp.aestronglyMeasurable_comp_iff hemb, ← heq]
    exact hW.aestronglyMeasurable
  -- Integrability of the square transfers (`MemLp 2 → Integrable (·²)`).
  have h2 : IntegrableOn (fun q : ℝ³ × ℝ³ => (W q.1 q.2) ^ 2)
      (acube s ×ˢ acube s) volume := by
    rw [IntegrableOn, ← hmp.integrable_comp_emb hemb]
    have heq2 : (fun x : X 2 => (W (x 0) (x 1)) ^ 2)
        = (fun q : ℝ³ × ℝ³ => (W q.1 q.2) ^ 2) ∘ e := by
      funext x; simp [he, Function.comp]
    rw [← heq2]
    exact (memLp_two_iff_integrable_sq hW.aestronglyMeasurable).mp hW
  refine ⟨h1, h2, ?_⟩
  -- The integrals agree since the measures are pushed forward.
  rw [← hmp.integral_comp hemb (fun q : ℝ³ × ℝ³ => (W q.1 q.2) ^ 2)]
  simp [he]

end Work.SmallBoxA0
