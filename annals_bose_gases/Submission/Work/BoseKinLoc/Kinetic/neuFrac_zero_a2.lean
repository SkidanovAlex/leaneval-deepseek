import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Kinetic.neuFrac_zero_a2`

At `a² = 0` the Neumann-resolvent fraction `Work.BoseKinLoc.neuFrac`, defined as the `sInf` of
the variational trial values

`c_φ(g) = ∫_{Λ(u)} φ² − 2a² ∫_{Λ(u)} φ·g + a² (Σ_k ∫_{Λ(u)} (∂_k g)² + a² ∫_{Λ(u)} g²)`,

collapses: the two terms carrying `a²` vanish, so **every** admissible trial `g` gives the same
value,

`c_φ(g) = ∫_{Λ(u)} φ²`.

Hence the trial set is the singleton `{∫_{Λ(u)} φ²}` (nonempty because `g = 0` is smooth and
compactly supported) and its `sInf` is that value:

    `neuFrac ℓ 0 u φ = ∫_{Λ(u)} φ²`.

No hypothesis on `φ` is needed: the integral notation is total (`0` when `φ²` is not integrable),
and both sides degenerate in exactly the same way.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Kinetic

theorem neuFrac_zero_a2 (ℓ : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseKinLoc.neuFrac ℓ 0 u φ
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2 := by
  unfold Work.BoseKinLoc.neuFrac
  have hset : { c : ℝ | ∃ g : EuclideanSpace ℝ (Fin 3) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
        c = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2)
            - 2 * (0 : ℝ) * (∫ z in Work.BoseKinLoc.lamBox ℓ u, φ z * g z)
            + (0 : ℝ) * ((∑ k : Fin 3,
                  ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                    (fderiv ℝ g z (Submission.BoseGases.kcStdBasis k)) ^ 2)
                + (0 : ℝ) * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (g z) ^ 2)) }
      = {∫ z in Work.BoseKinLoc.lamBox ℓ u, (φ z) ^ 2} := by
    ext c
    constructor
    · rintro ⟨g, hg1, hg2, rfl⟩
      simp
    · intro h
      rw [Set.mem_singleton_iff] at h
      exact ⟨0, contDiff_zero_fun, HasCompactSupport.zero, by simp [h]⟩
  rw [hset, csInf_singleton]

end Work.BoseKinLoc.Kinetic
