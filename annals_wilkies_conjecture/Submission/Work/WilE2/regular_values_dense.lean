/-
  `Work.WilE2.regular_values_dense` — regular values are dense.

  For a `C²` map `G : ℝ^{m+1} → ℝ^m`, the set of critical values is Lebesgue-null
  (`Work.WilE2.sard_codim_one`, assembled in `RegVals/Main.lean`), hence its complement — the
  regular values — is dense; a value `y` is regular exactly when at every preimage `z` the
  differential `fderiv ℝ G z` is surjective, which is the linear independence of the `m`
  component derivatives.
-/
import Mathlib
import Submission.Work.WilE2.RegVals.Main
import Submission.Work.WilE2.RegVals.Basic
import Submission.Work.WilE2.RegVals.surjective_iff_linearIndependent_coord
import Submission.Work.WilE2.avoid_null

open MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.WilE2

theorem regular_values_dense {m : ℕ} (G : (Fin (m + 1) → ℝ) → (Fin m → ℝ)) (hG : ContDiff ℝ 2 G) :
    ∀ (y₀ : Fin m → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin m → ℝ, dist y y₀ < ε ∧
      ∀ z, G z = y → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => G w a) z) := by
  intro y₀ ε hε
  have hset : ({y : Fin m → ℝ | ∃ z, G z = y ∧ ¬ Function.Surjective (fderiv ℝ G z)})
      = G '' critSet G := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image, mem_critSet]
    exact ⟨fun ⟨z, hz, hc⟩ => ⟨z, hc, hz⟩, fun ⟨z, hc, hz⟩ => ⟨z, hz, hc⟩⟩
  have hnull : volume {y : Fin m → ℝ | ∃ z, G z = y ∧ ¬ Function.Surjective (fderiv ℝ G z)}
      = 0 := by
    rw [hset]
    exact sard_codim_one (m + 1) G hG
  obtain ⟨y, hy, hybad⟩ := avoid_null hnull y₀ hε
  refine ⟨y, hy, fun z hz => ?_⟩
  have hsurj : Function.Surjective (fderiv ℝ G z) := by
    by_contra hc
    exact hybad ⟨z, hz, hc⟩
  rw [RegVals.surjective_iff_linearIndependent_coord] at hsurj
  have hfam : (fun a : Fin m => (ContinuousLinearMap.proj a).comp (fderiv ℝ G z))
      = fun a : Fin m => fderiv ℝ (fun w => G w a) z := by
    funext a
    exact (fderiv_coord G z ((hG.differentiable (by norm_num)) z) a).symm
  rwa [hfam] at hsurj

end Work.WilE2
