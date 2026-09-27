import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

/-!
# A space homeomorphic to `𝕊ⁿ` is the one-point compactification of some `ℝⁿ`_

Given a homeomorphism `e : M ≃ₜ 𝕊ⁿ`, the point `p = e.symm q` where `q` is the image of the
point at infinity of `OnePoint ℝⁿ` under the stereographic homeomorphism
`onePointEquivSphereOfFinrankEq` has complement `{p}ᶜ` homeomorphic to `ℝⁿ`:

`{p}ᶜ ≃ₜ {q}ᶜ ≃ₜ {∞}ᶜ ⊂ OnePoint ℝⁿ ≃ₜ ℝⁿ`,

where the middle homeomorphisms are the restrictions of `e.symm` and of the stereographic
homeomorphism to the complements of the corresponding points (`homeomorphComplSingleton`), and
the last one is `complInftyHomeomorph`.
-/

open scoped OnePoint

namespace Work.Endgame

theorem exists_compl_homeomorph_euclideanSpace_of_homeomorph_sphere {n : ℕ} {M : Type*}
    [TopologicalSpace M] (e : M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∃ p : M, Nonempty (({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) := by
  -- The stereographic homeomorphism `OnePoint ℝⁿ ≃ₜ 𝕊ⁿ`.
  let φ : OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  -- Puncture `M` at the preimage of the point corresponding to `∞`.
  refine ⟨e.symm (φ OnePoint.infty), ?_⟩
  refine ⟨(homeomorphComplSingleton e.symm (φ OnePoint.infty)).symm.trans
    ((homeomorphComplSingleton φ OnePoint.infty).symm.trans
      (complInftyHomeomorph (EuclideanSpace ℝ (Fin n))))⟩

end Work.Endgame
