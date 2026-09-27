import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

namespace Work.Endgame

/-- A compact Hausdorff space `M` is the one-point compactification of `ℝⁿ` exactly when its
complement at some point is `ℝⁿ`.

* (⇐) If `({p}ᶜ : Set M) ≃ₜ ℝⁿ`, then `M ≃ₜ OnePoint ({p}ᶜ) ≃ₜ OnePoint ℝⁿ`, via the universal
  property of `OnePoint` (`onePointComplHomeomorph`) and functoriality
  (`Homeomorph.onePointCongr`): this is `homeomorphOnePointOfComplHomeomorph`.
* (⇒) If `e : M ≃ₜ OnePoint ℝⁿ`, take `p := e.symm ∞`. Then `e` restricts to a homeomorphism
  `({p}ᶜ) ≃ₜ ({∞}ᶜ)`, and the complement of the point at infinity in `OnePoint ℝⁿ` is `ℝⁿ`
  (`complInftyHomeomorph`). -/
theorem nonempty_homeomorph_onePoint_iff {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] :
    Nonempty (M ≃ₜ OnePoint (EuclideanSpace ℝ (Fin n))) ↔
      ∃ p : M, Nonempty (({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n)) := by
  constructor
  · rintro ⟨e⟩
    refine ⟨e.symm OnePoint.infty, ⟨?_⟩⟩
    refine (homeomorphComplSingleton e (e.symm OnePoint.infty)).trans ?_
    refine (Homeomorph.setCongr ?_).trans
      (complInftyHomeomorph (EuclideanSpace ℝ (Fin n)))
    rw [e.apply_symm_apply]
  · rintro ⟨p, ⟨h⟩⟩
    exact ⟨homeomorphOnePointOfComplHomeomorph p h⟩

end Work.Endgame
