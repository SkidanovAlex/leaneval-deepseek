import Mathlib
import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.Basic

namespace Work.Endgame

theorem nonempty_homeomorph_sphere_of_nonempty_compl_homeomorph {n : ℕ} {M : Type*}
    [TopologicalSpace M] [T2Space M] [CompactSpace M] (p : M)
    (h : Nonempty (({p}ᶜ : Set M) ≃ₜ EuclideanSpace ℝ (Fin n))) :
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  h.elim fun e => ⟨homeomorphSphereOfComplHomeomorph p e⟩

end Work.Endgame
