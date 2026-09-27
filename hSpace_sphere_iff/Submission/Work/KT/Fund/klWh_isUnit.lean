import Mathlib
import Submission.Work.KT.Fund.kl_wh_defs
import Submission.Work.KT.Fund.isUnit_matrix_forall

namespace Work.KT.Fund

theorem klWh_isUnit (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ))
    (hout : ∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
      IsUnit ((((t : ℂ) * z) • (1 - E) + (1 - E) * b + E).map (fun f => f x))) :
    IsUnit (Work.KT.Fund.klWh X n b E) := by
  refine (isUnit_matrix_forall (X := (X × unitInterval) × Sph ℂ) n (klWh X n b E)).mpr ?_
  intro q
  obtain ⟨⟨x, s⟩, z⟩ := q
  rw [klWh_eval X n b E x s z]
  exact hout x (s : ℝ) (z : ℂ) s.2.1 s.2.2 (by simpa using z.2)

end Work.KT.Fund
