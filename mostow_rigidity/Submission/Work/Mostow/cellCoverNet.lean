import Mathlib
import Submission.Work.Mostow.KMCellDefs

namespace Work.Mostow

open Submission.Mostow

/-- The closed unit `hdist`-ball about the base point `0` is compact, hence it admits a finite
`e`-net consisting of points of the ball itself. -/
theorem cellCoverNet (k : ℕ) (hI : Submission.Mostow.HypIsometryProp k) (e : ℝ) (he : 0 < e) :
    ∃ t : Finset (Submission.Mostow.E k),
      (∀ j ∈ t, Submission.Mostow.hdist (0 : Submission.Mostow.E k) j ≤ 1) ∧
      ∀ v : Submission.Mostow.E k, Submission.Mostow.hdist (0 : Submission.Mostow.E k) v ≤ 1 →
        ∃ j ∈ t, Submission.Mostow.hdist v j < e := by
  obtain ⟨-, -, hzero, -, hcont, hcomp, -⟩ := hI
  classical
  have hK : IsCompact {v : E k | hdist (0 : E k) v ≤ 1} := hcomp 0 1
  have hcont' : ∀ j : E k, Continuous fun v : E k => hdist v j := by
    intro j
    change Continuous ((fun p : E k × E k => hdist p.1 p.2) ∘ (fun v : E k => (v, j)))
    exact hcont.comp (Continuous.prodMk continuous_id continuous_const)
  obtain ⟨t, htK, htcover⟩ :=
    hK.elim_nhds_subcover (fun j : E k => {v : E k | hdist v j < e / 2})
      (fun j _ => (isOpen_lt (hcont' j) continuous_const).mem_nhds (by
        show hdist j j < e / 2
        rw [(hzero j j).mpr rfl]
        linarith))
  refine ⟨t, fun j hj => htK j hj, fun v hv => ?_⟩
  rcases Set.mem_iUnion₂.mp (htcover hv) with ⟨j, hjt, hjv⟩
  exact ⟨j, hjt, lt_trans hjv (by linarith)⟩

end Work.Mostow
