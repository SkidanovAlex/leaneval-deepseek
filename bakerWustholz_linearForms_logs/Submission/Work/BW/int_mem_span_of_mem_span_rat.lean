import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.ratSpan_saturation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Saturation, in the form used by `multiplicity_prop`: an integral vector in the `ℚ`-span of
the rows of a primitive system already lies in their `ℤ`-span. (Clear denominators: `N • B` is a
`ℤ`-combination of the rows for some `N ≠ 0`, and `PrimSys M` says `ℤ span` is saturated.
`Work.BW.ratSpan_saturation` in `Submission/Work/BW/ratSpan_saturation.lean` is the contrapositive,
so the proof should be a few lines from it.) -/
theorem int_mem_span_of_mem_span_rat {ρ r : ℕ} {M : Fin ρ → Fin r → ℤ} (hM : PrimSys M)
    {B : Fin r → ℤ}
    (hBM : (fun i => (B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ))) :
    B ∈ Submodule.span ℤ (Set.range M) := by
  by_contra hB
  apply ratSpan_saturation M hM B _ hBM
  rintro ⟨c, hc⟩
  apply hB
  rw [Submodule.mem_span_range_iff_exists_fun ℤ]
  refine ⟨c, ?_⟩
  funext i
  simpa [Finset.sum_apply, Pi.smul_apply] using (hc i).symm

end Work.BW
