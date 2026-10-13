import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Stability.Cutoff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- The support of the physical cut-off `omegaCut L ω = chi(ρ(x)/L) • ω(x)` is contained in the
support of `ω`: where `ω` vanishes, so does any scalar multiple of it. -/
theorem support_omegaCut_subset {L : ℝ} {ω : Work.Cyl.R3 → Work.Cyl.R3} :
    Function.support (omegaCut L ω) ⊆ Function.support ω := by
  intro x hx
  contrapose! hx
  simp only [Function.mem_support, not_not] at hx ⊢
  simp [omegaCut, hx]

/-- **Compact support is preserved by the cut-off** (trivially, since
`supp (omegaCut L ω) ⊆ supp ω`).  This is the `C^{1,α}`-class preservation of the design's St1:
the data stays compactly supported. -/
theorem OmegaCutSupport {L : ℝ} {ω : Work.Cyl.R3 → Work.Cyl.R3}
    (h : HasCompactSupport ω) : HasCompactSupport (omegaCut L ω) :=
  HasCompactSupport.mono h support_omegaCut_subset

end Work.Stability
