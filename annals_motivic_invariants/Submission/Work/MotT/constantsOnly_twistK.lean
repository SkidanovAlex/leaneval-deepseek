import Submission.Work.MotT.Defs
import Submission.Work.MotT.twistFieldTK_descent
import Submission.Work.MotC.constantsOnly_of_descent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Node T5 (`constantsOnly_twistK`): constants-only for the T-twist field over an arbitrary base

`Work.MotV.ConstantsOnly K (twistFieldTK D h)` says that every `K`-embedding of the twist field into
a one-variable rational function field over a `K`-algebra `M` has image in the constants.  It is the
`hCO` input of `Work.MotT.certN3_of_linkCert` in the assembly `not_gen_three_of_val`.

The proof is the descent node `Work.MotC.constantsOnly_of_descent` (design node CR4, installed and
proved in `Submission/Work/MotC/constantsOnly_of_descent.lean`) applied to the `K`-form
`twistFieldTK D h ⊆ K̄(E)` supplied by T2 (`Work.MotT.twistFieldTK_descent`).
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-- **T5.**  Constants-only for the T-twist field, over an arbitrary base field `K` of
characteristic `≠ 5`. -/
theorem constantsOnly_twistK {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (hk : ringChar K ≠ 5) (h : K) (hh : h ≠ 0) :
    Work.MotV.ConstantsOnly K (twistFieldTK D h) := by
  obtain ⟨hLI, hsup⟩ := twistFieldTK_descent D hD hk h hh
  haveI : DecidableEq (KbK K) := Classical.decEq _
  haveI := hD.elliptic
  have hΔE : D.E.Δ ≠ 0 := isUnit_iff_ne_zero.mp (WeierstrassCurve.isUnit_Δ D.E)
  have hΔ : (D.E.baseChange (KbK K)).Δ ≠ 0 := by
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact fun h0 => hΔE ((algebraMap K (KbK K)).injective (by rw [h0, map_zero]))
  exact Work.MotC.constantsOnly_of_descent (D.E.baseChange (KbK K)) hΔ (twistFieldTK D h) hLI hsup

end

end Work.MotT
