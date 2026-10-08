/-
# `V ≤ W` from the two ω-existence branches

The linchpin of Stage A (Peterfalvi Ch. V §1 Prop. 2 / Kantor–Seitz §§14–15): under
`PSU3Hyp`, `ChIIFourProp`, `HigmanProp` and the Feit–Thompson hypothesis, `V = C_D(t)` is
contained in `W = C_V(K)`.

`Work.PSU3.StageA.centD_le_W_of_PSU3HypFT_of_pieces` isolates the whole Stage A→D assembly to
the single input "some frame carries an `Ω`-witness", and the two ω-existence nodes
`Work.PSU3.StageB.exists_omega_of_fpf_rebuilt` (fixed-point-free branch) and
`Work.PSU3.StageB.exists_omega_of_not_fpf_FT` (the `V ≠ W` branch) supply exactly that.
-/
import Submission.Work.PSU3.StageA.centD_le_W_of_PSU3HypFT
import Submission.Work.PSU3.StageB.exists_omega_of_fpf_rebuilt
import Submission.Work.PSU3.StageB.exists_omega_of_not_fpf_FT

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3.StageA

theorem centD_le_W_of_PSU3Hyp_closed {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) (hFT : Submission.Blueprint.FeitThompsonProp) :
    Submission.Blueprint.centD H t ≤ Work.ThmF.W H t :=
  centD_le_W_of_PSU3HypFT_of_pieces hS hC4 hFT
    (fun fr hfpf => Work.PSU3.StageB.exists_omega_of_fpf_rebuilt hS hC4 hHig fr hfpf)

end Work.PSU3.StageA
