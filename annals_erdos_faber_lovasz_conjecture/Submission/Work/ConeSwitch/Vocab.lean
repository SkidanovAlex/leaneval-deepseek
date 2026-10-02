import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.EFL.Reservoir
import Submission.EFL.NibbleFixed
import Submission.EFL.S12ANum
import Submission.EFL.S12BNum
import Submission.EFL.S12MainA
import Submission.EFL.S12MainA2
import Submission.EFL.S12MainB
import Submission.EFL.S12Step1Full
import Submission.Work.S12Faithful.Branch
import Submission.Work.S12Faithful.Small
import Submission.Work.Deep.GKO.Deliverable

/-!
# `Work.ConeSwitch` — the vocabulary module

Re-exports the cone vocabulary (§12's `IsFull`, `Vplus`, `S12ANum`, the branches, the faithful
Type-A₂ branch of `Work.S12Faithful`) together with the *hygiene shim*
`Submission.Work.ConeSwitch.MathlibNoHG` (all of Mathlib except the root-level `Hypergraph`
declaration), so that lemmas in `Work.ConeSwitch` can be stated in the cone's language without
re-introducing the `Hypergraph` ambiguity.
-/

set_option autoImplicit false
