/-
# `Work.PSU3.StageB.Omega.hcan_mem_KW_of_le`

Glue lemma isolating the single structural input that the proof of Stage B / node B1 needs from
the frame (see `STATUS_B1.md`): if the frame's `KW` is all of `D = twoPoint H t` — i.e. `ζ`
generates `W`, equivalently `|W| = orderOf fr.ζ` — then every `h`-component of a canonical form
lands in `fr.KW`, which is exactly the hypothesis (`hKW`) of
`Omega.square_eq_shift_of_good_cover_hKW` and the missing step of Peterfalvi's p. 274 argument.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Canon

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- If `D = twoPoint H t ≤ fr.KW` then `h (x) ∈ fr.KW` for every `x ∈ Q`. -/
theorem hcan_mem_KW_of_twoPoint_le_KW (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (hDK : twoPoint H t ≤ fr.KW) (x : ↥Q) :
    ((hcan hS.split x : ↥(twoPoint H t)) : G) ∈ fr.KW :=
  hDK (hcan hS.split x).2

/-- `hKW`-form: the hypothesis consumed by `Omega.square_eq_shift_of_good_cover_hKW`. -/
theorem hKW_of_twoPoint_le_KW (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    (hDK : twoPoint H t ≤ fr.KW) :
    ∀ x : ↥Q, (x : G) ∉ fr.Q0 →
      ((hcan hS.split x : ↥(twoPoint H t)) : G) ∈ fr.KW :=
  fun x _ => hcan_mem_KW_of_twoPoint_le_KW hS fr hDK x

end Work.PSU3.StageB.Omega
