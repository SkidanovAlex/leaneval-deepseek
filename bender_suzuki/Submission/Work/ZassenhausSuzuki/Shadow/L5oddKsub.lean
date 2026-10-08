import Submission.Work.ZassenhausSuzuki.SzSetting
import Mathlib
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ZassenhausSuzuki.Shadow.L5Struct

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ZassenhausSuzuki.Shadow.ChV12
open Submission.Blueprint

open Work.ThmF.ChV12
theorem L5oddKsub {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s) : Odd (Nat.card ↥(Work.ThmF.Ksub H t)) := by
  have hle : Work.ThmF.Ksub H t ≤ twoPoint H t :=
    Work.ThmF.Ksub_le_twoPoint (H := H) t
  have hdvd : Nat.card ↥(Work.ThmF.Ksub H t) ∣ Nat.card ↥(twoPoint H t) :=
    Subgroup.card_dvd_of_le hle
  exact (Work.ThmF.split_odd_card_twoPoint h.split).of_dvd_nat hdvd

end Work.ZassenhausSuzuki.Shadow.ChV12
