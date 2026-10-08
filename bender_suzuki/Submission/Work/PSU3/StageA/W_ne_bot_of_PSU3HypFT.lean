import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.Higman.Main
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageA.not_caseA
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.lemma2cHig
import Submission.Work.PSU3.StageA.caseWbot_abelian_eq_Q0sub
import Submission.Work.PSU3.StageA.caseB_false
import Submission.Work.PSU3.StageA.caseWbot_nonabelian_card_order

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

theorem W_ne_bot_of_PSU3HypFT {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp) :
    Work.ThmF.W H t ≠ ⊥ := by
  intro hW
  have hHig : Submission.Blueprint.HigmanProp := Work.Higman.higmanProp
  obtain ⟨s, hs, hs2, r, hr, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  -- Ch. V §1 Prop. 2, with the odd order theorem supplying `Group.IsSolvable ↥D`:
  -- the set `K = J(D,t)` is a cyclic normal subgroup of `D`.
  have hK : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    (Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hS.situation hS.split).2.1
  by_cases hab : Submission.Blueprint.IsAbelianSubgroup Q
  · -- case a): `Q = Q₀`, and the "Réduction" of Ch. VI §3 contradicts simplicity.
    have hQ : (Q : Set G) = Work.ThmF.Q0sub H :=
      caseWbot_abelian_eq_Q0sub hS hC4 hFT hW hab
    have hst : t * s * t = s * t * s :=
      Work.PSU3.StageA.tst_eq_sts_of_Q_eq_Q0sub hS hC4 hs hs2 hr hsr hQ
    exact Work.PSU3.StageA.not_caseA_of_FT hFT hS hC4 hHig hs hs2 hr hsr hst hQ
  · -- case b): `|Q| = q²` and `st` has order `5`; Ch. VI §2–§3 contradicts simplicity.
    obtain ⟨hcard, h5⟩ :=
      caseWbot_nonabelian_card_order hS hC4 hFT hs hs2 hr hsr hW hab
    exact caseB_false hS hC4 hs hs2 hr hsr h5 hab hcard hW hK

end Work.PSU3.StageA
