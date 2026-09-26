import Mathlib
import Submission.Work.Drive.Interfaces

/-!
# Drive interfaces, corrected (project lead, 2026-09-25)

`Work.Drive.CleansDiscsAllW` is FALSE (report lemma-Drive_cleansDiscsAllW.md): `InnermostDisc` lets an interior curve TOUCH the
boundary curve `α`, and then the weak cut-and-paste fails (the lens/crescent example). In Pardon's setting the curves of `S ∩ F`
are pairwise disjoint and `α` is one of them, so the other curves are DISJOINT FROM `α`. The corrected input quantifies only over such
discs.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive

open Work.CoreTopology

/-- The weak cut-and-paste for innermost discs whose interior curves are disjoint from the boundary curve. -/
def CleansDiscsWd (P : ParamTorus) : Prop :=
  ∀ (S : Set R3) (D : Work.InnermostDisk.InnermostDisc P S),
    (∀ i, Disjoint (Set.range (D.curves i).γ) (Set.range D.α.γ)) → BoundsDiskInComplementW P D.α

def CleansDiscsAllWd : Prop :=
  ∀ (ψ : Submission.Diffeo), CleansDiscsWd (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)

theorem cleansDiscsWd_of_W {P : ParamTorus} (h : CleansDiscsW P) : CleansDiscsWd P :=
  fun S D _ => h S D

end Work.Drive
