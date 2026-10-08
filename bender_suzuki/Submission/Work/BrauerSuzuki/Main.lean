import Mathlib
import Submission.Work.BrauerSuzuki.Dade.main
import Submission.Work.BrauerSuzuki.Glue.brauerSuzuki_of_weak
import Submission.Work.BrauerSuzuki.Glue.weak_of_large_and_q8
import Submission.Work.BrauerSuzuki.Group.isCyclicOrGenQuaternion_of_uniqueInvolution
import Submission.Work.BrauerSuzuki.Sylow.genQuaternion_sylow_quotient
import Submission.Work.BrauerSuzuki.Q8.main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `BrauerSuzuki`: assembly

The area's target is `Submission.Blueprint.BrauerSuzukiProp`: a finite group of 2-rank `≤ 1`
satisfies `G = O(G) C_G(t)` for every involution `t`.

Assembly of the proved pieces:

* `Glue/brauerSuzuki_of_weak` — §1.1/§1.2 of `REFS/brauer_suzuki.md`: the Prop follows from the
  weak Brauer–Suzuki form, the classification of 2-groups with a unique involution
  (`Group/isCyclicOrGenQuaternion_of_uniqueInvolution`), and the fact that `G ⧸ O(G)` has a
  generalized quaternion Sylow 2-subgroup if `G` does (`Sylow/genQuaternion_sylow_quotient`).
* `Glue/weak_of_large_and_q8` — the weak form from the two published cases:
  `BrauerSuzukiWeakLarge` (Dade 1971, Theorem 6.8, `|S| ≥ 16`) and `BrauerSuzukiQ8Strong`
  (Glauberman 1974, `S ≅ Q₈`).
* `Dade/main` — Dade's Theorem 6.8, proved here from the character theory of the generalized
  quaternion group, TI-set induction (Dade §5) and the complement `H = QK` of Lemma 6.9.
* `Q8/main` — Glauberman 1974, the `S ≅ Q₈` case, in the strong form `BrauerSuzukiQ8Strong`.
-/

set_option autoImplicit false

namespace Work.BrauerSuzuki

/-- **The area's Prop from Glauberman's `Q₈` case alone** (Dade's case being proved in
`Dade/main`): Brauer–Suzuki for `Q₈` Sylow 2-subgroups implies `BrauerSuzukiProp`. -/
theorem brauerSuzuki_of_q8 (hQ : BrauerSuzukiQ8Strong) :
    Submission.Blueprint.BrauerSuzukiProp :=
  Glue.brauerSuzuki_of_weak (Glue.weak_of_large_and_q8 Dade.main hQ)
    (fun _ _ _ hP hu => Group.isCyclicOrGenQuaternion_of_uniqueInvolution hP hu)
    (fun _ _ _ S hS => Sylow.genQuaternion_sylow_quotient S hS)

/-- **Area `BrauerSuzuki`, unconditional.**  A finite group of `2`-rank at most one satisfies
`G = O(G) C_G(t)` for every involution `t`.

This is the area's target `Submission.Blueprint.BrauerSuzukiProp`, obtained from
`brauerSuzuki_of_q8` and Glauberman's theorem `Q8/main`; Dade's `|S| ≥ 16` case `Dade/main` is
used inside `Glue/weak_of_large_and_q8`. -/
theorem brauerSuzuki : Submission.Blueprint.BrauerSuzukiProp :=
  brauerSuzuki_of_q8 Q8.main

end Work.BrauerSuzuki
