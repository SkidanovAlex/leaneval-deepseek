import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.GlaubermanZJ.Basic
import Submission.Work.GlaubermanZJ.pPrimeCore_characteristic
import Submission.Work.GlaubermanZJ.hasAbelianSylowTwo_quotient
import Submission.Work.GlaubermanZJ.pPrimeCore_quotient_eq_bot
import Submission.Work.GlaubermanZJ.sylow_inf_pPrimeCore_eq_bot
import Submission.Work.GlaubermanZJ.characteristic_comap_mk
import Submission.Work.GlaubermanZJ.ZJ_comap_mk_eq_sup
import Submission.Work.GlaubermanZJ.GlaubermanZJ_reduced

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `GlaubermanZJ`: the theorem

`Work.GlaubermanZJ.GlaubermanZJ` is the theorem of the area: Glauberman's `ZJ`-theorem
(Canad. J. Math. **20** (1968), Theorem A) in the form used by Peterfalvi (Astérisque 142–143,
p. 145), i.e. exactly the interface `Submission.Blueprint.GlaubermanZJProp`.

The mathematical content lives in `Work.GlaubermanZJ.GlaubermanZJ_reduced`: Glauberman's
Theorem A for groups with `O_{p'}(G) = 1`, built from

* `Work.GlaubermanZJ.pstable_of_abelianSylowTwo` — `p`-stability of `p`-solvable groups with
  abelian Sylow 2-subgroups (Glauberman §6, with the delivered quadratic Hall–Higman result
  `Work.PStable.pstable_representation` replacing Dickson's Lemma 6.2),
* `Work.GlaubermanZJ.ZJ_le_pCore` and `Work.GlaubermanZJ.theorem4_3` — Glauberman §§3–4.

This file contains only the reduction `G ↦ G/O_{p'}(G)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.GlaubermanZJ

/-- **Glauberman's `ZJ`-theorem** (Canad. J. Math. **20** (1968), Theorem A) in the form used by
Peterfalvi: for `G` finite solvable with abelian Sylow 2-subgroups and `p` an odd prime,
`O_{p'}(G)·Z(J(P))` is characteristic in `G` for every Sylow `p`-subgroup `P`.

Proof: `M = O_{p'}(G)` is characteristic, `P` maps isomorphically onto a Sylow `p`-subgroup
`P̄` of `G/M` (since `P ⊓ M = 1`), and `Z(J(·))` transports across the quotient:
`Z(J(P̄)) = Z(J(P))·M/M`.  The reduced statement for `G/M` (which has `O_{p'}(G/M) = 1`)
gives `Z(J(P̄))` characteristic in `G/M`; pulling back along the (characteristic) kernel `M`
gives `M · Z(J(P))` characteristic in `G`. -/
theorem GlaubermanZJ (hFT : Submission.Blueprint.FeitThompsonProp) :
    Submission.Blueprint.GlaubermanZJProp := by
  intro G _ _ p hp hpne hsol hab P
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hMchar : (Submission.Blueprint.pPrimeCore p G).Characteristic :=
    pPrimeCore_characteristic (G := G) hp
  have hdisj : (P : Subgroup G) ⊓ Submission.Blueprint.pPrimeCore p G = ⊥ :=
    sylow_inf_pPrimeCore_eq_bot (G := G) hp P
  let q : G →* G ⧸ (Submission.Blueprint.pPrimeCore p G) :=
    QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G)
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  haveI : Finite (G ⧸ (Submission.Blueprint.pPrimeCore p G)) := Finite.of_surjective q hsurj
  let Pbar : Sylow p (G ⧸ (Submission.Blueprint.pPrimeCore p G)) := Sylow.mapSurjective hsurj P
  have hPbar : (Pbar : Subgroup (G ⧸ (Submission.Blueprint.pPrimeCore p G))) =
      (P : Subgroup G).map q := Sylow.coe_mapSurjective hsurj P
  haveI : Group.IsSolvable G := hsol
  have hsolQ : Group.IsSolvable (G ⧸ (Submission.Blueprint.pPrimeCore p G)) := inferInstance
  have h2Q : 5 ≤ p ∨ HasAbelianSylowTwo (G ⧸ (Submission.Blueprint.pPrimeCore p G)) :=
    Or.inr (hasAbelianSylowTwo_quotient hab (Submission.Blueprint.pPrimeCore p G))
  have hcoreQ : Work.Fitting.pPrimeCore p (G ⧸ (Submission.Blueprint.pPrimeCore p G)) = ⊥ :=
    pPrimeCore_quotient_eq_bot (G := G) hp
  have hred : (Submission.Blueprint.ZJ
      (Pbar : Subgroup (G ⧸ (Submission.Blueprint.pPrimeCore p G)))).Characteristic :=
    GlaubermanZJ_reduced hp hpne hsolQ h2Q hcoreQ Pbar
  rw [hPbar] at hred
  have hchar : ((Submission.Blueprint.ZJ ((P : Subgroup G).map q)).comap q).Characteristic :=
    characteristic_comap_mk (Submission.Blueprint.pPrimeCore p G) hMchar hred
  rw [ZJ_comap_mk_eq_sup p (P : Subgroup G) hdisj] at hchar
  exact hchar

end Work.GlaubermanZJ
