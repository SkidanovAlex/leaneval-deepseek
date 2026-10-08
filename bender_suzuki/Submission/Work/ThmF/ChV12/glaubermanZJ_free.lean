import Mathlib
import Submission.Work.GlaubermanZJ.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman's `ZJ`-theorem, free of Feit–Thompson

`Work.GlaubermanZJ.GlaubermanZJ` proves `Submission.Blueprint.GlaubermanZJProp` from
`Submission.Blueprint.FeitThompsonProp`, but the Feit–Thompson hypothesis is *vestigial* there:
it is never used, and neither is it used by any lemma of the area
(`GlaubermanZJ_reduced`, `ZJ_le_pCore`, `theorem4_3`, `isPStable_of_isPSolvable_of_abelianSylowTwo`,
…).  The only structural input to the argument is that `G` — whence `G/O_{p'}(G)` — is
**solvable**, which gives `p`-solvability.

This file records that observation as a theorem: the area's statement holds unconditionally.

The proof is the standard two-step reduction, reproduced here without the Feit–Thompson
parameter:

* `G` has characteristic `p'`-core `M = O_{p'}(G)` (`pPrimeCore_characteristic`), and a Sylow
  `p`-subgroup `P` meets `M` trivially (`sylow_inf_pPrimeCore_eq_bot`), so `P` maps onto a Sylow
  `p`-subgroup `P̄` of `G/M` and `Z(J(P̄))` pulls back to `M·Z(J(P))`
  (`ZJ_comap_mk_eq_sup`);
* in `G/M` the `p'`-core is trivial (`pPrimeCore_quotient_eq_bot`), the Sylow 2-subgroups are
  still abelian (`hasAbelianSylowTwo_quotient`, being images of those of `G`), and `G/M` is
  solvable; so the reduced theorem `GlaubermanZJ_reduced` gives that `Z(J(P̄))` is
  characteristic in `G/M`;
* pulling a characteristic subgroup back along the quotient by a characteristic normal subgroup
  gives a characteristic subgroup (`characteristic_comap_mk`), i.e. `M·Z(J(P))` is
  characteristic in `G`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV12

variable {G : Type*} [Group G] [Finite G]

/-- The **quotient step**: for `G` finite solvable with abelian Sylow 2-subgroups, `p` an odd
prime and `P` a Sylow `p`-subgroup of `G`, the subgroup `Z(J(P M/M))` is characteristic in the
quotient `G/M`, where `M = O_{p'}(G)`.

This is the point at which the solvability hypothesis is consumed (via `p`-solvability of the
quotient): the `p'`-core of `G/M` is trivial, the Sylow 2-subgroups of `G/M` are abelian (images
of those of `G`), and `GlaubermanZJ_reduced` at `O_{p'} = 1` yields the claim.  No
Feit–Thompson hypothesis is needed, as the quotient of a solvable group is solvable. -/
theorem characteristic_ZJ_map_mk_quotient {p : ℕ} (hp : p.Prime) (hpne : p ≠ 2)
    (hsol : Group.IsSolvable G)
    (hab : ∀ S : Sylow 2 G, Submission.Blueprint.IsAbelianSubgroup (S : Subgroup G))
    (P : Sylow p G) [(Submission.Blueprint.pPrimeCore p G).Normal] :
    (Submission.Blueprint.ZJ ((P : Subgroup G).map
      (QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G)))).Characteristic := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- `P` meets `O_{p'}(G)` trivially, so it maps onto a Sylow `p`-subgroup of the quotient
  let q : G →* G ⧸ (Submission.Blueprint.pPrimeCore p G) :=
    QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G)
  have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective _
  haveI : Finite (G ⧸ (Submission.Blueprint.pPrimeCore p G)) := Finite.of_surjective q hsurj
  let Pbar : Sylow p (G ⧸ (Submission.Blueprint.pPrimeCore p G)) := Sylow.mapSurjective hsurj P
  have hPbar : (Pbar : Subgroup (G ⧸ (Submission.Blueprint.pPrimeCore p G))) =
      (P : Subgroup G).map q := Sylow.coe_mapSurjective hsurj P
  -- the hypotheses of the reduced theorem for the quotient
  haveI : Group.IsSolvable G := hsol
  have hsolQ : Group.IsSolvable (G ⧸ (Submission.Blueprint.pPrimeCore p G)) := inferInstance
  have h2Q : 5 ≤ p ∨ Work.GlaubermanZJ.HasAbelianSylowTwo
      (G ⧸ (Submission.Blueprint.pPrimeCore p G)) :=
    Or.inr (Work.GlaubermanZJ.hasAbelianSylowTwo_quotient (G := G) hab
      (Submission.Blueprint.pPrimeCore p G))
  have hcoreQ : Work.Fitting.pPrimeCore p (G ⧸ (Submission.Blueprint.pPrimeCore p G)) = ⊥ :=
    Work.GlaubermanZJ.pPrimeCore_quotient_eq_bot (G := G) hp
  have hred : (Submission.Blueprint.ZJ
      (Pbar : Subgroup (G ⧸ (Submission.Blueprint.pPrimeCore p G)))).Characteristic :=
    Work.GlaubermanZJ.GlaubermanZJ_reduced hp hpne hsolQ h2Q hcoreQ Pbar
  rwa [hPbar] at hred

/-- The **pull-back step**: if `M = O_{p'}(G)` is characteristic in `G`, `P` is a subgroup of `G`
with `P ⊓ M = 1`, and `Z(J(P M/M))` is characteristic in `G/M`, then `M·Z(J(P))` is
characteristic in `G`.

Indeed `Z(J(P M/M))` pulls back to `M ⊔ Z(J(P))` (`Work.GlaubermanZJ.ZJ_comap_mk_eq_sup`), and a
characteristic subgroup of the quotient pulls back to a characteristic subgroup of `G` when the
kernel is characteristic (`Work.GlaubermanZJ.characteristic_comap_mk`). -/
theorem characteristic_sup_ZJ_of_characteristic_quotient {p : ℕ} (P : Subgroup G)
    [(Submission.Blueprint.pPrimeCore p G).Normal]
    (hdisj : P ⊓ Submission.Blueprint.pPrimeCore p G = ⊥)
    (hM : (Submission.Blueprint.pPrimeCore p G).Characteristic)
    (h : (Submission.Blueprint.ZJ
      (P.map (QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G)))).Characteristic) :
    (Submission.Blueprint.pPrimeCore p G ⊔ Submission.Blueprint.ZJ P).Characteristic := by
  have hpull : ((Submission.Blueprint.ZJ
      (P.map (QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G)))).comap
      (QuotientGroup.mk' (Submission.Blueprint.pPrimeCore p G))).Characteristic :=
    Work.GlaubermanZJ.characteristic_comap_mk (Submission.Blueprint.pPrimeCore p G) hM h
  rwa [Work.GlaubermanZJ.ZJ_comap_mk_eq_sup p P hdisj] at hpull

/-- **Glauberman's `ZJ`-theorem without Feit–Thompson** (Canad. J. Math. **20** (1968),
Theorem A, in the form used by Peterfalvi, Astérisque 142–143, p. 145): for `G` finite
**solvable** with abelian Sylow 2-subgroups, `p` an odd prime and `P` a Sylow `p`-subgroup,
`O_{p'}(G)·Z(J(P))` is characteristic in `G`.

The Feit–Thompson hypothesis carried by `Work.GlaubermanZJ.GlaubermanZJ` is not needed: the
argument only uses that `G`, hence `G/O_{p'}(G)`, is solvable. -/
theorem glaubermanZJ_free : Submission.Blueprint.GlaubermanZJProp := by
  intro G _ _ p hp hpne hsol hab P
  haveI hM : (Submission.Blueprint.pPrimeCore p G).Characteristic :=
    Work.GlaubermanZJ.pPrimeCore_characteristic (G := G) hp
  haveI hMn : (Submission.Blueprint.pPrimeCore p G).Normal :=
    Subgroup.normal_of_characteristic (Submission.Blueprint.pPrimeCore p G)
  exact characteristic_sup_ZJ_of_characteristic_quotient (G := G) (p := p) (P : Subgroup G)
    (Work.GlaubermanZJ.sylow_inf_pPrimeCore_eq_bot (G := G) hp P)
    (Work.GlaubermanZJ.pPrimeCore_characteristic (G := G) hp)
    (characteristic_ZJ_map_mk_quotient (G := G) hp hpne hsol hab P)

end Work.ThmF.ChV12
