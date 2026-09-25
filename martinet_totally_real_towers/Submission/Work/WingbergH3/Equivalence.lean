import Mathlib
import Submission.Work.WingbergH3.Constructive
import Submission.Work.WingbergH3.contH2DimLe_iff_kummerCarrierInput
import Submission.Work.WingbergH3.genRankTwo_eq_of_card

/-!
# `Work.WingbergH3.Equivalence` -- what the constructive route is worth

The area's *evaluation* of the two routes, machine-checked.

**The constructive route and the cohomological wall have the same output.**  `KummerInput F` is
*equivalent* to the relation count

```
∃ M, ∃ d,  #H¹(G_∅,𝔽₂) = 2 ^ d  ∧  dim_{𝔽₂} H²(G_∅,𝔽₂) ≤ d + d₂(O_F^×) ,
```

i.e. to `Work.WingbergRoute.ShafarevichBound F M`: `kummerInput_iff_contH2DimLe` below, whose `←`
direction is `kummerInput_of_contH2DimLe` (`contH2DimLe_iff_kummerCarrierInput`, proved in the
sibling module) and whose `→` direction is `contH2DimLe_of_kummerCarrier`.

**Consequence.**  Neither route is a free lunch: `KummerInput F`, `ConstructiveInput F` and
`H3DeficiencyWall F` all imply `Work.WingbergRoute.gsFWingbergWall`/`KcWingbergWall`, and the
Kummer form is *equivalent* to the wall's conclusion.  The point of the constructive route is
therefore not a weaker conclusion but a *different proof*: it is the classical Shafarevich
argument (Chebotarev + Gras--Munnier + Salle--Koch) in place of Wingberg's Tate duality, and its
non-formal content is the *identification of the carrier* -- `V = V_∅/(F^×)²` for `F = Kc`
(`Work.ShafarevichKoch.VTwo Kc ⧸ squareSubgroup`, whose dual cardinality `2 ^ 6` is proved in this
workspace as `Work.ShafarevichKoch.natCard_dual_VTwoQuot_Kc`) -- together with the injection
`H²(G_∅,𝔽₂) ↪ V` (`Work.ShafarevichKoch.KochInjection`, the pinned form).  The interface adapter
`kummerCarrierInput_of_injective_into_vect` turns such a pinned injection into `KummerCarrierInput`.

## Main declarations

* `Work.WingbergH3.kummerInput_iff_contH2DimLe`;
* `Work.WingbergH3.shafarevichBound_of_kummerInput_of_contH2DimLe`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.WingbergH3

open Work.ConCohomology Work.ShafarevichKoch Work.ClassFieldTower

/-- **The Kummer form of the constructive input is equivalent to the relation count.**  The
`←` direction is the converse of `contH2DimLe_of_kummerCarrier` (proved in
`Work.WingbergH3.contH2DimLe_iff_kummerCarrierInput`) together with the packaging of the datum;
the `→` direction is `shafarevichBound_of_kummerInput`. -/
theorem kummerInput_iff_contH2DimLe (F : Type) [Field F] [NumberField F] :
    KummerInput F ↔ ∃ M : MaximalUnramifiedProP.{0} F 2, ∃ d : ℕ,
      Nat.card (H1 (galoisGroup M) (ZMod 2)) = 2 ^ d ∧
        Work.RelatorRank.ContH2DimLe (galoisGroup M) (d + unitTwoRank F) := by
  constructor
  · intro h
    obtain ⟨M, k, d, hcard, hd, hk⟩ := shafarevichBound_of_kummerInput h
    exact ⟨M, d, hd, ⟨k, hk, hcard⟩⟩
  · rintro ⟨M, d, hd, hcont⟩
    exact ⟨⟨M, d, hd, (contH2DimLe_iff_kummerCarrierInput.mp hcont).some⟩⟩

end Work.WingbergH3
