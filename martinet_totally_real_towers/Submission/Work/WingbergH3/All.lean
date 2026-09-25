import Submission.Work.WingbergH3.Defs
import Submission.Work.WingbergH3.Dual
import Submission.Work.WingbergH3.Deficiency
import Submission.Work.WingbergH3.H3Wall
import Submission.Work.WingbergH3.Constructive
import Submission.Work.WingbergH3.Obstruction
import Submission.Work.WingbergH3.Equivalence
import Submission.Work.WingbergH3.Wiring
import Submission.Work.WingbergH3.genRankTwo_eq_of_card
import Submission.Work.WingbergH3.relRankTwo_eq_of_card
import Submission.Work.WingbergH3.contH2DimLe_iff_kummerCarrierInput
import Submission.Work.WingbergH3.kummerCarrierInput_of_injective_into_vect
import Submission.Work.WingbergH3.kummerInput_Kc_of_kochInjection
import Submission.Work.WingbergH3.nonempty_inertiaModule

/-!
# `Submission/Work/WingbergH3/` -- the `H³`-half of Wingberg's duality, and the constructive route

**Namespace** `Work.WingbergH3`.  One import for the whole area:

```lean
import Submission.Work.WingbergH3.All
```

Read `README.md` first.  In one paragraph: the area receives the two walls of
`Submission/Work/WingbergRoute/` (`KcUnitDualityWall`, `gsFDeficiencyWall`) and does three things.
(1) It puts the `H³`-half of Wingberg's duality in three machine-checkedly equivalent forms
(`H3UnitDualityWall`, `H3DeficiencyWall`, `SharpH3Wall`), identifies them with the walls of
`WingbergRoute`, and proves the precise *obstruction* which shows that the `H³`-half is not a
formal consequence of the (unconditional) `H²`-half (`Obstruction.lean`).  (2) It develops the
*constructive* alternative (Shafarevich's own proof of `d₂(G_∅) ≤ d₁(G_∅) + d₂(O_F^×)`,
Hajir--Maire--Ramakrishna arXiv:2103.09508 §2.2, Koch Ch. 11 Thm. 11.3) in the two normalisations
in which such a proof is carried out -- a pro-`2` inertia module with `m` generators receiving
`H²(G_∅,𝔽₂)` in its `𝔽₂`-dual, and a finite `𝔽₂`-vector space ("Kummer carrier") receiving it
linearly -- and *proves all the group-theoretic content of both* (`Dual.lean`,
`Constructive.lean`).  (3) It proves that the constructive input and the wall have the *same*
conclusion (`Equivalence.lean`), so neither route is a free lunch, and wires every wall of this area
into the consumers of `WingbergRoute` (`Wiring.lean`).

## Files

| file | contents |
|---|---|
| `Defs.lean` | the vocabulary: `DualTwo`, `genRankTwo`, `relRankTwo`, `deficiencyTwo`, the three forms `H3DeficiencyWall`/`H3UnitDualityWall`/`SharpH3Wall` of the `H³`-half, the inertia harness `InertiaModule`/`SalleKochDetects`/`ConstructiveDatum`/`ConstructiveInput`, and the named classical theorems `SaturatedTameSetExists`/`KochSalleDuality` |
| `Dual.lean` | ★ the group-theoretic core: the `𝔽₂`-dual of a pro-`2` group with `m` dense generators has at most `2 ^ m` elements, hence `H²(G,𝔽₂) ↪ X^∨[2]` bounds `d₂(G) ≤ m` (`contH2DimLe_of_salleKochDetection`, `contH2DimLe_of_constructiveDatum`, `shafarevichBound_of_constructiveDatum`) |
| `H3Wall.lean` | ★ the `H³`-half reduced: `H3DeficiencyWall_of_H3UnitDualityWall`, `H3DeficiencyWall_of_sharpH3Wall`, `H3DeficiencyWall_iff_gsFDeficiencyWall`, `H3DeficiencyWall_Kc_iff_kcH3Wall`, `H3UnitDualityWall_Kc_iff_kcUnitDualityWall`, `shafarevichBound_of_H3DeficiencyWall`, `gsFWingbergWall_of_H3DeficiencyWall`, `kcWingbergWall_of_H3DeficiencyWall` |
| `Constructive.lean` | ★ the Kummer form: `KummerCarrier`, `KummerCarrierInput`, `contH2DimLe_of_kummerCarrier`, `KummerDatum`, `KummerInput`, `shafarevichBound_of_kummerInput`, `gsFWingbergWall_of_kummerInput`, `kcWingbergWall_of_kummerInput`, `gsFWingbergWall_of_constructiveInput` |
| `Obstruction.lean` | ★ the precise obstruction: `not_forall_twoTorsion_card_le_quot_card`, `pruefer_obstruction`, `h3_half_not_derivable_from_h2_half` |
| `Equivalence.lean` | ★ `kummerInput_iff_contH2DimLe`: the constructive input is *equivalent* to the relation count |
| `Wiring.lean` | the consumer wiring: `kcProTwoPresentationInput_of_...`, `hasProTwoPresentation_Kc_five_six_of_...`, `boundedRdTowerWall_of_...`, `unramifiedPro2TowerWall_of_...`, `infiniteProTwoExtension_Kc_of_...`, `exists_hasProP2Presentation_gsF_of_...`, and the `_seamFree` variants |
| delegated modules | `genRankTwo_eq_of_card`, `relRankTwo_eq_of_card`, `contH2DimLe_iff_kummerCarrierInput`, `kummerCarrierInput_of_injective_into_vect`, `kummerInput_Kc_of_kochInjection` |
| `README.md` | the report: the mathematics, the classical theorems quoted, the evaluation of the two routes, the exact residual |
-/

set_option autoImplicit false

namespace Work.WingbergH3
end Work.WingbergH3
