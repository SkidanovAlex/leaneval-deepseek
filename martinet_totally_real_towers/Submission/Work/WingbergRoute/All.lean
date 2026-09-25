import Submission.Work.WingbergRoute.Defs
import Submission.Work.WingbergRoute.Verification
import Submission.Work.WingbergRoute.Main
import Submission.Work.WingbergRoute.TotallyReal
import Submission.Work.WingbergRoute.Certificate
import Submission.Work.WingbergRoute.Traps
import Submission.Work.WingbergRoute.pruefer_twoTorsion_card_gt_quot
import Submission.Work.WingbergRoute.gsM_aut_exp_two
import Submission.Work.WingbergRoute.gsM_aut_gsF_equiv_pi
import Submission.Work.WingbergRoute.gsM_quotient_of_maximal
import Submission.Work.WingbergRoute.gsM_quotient_of_maximal_continuous
import Submission.Work.WingbergRoute.six_le_card_of_surjective_elementaryAbelian
import Submission.Work.WingbergRoute.CupProduct
import Submission.Work.WingbergRoute.cup_leibniz
import Submission.Work.WingbergRoute.cup_isLocallyConstant
import Submission.Work.WingbergRoute.cup_wellDefined
import Submission.Work.WingbergRoute.CupProductCohomology
import Submission.Work.WingbergRoute.cupH1_natural
import Submission.Work.WingbergRoute.cupH1_zmodTwo_swap
import Submission.Work.WingbergRoute.UnitWall

/-!
# `Submission/Work/WingbergRoute/` -- the unramified (Wingberg) route, one import

```lean
import Submission.Work.WingbergRoute.All
```

Namespace `Work.WingbergRoute`.  The area is the **unramified alternative route** to
`Submission.exists_totallyReal_discr_le`: the route through the Shafarevich--Koch
relation-rank bound / Wingberg's duality for the maximal unramified pro-`2` extension of a number
field with no real places, as opposed to the *tame* route over `ℚ` of `Submission/Work/GlobalRami`,
`LocalGlobalReal`, `IdelicCoker` and of the `Submission.lean` wall.

Read `Submission/Work/WingbergRoute/README.md` first.  Summary of the modules:

| module | contents |
|---|---|
| `Defs` | the vocabulary: `genDim`, `relDim`, `ShafarevichBound`, `WingbergUnitInstance`, `WingbergDualityFaithful`, the walls `KcWingbergWall`, `KcH3Wall`, `KcKochInjectionWall`, `gsFWingbergWall`, and the input `gsFArithmeticInput` |
| `Verification` | the machine-checked comparison of the workspace's `Work.ShafarevichKoch.WingbergDuality` with the literature (NSW Ch. VIII §8 Thm. 8.8.1 + Lemma 8.8.4; Hajir--Maire--Ramakrishna arXiv:2103.09508 Thm. 1.1, Cor. `prop:r-d_wingberg`; Shafarevich's relation-rank bound as in Mayer arXiv:1605.09617), and the equivalences between the normalisations of the wall |
| `Main` | the `Kc` endgame: the wall gives `HasProTwoPresentation Kc 5 6` (given the group-theoretic input), `InfiniteProTwoExtension Kc`, `UnramifiedPro2TowerWall`, `BoundedRdTowerWall`, and the **conditional** benchmark (real-part / CM-level / half-real clauses) |
| `TotallyReal` | the totally real instance `gsF = ℚ(√2576450045)`: `d₂(O_gsF^×) = 2`, the numerical bookkeeping, and **`exists_totallyReal_discr_le_of_gsFArithmeticInput`** — the benchmark from the unramified input at the totally real base |
| `Traps` | the machine-checked traps of the route: `not_twoTorsion_card_le_quot_twoMul` (the finiteness hypotheses of `KcH3Wall` cannot be dropped) and the `Kc`-vs-benchmark obstruction |
| `Certificate` | the provenance of the generator-rank clause `6 ≤ #α`: the multiquadratic certificate `gsM/gsF` unramified of degree `2^6`, giving `G_∅ ↠ (ℤ/2)^6` |
| `gsM_aut_exp_two`, `gsM_aut_gsF_equiv_pi`, `gsM_quotient_of_maximal`, `gsM_quotient_of_maximal_continuous`, `six_le_card_of_surjective_elementaryAbelian` | the delegated lemmas of the certificate |
| `CupProduct` | the cochain-level cup product: `IsEquivariantBilin`, `cup11Fun`, `cup21Fun`, `cup12Fun`, `cup01Fun`, `cup10Fun`, `cup31Fun`, `cup22Fun`, `cup13Fun` |
| `cup_leibniz`, `cup_isLocallyConstant`, `cup_wellDefined` | the three facts the cochain-level product satisfies: the Leibniz rule (`d2Fun_cup11`, `d3Fun_cup21`, `d3Fun_cup12`), local constancy of all products, and the descent identities |
| `CupProductCohomology` | ★ the cup products on cohomology, `cupH1 : H¹ × H¹ → H²` and `cupH2 : H² × H¹ → H³`, with their `𝔽₂` specialisations `cupH1_zmodTwo`, `cupH2_zmodTwo` (the norm-residue/Kummer leg of Wingberg duality) |
| `UnitWall` | ★★ the wall in its **sharpest form**: `KcUnitDualityWall` (the *unit half* of Wingberg's duality, the `H²`-half being unconditional), with `kcWingbergWall_of_unitDualityWall` and the whole endgame transported to it |
| `gsFWall` (import it separately: `import Submission.Work.WingbergRoute.gsFWall`) | the `gsF` wall in the classical **deficiency** form `df ≤ d₂(O_gsF^×)`, with the elementary `H²`-half proved for `gsF` (`natCard_H2Z_quot_two_le_card_H1_zmodTwo_gsF`) and the presentation step.  *Caution*: the two delegated modules below import this `All`, so `All` must **not** import them back -- use `gsFWall` (which re-exports both) as the entry point. |

-/
