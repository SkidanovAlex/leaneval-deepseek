import Submission.Work.Totaro.Defs
import Submission.Work.Totaro.Cohomology
import Submission.Work.Totaro.Paper
import Submission.Work.Totaro.Interface
import Submission.Work.Totaro.Cylinder
import Submission.Work.Totaro.isPseudoIso_of_isoOver
import Submission.Work.Totaro.StablyBirational_of_isoOver
import Submission.Work.Totaro.stablyBirational_congr
import Submission.Work.Totaro.StablyBirationalLaws
import Submission.Work.Totaro.CY3Data_not_resEquiv_z0
import Submission.Work.Totaro.partialIso_prod_affine
import Submission.Work.Totaro.stablyBirational_of_birationalMap
import Submission.Work.Totaro.stablyBirational_trans
import Submission.Work.Totaro.prodOver_affineSpace_canonical_variety
import Submission.Work.Totaro.stablyBirational_instance_independent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.Totaro` — the TOTARO area: the input both delivered L-link chapters consume

Single entry point: **`import Submission.Work.Totaro.Main`**.

Lin–Shinder, *Motivic invariants of birational maps*, Annals **199** (1), 2024, appendix
§ *Stably birational geometry of K-trivial varieties* (tex 2826–3125): Totaro's theorem
`thm:BurtCY` and its corollary `cor-CYnSB`.  This is the input which the CY3 chapter
(`Submission/Work/CY3`, the `n ≥ 5` case of Theorem 1.2 (3) of the challenge) and the K3 chapter
(`Submission/Work/K3`, the `n ≥ 4` case of Theorem 1.2 (2)) consume as `TotaroInput` in order to
know that the two centres of their L-link are not stably birational, i.e. that the exceptional
divisors have non-isomorphic function fields.

## The deliverable: `TotaroInput` *proved* from a finer, cohomological, named input

`Work.CY3.TotaroInput` and `Work.K3.TotaroInput` are

```lean
structure TotaroInput (𝕜 : Type) [Field 𝕜] : Prop where
  not_stablyBirat_of_not_iso : ∀ (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y],
    IsKTrivial 𝕜 X → IsKTrivial 𝕜 Y → PicardRankOne 𝕜 X → PicardRankOne 𝕜 Y →
    ¬ IsoOver 𝕜 X Y → ¬ StablyBirational 𝕜 X Y
```

This area proves both of them from named *cohomological* inputs, splitting Totaro's theorem into
the cohomology machinery (named, because Mathlib has no `l`-adic cohomology, no Betti cohomology, no
Künneth formula and no Tate twist) and the abstract implication layer (proved):

```lean
Work.Totaro.totaroInput_CY3 (h : CohDistinguishing 𝕜 (Work.CY3.PicardRankOne 𝕜)) :
    Work.CY3.TotaroInput 𝕜
Work.Totaro.totaroInput_K3  (h : CohDistinguishing 𝕜 (Work.K3.PicardRankOneGeom 𝕜)) :
    Work.K3.TotaroInput 𝕜
```

plus the weaker (per-pair, i.e. mathematically sharpest) named input
`Work.Totaro.CohSeparationDistinguishing` and the paper's own route through `Work.Totaro.CorCYnSB`:

```lean
Work.Totaro.totaroInput_CY3_of_separation, Work.Totaro.totaroInput_K3_of_separation
Work.Totaro.totaroInput_CY3_of_CorCYnSB,   Work.Totaro.totaroInput_K3_of_CorCYnSB
```

## What is *proved* here (sorry-free, no extra axioms — see `Submission/Work/Totaro/Axioms.lean`)

* **The abstract implication layer** (`Submission/Work/Totaro/Cohomology.lean`): from a birational
  invariant of the cohomology of a pair which is multiplicative (Künneth) and normalised so that
  affine space has the invariant of a point (Tate twist), the pair is not stably birational with
  *any* exponents:
  `Work.Totaro.affine_eq_of_kunneth` (the **product decomposition argument**),
  `Work.Totaro.CohKunneth.toCohSeparation`,
  `Work.Totaro.CohSeparation.not_stablyBirational`,
  `Work.Totaro.CohSeparation.not_nonempty_birationalMap`;
  and the invariance of the certificate: `Work.Totaro.CohSeparation.symm`,
  `Work.Totaro.CohSeparation.congr` (birational invariance of the pair),
  `Work.Totaro.CohSeparation.prod_affine` (the certificate is a *stable* birational invariant of the
  pair — the form in which the `cInv` count, read at a base point with residue field `κ(Z)(t)` of a
  cylinder, consumes it).
* **The paper's route** (`Submission/Work/Totaro/Paper.lean`): the paper's appendix recorded as the
  named inputs `Work.Totaro.ThmBurtCY`, `Work.Totaro.LemStbirCY`, `Work.Totaro.CorCYnSB`, and
  `Work.Totaro.corCYnSB_of_paper`, which derives **both** forms of `cor-CYnSB` from them (the
  `Pic`/`NS`/`Proj` clause of `thm:BurtCY` itself is derived in
  `Work.Totaro.ThmBurtCY.isoOver_of_birational_of_nef`), together with the cylinder
  (`Work.Totaro.CorCYnSB.not_birational_cylinder`), same-exponent
  (`Work.Totaro.CorCYnSB.not_birational_affine_same`) and `TotaroInput`-shaped
  (`Work.Totaro.CorCYnSB.not_stablyBirat_of_not_iso`) consequences.
* **The equivalence-relation laws of stable birationality**
  (`Submission/Work/Totaro/StablyBirationalLaws.lean`, `…/stablyBirational_trans.lean`,
  `…/stablyBirational_of_birationalMap.lean`, `…/stablyBirational_instance_independent.lean`,
  `…/partialIso_prod_affine.lean`): `Work.Totaro.StablyBirational` is reflexive, symmetric and
  transitive, contains birationality, is invariant under `IsoOver` in both variables
  (`Work.Totaro.stablyBirational_congr`) and does not depend on the chosen `𝕜`-structure of the two
  schemes (`Work.Totaro.stablyBirational_instance_independent`); multiplication by affine space
  preserves birationality (`Work.Totaro.partialIso_prod_affine`, the product missing from Mathlib's
  `PartialIso` API).
* **The consumers' distinguishings** (`Submission/Work/Totaro/Interface.lean`,
  `Submission/Work/Totaro/Cylinder.lean`): the residue-field/`z₀` statements which the `cInv` counts
  of the two chapters need — `Work.Totaro.not_resEquiv_of_cohom`,
  `Work.Totaro.CY3Data_not_resEquiv_yx`, `Work.Totaro.K3Data_not_resEquiv_yx`,
  `Work.Totaro.CY3Data_exists_cInv_ne_zero`, `Work.Totaro.K3Data_exists_cInv_ne_zero`,
  `Work.Totaro.not_sameCylinderField_of_distinguishing`,
  `Work.Totaro.not_sameCylinderField_of_CorCYnSB`,
  `Work.Totaro.not_stablyBirat_of_cohom` — and the two challenge statements of the chapters
  with `TotaroInput` replaced by the cohomological input:
  `Work.Totaro.not_gen_of_CY3_infiniteField_five`, `Work.Totaro.not_gen_of_CY3_infiniteField_of_le`,
  `Work.Totaro.not_gen_of_K3_kSubC`, `Work.Totaro.not_gen_of_K3_kSubC_of_le`.

## The per-link (concrete pair) inputs

Mathematically the cohomology theory gives the certificate for the two *concrete* centres
(`H³(Z_𝕜)(1)` for the CY3 centres, `H²` of the K3 surfaces for the K3 centres), not a universal
statement.  Those are `Work.Totaro.CY3CentreCohomology 𝕜 D` and
`Work.Totaro.K3CentreCohomology 𝕜 D` (for `D : Work.CY3.CY3Data 𝕜` resp. `Work.K3.K3Data 𝕜`),
with the interface

```lean
Work.Totaro.CY3Data_not_resEquiv_yx_of_centre     : CY3CentreCohomology 𝕜 D → ¬ ResEquiv 𝕜 D.y D.x
Work.Totaro.K3Data_not_resEquiv_yx_of_centre      : K3CentreCohomology 𝕜 D → ¬ ResEquiv 𝕜 D.y D.x
Work.Totaro.CY3Data_exists_cInv_ne_zero_of_centre : CY3CentreCohomology 𝕜 D → ∃ … Cr 𝕜 5
Work.Totaro.K3Data_exists_cInv_ne_zero_of_centre  : K3CentreCohomology 𝕜 D → ∃ … Cr 𝕜 4
```

In these per-link forms the non-isomorphism of the two centres is *not* a separate hypothesis: the
certificate already forbids the centres from being stably birational, hence from being isomorphic
(`Work.Totaro.StablyBirational_of_isoOver`).  The chapter statements with only that input are

```lean
Work.Totaro.not_gen_of_CY3_infiniteField_five_of_centre
    : [Infinite 𝕜] → Work.CY3.CY3Input 𝕜 → CY3CentreCohomology 𝕜 I.data → ¬ GenByPseudoRegularizable 𝕜 5
Work.Totaro.not_gen_of_K3_kSubC_of_centre
    : (𝕜 : Subfield ℂ) → TerasomaInput → HassettLaiTheorem T →
      K3CentreCohomology ↥𝕜 (toHLDescent h 𝕜).data → ¬ GenByPseudoRegularizable ↥𝕜 4
```

## What is *named* (not proved anywhere in Mathlib)

`Work.Totaro.CohKunneth` / `Work.Totaro.CohSeparation` (the cohomological distinction),
`Work.Totaro.CohDistinguishing` and `Work.Totaro.CohSeparationDistinguishing` (their universal
packagings), `Work.Totaro.ThmBurtCY`, `Work.Totaro.LemStbirCY`, `Work.Totaro.CorCYnSB` (the paper's
statement), and the geometric predicates `Work.Totaro.IsNefCanonical`,
`Work.Totaro.IsSeparablyRationallyConnected`, `Work.Totaro.IsNotSeparablyUniruled`.  See
`Submission/Work/Totaro/NOTES.md` for the exact Mathlib gap list and the roadmap for instantiating
the cohomological input.

## Conventions

* one notion per concept, two names: `Work.Totaro.IsoOver`, `Work.Totaro.StablyBirational`,
  `Work.Totaro.IsKTrivial`, `Work.Totaro.prodOver`, `Work.Totaro.AffineN` are the K3 chapter's
  notions (`Work.K3.*`), and the CY3 chapter's are abbreviations of the same;
* `𝔸¹` models `ℙ¹` (only the birational class matters);
* the family `Work.Totaro.Pic1Family 𝕜` is `(X : Scheme.{0}) → [Variety 𝕜 X] → Prop`, and the two
  chapters' Picard-rank-one predicates are `Work.CY3.PicardRankOne 𝕜` resp.
  `Work.K3.PicardRankOneGeom 𝕜`; every statement of this area is uniform in that family.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.Totaro
end Work.Totaro
