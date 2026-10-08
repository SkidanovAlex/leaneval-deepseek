/-
# The area theorem: `PSU3Prop` from the two remaining design nodes

This file closes the area `PSU3` up to exactly two named statements, both of which are nodes of
the lead's design (`Submission/Work/PSU3/NOTES_LEAD_bs_psu3.md`,
`_design/PSU3Route.lean`):

* `Work.PSU3.PSU3CoordsProp` — the Stage A–C output (design node `psu3_coords`):
  under `PSU3Hyp`, `ChIIFourProp` and `HigmanProp`, the split rank-one datum is coordinatised
  by `SZ (E n)` in such a way that `FRel` becomes `fMapTot`;
* `Work.PSU3.PSU3DatumProp` — the model datum of `PSU3Model n` (design node `psu3_datum`):
  a `ModelRankOneDatum` for `↥(PSU3Model n)` with coordinates `(SZ (E n), fMapTot)`
  (its `frel` half is `Work.PSU3.Model.weylConj_matFun`, its split datum
  `Work.PSU3.Model.psu3_isSplitRankOne`, its `c` the embedding `Work.PSU3.pglHom_injective`).

Everything else is delivered: `Work.RankOneUniqueness.rankOneQUniqueness` (unconditional) and
`Work.RankOneUniqueness.recognize` give the isomorphism from a `ModelRankOneDatum` and a
coordination `e : Q ≃* C` turning `FRel` into `fC`; H1–H6, the `f`-map, the matrix model and
Stage A's opening nodes are in `Submission.Work.PSU3.*`.

`Work.PSU3.psu3Prop_of` below is therefore fully proved, with the two Props as its explicit
hypotheses, so the area theorem has exactly that shape and `Assembly.lean` can be wired to
`fun hC4 hHig => psu3Prop_of hC4 hHig hCoords hDatum` as soon as the two Props are proved.
-/
import Submission.Work.PSU3.Defs
import Submission.Work.RankOneUniqueness.Statements
import Submission.Work.RankOneUniqueness.recognize

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.PSU3

/-- **Design node `psu3_coords`** (Stages A–C): under the hypotheses of `PSU3Prop`, the group
`Q` is coordinatised by the case-c Suzuki group `SZ (E n)`, `n ≥ 2`, in such a way that
Peterfalvi's `f`-relation `FRel` becomes the model map `fMapTot`. -/
def PSU3CoordsProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H Q : Subgroup G) (t : G),
    PSU3Hyp H Q t → ChIIFourProp → HigmanProp →
    ∃ n : ℕ, 2 ≤ n ∧ ∃ e : Q ≃* SZ (E n),
      ∀ x y : Q, (x : G) ≠ 1 → FRel H t (x : G) (y : G) → e y = fMapTot (e x)

/-- `↥(PSU3Model n)` is finite (a subgroup of the finite group `PGL(3,GF(2^{2n}))`). -/
instance instFinitePSU3Model (n : ℕ) : Finite ↥(PSU3Model n) := by
  haveI : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) (E n)) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk) Matrix.ProjGenLinGroup.mk_surjective
  exact Finite.of_injective (Subtype.val : ↥(PSU3Model n) → Matrix.ProjGenLinGroup (Fin 3) (E n))
    Subtype.val_injective

/-- **Design node `psu3_datum`** (Stage D): `PSU3Model n` carries a `ModelRankOneDatum` with
coordinates `(SZ (E n), fMapTot)`. -/
def PSU3DatumProp : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    Nonempty (ModelRankOneDatum ↥(PSU3Model n) (SZ (E n)) fMapTot)

/-- **The area theorem**, from the two design nodes, `ChIIFourProp` and `HigmanProp`.
This is `PSU3Prop` of `Submission/Blueprint/Interfaces.lean`. -/
theorem psu3Prop_of (hC4 : ChIIFourProp) (hHig : HigmanProp)
    (hCoords : PSU3CoordsProp) (hDatum : PSU3DatumProp) : PSU3Prop := by
  intro G _ _ hSit hsimple H Q t hsplit hnotZ hB3 htwo
  haveI : IsSimpleGroup G := hsimple
  obtain ⟨n, hn, e, he⟩ :=
    hCoords G H Q t ⟨hSit, hsimple, hsplit, hnotZ, hB3, htwo⟩ hC4 hHig
  obtain ⟨M⟩ := hDatum n hn
  exact ⟨n, hn, recognize rankOneQUniqueness hsplit
    (Y := ↥(PSU3Model n)) (C := SZ (E n)) (fC := fMapTot) M e he⟩

end Work.PSU3
