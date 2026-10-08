import Submission.Work.ZassenhausSuzuki.CoreV2
import Submission.Work.ZassenhausSuzuki.ModelDatum
import Submission.Work.ZassenhausSuzuki.SymmWitness
import Submission.Work.ZassenhausSuzuki.SzModelCoords
import Submission.Work.ZassenhausSuzuki.CoreV3
import Submission.Work.ZassenhausSuzuki.suzukiDataProp0
import Submission.Work.ZassenhausSuzuki.suzuki_lemma6
import Submission.Work.ZassenhausSuzuki.twoPoint_cyclic_cyclic
import Submission.Work.ZassenhausSuzuki.ModelFinal
import Submission.Work.ZassenhausSuzuki.DataFinal
import Submission.Work.ZassenhausSuzuki.suzukiCoordsProp

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ZassenhausSuzuki`: the Suzuki case of Bender–Suzuki

The main theorem of the area (Suzuki 1962; Peterfalvi II Ch. VII §1; Baumeister–Grüninger §5):
a finite **simple** group with a Zassenhaus split rank-one configuration whose root group `Q`
is a non-abelian 2-group is isomorphic to the literal model `Sz(2^(2n+1))`.

Route.  `SuzukiCoreProp` (the family-specific computation: `Q ≅ A(K,θ)`, `f = τ`) and
`SzModelDatumProp` (the model `SzModel n` in the same coordinates) give two data with the same
coordinates; `recognize_szModel` = S6 of the lead's design, resting on the delivered
`Work.RankOneUniqueness.rankOneQUniqueness` (Peterfalvi II Ch. VII §1, Lemma p. 268, proved
unconditionally in area `RankOneUniqueness`), identifies them.

The recognition step is *unconditional* (area `RankOneUniqueness` is delivered); `hFT`, `hHig`
and `hMod` are kept in the signature because the proofs of `SuzukiCoreProp` and
`SzModelDatumProp` (Suzuki 1962 §4–5, Feit 1960, Higman 1963) consume them through the
Feit–Thompson, Higman and Models interfaces.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.ZassenhausSuzuki

/-- **The Suzuki case.**  A finite simple group with a Zassenhaus split rank-one
configuration with non-abelian 2-group `Q` is `Sz(2^(2n+1))` for some `n ≥ 1`. -/
theorem zassenhausSuzuki (hFT : FeitThompsonProp) (hHig : HigmanProp)
    (hMod : ModelFactsProp)
    (hCore : SuzukiCoreProp) (hDatum : SzModelDatumProp) :
    ZassenhausSzProp := by
  intro G hGrp hFin hsimple H Q t hsplit hzass h2grp hnab
  letI := hGrp
  letI := hFin
  haveI : IsSimpleGroup G := hsimple
  obtain ⟨m, hm, hm3, θ, hθ, ⟨c⟩⟩ := hCore G hsimple H Q t hsplit hzass h2grp hnab
  obtain ⟨M⟩ := hDatum m hm hm3 θ hθ
  refine ⟨(m - 1) / 2, ?_, recognize_szModel hsplit θ M c⟩
  obtain ⟨k, rfl⟩ := hm
  omega

/-- **The Suzuki case, from the corrected decomposition** (`CoreV2.lean`, `CoreV3.lean`): the
structure half `SuzukiDataProp0`, the Tits half `SuzukiTitsProp`, the corrected `f` half
`SuzukiCoordsProp` and the model half `SzModelDatumProp` give the theorem.

(`SuzukiFProp` of `Core.lean` is *false* — see `not_suzukiFProp` in `suzukiFProp.lean` — because
the torus hypothesis on the coordinatisation is invariant under the twist `e ↦ h_μ ∘ e` while
`f = τ` is not; `SuzukiCoordsProp` asks for the existence of the good coordinatisation, which is
what Suzuki's computation and the recognition step actually produce.) -/
theorem zassenhausSuzuki_of_data (hFT : FeitThompsonProp) (hHig : HigmanProp)
    (hMod : ModelFactsProp) (hD0 : SuzukiDataProp0) (hT : SuzukiTitsProp)
    (hC : SuzukiCoordsProp) (hDatum : SzModelDatumProp) : ZassenhausSzProp :=
  zassenhausSuzuki hFT hHig hMod (suzukiCoreProp_of_coords hD0 hT hC) hDatum

/-- **The Suzuki case, with the model half reduced** (`ModelDatum.lean`): D1 (uniqueness of the
Tits endomorphism, *proved* as `titsThetaUniqueProp`) and D2 (the model datum at `titsTheta`) in
place of `SzModelDatumProp`. -/
theorem zassenhausSuzuki_of_all (hFT : FeitThompsonProp) (hHig : HigmanProp)
    (hMod : ModelFactsProp) (hD0 : SuzukiDataProp0)
    (hT : SuzukiTitsProp) (hC : SuzukiCoordsProp) (h1 : TitsThetaUniqueProp)
    (h2 : SzModelDatumTitsProp) : ZassenhausSzProp :=
  zassenhausSuzuki_of_data hFT hHig hMod hD0 hT hC (szModelDatumProp_of h1 h2)

/-- **The Suzuki case with D2 reduced to the matrix computation `SzFrelProp`**
(`SzModelCoords.lean`, recipe in `NOTES_SzFrel.md`). -/
theorem zassenhausSuzuki_of_frel (hFT : FeitThompsonProp) (hHig : HigmanProp)
    (hMod : ModelFactsProp) (hD0 : SuzukiDataProp0)
    (hT : SuzukiTitsProp) (hC : SuzukiCoordsProp) (h1 : TitsThetaUniqueProp)
    (h2 : SzFrelProp) : ZassenhausSzProp :=
  zassenhausSuzuki_of_all hFT hHig hMod hD0 hT hC h1 (szModelDatumTitsProp_of h2)

/-- **The Suzuki case from the four named inputs** (using the *proved* assembly
`suzukiDataProp0`): Suzuki's Lemma 6, the two classification inputs `Q_suzuki_sq` (L3) and
`twoPoint_cyclic` (L2), the Tits half, the corrected `f` half, D1 and `SzFrelProp`. -/
theorem zassenhausSuzuki_of_pieces (hFT : FeitThompsonProp) (hHig : HigmanProp)
    (hMod : ModelFactsProp) (h6 : SuzukiLemma6Prop)
    (hL3 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (H Q : Subgroup G) (t : G),
      Submission.Blueprint.IsSplitRankOne H Q t → Submission.Blueprint.IsZassenhaus H →
      IsPGroup 2 Q → ¬ Submission.Blueprint.IsAbelianSubgroup Q →
      Submission.Blueprint.IsSuzukiTwoGroup ↥Q
        ∧ Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 2)
    (hL2 : ∀ (G : Type) [Group G] [Finite G] {H Q : Subgroup G} {t : G},
      Submission.Blueprint.IsSplitRankOne H Q t → Submission.Blueprint.IsZassenhaus H →
      IsPGroup 2 Q → Submission.Blueprint.HigmanProp →
      Submission.Blueprint.IsSuzukiTwoGroup ↥Q → IsCyclic ↥(Submission.Blueprint.twoPoint H t))
    (hT : SuzukiTitsProp) (hC : SuzukiCoordsProp) (h1 : TitsThetaUniqueProp)
    (h2 : SzFrelProp) : ZassenhausSzProp :=
  zassenhausSuzuki_of_frel hFT hHig hMod (suzukiDataProp0 hHig h6 hL3 hL2) hT hC h1 h2

/-- **The Suzuki case with only three explicit inputs left.**  Everything else of the area is
now *proved*:

* `suzukiDataProp0` (the structure of `Q`), built from Suzuki's Lemma 6 (`suzuki_lemma6`),
  L2-cyclicity (`twoPoint_cyclic_cyclic`) and L3;
* D1, uniqueness of the Tits endomorphism (`titsThetaUniqueProp`);
* the model half `szModelDatumProp` (from D1 and the matrix identity `szFrelProp`).

The remaining inputs are

* `hL3` — `Q` is a Suzuki 2-group with `|Q| = |Z(Q)|²` (Feit 1960 / Higman 1963 / BG 4.6, 5.6;
  written as `Q_suzuki_sq.lean`, currently not buildable because of an import cycle in area
  `Higman`, not because of this area);
* `SuzukiTitsProp` — BG 5.16–5.21 (Tits half);
* `SuzukiCoordsProp` — BG 5.16–5.21 (the corrected `f` half). -/
theorem zassenhausSuzuki_of_L3 (hFT : FeitThompsonProp) (hHig : HigmanProp)
    (hMod : ModelFactsProp)
    (hL3 : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → ∀ (H Q : Subgroup G) (t : G),
      Submission.Blueprint.IsSplitRankOne H Q t → Submission.Blueprint.IsZassenhaus H →
      IsPGroup 2 Q → ¬ Submission.Blueprint.IsAbelianSubgroup Q →
      Submission.Blueprint.IsSuzukiTwoGroup ↥Q
        ∧ Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 2)
    (hT : SuzukiTitsProp) (hC : SuzukiCoordsProp) : ZassenhausSzProp :=
  zassenhausSuzuki hFT hHig hMod
    (suzukiCoreProp_of_coords (suzukiDataProp0_of_L3 hHig hL3) hT hC)
    szModelDatumProp

/-- **The Suzuki case with only two explicit inputs left** (the Tits half and the corrected `f`
half of BG 5.16–5.21).  Used here: `SuzukiDataProp0` modulo `HigmanProp` (`suzukiDataProp0_uncond`,
i.e. L3 `Q_suzuki_sq` + Suzuki's Lemma 6 `suzuki_lemma6` + L2 `twoPoint_cyclic_cyclic`) and the
model half `szModelDatumProp` (D1 + `szFrelProp`). -/
theorem zassenhausSuzuki_of_tits_coords (hFT : FeitThompsonProp) (hHig : HigmanProp)
    (hMod : ModelFactsProp) (hT : SuzukiTitsProp) (hC : SuzukiCoordsProp) :
    ZassenhausSzProp :=
  zassenhausSuzuki hFT hHig hMod
    (suzukiCoreProp_of_coords (suzukiDataProp0_uncond hHig) hT hC)
    szModelDatumProp

/-- **The Suzuki case with a single explicit input left**: the Tits half `SuzukiTitsProp`
(BG 5.16–5.21).  Everything else of the area is proved and axiom-clean:
`SuzukiDataProp0` modulo `HigmanProp` (`suzukiDataProp0_uncond`), the corrected `f` half
(`suzukiCoordsProp`, `CoreV3`) and the model half (`szModelDatumProp`). -/
theorem zassenhausSuzuki_of_tits (hFT : FeitThompsonProp) (hHig : HigmanProp)
    (hMod : ModelFactsProp) (hT : SuzukiTitsProp) : ZassenhausSzProp :=
  zassenhausSuzuki hFT hHig hMod
    (suzukiCoreProp_of_coords (suzukiDataProp0_uncond hHig) hT suzukiCoordsProp)
    szModelDatumProp

end Work.ZassenhausSuzuki
