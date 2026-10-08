import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.LayerCtx6

/-!
# The layer of a proper subgroup with a normal quasisimple subgroup

`Work.CORE4.Case2Six9Aux.layerIn_eq_of_normal_quasisimple`:

If `K < G` (`K ≠ ⊤`, `G` finite), `E ≤ K` is quasisimple **and is normalized by `K`** (so
`E ⊴ K`), and `G` is a D-group in the sense of the §4 setup (`Work.GW2.BenderCtx G`, hence every
subgroup of `G` has dihedral or cyclic Sylow 2-subgroups and `G`'s induction hypothesis
`Work.GW2.SmallerDGroups G` applies to the proper subgroup `K`), then `E` **is** the layer of
`K`: `layerIn K = E = E(K)`.

## Mathematics

This is the uniqueness of the normal quasisimple subgroup (the "component") of a D-group, in the
form used in §4 (6) of Bender 1981 (p. 225): two normal quasisimple subgroups `E`, `E^g` of a
proper subgroup `K` of the D-group `G` must coincide, because each of them equals `E(K)`.

* `K ≠ ⊤` gives `|K| < |G|`, so `K` (which inherits the dihedral/cyclic Sylow 2-subgroup property
  from `G` by `Work.CORE4.DihOrCycSub`) is a D-group by the induction hypothesis `hbc.ih`.
* `E ⊴ K` is exactly `K ≤ N_G(E)` (`Subgroup.normal_subgroupOf_iff_le_normalizer`), and `E`, viewed
  inside `K`, is still quasisimple (transport along `Subgroup.subgroupOfEquivOfLe`).
* `Work.GW2.LayerProp` (`I.toolkit.lay`, Bender 1.6) applied to the D-group `↥K` then says
  `Work.GW2.layer ↥K = E.subgroupOf K`.
* Mapping back along `K.subtype` (which is injective on the subgroup `E ≤ K`) gives
  `layerIn K = E`.

Note that no hypothesis on `E` beyond normality in `K` and quasisimplicity is needed: the
"at most one component" statement is a consequence of `LayerProp`, which is why the hypothesis
`K ≠ ⊤` (the induction hypothesis at `K`) is essential.
-/

set_option linter.style.haveILetI false

namespace Work.CORE4.Case2Six9Aux

/-- **The layer of a proper subgroup is its normal quasisimple subgroup.**  See the module
docstring. -/
theorem layerIn_eq_of_normal_quasisimple {G : Type} [Group G] [Finite G] (I : Work.GW2.C4Inputs)
    (hbc : Work.GW2.BenderCtx G) {K E : Subgroup G} (hK : K ≠ ⊤) (hEK : E ≤ K)
    (hN : K ≤ Subgroup.normalizer (E : Set G)) (hQ : Work.GW2.IsQuasisimple E) :
    Work.GW2.layerIn K = E := by
  -- `K` is proper, hence smaller than `G`
  have hcard : Nat.card ↥K < Nat.card G := card_lt_card_of_ne_top hK
  -- `K` inherits the dihedral/cyclic Sylow 2-subgroups of `G`, so it is a D-group by induction
  have hDsub : Work.GW2.DihOrCycSylow ↥K := DihOrCycSub hbc.sylow K
  have hIsD : Work.GW2.IsDGroup ↥K := hbc.ih ↥K hcard hDsub
  -- `E ⊴ K`, and `E` is still quasisimple inside `K`
  have hEn : (E.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mpr hN
  have hQ' : Work.GW2.IsQuasisimple (E.subgroupOf K) := by
    obtain ⟨h1, h2⟩ := hQ
    haveI := h2
    refine ⟨?_, ?_⟩
    · apply Subgroup.map_injective (f := K.subtype) K.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEK]
      exact h1
    · have hcen : Subgroup.map (Subgroup.subgroupOfEquivOfLe hEK : ↥(E.subgroupOf K) →* ↥E)
          (Subgroup.center ↥(E.subgroupOf K)) = Subgroup.center ↥E :=
        Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hEK)
      exact MulEquiv.isSimpleGroup
        (QuotientGroup.congr (Subgroup.center ↥(E.subgroupOf K)) (Subgroup.center ↥E)
          (Subgroup.subgroupOfEquivOfLe hEK) hcen)
  -- Bender 1.6 (`LayerProp`) for the D-group `↥K`: its layer is its (unique) normal quasisimple
  -- subgroup
  have hlay : Work.GW2.layer ↥K = E.subgroupOf K :=
    (I.toolkit.lay ↥K I.toolkit.ft hDsub hIsD (E.subgroupOf K) hEn hQ').1
  rw [Work.GW2.layerIn, hlay, Subgroup.map_subgroupOf_eq_of_le hEK]

end Work.CORE4.Case2Six9Aux
