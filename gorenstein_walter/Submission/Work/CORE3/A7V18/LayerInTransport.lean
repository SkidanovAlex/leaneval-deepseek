import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.ASM.oddCore_odd

namespace Work.CORE3.A7V18

/-!
# CORE3 / A7V18: transporting an `A₇`-shape from `layerIn M` down to `layer ↥M`

`Work.GW2.layerIn M = (Work.GW2.layer ↥M).map M.subtype` is definitionally the image of the
layer of the carrier `↥M` under the (injective) inclusion `↥M → G`.  Hence the two groups
`↥(Work.GW2.layerIn M)` and `↥(Work.GW2.layer ↥M)` are canonically isomorphic, and so are
their central quotients.  The statement below makes that transport explicit in the shape
needed by Bender §3 (the `A₇`-analysis of the maximal subgroup `M`).

The two hypotheses `x ∈ layerIn M`, `x ≠ 1`, `orderOf x = 2` are used to see that the layer is
nonzero and is *not* contained in the odd core: an element of order `2` inside the (odd-order)
odd core is impossible.
-/

theorem LayerInTransport {G : Type} [Group G] [Finite G] (M : Subgroup G) {x : G} (hx : x ∈ Work.GW2.layerIn M) (hx1 : x ≠ 1) (hxo : orderOf x = 2) (hA7 : Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃* alternatingGroup (Fin 7))) : Work.GW2.layer ↥M ≠ ⊥ ∧ ¬ Work.GW2.layer ↥M ≤ Work.GW2.oddCore ↥M ∧ Nonempty ((↥(Work.GW2.layer ↥M) ⧸ Subgroup.center ↥(Work.GW2.layer ↥M)) ≃* alternatingGroup (Fin 7)) := by
  -- `layerIn M` and `oddCoreIn M` are, by definition, the images of the corresponding
  -- subgroups of the carrier `↥M` under the injective inclusion.
  have hLmap : Work.GW2.layerIn M = (Work.GW2.layer ↥M).map M.subtype := rfl
  have hOmap : Work.GW2.oddCoreIn M = (Work.GW2.oddCore ↥M).map M.subtype := rfl
  refine ⟨?_, ?_, ?_⟩
  · -- `layer ↥M ≠ ⊥`: otherwise `layerIn M = ⊥` and `x = 1`.
    intro hbot
    have hb : Work.GW2.layerIn M = ⊥ := by rw [hLmap, hbot, Subgroup.map_bot]
    rw [hb] at hx
    exact hx1 (Subgroup.mem_bot.mp hx)
  · -- `layer ↥M ≰ oddCore ↥M`: otherwise `x` of order `2` would lie in the odd-order
    -- odd core `O(↥M) = oddCoreIn M`.
    intro hle
    have hxoc : x ∈ Work.GW2.oddCoreIn M := by
      have h1 : Work.GW2.layerIn M ≤ Work.GW2.oddCoreIn M := by
        rw [hLmap, hOmap]
        exact Subgroup.map_mono hle
      exact h1 hx
    have hzle : Subgroup.zpowers x ≤ Work.GW2.oddCoreIn M := Subgroup.zpowers_le.mpr hxoc
    have hcard2 : Nat.card ↥(Subgroup.zpowers x) = 2 := by rw [Nat.card_zpowers, hxo]
    have hdvd : Nat.card ↥(Subgroup.zpowers x) ∣ Nat.card ↥(Work.GW2.oddCoreIn M) :=
      Subgroup.card_dvd_of_le hzle
    have hEven : Even (Nat.card ↥(Work.GW2.oddCoreIn M)) :=
      even_iff_two_dvd.mpr (hcard2 ▸ hdvd)
    have hodd : Odd (Nat.card ↥(Work.GW2.oddCoreIn M)) := by
      rw [hOmap]
      rw [Subgroup.card_map_of_injective M.subtype_injective]
      exact Work.ASM.oddCore_odd ↥M
    exact Nat.not_odd_iff_even.mpr hEven hodd
  · -- The `A₇`-shape transports along `↥(layer ↥M) ≃* ↥(layerIn M)`, which carries the
    -- centre onto the centre and hence induces an isomorphism of central quotients.
    obtain ⟨eA7⟩ := hA7
    let L := Work.GW2.layer ↥M
    have eL : ↥L ≃* ↥(Work.GW2.layerIn M) :=
      Subgroup.equivMapOfInjective L M.subtype M.subtype_injective
    have hcen : (Subgroup.center ↥L).map eL.toMonoidHom =
        Subgroup.center ↥(Work.GW2.layerIn M) :=
      Subgroup.map_center_eq eL
    have eQ : (↥L ⧸ Subgroup.center ↥L) ≃*
        (↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) :=
      QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥(Work.GW2.layerIn M)) eL hcen
    exact ⟨eQ.trans eA7⟩

end Work.CORE3.A7V18
