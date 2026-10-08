import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.isQuasisimple_four_dvd

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false

/-- For a subgroup `K` of `G`, mapping a subgroup `H ≤ ↥K` forward along `K.subtype` and then
restricting back to `K` recovers `H`.  (The map `Subgroup.map K.subtype` is an order isomorphism
onto the subgroups of `G` contained in `K`.) -/
theorem subgroupOf_map_subtype_eq {G : Type*} [Group G] (K : Subgroup G) (H : Subgroup ↥K) :
    (H.map K.subtype).subgroupOf K = H := by
  rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

-- Glue in area CORE2B (Bender 1981, Lemma 2.7 step 2): the leaf `L27_layer_eq_bot` follows from the
-- leaf `L27_normal_contains_t` together with `Work.CORE2B.isQuasisimple_four_dvd`.
-- Route: `layerIn M` is normal in `M` (it is the image of `layer M = sSup {E | E.Normal ∧ IsQuasisimple E}`,
-- which is normal by `Subgroup.sSup_normal`); if `layerIn M ≠ ⊥` there is a normal quasisimple
-- `E ≤ layer M` with `E ≠ ⊥`, hence `4 ∣ |E| ∣ |layerIn M|`, so `L27_normal_contains_t` applied to
-- `N := E.map M.subtype` gives `t ∈ layerIn M`, contradicting `L27Hyp.t_not_layer`.
theorem layer_eq_bot_of_normal_contains_t :
    Work.CORE2B.L27_normal_contains_t → Work.CORE2B.L27_layer_eq_bot := by
  intro h T h23 h26 G _ _ hFT hCtx B M hM
  by_contra hne
  -- `layer M ≠ ⊥`: the map along the injective `M.subtype` does not kill it.
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := fun hc =>
    hne (by rw [Work.GW2.layerIn, hc, Subgroup.map_bot])
  -- so some normal quasisimple `E ≤ ↥M` is nontrivial
  obtain ⟨E, hE⟩ : ∃ E ∈ {E : Subgroup ↥M | E.Normal ∧ Work.GW2.IsQuasisimple E},
      E ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hlayer_ne (le_bot_iff.mp (sSup_le_iff.mpr
      (fun H hH => by rw [hcon H hH])))
  obtain ⟨hEnorm, hEquasi⟩ := hE.1
  -- `4 ∣ |E|`, and `E.map M.subtype` is a normal subgroup of `M` of the same order
  have h4E : 4 ∣ Nat.card ↥E := isQuasisimple_four_dvd E hEquasi hE.2
  have hNM : E.map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hNnorm : ((E.map M.subtype).subgroupOf M).Normal := by
    rw [subgroupOf_map_subtype_eq M E]
    exact hEnorm
  have h4N : 4 ∣ Nat.card ↥(E.map M.subtype) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact h4E
  have htN : B.t ∈ E.map M.subtype :=
    h T h23 h26 G hFT hCtx B M hM _ hNM hNnorm h4N
  -- and it lies in `layerIn M`, contradicting `t ∉ E(M)`
  exact hM.t_not_layer (Subgroup.map_mono (le_sSup hE.1) htN)

end Work.CORE2B
