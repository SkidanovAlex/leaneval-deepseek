import Mathlib
import Submission.Work.ThreePoints.P3Sub.Helpers
import Submission.Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.NormalComplement.sec1_lemma3_struct_commute

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- **Peterfalvi I Ch. III §1 Lemma 3** (p.175), in the form used by the `NormalComplement`
area: for `1 ≠ X ≤ V = C_D(t) = C_{H ∩ H^t}(t)` and a nontrivial `k ∈ J(D,t) ∩ N_G(X)`
(`J(D,t) = {x ∈ D | t x t⁻¹ = x⁻¹}`), the involutions of `H ⊓ N_G(X)` commute pairwise.

This is exactly `Work.NormalComplement.sec1_lemma3_struct_commute` (whose hypothesis is stated
with the vocabulary abbreviation `NK H t X = Kset (twoPoint H t) t ∩ N_G(X)`, where
`Kset D t = invertedBy D t`); we only unfold the abbreviation. -/
theorem involutions_commute_of_hC4 (hC4 : Submission.Blueprint.ChIIFourProp)
    (hMod : Submission.Blueprint.ModelFactsProp)
    {G : Type} [Group G] [Finite G] (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXV : X ≤ Submission.Blueprint.centD H t)
    (hNK : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G)) :
    ∀ u ∈ Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G),
      ∀ v ∈ Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G), u * v = v * u := by
  obtain ⟨k, hkK, hk1, hkN⟩ := hNK
  exact sec1_lemma3_struct_commute hC4 hMod hS hH ht htH hX hXV ⟨k, ⟨hkK, hkN⟩, hk1⟩

end Work.NormalComplement
