import Mathlib
import Submission.Work.NormalComplement.case2_prop3b_v2
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.IsSubnormalInPgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- **Peterfalvi I Ch. II §4 Prop. 3 (b)** in the form used downstream, with `X` already inside
`V = centD H t` (so no `D`-conjugation is needed) and with the `k ∈ K` hypothesis attached to
`Y ≤ X` directly.  Since `X` is a `p`-group and `Y ≤ X`, `Y` is automatically subnormal in `X`
(`isSubnormalIn_of_isPGroup`), so the blue-print input `ChIIFourP3SubnormalProp` applies to the
pair `(X, Y)` at once. -/
theorem case2_prop3b_v3 (G : Type) [Group G] [Finite G]
    (hS : Submission.Blueprint.Situation G) (hBP : Work.NormalComplement.BenderPrelimProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hP3 : Submission.Blueprint.ChIIFourP3SubnormalProp)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {p : ℕ} [Fact p.Prime] {X : Subgroup G} (hXV : X ≤ Submission.Blueprint.centD H t)
    (hXp : IsPGroup p X)
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    {Y : Subgroup G} (hYX : Y ≤ X) (hYne : Y ≠ ⊥)
    (hkY : ∃ k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t,
        k ≠ 1 ∧ k ∈ Subgroup.normalizer (Y : Set G)) :
    ∃ S : Subgroup G, IsPGroup 2 S ∧ S ≤ H ⊓ Subgroup.centralizer (X : Set G) ∧
      S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
      Subgroup.normalizer (X : Set G) ⊓ H ≤ Subgroup.normalizer (S : Set G) ∧
      H ⊓ Subgroup.normalizer (X : Set G) =
        S ⊔ (Submission.Blueprint.twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) := by
  classical
  obtain ⟨k, hkK, hkne, hkN⟩ := hkY
  -- `Y ≤ X` with `X` a `p`-group, so `Y` is subnormal in `X`.
  have hsub : Submission.Blueprint.IsSubnormalIn Y X :=
    isSubnormalIn_of_isPGroup hYX hXp
  -- Apply the blue-print input to the pair `(X, Y)` directly.
  obtain ⟨_, S, hS2, hSFH, _, hSN, hSD, hSsup⟩ :=
    hP3 G hS H hH t ht htH X Y hXV hYne hsub ⟨k, hkK, hkne, hkN⟩
  refine ⟨S, hS2, ?_, hSD, ?_, hSsup.symm⟩
  · -- `S ≤ F ⊓ H` with `F = O^{2'}(C_G(X)) ≤ C_G(X)`, so `S ≤ H ⊓ C_G(X)`.
    refine le_inf (le_inf_iff.mp hSFH).2 ?_
    exact (le_inf_iff.mp hSFH).1.trans (by
      calc (Submission.Blueprint.oddResidual
              (Subgroup.centralizer (X : Set G))).map
              (Subgroup.centralizer (X : Set G)).subtype
          ≤ (⊤ : Subgroup ↥(Subgroup.centralizer (X : Set G))).map
              (Subgroup.centralizer (X : Set G)).subtype := Subgroup.map_mono le_top
        _ = Subgroup.centralizer (X : Set G) := by
            rw [Subgroup.map_top, Subgroup.range_subtype])
  · -- `N_G(X) ⊓ H ≤ N_G(S)` (the blue-print input gives `H ⊓ N_G(X) ≤ N_G(S)`).
    rwa [inf_comm]

end Work.NormalComplement
