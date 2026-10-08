import Mathlib
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.three_le_fixedPts_of_centralizes
import Submission.Work.PSU3.StageA.lemma2cAux
import Submission.Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd
import Submission.Work.PSU3.StageA.modelDataBorel
import Submission.Work.PSU3.BenderST.transport
import Submission.Work.ThmF.ChV12.exists_k_normalizing
import Submission.Work.PSU3.StageB.isSplitRankOne_map_of_surjective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageB.NotFpfStep2.twoTransitive_centralizerOddResidual`

Peterfalvi II, Ch. VII §4, Step 2 (the `twoTransitive` field of the relative split rank-one
datum): for a prime-order `P ≤ V = centD H t` centralising a nontrivial element of `Q ∖ Q₀`,
the group `U = O^{2'}(C_G(P))` acts `2`-transitively on `U ⧸ (H ⊓ U)`.

Route.  The `Prop. 3` clause of `ChIIFourProp` at `X = P` provides an epimorphism
`φ : ↥U ↠ Y` onto a simple Bender group `Y` with central kernel `Z(U)` (the normalising
element `k ∈ J(D,t)` is supplied by `ChV12.exists_k_normalizing`, whose four-group hypothesis
is `hB3`, and whose `3 ≤ #fixedPts H P` hypothesis comes from the element
`y ∈ Q ∖ Q₀` centralised by `P`).  Since `Z(U) ≤ H ⊓ U` (a central element of a group lies in
every strongly embedded subgroup), the image `φ(H ⊓ U)` is strongly embedded in `Y` and hence
the Borel of a `ModelData` (`Work.PSU3.StageA.modelDataBorel`), which makes `Y` act
`2`-transitively on `Y ⧸ φ(H ⊓ U)`.  Finally `2`-transitivity descends along the surjection `φ`
(`isMultiplyPretransitive_of_map_ker_le`, proved below), giving the claim.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.PSU3.StageB.NotFpfStep2

/-- **Descent of `2`-transitivity along a surjection whose kernel lies in the point stabiliser.**
If `φ : F ↠ Y` is a surjective homomorphism with `φ.ker ≤ H` and `Y` acts `2`-transitively on
`Y ⧸ H.map φ`, then `F` acts `2`-transitively on `F ⧸ H`.

The map `F ⧸ H → Y ⧸ H.map φ`, `xH ↦ φ x · (H.map φ)`, is an injection (`φ.ker ≤ H`) that is
equivariant for the `F`-action (through `φ`); since `φ` is onto, `2`-transitivity of the `Y`-set
transfers. -/
theorem isMultiplyPretransitive_of_map_ker_le {F Y : Type} [Group F] [Group Y]
    {φ : F →* Y} (hsurj : Function.Surjective φ) {H : Subgroup F} (hker : φ.ker ≤ H)
    (h2 : MulAction.IsMultiplyPretransitive Y (Y ⧸ H.map φ) 2) :
    MulAction.IsMultiplyPretransitive F (F ⧸ H) 2 := by
  classical
  set f : F → Y ⧸ H.map φ := fun x => (φ x : Y ⧸ H.map φ) with hf
  have hwell : ∀ a b : F, QuotientGroup.leftRel H a b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    rw [hf]
    show ((φ a : Y ⧸ H.map φ)) = (φ b : Y ⧸ H.map φ)
    rw [QuotientGroup.eq]
    have h1 : (φ a)⁻¹ * φ b = φ (a⁻¹ * b) := by rw [map_mul, map_inv]
    rw [h1]
    exact Subgroup.mem_map_of_mem φ hab
  set ψ : F ⧸ H → Y ⧸ H.map φ := Quotient.lift f hwell with hψdef
  have hψ : ∀ x : F, ψ (QuotientGroup.mk x) = ((φ x : Y ⧸ H.map φ)) := by
    intro x
    rw [hψdef]
    rfl
  have hinjψ : Function.Injective ψ := by
    intro p q hpq
    induction p using Quotient.inductionOn' with
    | h a =>
      induction q using Quotient.inductionOn' with
      | h b =>
        rw [hψ, hψ] at hpq
        rw [QuotientGroup.eq] at hpq ⊢
        obtain ⟨h, hh, hhφ⟩ := Subgroup.mem_map.mp hpq
        have h1 : φ (a⁻¹ * b) = φ h := by rw [map_mul, map_inv, hhφ]
        have hmem : a⁻¹ * b * h⁻¹ ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
        have hk := hker hmem
        have heq : a⁻¹ * b = (a⁻¹ * b * h⁻¹) * h := by group
        rw [heq]
        exact H.mul_mem hk hh
  have heq : ∀ (g : F) (x : F ⧸ H), ψ (g • x) = φ g • ψ x := by
    intro g x
    induction x using Quotient.inductionOn' with
    | h a =>
      show ψ (g • (a : F ⧸ H)) = φ g • ψ (a : F ⧸ H)
      rw [show g • (a : F ⧸ H) = ((g * a : F) : F ⧸ H) from rfl, hψ, hψ]
      show ((φ (g * a) : Y ⧸ H.map φ)) = φ g • ((φ a : Y ⧸ H.map φ))
      rw [map_mul]
      rfl
  rw [MulAction.is_two_pretransitive_iff] at h2 ⊢
  intro a b c d hab hcd
  have h1 : ψ a ≠ ψ b := fun h => hab (hinjψ h)
  have h2' : ψ c ≠ ψ d := fun h => hcd (hinjψ h)
  obtain ⟨w, hw1, hw2⟩ := h2 h1 h2'
  obtain ⟨g, hg⟩ := hsurj w
  refine ⟨g, hinjψ ?_, hinjψ ?_⟩
  · rw [heq g a, hg, hw1]
  · rw [heq g b, hg, hw2]

theorem twoTransitive_centralizerOddResidual {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G}
    (hSit : Submission.Blueprint.Situation G)
    (hSplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hB3 : ∀ P' : Subgroup G, P' ≤ Submission.Blueprint.centD H t → (Nat.card P').Prime →
      Submission.Blueprint.HasFourGroup (Subgroup.centralizer (P' : Set G)))
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    (hPne : P ≠ ⊥) {y : G} (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H)
    (hyc : ∀ p ∈ P, p⁻¹ * y * p = y)
    (hStrong : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P))) :
    Submission.Blueprint.IsTwoTransitiveOn
      ((H ⊓ Work.PSU3.StageB.centralizerOddResidual P).subgroupOf
        (Work.PSU3.StageB.centralizerOddResidual P)) := by
  classical
  let F : Subgroup G := Work.PSU3.StageB.centralizerOddResidual P
  have hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H := hSplit.stronglyEmbedded
  have ht2 : orderOf t = 2 := hSplit.invol
  have htH : t ∉ H := hSplit.not_mem
  have hP1b := (hC4 G hSit H hH t ht2 htH).1
  have hP3 := (hC4 G hSit H hH t ht2 htH).2.2.2.1
  -- `P` fixes at least three points of `Ω = G ⧸ H`
  have hy1 : y ≠ 1 := fun h => hy0 (h ▸ Work.ThmF.Q0_le_Q0sub H (Work.ThmF.one_mem_Q0 H))
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H P).ncard :=
    three_le_fixedPts_of_centralizes hSplit
      (hPV.trans (Work.ThmF.centD_le_twoPoint t)) hyQ hy1 hyc
  have hfour : Submission.Blueprint.HasFourGroup (Subgroup.centralizer (P : Set G)) :=
    hB3 P hPV hPp
  -- the normalising element `k ∈ J(D,t)` required by the `Prop. 3` clause
  obtain ⟨k0, hk0K, hk01, hk0N⟩ :=
    Work.ThmF.ChV12.exists_k_normalizing hH ht2 htH hPV hX3 hfour hP1b
  have hP3c := hP3 P hPne hPV ⟨k0, hk0K, hk01, hk0N⟩
  dsimp only at hP3c
  obtain ⟨-, ⟨S, hSp, hSFH, hSidx, hSNorm, hSD, hSsup⟩, ⟨hZc, hYZc⟩, -⟩ := hP3c
  obtain ⟨Y, hYG, φ, hφsurj, hφker, hYbender⟩ := hYZc
  letI : Group Y := hYG
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  -- restate the `Prop. 3` output in terms of `F`
  have hZc' : Submission.Blueprint.oddCore ↥F = Subgroup.center ↥F := hZc
  have hφker' : φ.ker = Subgroup.center ↥F := hφker
  -- `H ⊓ F` is strongly embedded in `↥F` (this is the hypothesis `hStrong`)
  have hHF : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((H ⊓ F).subgroupOf F) := hStrong
  -- `Z(F) = ker φ ≤ H ⊓ F`
  have hkerH : φ.ker ≤ (H ⊓ F).subgroupOf F := by
    rw [hφker']
    exact Work.PSU3.StageA.center_le_of_isStronglyEmbedded hHF
  -- `ker φ` has odd order
  have hoddKer : Odd (Nat.card φ.ker) := by
    rw [hφker', ← hZc']
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  -- strong embeddedness passes to the image in the simple Bender group `Y`
  have himgSemb : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      (((H ⊓ F).subgroupOf F).map φ) :=
    Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd φ hφsurj hoddKer hkerH hHF
  obtain ⟨Pmd, hPmdB⟩ := Work.PSU3.StageA.modelDataBorel hYbender himgSemb
  -- the Bender action of `Y` on `Y ⧸ φ(H ⊓ F)`
  have h2Y : MulAction.IsMultiplyPretransitive Y (Y ⧸ ((H ⊓ F).subgroupOf F).map φ) 2 := by
    rw [← hPmdB]
    exact Pmd.isMultiplyPretransitive_two
  -- descend along `φ`
  have hfinal : MulAction.IsMultiplyPretransitive ↥F (↥F ⧸ (H ⊓ F).subgroupOf F) 2 :=
    isMultiplyPretransitive_of_map_ker_le hφsurj hkerH h2Y
  exact hfinal

end Work.PSU3.StageB.NotFpfStep2
