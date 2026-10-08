import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3Sub.prop1a_fixes_three
import Submission.Work.ThreePoints.ch1_lem2
import Submission.Work.ThreePoints.P3NeBot.p3_twoTransitive
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.p3cd_transitive`

Peterfalvi I Ch. II §4 Prop. 3 (a), the transitivity part: let `H` be strongly embedded in the
finite group `G`, `t ∉ H` an involution, `D = H ⊓ H^t`, `V = C_D(t)`, `K = J(D,t)`, and let
`X ≠ ⊥` with `X ≤ V` and `N_K(X) ≠ 1`.  Then `F = O^{2'}(C_G(X))` is *transitive* on the set
`Ω_X` of conjugates of `H` containing `X`: every `M ∈ Ω_X` is `H^f` for some `f ∈ F`.

The proof is short once two ingredients are in place.

* `Work.ThreePoints.P3Sub.prop1a_fixes_three` (Ch. II §4 Prop. 1 (a) with Brauer–Suzuki): if
  `X ≤ M = H^g` fixes at least three points of `Ω = G ⧸ H`, then `|C_M(X)|` is even.  In
  particular, for every `M ∈ Ω_X` both intersections `C_G(X) ⊓ H` and `C_G(X) ⊓ M` have even
  order.
* `Work.ThreePoints.exists_involution_conj_of_even_card_inf` (Ch. I §2 Lemma 2): two distinct
  conjugates `H₁ ≠ H₂` of `H` whose intersections with a subgroup `F` have even order are
  exchanged by an *involution* of `F`.  Applied to `F = C_G(X)` this gives, for every
  `M ∈ Ω_X ∖ {H}`, an involution `u ∈ C_G(X)` with `M = H^u`.

Finally an involution of `C_G(X)` lies in `O^{2'}(C_G(X)) = p3F X`: the quotient of a finite
group by `O^{2'}` has odd order, so every element of order two lies in `O^{2'}`.

Note that `X ≠ ⊥` and `N_K(X) ≠ 1` are *not* used: they are hypotheses of the surrounding
statement of Prop. 3, while its transitivity clause holds for every `X` with `|Ω_X| ≥ 3`.  The
extra hypotheses are kept because the statement is the one requested by the caller.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThreePoints

theorem p3cd_transitive {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (X : Subgroup G) (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    ∀ g : G, X ≤ Submission.Blueprint.conj g H →
      ∃ f ∈ Work.ThreePoints.p3F X,
        Submission.Blueprint.conj g H = Submission.Blueprint.conj f H := by
  intro g hg
  -- ### `X ≤ H`, and `X` fixes at least three points of `Ω`
  have hXH : X ≤ H := fun x hx => (mem_centD.mp (hX hx)).1
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard :=
    P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  by_cases hMH : Submission.Blueprint.conj g H = H
  · -- the point is the base point: `f = 1` works
    exact ⟨1, (p3F X).one_mem, by rw [hMH, conj_one]⟩
  · -- ### Ch. II §4 Prop. 1 (a): the two intersections with `C_G(X)` have even order
    have h1 : Even (Nat.card (Subgroup.centralizer (X : Set G) ⊓
        Submission.Blueprint.conj (1 : G) H : Subgroup G)) := by
      have h := P3Sub.prop1a_fixes_three (H := H) (X := X) (M := H) hFT hC hA hBrSz hS hH hX3
        ⟨1, (conj_one H).symm⟩ hXH
      simpa only [conj_one, inf_comm] using h
    have h2 : Even (Nat.card (Subgroup.centralizer (X : Set G) ⊓
        Submission.Blueprint.conj g H : Subgroup G)) := by
      have h := P3Sub.prop1a_fixes_three (H := H) (X := X) (M := Submission.Blueprint.conj g H)
        hFT hC hA hBrSz hS hH hX3 ⟨g, rfl⟩ hg
      simpa only [inf_comm] using h
    have hne : Submission.Blueprint.conj (1 : G) H ≠ Submission.Blueprint.conj g H := by
      rw [conj_one]
      exact fun h => hMH h.symm
    -- ### Ch. I §2 Lemma 2: an involution of `C_G(X)` moves the base point to `H^g`
    obtain ⟨u, hu_inv, hu_conj⟩ :=
      exists_involution_conj_of_even_card_inf (F := Subgroup.centralizer (X : Set G))
        hH hne h1 h2
    have huC : u ∈ Subgroup.centralizer (X : Set G) := (mem_involutions.mp hu_inv).1
    have hu2 : orderOf u = 2 := (mem_involutions.mp hu_inv).2
    refine ⟨u, ?_, ?_⟩
    · -- ### an involution of `C_G(X)` lies in `O^{2'}(C_G(X)) = p3F X`
      rw [mem_p3F]
      refine ⟨⟨u, huC⟩, ?_, rfl⟩
      exact involution_mem_oddResidual
        (x := (⟨u, huC⟩ : ↥(Subgroup.centralizer (X : Set G))))
        (Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hu2))
    · -- ### the two points coincide
      rw [← hu_conj, conj_one]

end Work.ThreePoints
