import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz
import Submission.Work.DoubleTransitivity.Sec4.prop2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.ThreePoints.P3Sub

open LeanEval.GroupTheory.Defs

/-!
# Peterfalvi I Ch. II §4 Prop. 1 (a) under (B0)–(B2), with Brauer–Suzuki

Under the situation (B0)–(B2) (`hS : Situation G`), a strongly embedded `H ≤ G`, and a subgroup
`X ≤ M = H^g` fixing at least three points of `Ω = G ⧸ H`, the centraliser `C_M(X)` has even
order.

The mathematical work is already in the library; this file assembles it:

* `Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz` proves Ch. II §4
  Prop. 1 (a) by strong induction on `|X|`, consuming as input the Ch. I §4 Prop. 2 statement
  `hS4`: for a finite group `F` with strongly embedded `K ≤ F`, and a `p`-subgroup `Q ≤ K`
  (`p ≠ 2`) maximal among the `p`-subgroups of `K` with at least three fixed points of `F ⧸ K`,
  the normaliser `N_K(Q)` has even order;
* Ch. I §4 Prop. 2 in exactly that form is supplied here by
  `Work.DoubleTransitivity.Sec4.prop2`, which is unconditional (given the Brauer–Suzuki
  hypothesis `hBrSz`) and yields, for such a `Q`, that `Q` is maximal among the `p`-subgroups of
  `F` with at least three fixed points and that `|N_F(Q) ⊓ K|` is even;
* `card_normalizer_subgroupOf_eq_card_inf` transfers the latter to `|N_K(Q)|`.
-/

/-- The normaliser inside `↥K` of `Q.subgroupOf K` has the same cardinality as `K ⊓ N_F(Q)`: the
map argument `(Subgroup.normalizer (Q.subgroupOf K)).map K.subtype = K ⊓ N_F(Q)`. -/
theorem card_normalizer_subgroupOf_eq_card_inf {F : Type} [Group F] {K Q : Subgroup F}
    (hQK : Q ≤ K) :
    Nat.card ↥(Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K) =
      Nat.card ↥(K ⊓ Subgroup.normalizer (Q : Set F) : Subgroup F) := by
  have hmap : (Subgroup.normalizer (Q.subgroupOf K : Set K)).map K.subtype =
      K ⊓ Subgroup.normalizer (Q : Set F) := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hy' : (Q.subgroupOf K).map (MulAut.conj y).toMonoidHom = Q.subgroupOf K :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
      calc Q.map (MulAut.conj (y : F)).toMonoidHom
          = ((Q.subgroupOf K).map K.subtype).map (MulAut.conj (y : F)).toMonoidHom := by
            conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hQK]
        _ = (Q.subgroupOf K).map ((MulAut.conj (y : F)).toMonoidHom.comp K.subtype) := by
            rw [Subgroup.map_map]
        _ = (Q.subgroupOf K).map (K.subtype.comp (MulAut.conj y).toMonoidHom) := by
            rw [show (MulAut.conj (y : F)).toMonoidHom.comp K.subtype =
              K.subtype.comp (MulAut.conj y).toMonoidHom from by
                ext z
                simp [MulAut.conj_apply]]
        _ = ((Q.subgroupOf K).map (MulAut.conj y).toMonoidHom).map K.subtype := by
            rw [Subgroup.map_map]
        _ = (Q.subgroupOf K).map K.subtype := by rw [hy']
        _ = Q := Subgroup.map_subgroupOf_eq_of_le hQK
    · rintro ⟨hxK, hxN⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyQ : (y : F) ∈ Q := Subgroup.mem_subgroupOf.mp hy
        have h1 : x * (y : F) * x⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hxN) (y : F) |>.mp hyQ
        rw [Subgroup.mem_subgroupOf]
        simpa using h1
      · intro hy
        have hyQ : x * (y : F) * x⁻¹ ∈ Q := by
          have h := Subgroup.mem_subgroupOf.mp hy
          simpa using h
        have hxi : x⁻¹ ∈ Subgroup.normalizer (Q : Set F) :=
          (Subgroup.normalizer (Q : Set F)).inv_mem hxN
        have h1 : x⁻¹ * (x * (y : F) * x⁻¹) * x⁻¹⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hxi) (x * (y : F) * x⁻¹) |>.mp hyQ
        have h2 : x⁻¹ * (x * (y : F) * x⁻¹) * x⁻¹⁻¹ = (y : F) := by group
        rw [h2] at h1
        exact Subgroup.mem_subgroupOf.mpr h1
  rw [← hmap]
  exact (Subgroup.card_map_of_injective (f := K.subtype) Subtype.coe_injective).symm

/-- Ch. I §4 Prop. 2 (Peterfalvi I p. 156), in the form consumed by Ch. II §4 Prop. 1 (a): for a
finite group `F` of any 2-rank, a strongly embedded `K ≤ F`, `p ≠ 2` a prime and `Q ≤ K` a
`p`-subgroup maximal among the `p`-subgroups of `K` fixing at least three points of `F ⧸ K`, the
normaliser of `Q` in `K` has even order.  This is
`Work.DoubleTransitivity.Sec4.prop2` (unconditional, given Brauer–Suzuki) transported along
`card_normalizer_subgroupOf_eq_card_inf`. -/
theorem ch1_s4_prop2 (hBrSz : Submission.Blueprint.BrauerSuzukiProp) :
    ∀ (F : Type) [Group F] [Finite F] {K : Subgroup F},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded K →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ Q : Subgroup F, Q ≤ K → IsPGroup p Q →
        3 ≤ (Submission.Blueprint.fixedPts K Q).ncard →
        (∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
          3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) →
        Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  intro F _ _ K hK p hp hp2 Q hQK hQp hQ3 hQmax
  have hmax : Work.DoubleTransitivity.MaxFixesThreeIn p K Q :=
    ⟨hQp, hQK, hQ3, fun R hRp hRK hR3 hQR => le_of_eq (hQmax R hQR hRK hRp hR3)⟩
  have h := (Work.DoubleTransitivity.Sec4.prop2 (H := K) (P := Q) hBrSz hK hp hp2 hmax).2
  rw [card_normalizer_subgroupOf_eq_card_inf hQK, inf_comm]
  exact h

theorem prop1a_fixes_three {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {X M : Subgroup G} (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz
    hFT hC (ch1_s4_prop2 hBrSz) hS hH hX3 hM hXM

end Work.ThreePoints.P3Sub
