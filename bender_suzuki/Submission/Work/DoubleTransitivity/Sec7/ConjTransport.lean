import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.Sec4.RpDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec7.ConjTransport`

Transport of the Chapter I vocabulary along the canonical `G`-equivariant bijection
`G ⧸ (conj x H) ≃ G ⧸ H` (`y (conj x H) ↦ (y * x) H`), used in the final assembly of
Theorem A (Peterfalvi I Ch. I §6): the argument of §6 is carried out with the base a point of
`Ω_P`, which is a conjugate of the originally given strongly embedded subgroup.

* `conj_IsTwoTransitiveOn` : `IsTwoTransitiveOn (conj x H) → IsTwoTransitiveOn H`.
* `fixedPts_conj_ncard` : the number of fixed points is invariant.
* `MaxFixesThree.conj` : maximality transfers.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.DoubleTransitivity.Sec7

/-! ## The canonical `G`-equivariant bijection `G ⧸ (conj x H) → G ⧸ H` -/

/-- The map `ψ y = y * x` from `G ⧸ conj x H` to `G ⧸ H` is well defined. -/
theorem conjQuotientMap_wellDefined {G : Type} [Group G] {H : Subgroup G} (x : G) :
    ∀ a b : G, QuotientGroup.leftRel (Submission.Blueprint.conj x H) a b →
      (QuotientGroup.mk (a * x) : G ⧸ H) = QuotientGroup.mk (b * x) := by
  intro a b hab
  rw [QuotientGroup.leftRel_apply] at hab
  rw [QuotientGroup.eq]
  obtain ⟨h₀, hh₀, hh₀x⟩ := Subgroup.mem_map.mp hab
  have hthis : a⁻¹ * b = x * h₀ * x⁻¹ := hh₀x.symm
  have hgoal : (a * x)⁻¹ * (b * x) = h₀ := by
    calc (a * x)⁻¹ * (b * x) = x⁻¹ * (a⁻¹ * b) * x := by group
      _ = x⁻¹ * (x * h₀ * x⁻¹) * x := by rw [hthis]
      _ = h₀ := by group
  rw [hgoal]; exact hh₀

/-- The canonical map `G ⧸ (conj x H) → G ⧸ H`, `y (conj x H) ↦ (y * x) H`. -/
noncomputable def conjQuotientMap {G : Type} [Group G] {H : Subgroup G} (x : G) :
    (G ⧸ Submission.Blueprint.conj x H) → (G ⧸ H) :=
  Quotient.lift (fun y => (QuotientGroup.mk (y * x) : G ⧸ H)) (conjQuotientMap_wellDefined x)

@[simp] theorem conjQuotientMap_mk {G : Type} [Group G] {H : Subgroup G} (x y : G) :
    conjQuotientMap x (QuotientGroup.mk y : G ⧸ Submission.Blueprint.conj x H) =
      (QuotientGroup.mk (y * x) : G ⧸ H) := rfl

/-- `conjQuotientMap x` is `G`-equivariant. -/
theorem conjQuotientMap_smul {G : Type} [Group G] {H : Subgroup G} (x : G) (g : G)
    (a : G ⧸ Submission.Blueprint.conj x H) :
    conjQuotientMap x (g • a) = g • conjQuotientMap x a := by
  refine QuotientGroup.induction_on a ?_
  intro y
  show conjQuotientMap x (QuotientGroup.mk (g * y)) =
    g • conjQuotientMap x (QuotientGroup.mk y)
  rw [conjQuotientMap_mk, conjQuotientMap_mk]
  show (QuotientGroup.mk ((g * y) * x) : G ⧸ H) =
    g • (QuotientGroup.mk (y * x) : G ⧸ H)
  rw [mul_assoc]; rfl

theorem conjQuotientMap_wellDefined_inv {G : Type} [Group G] {H : Subgroup G} (x : G) :
    ∀ a b : G, QuotientGroup.leftRel H a b →
      (QuotientGroup.mk (a * x⁻¹) : G ⧸ Submission.Blueprint.conj x H) =
        QuotientGroup.mk (b * x⁻¹) := by
  intro a b hab
  rw [QuotientGroup.leftRel_apply] at hab
  rw [QuotientGroup.eq]
  apply Subgroup.mem_map.mpr
  refine ⟨a⁻¹ * b, hab, ?_⟩
  show MulAut.conj x (a⁻¹ * b) = (a * x⁻¹)⁻¹ * (b * x⁻¹)
  rw [MulAut.conj_apply]; group

/-- The inverse of `conjQuotientMap x`. -/
noncomputable def conjQuotientMapInv {G : Type} [Group G] {H : Subgroup G} (x : G) :
    (G ⧸ H) → (G ⧸ Submission.Blueprint.conj x H) :=
  Quotient.lift (fun z => (QuotientGroup.mk (z * x⁻¹) : G ⧸ Submission.Blueprint.conj x H))
    (conjQuotientMap_wellDefined_inv x)

@[simp] theorem conjQuotientMapInv_mk {G : Type} [Group G] {H : Subgroup G} (x z : G) :
    conjQuotientMapInv x (QuotientGroup.mk z : G ⧸ H) =
      (QuotientGroup.mk (z * x⁻¹) : G ⧸ Submission.Blueprint.conj x H) := rfl

theorem conjQuotientMap_leftInverse {G : Type} [Group G] {H : Subgroup G} (x : G) :
    Function.LeftInverse (conjQuotientMapInv (H := H) x) (conjQuotientMap (H := H) x) := by
  intro y
  refine QuotientGroup.induction_on y ?_
  intro y
  show conjQuotientMapInv x (conjQuotientMap x (QuotientGroup.mk y)) = QuotientGroup.mk y
  rw [conjQuotientMap_mk, conjQuotientMapInv_mk]
  congr 1
  group

theorem conjQuotientMap_rightInverse {G : Type} [Group G] {H : Subgroup G} (x : G) :
    Function.RightInverse (conjQuotientMapInv (H := H) x) (conjQuotientMap (H := H) x) := by
  intro z
  refine QuotientGroup.induction_on z ?_
  intro z
  show conjQuotientMap x (conjQuotientMapInv x (QuotientGroup.mk z)) = QuotientGroup.mk z
  rw [conjQuotientMapInv_mk, conjQuotientMap_mk]
  congr 1
  group

theorem conjQuotientMap_injective {G : Type} [Group G] {H : Subgroup G} (x : G) :
    Function.Injective (conjQuotientMap (H := H) x) :=
  (conjQuotientMap_leftInverse (H := H) x).injective

/-- `IsTwoTransitiveOn` is invariant under replacing the base by a conjugate. -/
theorem conj_IsTwoTransitiveOn {G : Type} [Group G] {H : Subgroup G} (x : G)
    (h : Submission.Blueprint.IsTwoTransitiveOn (Submission.Blueprint.conj x H)) :
    Submission.Blueprint.IsTwoTransitiveOn H := by
  classical
  unfold Submission.Blueprint.IsTwoTransitiveOn at h ⊢
  rw [MulAction.is_two_pretransitive_iff] at h ⊢
  intro a b c d hab hcd
  have hab' : conjQuotientMapInv x a ≠ conjQuotientMapInv x b :=
    fun hh => hab (by rw [← conjQuotientMap_rightInverse (H := H) x a, ← conjQuotientMap_rightInverse (H := H) x b,
      hh])
  have hcd' : conjQuotientMapInv x c ≠ conjQuotientMapInv x d :=
    fun hh => hcd (by rw [← conjQuotientMap_rightInverse (H := H) x c, ← conjQuotientMap_rightInverse (H := H) x d,
      hh])
  obtain ⟨g, hg1, hg2⟩ := h hab' hcd'
  refine ⟨g, ?_, ?_⟩
  · calc g • a = g • conjQuotientMap x (conjQuotientMapInv x a) := by
          rw [conjQuotientMap_rightInverse (H := H) x a]
      _ = conjQuotientMap x (g • conjQuotientMapInv x a) :=
          (conjQuotientMap_smul x g (conjQuotientMapInv x a)).symm
      _ = conjQuotientMap x (conjQuotientMapInv x c) := by rw [hg1]
      _ = c := conjQuotientMap_rightInverse (H := H) x c
  · calc g • b = g • conjQuotientMap x (conjQuotientMapInv x b) := by
          rw [conjQuotientMap_rightInverse (H := H) x b]
      _ = conjQuotientMap x (g • conjQuotientMapInv x b) :=
          (conjQuotientMap_smul x g (conjQuotientMapInv x b)).symm
      _ = conjQuotientMap x (conjQuotientMapInv x d) := by rw [hg2]
      _ = d := conjQuotientMap_rightInverse (H := H) x d

/-! ## Fixed points and maximality -/

/-- The number of fixed points of a subgroup is invariant under conjugating the base. -/
theorem fixedPts_conj_ncard {G : Type} [Group G] {H : Subgroup G} (x : G) (P : Subgroup G) :
    (Submission.Blueprint.fixedPts (Submission.Blueprint.conj x H) P).ncard =
      (Submission.Blueprint.fixedPts H P).ncard := by
  classical
  refine Set.ncard_congr (fun ω _ => conjQuotientMap x ω) ?_ ?_ ?_
  · intro ω hω p hp
    rw [← conjQuotientMap_smul x p ω, hω p hp]
  · intro a b _ _ hab
    exact conjQuotientMap_injective (H := H) x hab
  · intro ω hω
    refine ⟨conjQuotientMapInv x ω, ?_, conjQuotientMap_rightInverse (H := H) x ω⟩
    intro p hp
    have h1 : conjQuotientMap x (p • conjQuotientMapInv x ω) =
        conjQuotientMap x (conjQuotientMapInv x ω) := by
      rw [conjQuotientMap_smul x p (conjQuotientMapInv x ω),
        conjQuotientMap_rightInverse (H := H) x ω, hω p hp]
    exact conjQuotientMap_injective (H := H) x h1

/-- Maximality of a `p`-subgroup fixing three points transfers to a conjugate base. -/
theorem MaxFixesThree.conj {G : Type} [Group G] {H : Subgroup G} (x : G) {p : ℕ} {P : Subgroup G}
    (h : Work.DoubleTransitivity.MaxFixesThree p H P) :
    Work.DoubleTransitivity.MaxFixesThree p (Submission.Blueprint.conj x H) P := by
  obtain ⟨hp, h3, hmax⟩ := h
  refine ⟨hp, ?_, ?_⟩
  · show 3 ≤ (Submission.Blueprint.fixedPts (Submission.Blueprint.conj x H) P).ncard
    rw [fixedPts_conj_ncard x P]; exact h3
  · intro Q hQp hQ3 hPQ
    exact hmax Q hQp (by
      show 3 ≤ (Submission.Blueprint.fixedPts H Q).ncard
      rw [← fixedPts_conj_ncard x Q]
      exact hQ3) hPQ

/-! ## Transport of the two-point Sylow data and of `IsSylowSubgroupOf` -/

/-- The stabiliser of a point is unchanged by the canonical identification. -/
theorem stabilizer_conjQuotientMapInv {G : Type} [Group G] {H : Subgroup G} (x : G)
    (ω : G ⧸ H) :
    MulAction.stabilizer G (conjQuotientMapInv x ω) = MulAction.stabilizer G ω := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h1 : conjQuotientMap x (g • conjQuotientMapInv x ω) =
        conjQuotientMap x (conjQuotientMapInv x ω) := by rw [h]
    rwa [conjQuotientMap_smul x g (conjQuotientMapInv x ω),
      conjQuotientMap_rightInverse x ω] at h1
  · intro h
    exact conjQuotientMap_injective x (by
      rw [conjQuotientMap_smul x g (conjQuotientMapInv x ω),
        conjQuotientMap_rightInverse x ω, h])

/-- `TwoPointSylowData` is base-independent: it only records which *subgroups* are two-point
stabilisers, and conjugating the base permutes these. -/
theorem TwoPointSylowData.conj {G : Type} [Group G] {H : Subgroup G} (x : G) {p : ℕ}
    {P : Subgroup G} (h : Work.DoubleTransitivity.Sec4.TwoPointSylowData p H P) :
    Work.DoubleTransitivity.Sec4.TwoPointSylowData p (Submission.Blueprint.conj x H) P := by
  obtain ⟨ω₁, ω₂, hne, Q₀, hQ₀syl, hQ₀P⟩ := h
  refine ⟨conjQuotientMapInv x ω₁, conjQuotientMapInv x ω₂, ?_, Q₀, ?_, hQ₀P⟩
  · intro hcontra
    have h1 : ω₁ = ω₂ := by
      have h2 := congrArg (conjQuotientMap x) hcontra
      rw [conjQuotientMap_rightInverse x ω₁, conjQuotientMap_rightInverse x ω₂] at h2
      exact h2.symm
    exact hne h1.symm
  · rw [stabilizer_conjQuotientMapInv x ω₁, stabilizer_conjQuotientMapInv x ω₂]
    exact hQ₀syl

/-- Conjugating a `p`-Sylow of `D` gives a `p`-Sylow of the conjugate of `D`. -/
theorem IsSylowSubgroupOf.conj {G : Type} [Group G] [Finite G] {p : ℕ} {Q D : Subgroup G} (g : G)
    (h : Work.DoubleTransitivity.IsSylowSubgroupOf p Q D) :
    Work.DoubleTransitivity.IsSylowSubgroupOf p (Submission.Blueprint.conj g Q)
      (Submission.Blueprint.conj g D) := by
  haveI : Finite ↥D := Subtype.finite
  haveI : Finite ↥(Q.subgroupOf D) := Subtype.finite
  haveI : Finite ↥(Submission.Blueprint.conj g D) := Subtype.finite
  haveI : Finite ↥((Submission.Blueprint.conj g Q).subgroupOf (Submission.Blueprint.conj g D)) :=
    Subtype.finite
  obtain ⟨hQD, hQp, hidx⟩ := h
  have hQD' : Submission.Blueprint.conj g Q ≤ Submission.Blueprint.conj g D :=
    Subgroup.map_mono hQD
  refine ⟨hQD', hQp.map _, ?_⟩
  have hcard : Nat.card ↥((Submission.Blueprint.conj g Q).subgroupOf
      (Submission.Blueprint.conj g D)) = Nat.card ↥(Q.subgroupOf D) := by
    have e1 : ((Submission.Blueprint.conj g Q).subgroupOf (Submission.Blueprint.conj g D)).map
        (Submission.Blueprint.conj g D).subtype = Submission.Blueprint.conj g Q :=
      Subgroup.map_subgroupOf_eq_of_le hQD'
    have e2 : (Q.subgroupOf D).map D.subtype = Q := Subgroup.map_subgroupOf_eq_of_le hQD
    rw [← Subgroup.card_map_of_injective (f := (Submission.Blueprint.conj g D).subtype)
        ((Submission.Blueprint.conj g D).subtype_injective), e1,
      ← Subgroup.card_map_of_injective (f := D.subtype) (D.subtype_injective), e2]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
  have hcardD : Nat.card ↥(Submission.Blueprint.conj g D) = Nat.card ↥D :=
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
  rw [Subgroup.index_eq_card_div] at hidx
  rw [Subgroup.index_eq_card_div, hcardD, hcard]
  exact hidx

end Work.DoubleTransitivity.Sec7
