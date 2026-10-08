/-
Area A9 of the Feit--Thompson drive: Frobenius' hypothesis.

Frobenius' hypothesis is **inherited by subgroups**: if `N_G(Q)/C_G(Q)` is a `p`-group for
every non-trivial `p`-subgroup `Q ≤ G`, then the same holds in every subgroup `A ≤ G`.

The point is that for `Q ≤ A ≤ G` the natural map
`N_A(Q)/C_A(Q) → N_G(Q)/C_G(Q)`
is injective (it is the map induced by the inclusion `A ↪ G`; its kernel is exactly
`C_A(Q)`), and a subgroup of a `p`-group is a `p`-group.  Formally we build an injective
monoid homomorphism `N_A(Q) →* N_G(Q)/C_G(Q)`, whose kernel is `C_A(Q)`, and apply
`IsPGroup.of_injective` together with the first isomorphism theorem.

## Main results

* `Work.NPC.Frobenius.isConjPGroup_map_subtype` : `IsConjPGroup p (Q.map A.subtype)` implies
  `IsConjPGroup p Q` for a subgroup `Q ≤ A`, i.e. the Frobenius condition is inherited by
  subgroups.
* `Work.NPC.Frobenius.hasFrobeniusCondition_subgroup` : `HasFrobeniusCondition p G` implies
  `HasFrobeniusCondition p A` for every subgroup `A ≤ G`.
-/
import Mathlib
import Submission.Work.NPC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise

namespace Work.NPC.Frobenius

variable {G : Type*} [Group G]

/-- For a subgroup `A ≤ G` and a subgroup `Q ≤ A`, viewed as a subgroup `Q.map A.subtype` of
`G`, restricting back to `A` recovers `Q`. -/
lemma subgroupOf_map_subtype_self (A : Subgroup G) (Q : Subgroup ↥A) :
    (Q.map A.subtype).subgroupOf A = Q := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    have h : x = y := Subtype.ext hxy
    rwa [← h]
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- An element `a ∈ A` centralizes the image of `Q ≤ A` in `G` if and only if it centralizes
`Q` inside `A`. -/
lemma mem_centralizer_map_subtype (A : Subgroup G) (Q : Subgroup ↥A) (a : ↥A) :
    (a : G) ∈ Subgroup.centralizer ((Q.map A.subtype : Subgroup G) : Set G) ↔
      a ∈ Subgroup.centralizer (Q : Set ↥A) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have h1 := h (A.subtype y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
    exact Subtype.ext h1
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact congrArg (fun z : ↥A => (z : G)) (h y hy)

/-- **The Frobenius condition is inherited by subgroups, in the form needed for the
induction.**  For a subgroup `A ≤ G` and a subgroup `Q ≤ A`, if `N_G(Q)/C_G(Q)` is a
`p`-group then so is `N_A(Q)/C_A(Q)`.

Indeed the inclusion `A ↪ G` induces a monoid homomorphism
`N_A(Q) →* N_G(Q.make)/C_G(Q.make)` whose kernel is `C_A(Q)`; it is therefore injective on
`N_A(Q)/C_A(Q)`, and a subgroup of a `p`-group is a `p`-group. -/
theorem isConjPGroup_map_subtype {p : ℕ} (A : Subgroup G) (Q : Subgroup ↥A)
    (h : Work.NPC.IsConjPGroup p (Q.map A.subtype)) : Work.NPC.IsConjPGroup p Q := by
  classical
  set H : Subgroup G := Q.map A.subtype with hH
  have hHle : H ≤ A := Subgroup.map_subtype_le Q
  have hsub : H.subgroupOf A = Q := subgroupOf_map_subtype_self A Q
  -- `N_A(Q)` is the trace of `N_G(H)` on `A`.
  have hnorm : (Subgroup.normalizer (H : Set G)).subgroupOf A
      = Subgroup.normalizer (Q : Set ↥A) := by
    rw [Subgroup.subgroupOf_normalizer_eq hHle, hsub]
  -- The homomorphism `N_A(Q) →* N_G(H)` induced by the inclusion `A ↪ G`.
  let φ : ↥(Subgroup.normalizer (Q : Set ↥A)) →* ↥(Subgroup.normalizer (H : Set G)) :=
    { toFun := fun x => ⟨(x : ↥A), by
        have hx : (x : ↥A) ∈ (Subgroup.normalizer (H : Set G)).subgroupOf A := by
          rw [hnorm]; exact x.2
        exact Subgroup.mem_subgroupOf.mp hx⟩
      map_one' := by ext; rfl
      map_mul' := by intro a b; ext; rfl }
  -- Its composition with the quotient map `N_G(H) →* N_G(H)/C_G(H)`.
  let Φ : ↥(Subgroup.normalizer (Q : Set ↥A)) →*
      (↥(Subgroup.normalizer (H : Set G)) ⧸
        (Subgroup.centralizer (H : Set G)).subgroupOf (Subgroup.normalizer (H : Set G))) :=
    (QuotientGroup.mk' _).comp φ
  -- The kernel is `C_A(Q)`.
  have hker : Φ.ker = (Subgroup.centralizer (Q : Set ↥A)).subgroupOf
      (Subgroup.normalizer (Q : Set ↥A)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (QuotientGroup.mk' ((Subgroup.centralizer (H : Set G)).subgroupOf
      (Subgroup.normalizer (H : Set G)))) (φ x) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    show (φ x : ↥(Subgroup.normalizer (H : Set G))) ∈
      (Subgroup.centralizer (H : Set G)).subgroupOf (Subgroup.normalizer (H : Set G)) ↔ _
    rw [Subgroup.mem_subgroupOf]
    show ((φ x : ↥(Subgroup.normalizer (H : Set G))) : G) ∈
      Subgroup.centralizer (H : Set G) ↔ _
    exact mem_centralizer_map_subtype A Q (x : ↥A)
  have hP : IsPGroup p (↥(Subgroup.normalizer (H : Set G)) ⧸
      (Subgroup.centralizer (H : Set G)).subgroupOf (Subgroup.normalizer (H : Set G))) := h
  -- `N_A(Q)/C_A(Q)` embeds into the `p`-group `N_G(H)/C_G(H)` via the first isomorphism
  -- theorem, applied to `Φ`.
  have h1 : IsPGroup p (↥(Subgroup.normalizer (Q : Set ↥A)) ⧸ Φ.ker) :=
    IsPGroup.of_injective hP (QuotientGroup.kerLift Φ) (QuotientGroup.kerLift_injective Φ)
  have h2 : IsPGroup p (↥(Subgroup.normalizer (Q : Set ↥A)) ⧸
      (Subgroup.centralizer (Q : Set ↥A)).subgroupOf (Subgroup.normalizer (Q : Set ↥A))) :=
    IsPGroup.of_equiv h1 (QuotientGroup.quotientMulEquivOfEq hker)
  exact h2

/-- **Frobenius' hypothesis is inherited by subgroups.**  If `N_G(Q)/C_G(Q)` is a `p`-group
for every non-trivial `p`-subgroup `Q ≤ G`, then `N_A(Q)/C_A(Q)` is a `p`-group for every
non-trivial `p`-subgroup `Q ≤ A`, for any subgroup `A ≤ G`. -/
theorem hasFrobeniusCondition_subgroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (A : Subgroup G) (h : Work.NPC.HasFrobeniusCondition p G) :
    Work.NPC.HasFrobeniusCondition p ↥A := by
  intro Q hQp hQne
  have hHne : Q.map A.subtype ≠ ⊥ := by
    intro hbot
    apply hQne
    rw [← subgroupOf_map_subtype_self A Q, hbot, Subgroup.bot_subgroupOf]
  exact isConjPGroup_map_subtype A Q (h _ (IsPGroup.map hQp A.subtype) hHne)

end Work.NPC.Frobenius
