import Mathlib
import Submission.Work.PSU3.BenderST
import Submission.Work.Models.Port.BenderSetup
import Submission.Work.Models.Port.BenderBasic
import Submission.Work.Models.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.BenderST.transport` — invariance of the hypotheses and of the conclusion of
`BenderSTProp` under a group isomorphism

`BenderSTProp` is proved by transporting a split rank-one datum of an arbitrary simple Bender
group `Y` into one of the three models along an isomorphism `e : Y ≃* M`.  This file contains
the transport lemmas:

* `isSplitRankOne_map` — `IsSplitRankOne` is invariant under a group isomorphism (the only
  non-formal field is `twoTransitive`, transported through `isMultiplyPretransitive_of_mulEquiv`
  and the canonical equiv `cosetEquiv e H : G ⧸ H ≃ G' ⧸ H.map e`);
* `twoPoint_map`, `conj_map` — two-point stabilisers and conjugates commute with the
  isomorphism;
* `ncard_involutions_map`, `isAbelianSubgroup_map` — the two set-theoretic ingredients of the
  clauses of `BenderSTProp`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint (involutions twoPoint IsAbelianSubgroup IsSplitRankOne)

namespace Work.PSU3.BenderST

/-! ## Multiple transitivity across an isomorphism of the acting groups -/

/-- `IsMultiplyPretransitive` is preserved by an isomorphism `σ : G ≃* G'` of the acting groups
together with an equivariant equivalence `e : α ≃ β` of the acted-on types. -/
theorem isMultiplyPretransitive_of_mulEquiv {G G' α β : Type*} [Group G] [Group G']
    [MulAction G α] [MulAction G' β] (σ : G ≃* G') (e : α ≃ β)
    (he : ∀ (g : G) (x : α), e (g • x) = σ g • e x) {n : ℕ}
    (hα : MulAction.IsMultiplyPretransitive G α n) :
    MulAction.IsMultiplyPretransitive G' β n := by
  change MulAction.IsPretransitive G' (Fin n ↪ β)
  refine ⟨fun f₁ f₂ => ?_⟩
  obtain ⟨g, hg⟩ :=
    hα.exists_smul_eq (f₁.trans e.symm.toEmbedding) (f₂.trans e.symm.toEmbedding)
  refine ⟨σ g, ?_⟩
  ext i
  have h : g • (e.symm (f₁ i)) = e.symm (f₂ i) := by
    have h1 := congrArg (fun f : Fin n ↪ α => (f : Fin n → α) i) hg
    simpa [Function.Embedding.trans_apply] using h1
  calc (σ g • f₁) i = σ g • f₁ i := by simp
    _ = σ g • e (e.symm (f₁ i)) := by simp
    _ = e (g • e.symm (f₁ i)) := by rw [he]
    _ = e (e.symm (f₂ i)) := by rw [h]
    _ = f₂ i := by simp

/-! ## The canonical equivalence of coset spaces -/

/-- The setoid relation of the coset spaces matches under the isomorphism (used to define
`cosetEquiv`). -/
theorem cosetEquiv_rel {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G) :
    ∀ a b : G, QuotientGroup.leftRel H a b ↔
      QuotientGroup.leftRel (H.map e.toMonoidHom) (e a) (e b) := by
  intro a b
  rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, Subgroup.mem_map]
  change a⁻¹ * b ∈ H ↔ ∃ y ∈ H, e y = (e a)⁻¹ * e b
  constructor
  · intro hx
    exact ⟨a⁻¹ * b, hx, by rw [map_mul, map_inv]⟩
  · rintro ⟨y, hy, hye⟩
    have : y = a⁻¹ * b := e.injective (by rw [hye, map_mul, map_inv])
    rwa [← this]

/-- The canonical equivalence `G ⧸ H ≃ G' ⧸ H.map e` induced by a group isomorphism
`e : G ≃* G'`. -/
noncomputable def cosetEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G) :
    G ⧸ H ≃ G' ⧸ H.map e.toMonoidHom :=
  Quotient.congr e.toEquiv (cosetEquiv_rel e H)

/-- `cosetEquiv` on representatives. -/
theorem cosetEquiv_mk {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G) (a : G) :
    cosetEquiv e H ((a : G) : G ⧸ H) = ((e a : G') : G' ⧸ H.map e.toMonoidHom) :=
  Quotient.congr_mk e.toEquiv (cosetEquiv_rel e H) a

/-- `cosetEquiv` is equivariant. -/
theorem cosetEquiv_smul {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G)
    (g : G) (x : G ⧸ H) : cosetEquiv e H (g • x) = e g • cosetEquiv e H x := by
  induction x using Quotient.inductionOn with
  | h a =>
    rw [show g • ((a : G) : G ⧸ H) = ((g * a : G) : G ⧸ H) from rfl, cosetEquiv_mk, cosetEquiv_mk,
      map_mul]
    rfl

/-! ## Conjugates and two-point stabilisers -/

/-- Conjugating a subgroup commutes with a group isomorphism. -/
theorem conj_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (g : G) (H : Subgroup G) :
    Submission.Blueprint.conj (e g) (H.map e.toMonoidHom)
      = (Submission.Blueprint.conj g H).map e.toMonoidHom := by
  show (H.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom
    = (H.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  show e g * e x * (e g)⁻¹ = e (g * x * g⁻¹)
  rw [map_mul, map_mul, map_inv]

/-- The two-point stabiliser commutes with a group isomorphism. -/
theorem twoPoint_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (H : Subgroup G) (t : G) :
    twoPoint (H.map e.toMonoidHom) (e t) = (twoPoint H t).map e.toMonoidHom := by
  show H.map e.toMonoidHom ⊓ Submission.Blueprint.conj (e t) (H.map e.toMonoidHom) = _
  rw [conj_map, Subgroup.map_inf _ _ _ e.injective]

/-- A subgroup normalised by `H` stays normalised after transport. -/
theorem map_le_normalizer {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {H Q : Subgroup G} (h : H ≤ Subgroup.normalizer (Q : Set G)) :
    H.map e.toMonoidHom ≤ Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup G') : Set G') := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro x hx k hk
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hk
  simpa only [map_mul, map_inv] using Subgroup.mem_map_of_mem e.toMonoidHom (h y hy w hw)

/-! ## `IsSplitRankOne` -/

/-- `IsSplitRankOne` is invariant under a group isomorphism. -/
theorem isSplitRankOne_map {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) :
    IsSplitRankOne (H.map e.toMonoidHom) (Q.map e.toMonoidHom) (e t) where
  stronglyEmbedded := Submission.isStronglyEmbedded_of_mulEquiv H h.stronglyEmbedded e
  twoTransitive :=
    isMultiplyPretransitive_of_mulEquiv e (cosetEquiv e H) (cosetEquiv_smul e H) h.twoTransitive
  invol := by
    simpa using (orderOf_injective e.toMonoidHom e.injective t).trans h.invol
  not_mem := by
    intro hmem
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp hmem
    exact h.not_mem (e.injective hxe ▸ hx)
  le := Subgroup.map_mono h.le
  normal := map_le_normalizer e h.normal
  inf_eq := by
    rw [twoPoint_map e H t, ← Subgroup.map_inf _ _ _ e.injective, h.inf_eq, Subgroup.map_bot]
  sup_eq := by
    rw [twoPoint_map e H t, ← Subgroup.map_sup, h.sup_eq]

/-! ## The two set-theoretic ingredients of the clauses -/

/-- The involutions of a subgroup transported along a group isomorphism. -/
theorem involutions_map_eq {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (S : Subgroup G) :
    involutions ((S.map e.toMonoidHom) : Set G') = e '' involutions (S : Set G) := by
  ext y
  constructor
  · rintro ⟨hy, hy2⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    simpa using (orderOf_injective e.toMonoidHom e.injective x).symm.trans hy2
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem e.toMonoidHom hx,
      by simpa using (orderOf_injective e.toMonoidHom e.injective x).trans hx2⟩

/-- The number of involutions of a subgroup is invariant under a group isomorphism. -/
theorem ncard_involutions_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (S : Subgroup G) :
    (involutions ((S.map e.toMonoidHom) : Set G')).ncard = (involutions (S : Set G)).ncard := by
  rw [involutions_map_eq e S, Set.ncard_image_of_injective _ e.injective]

/-- Abelianness of a subgroup is invariant under a group isomorphism. -/
theorem isAbelianSubgroup_map {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (S : Subgroup G) :
    IsAbelianSubgroup (S.map e.toMonoidHom) ↔ IsAbelianSubgroup S := by
  constructor
  · intro h x hx y hy
    refine e.injective ?_
    rw [map_mul, map_mul]
    exact h (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
      (e y) (Subgroup.mem_map_of_mem e.toMonoidHom hy)
  · intro h x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, h a ha b hb]

end Work.PSU3.BenderST
