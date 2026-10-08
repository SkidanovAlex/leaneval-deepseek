import Mathlib
import Submission.Work.ThmG.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `rankOne_index`: the index of `H` in a split rank-one group

If `H = Q ⋊ D` is the rank-one datum of `IsSplitRankOne H Q t` (`D = H ∩ Hᵗ`, `t ∉ H`,
`G` acting 2-transitively on `G ⧸ H`), then `Q` acts regularly on the complement of the
base point in `G ⧸ H`, so `|G : H| = |Q| + 1`.

The proof is the standard count: `G` acts 2-transitively on `Ω = G ⧸ H` with point
stabiliser `H`; hence `H` (the stabiliser of the base point `ω₀`) is transitive on the
complement `Ω \ {ω₀}` (that is `orbit_stabilizer_eq_compl`), the stabiliser in `H` of the
point `ω₁ = t • ω₀` is `D = twoPoint H t`, and `|H : D| = |Q|` (`index_subgroupOf_eq_card`).
Thus

`|Ω| = |Ω \ {ω₀}| + 1 = |H : D| + 1 = |Q| + 1`.
-/

open scoped Pointwise

set_option linter.style.haveILetI false

namespace Work.ThmG

open Submission.Blueprint

/-- The stabiliser of a point for a subgroup action is the `subgroupOf` of the ambient
stabiliser. -/
theorem stabilizer_subgroupOf {G Ω : Type*} [Group G] [MulAction G Ω] (H : Subgroup G) (a : Ω) :
    MulAction.stabilizer H a = (MulAction.stabilizer G a).subgroupOf H := by
  ext y
  rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  exact Iff.rfl

/-- The stabilisers of the coset `tH` under the left action of `G` (resp. `H`) on `G ⧸ H`:
they are `t H t⁻¹ = H.map (MulAut.conj t)` and its intersection with `H`. -/
theorem stabilizer_quotientGroup_mk {G : Type*} [Group G] (H : Subgroup G) (t : G) :
    MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) = H.map (MulAut.conj t).toMonoidHom ∧
    MulAction.stabilizer H (QuotientGroup.mk t : G ⧸ H) =
      (H ⊓ H.map (MulAut.conj t).toMonoidHom).subgroupOf H := by
  have h1 : (QuotientGroup.mk t : G ⧸ H) = t • QuotientGroup.mk (1 : G) := by
    rw [show t • (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk (t * 1) from rfl, mul_one]
  have hG : MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) =
      H.map (MulAut.conj t).toMonoidHom := by
    rw [h1, MulAction.stabilizer_smul_eq_stabilizer_map_conj, MulAction.stabilizer_quotient]
  refine ⟨hG, ?_⟩
  rw [stabilizer_subgroupOf, hG, inf_comm, Subgroup.inf_subgroupOf_right]

/-- In a 2-transitive action, the stabiliser of a point `a` is transitive on the complement
of `a`: the orbit of any `b ≠ a` under `stabilizer G a` is exactly `Ω \ {a}`. -/
theorem orbit_stabilizer_eq_compl {G Ω : Type*} [Group G] [MulAction G Ω]
    (h2 : MulAction.IsMultiplyPretransitive G Ω 2) {a b : Ω} (hb : b ≠ a) :
    MulAction.orbit (MulAction.stabilizer G a) b = {c : Ω | c ≠ a} := by
  ext c
  constructor
  · intro hc
    rw [MulAction.mem_orbit_iff] at hc
    obtain ⟨g, rfl⟩ := hc
    intro hcontra
    have hga : (g : G) • a = a := MulAction.mem_stabilizer_iff.mp g.2
    have h1 : (g : G) • b = a := hcontra
    exact hb (smul_left_cancel (g : G) (by rw [h1, hga]))
  · intro hc
    rw [MulAction.mem_orbit_iff]
    obtain ⟨g, hga, hgb⟩ := (MulAction.is_two_pretransitive_iff.mp h2) (Ne.symm hb) (Ne.symm hc)
    exact ⟨⟨g, by rwa [MulAction.mem_stabilizer_iff]⟩, hgb⟩

/-- If `H = Q · D` with `Q` normalised by `H` and `Q ⊓ D = ⊥`, then `D` has index `|Q|`
in `H` (so that `H = Q ⋊ D`, with `Q` the normal factor). -/
theorem index_subgroupOf_eq_card {G : Type*} [Group G] {H Q D : Subgroup G}
    (hQH : Q ≤ H) (hDH : D ≤ H) (hN : H ≤ Subgroup.normalizer (Q : Set G))
    (hinf : Q ⊓ D = ⊥) (hsup : Q ⊔ D = H) :
    (D.subgroupOf H).index = Nat.card Q := by
  have hQn : (Q.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hN
  haveI := hQn
  have hsup' : Q.subgroupOf H ⊔ D.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQH hDH, hsup, Subgroup.subgroupOf_self]
  have hinf' : Q.subgroupOf H ⊓ D.subgroupOf H = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    have hmem : (x : G) ∈ Q ⊓ D := ⟨hx.1, hx.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hmul : (↑(Q.subgroupOf H) : Set ↥H) * (↑(D.subgroupOf H) : Set ↥H) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ Q.subgroupOf H ⊔ D.subgroupOf H := by rw [hsup']; exact Subgroup.mem_top x
    rw [Subgroup.mem_sup_of_normal_left] at hx
    obtain ⟨q, hq, d, hd, hqd⟩ := hx
    exact ⟨q, hq, d, hd, hqd⟩
  have hcomp : Subgroup.IsComplement' (Q.subgroupOf H) (D.subgroupOf H) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf') hmul
  exact (Subgroup.IsComplement'.index_eq_card hcomp).trans
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv)

/-- The complement of a point in a finite type has one element less. -/
theorem natCard_ne_add_one {α : Type*} [Finite α] (x : α) :
    Nat.card α = Nat.card {y : α // y ≠ x} + 1 := by
  classical
  have h1 : Nat.card α = Nat.card ({y : α // y = x} ⊕ {y : α // y ≠ x}) :=
    Nat.card_congr (Equiv.sumCompl (fun y : α => y = x)).symm
  rw [h1, Nat.card_sum]
  have h2 : Nat.card {y : α // y = x} = 1 := by
    haveI : Nonempty {y : α // y = x} := ⟨⟨x, rfl⟩⟩
    haveI : Subsingleton {y : α // y = x} := ⟨fun a b => Subtype.ext (a.2.trans b.2.symm)⟩
    exact Nat.card_unique
  rw [h2, Nat.add_comm]

/-- **Bender–Suzuki, split rank-one index.**  In a split rank-one configuration `H = Q ⋊ D`
with `D = H ∩ Hᵗ` the stabiliser of a second point, the subgroup `Q` is regular on the
complement of the base point in `G ⧸ H`, so `|G : H| = |Q| + 1`. -/
theorem rankOne_index {G : Type*} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) : H.index = Nat.card Q + 1 := by
  classical
  set ω₀ : G ⧸ H := QuotientGroup.mk (1 : G) with hω₀
  set ω₁ : G ⧸ H := t • ω₀ with hω₁
  have h2 : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := h.twoTransitive
  -- the stabiliser of the base point in `G` is `H`
  have hstab0 : MulAction.stabilizer G ω₀ = H := by
    rw [hω₀]; exact MulAction.stabilizer_quotient H
  -- `ω₁ = t • ω₀` is different from `ω₀`
  have hmk : (QuotientGroup.mk t : G ⧸ H) = ω₁ := by
    rw [hω₁, hω₀,
      show t • (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk (t * 1) from rfl, mul_one]
  have hne : ω₁ ≠ ω₀ := by
    intro hEq
    have ht : t ∈ H := by
      rw [← hstab0, MulAction.mem_stabilizer_iff, ← hω₁, hEq]
    exact h.not_mem ht
  -- the stabiliser in `H` of `ω₁` is `D = twoPoint H t`
  have hstab1 : MulAction.stabilizer H ω₁ = (twoPoint H t).subgroupOf H := by
    rw [← hmk, (stabilizer_quotientGroup_mk H t).2]
  -- `H` is transitive on the complement of the base point
  have horbit : (MulAction.orbit H ω₁ : Set (G ⧸ H)) = {ω : G ⧸ H | ω ≠ ω₀} := by
    have hh := orbit_stabilizer_eq_compl h2 (a := ω₀) (b := ω₁) hne
    rwa [hstab0] at hh
  -- cardinality bookkeeping
  have e1 : Nat.card (G ⧸ H) = Nat.card {ω : G ⧸ H // ω ≠ ω₀} + 1 := natCard_ne_add_one ω₀
  have e2 : Nat.card {ω : G ⧸ H // ω ≠ ω₀} = Nat.card ↑(MulAction.orbit H ω₁) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun ω : G ⧸ H => by simp [horbit]))
  have e3 : Nat.card ↑(MulAction.orbit H ω₁) =
      Nat.card (H ⧸ MulAction.stabilizer H ω₁) :=
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer H ω₁)
  have e4 : Nat.card (H ⧸ MulAction.stabilizer H ω₁) =
      (MulAction.stabilizer H ω₁).index := (Subgroup.index_eq_card _).symm
  have e5 : (MulAction.stabilizer H ω₁).index = Nat.card Q := by
    rw [hstab1]
    exact index_subgroupOf_eq_card h.le (show twoPoint H t ≤ H from inf_le_left) h.normal
      h.inf_eq h.sup_eq
  calc H.index = Nat.card (G ⧸ H) := Subgroup.index_eq_card H
    _ = Nat.card {ω : G ⧸ H // ω ≠ ω₀} + 1 := e1
    _ = Nat.card ↑(MulAction.orbit H ω₁) + 1 := by rw [e2]
    _ = Nat.card (H ⧸ MulAction.stabilizer H ω₁) + 1 := by rw [e3]
    _ = (MulAction.stabilizer H ω₁).index + 1 := by rw [e4]
    _ = Nat.card Q + 1 := by rw [e5]

end Work.ThmG
