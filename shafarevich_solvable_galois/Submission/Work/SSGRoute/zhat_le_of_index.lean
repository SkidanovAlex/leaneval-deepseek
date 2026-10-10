import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.Work.SSGRoute.local_tame_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The finite-index subgroups of `Ẑ` are the power subgroups

Let `Ẑ = NK.LocalAnabelian.Zhat` be the profinite completion of `ℤ` and
`NK.TowerRank.powSubgroup n = Ẑ ^ n = {x ^ n : x ∈ Ẑ}` the subgroup of `n`-th powers
(`NK.TowerRank.powSubgroup`, defined in `Submission.NK.TowerRank.isProCyclic_zhat`).

The contents of this file are the group theory of the finite-index subgroups of `Ẑ`:

* `Work.SSGRoute.powSubgroup_le_of_index` : every element of a subgroup `H ≤ Ẑ` of index `n`
  has its `n`-th power in `H` (this is `Subgroup.pow_index_mem`, `Ẑ` being commutative);
  equivalently `Ẑ ^ n ≤ H`;
* `Work.SSGRoute.powSubgroup_index` : `Ẑ ^ n` has index `n` in `Ẑ`; indeed the `n`-th
  component map `NK.TameStructureDeep.Degree.compHomZMod n hn : Ẑ →* ℤ ⧸ nℤ` is surjective
  with kernel `Ẑ ^ n` (`NK.TameStructureDeep.Degree.ker_compHomZMod_eq_powSubgroup`), so
  `Ẑ ⧸ Ẑ ^ n ≃* ℤ ⧸ nℤ` is finite of cardinality `n`;
* `Work.SSGRoute.eq_powSubgroup_of_index` : consequently a subgroup of index `n` *is* the
  `n`-th power subgroup — the finite-index subgroups of `Ẑ` are exactly the `Ẑ ^ n`
  (contrast with the closed subgroups, which are the `Ẑ ^ n` as well, but the point here is
  that *every* finite-index subgroup is one of them, i.e. is closed);
* `Work.SSGRoute.powSubgroup_le_powSubgroup` : monotonicity `Ẑ ^ n ≤ Ẑ ^ d` for `d ∣ n`;
* `Work.SSGRoute.zhat_le_of_index` : a subgroup of index `n` is contained in `Ẑ ^ d` for
  every `d ∣ n`.
-/

namespace Work.SSGRoute

set_option linter.style.haveILetI false

/-- **The `n`-th powers lie in a subgroup of index `n`.**  If `H ≤ Ẑ` has index `n`, then
`x ^ n ∈ H` for every `x ∈ Ẑ` (`Subgroup.pow_index_mem`, applicable because `Ẑ` is
commutative), i.e. `Ẑ ^ n ≤ H`. -/
theorem powSubgroup_le_of_index {H : Subgroup NK.LocalAnabelian.Zhat} {n : ℕ}
    (hH : H.index = n) : NK.TowerRank.powSubgroup n ≤ H := by
  haveI : H.Normal := Subgroup.normal_of_isMulCommutative H
  intro x hx
  change x ∈ (NK.TowerRank.powSubgroup n : Set NK.LocalAnabelian.Zhat) at hx
  rw [NK.TowerRank.coe_powSubgroup] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [← hH]
  exact Subgroup.pow_index_mem H y

/-- **`Ẑ ^ n` has index `n` in `Ẑ`** (for `n > 0`).

The `n`-th component map `compHomZMod n hn : Ẑ →* ℤ ⧸ nℤ` is surjective with kernel `Ẑ ^ n`,
so it induces an isomorphism `Ẑ ⧸ Ẑ ^ n ≃* ℤ ⧸ nℤ`; taking cardinalities gives the index. -/
theorem powSubgroup_index (n : ℕ) (hn : 0 < n) : (NK.TowerRank.powSubgroup n).index = n := by
  have hnne : n ≠ 0 := hn.ne'
  haveI : NeZero n := ⟨hnne⟩
  have e : (NK.LocalAnabelian.Zhat ⧸ NK.TowerRank.powSubgroup n) ≃*
      Multiplicative (ZMod n) :=
    (QuotientGroup.quotientMulEquivOfEq
        (NK.TameStructureDeep.Degree.ker_compHomZMod_eq_powSubgroup n hnne).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (NK.TameStructureDeep.Degree.compHomZMod_surjective n hnne))
  rw [Subgroup.index_eq_card,
    Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    ZMod.card]

/-- **The subgroups of `Ẑ` of index `n` are exactly the `n`-th power subgroups.**

`Ẑ ^ n ≤ H` by `powSubgroup_le_of_index`, and `[Ẑ : Ẑ ^ n] = [Ẑ : H] = n` by
`powSubgroup_index`, so `H = Ẑ ^ n` (`Subgroup.relIndex_mul_index`: the relative index
`[Ẑ ^ n : H]` is `1`, and `Subgroup.relIndex_eq_one`). -/
theorem eq_powSubgroup_of_index {H : Subgroup NK.LocalAnabelian.Zhat} {n : ℕ}
    (hn : 0 < n) (hH : H.index = n) : H = NK.TowerRank.powSubgroup n := by
  refine le_antisymm ?_ (powSubgroup_le_of_index hH)
  have hrel : (NK.TowerRank.powSubgroup n).relIndex H * H.index =
      (NK.TowerRank.powSubgroup n).index :=
    Subgroup.relIndex_mul_index (powSubgroup_le_of_index hH)
  rw [powSubgroup_index n hn, hH] at hrel
  have h1 : (NK.TowerRank.powSubgroup n).relIndex H = 1 := by
    have h2 : (NK.TowerRank.powSubgroup n).relIndex H * n = 1 * n := by
      rw [one_mul]
      exact hrel
    exact Nat.eq_of_mul_eq_mul_right hn h2
  exact Subgroup.relIndex_eq_one.mp h1

/-- **Monotonicity of the power subgroups**: `Ẑ ^ n ≤ Ẑ ^ d` whenever `d ∣ n`
(write `n = d * (n / d)` and use `(x ^ (n / d)) ^ d = x ^ n`). -/
theorem powSubgroup_le_powSubgroup {n d : ℕ} (hd : d ∣ n) :
    NK.TowerRank.powSubgroup n ≤ NK.TowerRank.powSubgroup d := by
  intro x hx
  rw [NK.TowerRank.powSubgroup] at hx ⊢
  rw [MonoidHom.mem_range] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y ^ (n / d), ?_⟩
  show (y ^ (n / d)) ^ d = y ^ n
  rw [← pow_mul, Nat.div_mul_cancel hd]

/-- **A subgroup of `Ẑ` of index `n` is contained in `Ẑ ^ d` for every `d ∣ n`.**

By `eq_powSubgroup_of_index` such a subgroup is `Ẑ ^ n`, and `Ẑ ^ n ≤ Ẑ ^ d` because
`d ∣ n`. -/
theorem zhat_le_of_index {H : Subgroup NK.LocalAnabelian.Zhat} {n d : ℕ}
    (hn : 0 < n) (hH : H.index = n) (hd : d ∣ n) :
    H ≤ NK.TowerRank.powSubgroup d := by
  rw [eq_powSubgroup_of_index hn hH]
  exact powSubgroup_le_powSubgroup hd

end Work.SSGRoute
