import Mathlib
import Submission.Work.FeitSibley.Defs
import Submission.Work.CharCore.sum_irr_degree_sq
import Submission.Work.ZassenhausPSL2.Feit.card_excl
import Submission.Work.ZassenhausPSL2.Feit.excl_degree_support
import Submission.Work.ZassenhausPSL2.Feit.not_excl_linear
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.Feit.final_card_lin`

In a split rank-one Zassenhaus configuration `H = Q ⋊ D` with `Q` a normal abelian `2`-subgroup
and `D = twoPoint H t = H ∩ Hᵗ`, the number of irreducible characters of `H` which are trivial on
`Q` equals the order of `D`:

`#{χ ∈ Irr H | ∀ x ∈ Q, χ x = 1} = |D|`.

## The argument

Write `𝒯` for the set on the left and `𝒰 = {χ ∈ Irr H | Q ⊆ ker χ}` for the set of irreducible
characters of `H` whose kernel (in the sense of `charKernel`) contains `Q`.

* `𝒯 = 𝒰`.  `𝒯 ⊆ 𝒰` because `1 ∈ Q`, so `χ ∈ 𝒯` has `χ 1 = 1` and `χ x = 1 = χ 1` for every
  `x ∈ Q`.  For `𝒰 ⊆ 𝒯`: if `χ ∈ Irr H` has `Q ⊆ charKernel χ`, then `χ ∉ 𝒮 = excludingKernel H Q`
  (membership in `𝒮` would exhibit `x ∈ Q` with `χ x ≠ χ 1`), so `not_excl_linear` gives
  `χ 1 = 1` and `χ = 1` on `Q`.

* `|𝒰| = |D|`.  The irreducible characters of `H` trivial on `Q` are exactly the inflations of
  the irreducible characters of `H ⧸ Q` and inflation preserves degrees, so
  `∑_{χ ∈ 𝒰} χ(1)² = [H : Q]` (`Work.CohApps.sum_irr_deg_sq_le_ker`).  Since `H ⧸ Q ≅ D` is
  abelian — `D` is abelian because `t` inverts each of its elements — every such `χ` is linear,
  `χ(1) = 1` (`not_excl_linear` again).  Hence the sum is simply `|𝒰|`, and
  `[H : Q] = |D|` is `index_subgroupOf_Q`.

The two `Finset`s of `Irr H` occurring below differ only in the shape of the predicate
(`∀ x ∈ Q, χ x = 1` versus `Q ⊆ charKernel χ`), which is why the sum of squared degrees can be
evaluated on the second one.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open Classical

namespace Work.ZassenhausPSL2.Feit

/-- **The number of irreducible characters of `H` trivial on the normal `2`-subgroup `Q` is
`|D|`, `D = twoPoint H t`.** -/
theorem final_card_lin {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) :
    ((Work.CharCore.Irr H).filter (fun lc => ∀ x : H, (x : G) ∈ Q → lc x = 1)).card
      = Nat.card (Submission.Blueprint.twoPoint H t) := by
  classical
  have hN : (Q.subgroupOf H).Normal := qSubgroupOf_normal h
  -- `𝒯 = 𝒰`: the two predicates cut out the same subset of `Irr H`.
  have hfinset : (Work.CharCore.Irr H).filter (fun lc => ∀ x : H, (x : G) ∈ Q → lc x = 1)
      = (Work.CharCore.Irr H).filter
          (fun χ => ((Q.subgroupOf H : Subgroup H) : Set H) ⊆ Work.CharCore.charKernel χ) := by
    apply Finset.ext
    intro χ
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hχIrr, htriv⟩
      refine ⟨hχIrr, fun y hy => ?_⟩
      have hyQ : (y : G) ∈ Q := Subgroup.mem_subgroupOf.mp hy
      show χ y = χ 1
      rw [htriv y hyQ, htriv 1 (by simp : ((1 : H) : G) ∈ Q)]
    · rintro ⟨hχIrr, hker⟩
      have hnotexcl : χ ∉ Submission.Blueprint.excludingKernel H Q := by
        intro hexcl
        obtain ⟨-, y, hyQ, hyne⟩ :=
          (mem_excludingKernel_iff (Q := Q) (χ := χ)).mp hexcl
        exact hyne (hker (Subgroup.mem_subgroupOf.mpr hyQ))
      exact ⟨hχIrr, (not_excl_linear h hz h2 hab hχIrr hnotexcl).2⟩
  -- Every member of `𝒰` is linear.
  have hdeg : ∀ χ ∈ (Work.CharCore.Irr H).filter
        (fun χ => ((Q.subgroupOf H : Subgroup H) : Set H) ⊆ Work.CharCore.charKernel χ),
      (Work.CharCore.irrDeg χ : ℝ) ^ 2 = 1 := by
    intro χ hχ
    have hχIrr : χ ∈ Work.CharCore.Irr H := (Finset.mem_filter.mp hχ).1
    have hker := (Finset.mem_filter.mp hχ).2
    have hnotexcl : χ ∉ Submission.Blueprint.excludingKernel H Q := by
      intro hexcl
      obtain ⟨-, y, hyQ, hyne⟩ :=
        (mem_excludingKernel_iff (Q := Q) (χ := χ)).mp hexcl
      exact hyne (hker (Subgroup.mem_subgroupOf.mpr hyQ))
    have h1 : χ 1 = 1 := (not_excl_linear h hz h2 hab hχIrr hnotexcl).1
    have hspec := Work.CharCore.irrDeg_spec (χ := χ) hχIrr
    rw [h1] at hspec
    have : Work.CharCore.irrDeg χ = 1 := by exact_mod_cast hspec.symm
    rw [this]; norm_num
  -- `∑_{χ ∈ 𝒰} χ(1)² = [H : Q]`, and each term is `1`.
  have hsum := @Work.CohApps.sum_irr_deg_sq_le_ker H _ _ (Q.subgroupOf H) hN
  rw [Finset.sum_congr rfl hdeg, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hcard : ((Work.CharCore.Irr H).filter
        (fun χ => ((Q.subgroupOf H : Subgroup H) : Set H) ⊆ Work.CharCore.charKernel χ)).card
      = Nat.card (Submission.Blueprint.twoPoint H t) := by
    have hnat : ((Work.CharCore.Irr H).filter
        (fun χ => ((Q.subgroupOf H : Subgroup H) : Set H) ⊆ Work.CharCore.charKernel χ)).card
        = (Q.subgroupOf H).index := Nat.cast_injective hsum
    rw [hnat, index_subgroupOf_Q h]
  rw [hfinset]
  exact hcard

end Work.ZassenhausPSL2.Feit
