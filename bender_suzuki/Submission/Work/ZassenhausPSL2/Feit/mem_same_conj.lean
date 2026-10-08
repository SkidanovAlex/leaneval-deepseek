import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs
import Submission.Work.ZassenhausPSL2.Feit.sylow_conj_le
import Submission.Work.ZassenhausPSL2.Feit.closure_invol_isPGroup_two
import Submission.Work.ZassenhausPSL2.Feit.odd_index_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Feit's step `mem_same_conj`: two involutions whose product is a `2`-element lie in a
common conjugate of the root group `Q`

In a split rank-one configuration `(H, Q, t)` (`Q` a `2`-group), `Q` is a Sylow
`2`-subgroup of `G`: Feit's count `|G| = (|Q| + 1)·|Q|·|D|` (`Feit.card_G_eq`) has
`(2)`-part `|Q|`, because `|Q| + 1` is odd (`Q ≠ ⊥` from `Even |H|` and `|H| = |Q|·|D|`
with `|D|` odd) and `|D|` is odd (the two-point stabiliser of a strongly embedded
subgroup).  Hence `Q.index` is odd.

If `u, v` are involutions with `u * v` of `2`-power order, then `u, v` generate the
dihedral `2`-group `⟨u, v⟩ = ⟨u * v⟩ ⋊ ⟨u⟩` of order `≤ 2 ^ (k+1)`, a `2`-subgroup;
by Sylow's theorem it is contained in a conjugate `Q ^ g` of the Sylow `2`-subgroup `Q`,
so both `u` and `v` lie in `Q ^ g`.

This is the leaf **F0d** of `NOTES_LEAD_bs_psl2core.md` (Feit 1960, §2): it makes the
involutions with `2`-power product a single "class" of the associated partition of the
involutions of `G`.
-/

set_option autoImplicit false

namespace Work.ZassenhausPSL2.Feit

/-- **Feit's step.** Two involutions `u`, `v` whose product has `2`-power order lie in a
common conjugate of the root group `Q` (which is a Sylow `2`-subgroup of `G`). -/
theorem mem_same_conj {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (h2 : IsPGroup 2 Q) {u v : G}
    (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : ∃ k : ℕ, orderOf (u * v) = 2 ^ k) :
    ∃ g : G, u ∈ Submission.Blueprint.conj g Q ∧ v ∈ Submission.Blueprint.conj g Q := by
  -- `Q` is a Sylow `2`-subgroup of `G`, so its index is odd
  have hidx : ¬ (2:ℕ) ∣ Q.index := fun hd =>
    (Nat.not_even_iff_odd.mpr (odd_index_Q h h2)) (even_iff_two_dvd.mpr hd)
  -- `u` and `v` generate a `2`-subgroup, which lies in a conjugate of `Q`
  have hP : IsPGroup 2 (Subgroup.closure ({u, v} : Set G)) :=
    closure_invol_isPGroup_two hu hv huv
  obtain ⟨g, hg⟩ := sylow_conj_le (p := 2) (by norm_num) h2 hidx hP
  exact ⟨g, hg (Subgroup.subset_closure (by simp)), hg (Subgroup.subset_closure (by simp))⟩

end Work.ZassenhausPSL2.Feit
