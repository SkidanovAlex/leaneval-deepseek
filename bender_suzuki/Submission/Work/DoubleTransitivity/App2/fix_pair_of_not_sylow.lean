import Mathlib
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.Coprime.lt_inf_normalizer_of_lt
import Submission.Work.ThreePoints.app2_6_uniform

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.DoubleTransitivity.App2

/-- Peterfalvi, Appendix II (6), the "`N(P)`" step.  (`fixedBySub Q` is the set of points of `E`
fixed by `Q`; `X_a` is `MulAction.stabilizer X a`.)

Let `p` be a prime, `X` a finite group acting on a *finite* set `E`, `P` a `p`-subgroup of `X`
whose fixed points contain `a ≠ c`, and suppose `P` is not a Sylow `p`-subgroup of
`D = X_a ⊓ X_c`.  If `P` is maximal among the `p`-subgroups of `X_a` fixing at least three
points of `E`, then `P` is strictly contained in a `p`-subgroup `R` of `N_X(P) ⊓ X_a` whose
fixed point set is exactly `{a, c}`.

Proof: from `¬ IsSylowSubgroupOf p P D` and `P ≤ D`, `p ∣ P.relIndex D`, so there is a
`p`-subgroup `R ≤ D ⊓ N_X(P) = N_D(P)` with `P ≤ R` and `R ≠ P` (this is exactly the auxiliary
lemma `Work.DoubleTransitivity.App2.exists_pSubgroup_gt_in_normalizer` if that module is in the
workspace; it can also be proved inline, e.g. via
`Work.ThreePoints.app2_6_exists_pSubgroup_lt_of_dvd_index` together with
`Work.Coprime.lt_inf_normalizer_of_lt`).  As `R ≤ X_a` and `P ≤ R` with `R` a `p`-subgroup,
maximality of `P` forces `|E_R| < 3` (otherwise `R = P`); but `a, c ∈ E_R`, so `|E_R| = 2` and
`E_R = {a, c}`.

NOTE: `[Fintype E]` is essential (without finiteness `ncard` of an infinite fixed set is `0`, so
`hmax` is vacuous and the statement is false). -/
theorem fix_pair_of_not_sylow {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} [Fact p.Prime] {a c : E} {P : Subgroup X} (hP : IsPGroup p P)
    (ha : a ∈ (fixedBySub P : Set E)) (hc : c ∈ (fixedBySub P : Set E)) (hac : c ≠ a)
    (hnotsyl : ¬ IsSylowSubgroupOf p P
      (MulAction.stabilizer X a ⊓ MulAction.stabilizer X c))
    (hmax : ∀ Q : Subgroup X, IsPGroup p Q → Q ≤ MulAction.stabilizer X a →
      3 ≤ (fixedBySub Q : Set E).ncard → P ≤ Q → Q ≤ P) :
    ∃ R : Subgroup X, IsPGroup p R ∧ P ≤ R ∧
      R ≤ Subgroup.normalizer (P : Set X) ⊓ MulAction.stabilizer X a ∧
      fixedBySub R = {a, c} := by
  classical
  -- `P` lies in the two-point stabiliser `D = X_a ⊓ X_c`
  have haP : P ≤ MulAction.stabilizer X a :=
    fun m hm => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp ha) m hm)
  have hcP : P ≤ MulAction.stabilizer X c :=
    fun m hm => MulAction.mem_stabilizer_iff.mpr ((mem_fixedBySub.mp hc) m hm)
  set D : Subgroup X := MulAction.stabilizer X a ⊓ MulAction.stabilizer X c with hD
  have hPD : P ≤ D := fun m hm => ⟨haP hm, hcP hm⟩
  -- `P` is not Sylow in `D`, so it does not exhaust the `p`-part of `D`
  have hdvd : p ∣ (P.subgroupOf D).index := by
    by_contra hcon
    exact hnotsyl ⟨hPD, hP, hcon⟩
  -- a `p`-subgroup `Q ≤ D` strictly containing `P`
  obtain ⟨Q, hQD, hQg, hQlt⟩ :=
    Work.ThreePoints.app2_6_exists_pSubgroup_lt_of_dvd_index (Fact.out : p.Prime) hP hPD hdvd
  set N : Subgroup X := Subgroup.normalizer (P : Set X) with hN
  -- the normalizer condition inside the `p`-group `Q` gives `P < Q ⊓ N_X(P)`
  have hlt : P < Q ⊓ N := Work.Coprime.lt_inf_normalizer_of_lt hQg hQlt
  have hRa : Q ⊓ N ≤ MulAction.stabilizer X a :=
    le_trans inf_le_left (le_trans hQD inf_le_left)
  have hRc : Q ⊓ N ≤ MulAction.stabilizer X c :=
    le_trans inf_le_left (le_trans hQD inf_le_right)
  refine ⟨Q ⊓ N, hQg.to_inf_left, hlt.le, le_inf inf_le_right hRa, ?_⟩
  -- maximality of `P` bounds the fixed point set of `Q ⊓ N`
  have hR3 : ¬ 3 ≤ (fixedBySub (Q ⊓ N) : Set E).ncard := by
    intro h3
    have hle : Q ⊓ N ≤ P := hmax (Q ⊓ N) hQg.to_inf_left hRa h3 hlt.le
    exact hlt.ne (le_antisymm hlt.le hle)
  -- `a` and `c` are fixed
  have hsub : ({a, c} : Set E) ⊆ (fixedBySub (Q ⊓ N) : Set E) := by
    intro x hx
    rcases hx with h | h
    · rw [h]
      exact fun m hm => MulAction.mem_stabilizer_iff.mp (hRa hm)
    · rw [h]
      exact fun m hm => MulAction.mem_stabilizer_iff.mp (hRc hm)
  have hle2 : (fixedBySub (Q ⊓ N) : Set E).ncard ≤ ({a, c} : Set E).ncard := by
    rw [Set.ncard_pair hac.symm]
    omega
  exact (Set.eq_of_subset_of_ncard_le hsub hle2).symm

end Work.DoubleTransitivity.App2
