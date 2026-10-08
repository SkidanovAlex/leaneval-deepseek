import Mathlib
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.Sz.Weyl
import Submission.Work.BSLit.BenderFacts2.MyAux.eq_of_three_fixedPoints

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2.MyAux

open LeanEval.GroupTheory.Defs

/-- If a non-trivial element `b` of an abelian subgroup `A` of odd order fixes a point `ω` of the
coset space `SzModel n ⧸ szBorelS n`, then every element of `A` fixes `ω`.

The proof is the classical fixed-point argument for a Zassenhaus group: a non-identity element of
`Sz(2^(2n+1))` fixes at most two points (`eq_of_three_fixedPoints`), and since `A` is abelian, the
whole orbit `A • ω` consists of fixed points of `b`.  This orbit therefore has at most two points;
on the other hand its cardinality divides the odd number `|A|`, so it is odd, hence a single
point. -/
theorem smul_eq_of_mem_of_fixedPoint (n : ℕ) (hn : 1 ≤ n)
    {A : Subgroup (LeanEval.GroupTheory.Defs.SzModel n)} {b : LeanEval.GroupTheory.Defs.SzModel n}
    (hbA : b ∈ A) (hb1 : b ≠ 1) (hAbel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hodd : Odd (Nat.card ↥A))
    {ω : LeanEval.GroupTheory.Defs.SzModel n ⧸ Submission.Sz.szBorelS n} (hω : b • ω = ω) :
    ∀ x ∈ A, x • ω = ω := by
  classical
  -- The set of points fixed by `b`.
  set Fix : Set (LeanEval.GroupTheory.Defs.SzModel n ⧸ Submission.Sz.szBorelS n) :=
    {a | b • a = a}
  -- `b ≠ 1` fixes at most two points.
  have hFix3 : ¬ 3 ≤ Fix.ncard := by
    intro h3
    obtain ⟨t, hts, htcard⟩ := Set.exists_subset_card_eq h3
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Set.ncard_eq_three.mp htcard
    have hx : x ∈ Fix := hts (by simp)
    have hy : y ∈ Fix := hts (by simp)
    have hz : z ∈ Fix := hts (by simp)
    rcases eq_of_three_fixedPoints n hn hb1 hx hy hz with h | h | h
    · exact hxy h
    · exact hxz h
    · exact hyz h
  have hFix_le : Fix.ncard ≤ 2 := by omega
  -- The orbit of `ω` under `A`.
  set O : Set (LeanEval.GroupTheory.Defs.SzModel n ⧸ Submission.Sz.szBorelS n) :=
      (MulAction.orbit ↥A ω : Set _) with hO
  -- Every point of the orbit is fixed by `b` (abelianness).
  have hOsub : O ⊆ Fix := by
    intro y hy
    have hy' : y ∈ (MulAction.orbit ↥A ω : Set _) := by rw [← hO]; exact hy
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hy'
    rw [← ha]
    show b • ((a : ↥A) • ω) = (a : ↥A) • ω
    rw [show ((a : ↥A) • ω) = (a : LeanEval.GroupTheory.Defs.SzModel n) • ω from rfl]
    rw [← mul_smul, hAbel b hbA (a : LeanEval.GroupTheory.Defs.SzModel n) a.2, mul_smul, hω]
  have hOle : O.ncard ≤ 2 := (Set.ncard_le_ncard hOsub).trans hFix_le
  have hcard_eq : O.ncard = Nat.card (MulAction.orbit ↥A ω) := by
    rw [hO]; exact (Nat.card_coe_set_eq _).symm
  -- The orbit size divides the odd number `|A|`.
  have hdvd : Nat.card (MulAction.orbit ↥A ω) ∣ Nat.card ↥A := by
    rw [show Nat.card (MulAction.orbit ↥A ω) = (MulAction.stabilizer ↥A ω).index from by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer ↥A ω)]
    exact ⟨Nat.card ↥(MulAction.stabilizer ↥A ω),
      (Subgroup.card_mul_index (MulAction.stabilizer ↥A ω)).symm.trans (mul_comm _ _)⟩
  have hOddO : Odd O.ncard := by
    rw [hcard_eq]
    exact Odd.of_dvd_nat hodd hdvd
  -- An odd number `≤ 2` is `1`.
  have hO1 : O.ncard = 1 := by
    obtain ⟨k, hk⟩ := hOddO
    omega
  have hOsubsing : O.Subsingleton := by
    rw [← Set.ncard_le_one_iff_subsingleton]
    omega
  intro x hx
  have hxO : x • ω ∈ O := by
    rw [hO]
    exact MulAction.mem_orbit ω (⟨x, hx⟩ : ↥A)
  have hωO : ω ∈ O := by
    rw [hO]
    exact MulAction.mem_orbit_self ω
  exact hOsubsing hxO hωO

end Work.BSLit.BenderFacts2.MyAux
