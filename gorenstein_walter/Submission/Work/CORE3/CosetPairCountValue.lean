import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.CosetInvCountAPI
import Submission.Work.CORE3.CosetPairCountValueOfInvolution

namespace Work.CORE3

open Work.GW2

/-!
# The value of `cosetPairCount` on a nontrivial coset

`Work.CORE3.CosetPairCountValue` computes the number of ordered pairs of distinct commuting
involutions in the coset `(Quotient.out c) · Hh` for `c ≠ 1` in terms of the number
`cosetInvCount Hh (Quotient.out c)` of involutions of that coset:

* `2` involutions give `2` ordered pairs,
* `4` involutions give `6` ordered pairs,
* every other value gives `0`.

The hypotheses `hLe4` and `hFour` are the two Bender §3 inputs (a coset has at most four
involutions, and a coset with four contributes six pairs).

## Strategy

The pair count `cosetPairCount Hh y` and the involution count `cosetInvCount Hh y` depend only on
the left coset `y Hh` (`cosetPairCount_congr` below).  So if `y = Quotient.out c ∉ Hh` and the
coset is nontrivial in the sense that it contains an involution `z`, we may replace `y` by `z`
(`cosetInvCount_congr`).  `z` is a genuine involution, and the value is computed for an
involution representative by `CosetPairCountValueOfInvolution`.  If the coset contains no
involution at all both sides are `0`.
-/

section Helpers

variable {G : Type} [Group G]

/-- `cosetPairCount` depends only on the left coset: if `x` and `y` lie in the same left coset
of `Hh` (`x⁻¹ * y ∈ Hh`) then the involutions of `x Hh` and `y Hh` coincide, hence so do the
counts of ordered commuting pairs. -/
theorem cosetPairCount_congr {Hh : Subgroup G} {x y : G} (hxy : x⁻¹ * y ∈ Hh) :
    cosetPairCount Hh x = cosetPairCount Hh y := by
  have hset : cosetInvolSet Hh x = cosetInvolSet Hh y := by
    ext z
    simp only [mem_cosetInvolSet]
    constructor
    · rintro ⟨hz, hz'⟩
      refine ⟨hz, ?_⟩
      rw [show y⁻¹ * z = (x⁻¹ * y)⁻¹ * (x⁻¹ * z) from by group]
      exact Hh.mul_mem (Hh.inv_mem hxy) hz'
    · rintro ⟨hz, hz'⟩
      refine ⟨hz, ?_⟩
      rw [show x⁻¹ * z = (x⁻¹ * y) * (y⁻¹ * z) from by group]
      exact Hh.mul_mem hxy hz'
  unfold cosetPairCount
  rw [hset]

/-- A coset with at most one involution contains no ordered pair of distinct commuting
involutions. -/
theorem cosetPairCount_eq_zero_of_ncard_le_one {Hh : Subgroup G} [Finite G] {y : G}
    (h1 : (cosetInvolSet Hh y).ncard ≤ 1) : cosetPairCount Hh y = 0 := by
  have hsub : ∀ a ∈ cosetInvolSet Hh y, ∀ b ∈ cosetInvolSet Hh y, a = b := by
    rw [← Set.ncard_le_one]
    exact h1
  unfold cosetPairCount
  have hempty : {p : G × G | p.1 ∈ cosetInvolSet Hh y ∧ p.2 ∈ cosetInvolSet Hh y ∧
        p.1 ≠ p.2 ∧ p.1 * p.2 = p.2 * p.1} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro ⟨p1, p2⟩ ⟨hp1, hp2, hne, -⟩
    exact hne (hsub p1 hp1 p2 hp2)
  rw [hempty, Set.ncard_empty]

/-- A coset whose involution count is positive contains an involution: the involutions of `y Hh`
are exactly the elements counted by `cosetInvCount Hh y`. -/
theorem exists_involution_of_cosetInvCount_pos {Hh : Subgroup G} [Finite G] {y : G}
    (h : 0 < cosetInvCount Hh y) : ∃ z : G, orderOf z = 2 ∧ y⁻¹ * z ∈ Hh := by
  have hpos : ({z : G | orderOf z = 2 ∧ y⁻¹ * z ∈ Hh} : Set G).Nonempty := by
    rw [← Set.ncard_pos]
    exact h
  obtain ⟨z, hz⟩ := hpos
  exact ⟨z, hz.1, hz.2⟩

end Helpers

theorem CosetPairCountValue (G : Type) [Group G] [Finite G] (Hh : Subgroup G)
    (hLe4 : ∀ y : G, orderOf y = 2 → y ∉ Hh → Work.GW2.cosetInvCount Hh y ≤ 4)
    (hFour : ∀ y : G, orderOf y = 2 → y ∉ Hh → Work.GW2.cosetInvCount Hh y = 4 →
      Work.CORE3.cosetPairCount Hh y = 6)
    (c : G ⧸ Hh) (hc : c ≠ ((1 : G) : G ⧸ Hh)) :
    Work.CORE3.cosetPairCount Hh (Quotient.out c) =
      (if Work.GW2.cosetInvCount Hh (Quotient.out c) = 2 then 2
        else if Work.GW2.cosetInvCount Hh (Quotient.out c) = 4 then 6 else 0) := by
  have hyH : Quotient.out c ∉ Hh := quotient_out_notMem (Hh := Hh) hc
  by_cases h0 : Work.GW2.cosetInvCount Hh (Quotient.out c) = 0
  · -- The coset contains no involution: both sides vanish.
    rw [cosetPairCount_eq_zero_of_cosetInvCount_le_one Hh (by omega),
      ite_eq_right (by omega : ¬ (Work.GW2.cosetInvCount Hh (Quotient.out c) = 2)),
      ite_eq_right (by omega : ¬ (Work.GW2.cosetInvCount Hh (Quotient.out c) = 4))]
  · -- The coset contains an involution `z`; replace the representative by it.
    obtain ⟨z, hz2, hyz⟩ :=
      exists_involution_of_cosetInvCount_pos (Hh := Hh) (Nat.pos_of_ne_zero h0)
    have hzH : z ∉ Hh := by
      intro hzh
      apply hyH
      have h1 : z⁻¹ * Quotient.out c ∈ Hh := by
        have h2 : ((Quotient.out c)⁻¹ * z)⁻¹ ∈ Hh := Hh.inv_mem hyz
        rwa [show ((Quotient.out c)⁻¹ * z)⁻¹ = z⁻¹ * Quotient.out c from by group] at h2
      have hEq : Quotient.out c = z * (z⁻¹ * Quotient.out c) := by group
      rw [hEq]
      exact Hh.mul_mem hzh h1
    rw [cosetPairCount_congr (Hh := Hh) (x := Quotient.out c) (y := z) hyz]
    simp only [cosetInvCount_congr Hh hyz]
    exact CosetPairCountValueOfInvolution G Hh hLe4 hFour z hz2 hzH

end Work.CORE3
