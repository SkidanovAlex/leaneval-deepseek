import Mathlib
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Auxiliary lemmas for Peterfalvi I, Appendix II (1)

Two general, self-contained lemmas used in the proof of `app2_1`:

* `not_dvd_index_of_not_dvd_relIndex_normalizer`: a `p`-subgroup of a finite group which is a
  Sylow `p`-subgroup of its own normalizer is a Sylow `p`-subgroup of the whole group.
* `relIndex_normalizer_inf_stabilizer_le_two`: if a subgroup `Q` has exactly the two fixed
  points `a ≠ b` on a set `E`, then the stabiliser of `a` has index at most `2` inside the
  normalizer of `Q`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.DoubleTransitivity.App2

open Work.DoubleTransitivity

/-- A `p`-subgroup `Q` of a finite group `G` which is a Sylow `p`-subgroup of its own normalizer
is a Sylow `p`-subgroup of `G`.  Equivalently, if `p` does not divide the index of `Q` in its
normalizer, then `p` does not divide the index of `Q` in `G`. -/
theorem not_dvd_index_of_not_dvd_relIndex_normalizer {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {Q : Subgroup G} (hQ : IsPGroup p Q)
    (hN : ¬ p ∣ Q.relIndex (Subgroup.normalizer (Q : Set G))) :
    ¬ p ∣ Q.index := by
  intro hp
  obtain ⟨P, hQP⟩ := hQ.exists_le_sylow
  have hne : Q ≠ (P : Subgroup G) := by
    intro heq
    rw [heq] at hp
    exact Sylow.not_dvd_index P hp
  have hproper : Q.subgroupOf (P : Subgroup G) ≠ ⊤ := by
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact hne (le_antisymm hQP h)
  haveI : Group.IsNilpotent ↥(P : Subgroup G) := (P : Sylow p G).isPGroup'.isNilpotent
  have hnc : NormalizerCondition ↥(P : Subgroup G) := Group.normalizerCondition_of_isNilpotent
  have hlt' : Q.subgroupOf (P : Subgroup G) <
      Subgroup.normalizer (Q.subgroupOf (P : Subgroup G) : Set ↥(P : Subgroup G)) :=
    hnc _ (lt_of_le_of_ne le_top hproper)
  obtain ⟨-, x, hxB, hxA⟩ := SetLike.lt_iff_le_and_exists.mp hlt'
  rw [← Subgroup.subgroupOf_normalizer_eq hQP] at hxB
  have hxQ : ((x : ↥(P : Subgroup G)) : G) ∈ Subgroup.normalizer (Q : Set G) := hxB
  have hxnotQ : ((x : ↥(P : Subgroup G)) : G) ∉ Q := fun h =>
    hxA (Subgroup.mem_subgroupOf.mpr h)
  set R : Subgroup G := Subgroup.normalizer (Q : Set G) ⊓ (P : Subgroup G) with hR
  have hQR : Q ≤ R := le_inf Subgroup.le_normalizer hQP
  have hRlN : R ≤ Subgroup.normalizer (Q : Set G) := inf_le_left
  have hxR : ((x : ↥(P : Subgroup G)) : G) ∈ R := ⟨hxQ, x.2⟩
  have hRpg : IsPGroup p R := ((P : Sylow p G).isPGroup').to_le inf_le_right
  have hltR : Q < R := lt_of_le_of_ne hQR (fun heq => hxnotQ (heq ▸ hxR))
  have hdiv : p ∣ Q.relIndex R := by
    have hidx : Q.relIndex R = (Q.subgroupOf R).index := rfl
    rw [hidx]
    obtain ⟨n, hn⟩ := hRpg.index (Q.subgroupOf R)
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      have : Q.subgroupOf R = ⊤ := Subgroup.index_eq_one.mp hn
      rw [Subgroup.subgroupOf_eq_top] at this
      exact hltR.ne (le_antisymm hQR this)
    rw [hn]
    exact dvd_pow_self p hn0
  have : p ∣ Q.relIndex (Subgroup.normalizer (Q : Set G)) := by
    rw [← Subgroup.relIndex_mul_relIndex Q R (Subgroup.normalizer (Q : Set G)) hQR hRlN]
    exact dvd_mul_of_dvd_left hdiv _
  exact hN this

/-- If `Q` is a subgroup of `X` whose set of fixed points on `E` is exactly `{a, b}` with
`a ≠ b`, then the stabiliser of `a` has index at most `2` in the normalizer of `Q`. -/
theorem relIndex_normalizer_inf_stabilizer_le_two {X E : Type} [Group X] [MulAction X E]
    {Q : Subgroup X} {a b : E} (hab : a ≠ b) (hfix : fixedBySub Q = {a, b}) :
    (Subgroup.normalizer (Q : Set X) ⊓ MulAction.stabilizer X a).relIndex
      (Subgroup.normalizer (Q : Set X)) ≤ 2 := by
  set Y : Subgroup X := Subgroup.normalizer (Q : Set X) with hY
  set S : Subgroup X := MulAction.stabilizer X a with hS
  have ha_mem : a ∈ fixedBySub Q := by rw [hfix]; simp
  have hpres : ∀ y : X, y ∈ Y → ∀ c : E, c ∈ fixedBySub Q → y • c ∈ fixedBySub Q := by
    intro y hy c hc m hm
    have hcomm : y⁻¹ * m * y ∈ Q := ((Subgroup.mem_normalizer_iff''.mp hy) m).mp hm
    calc m • (y • c) = (m * y) • c := (mul_smul m y c).symm
      _ = (y * (y⁻¹ * m * y)) • c := by
            rw [show y * (y⁻¹ * m * y) = m * y from by group]
      _ = y • ((y⁻¹ * m * y) • c) := mul_smul y _ c
      _ = y • c := by rw [hc _ hcomm]
  have horbit_sub : (MulAction.orbit ↥Y a : Set E) ⊆ ({a, b} : Set E) := by
    rw [← hfix]
    intro c hc
    obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.mp hc
    rw [← hy]
    exact hpres y y.2 a ha_mem
  have hstab : MulAction.stabilizer (↥Y) a = S.subgroupOf Y := by
    ext y
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, hS, MulAction.mem_stabilizer_iff]
    exact Iff.rfl
  calc (Y ⊓ S).relIndex Y = (S.subgroupOf Y).index := by
        show ((Y ⊓ S).subgroupOf Y).index = _
        rw [Subgroup.inf_subgroupOf_left]
    _ = (MulAction.stabilizer (↥Y) a).index := by rw [hstab]
    _ = (MulAction.orbit (↥Y) a).ncard := MulAction.index_stabilizer (↥Y) a
    _ ≤ ({a, b} : Set E).ncard := Set.ncard_le_ncard horbit_sub
    _ = 2 := Set.ncard_pair hab

end Work.DoubleTransitivity.App2
