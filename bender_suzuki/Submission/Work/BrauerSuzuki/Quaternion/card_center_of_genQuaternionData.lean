import Mathlib
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.BrauerSuzuki.Dade.sylow_conj_structure
import Submission.Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The centre of a generalized quaternion group

Let `P = ⟨τ, ρ⟩` be a generalized quaternion group in Dade's normal form
(`Work.BrauerSuzuki.GenQuaternionData`), i.e. `orderOf τ = 2 ^ n` with `n ≥ 2`,
`ρ τ ρ⁻¹ = τ⁻¹` and `ρ ^ 2 = τ ^ (2 ^ (n-1))`.  Then

  `Z(P) = ⟨τ ^ (2 ^ (n-1))⟩`

is cyclic of order `2`: the involution `z = τ ^ (2 ^ (n-1))` is the unique involution of `P`
(`genQuaternionData_basic`) and generates the centre.

The two inclusions are proved separately:

* `pow_half_mem_center`: `z ∈ Z(P)`.  `z` is an involution, so every conjugate `g z g⁻¹` of `z`
  is an involution as well and hence equals `z` (uniqueness); this is centrality.
* `center_le_zpowers_half`: `Z(P) ≤ ⟨z⟩`.  Every central element satisfies `x ^ 2 = 1`
  (`Work.BrauerSuzuki.Dade.genQuaternionData_center_sq`), and `x ^ 2 = 1` with `x ≠ 1`
  forces `orderOf x = 2`, hence `x = z` by uniqueness.

The theorem `card_center_of_genQuaternionData` is then an immediate consequence of
`Nat.card_zpowers`.
-/

namespace Work.BrauerSuzuki.Quaternion

open Work.BrauerSuzuki

/-- In a group in which `z` is the unique element of order `2`, every element squaring to `1`
is either `1` or `z`. -/
private theorem eq_one_or_eq_of_sq_eq_one {G : Type*} [Group G] {z x : G}
    (huniq : ∀ w : G, orderOf w = 2 → w = z) (hx : x ^ 2 = 1) : x = 1 ∨ x = z := by
  by_cases h1 : x = 1
  · exact Or.inl h1
  · refine Or.inr (huniq x ?_)
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h

/-- The involution `τ ^ (2 ^ (n-1))` of a generalized quaternion group is central: it is the
unique involution, so it is fixed by every conjugation. -/
private theorem pow_half_mem_center {P : Type*} [Group P] [Finite P]
    (d : GenQuaternionData P) :
    d.tau ^ (2 ^ (d.n - 1)) ∈ Subgroup.center P := by
  obtain ⟨-, -, hord, huniq, -⟩ := genQuaternionData_basic d
  rw [Subgroup.mem_center_iff]
  intro g
  have hconj : g * d.tau ^ (2 ^ (d.n - 1)) * g⁻¹ = d.tau ^ (2 ^ (d.n - 1)) := by
    refine huniq _ ?_
    rw [Work.BrauerSuzuki.Group.orderOf_conj_eq, hord]
  calc g * d.tau ^ (2 ^ (d.n - 1))
      = g * d.tau ^ (2 ^ (d.n - 1)) * g⁻¹ * g := by group
    _ = d.tau ^ (2 ^ (d.n - 1)) * g := by rw [hconj]

/-- Every central element of a generalized quaternion group is `1` or the involution
`τ ^ (2 ^ (n-1))`. -/
private theorem center_le_zpowers_half {P : Type*} [Group P] [Finite P]
    (d : GenQuaternionData P) :
    Subgroup.center P ≤ Subgroup.zpowers (d.tau ^ (2 ^ (d.n - 1))) := by
  obtain ⟨-, -, -, huniq, -⟩ := genQuaternionData_basic d
  intro x hx
  have hx2 : x ^ 2 = 1 :=
    Dade.genQuaternionData_center_sq d fun y => (Subgroup.mem_center_iff.mp hx y).symm
  rcases eq_one_or_eq_of_sq_eq_one huniq hx2 with h1 | h1
  · rw [h1]; exact Subgroup.one_mem _
  · rw [h1]; exact Subgroup.mem_zpowers _

theorem card_center_of_genQuaternionData {P : Type*} [Group P] [Finite P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) :
    Nat.card ↥(Subgroup.center P) = 2 := by
  have hz2 : orderOf (d.tau ^ (2 ^ (d.n - 1))) = 2 := (genQuaternionData_basic d).2.2.1
  have hcenter : Subgroup.center P = Subgroup.zpowers (d.tau ^ (2 ^ (d.n - 1))) :=
    le_antisymm (center_le_zpowers_half d)
      (by rw [Subgroup.zpowers_le]; exact pow_half_mem_center d)
  rw [hcenter, Nat.card_zpowers, hz2]

end Work.BrauerSuzuki.Quaternion
