import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_mem_or

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

/-- Conjugation by `rho` inverts powers of `tau`. -/
private lemma gq_conj {P : Type*} [Group P] (d : Work.BrauerSuzuki.GenQuaternionData P) (z : ℤ) :
    d.rho * d.tau ^ z * d.rho⁻¹ = d.tau ^ (-z) := by
  rw [← conj_zpow (a := d.rho) (b := d.tau) (i := z), d.rho_conj, inv_zpow']

/-- `rho` moves across powers of `tau`, up to inverting the exponent. -/
private lemma gq_move {P : Type*} [Group P] (d : Work.BrauerSuzuki.GenQuaternionData P) (z : ℤ) :
    d.rho * d.tau ^ z = d.tau ^ (-z) * d.rho := by
  rw [← gq_conj d z, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]

/-- `rho` moves across powers of `tau` (other orientation). -/
private lemma gq_move' {P : Type*} [Group P] (d : Work.BrauerSuzuki.GenQuaternionData P) (z : ℤ) :
    d.tau ^ z * d.rho = d.rho * d.tau ^ (-z) := by
  have h : d.rho * d.tau ^ (-z) = d.tau ^ z * d.rho := by
    rw [gq_move d (-z), neg_neg]
  rw [← h]

/-- `rho ^ 2` is the central involution, as a `zpow`. -/
private lemma gq_rho_sq {P : Type*} [Group P] (d : Work.BrauerSuzuki.GenQuaternionData P) :
    d.rho * d.rho = d.tau ^ ((2 ^ (d.n - 1) : ℕ) : ℤ) := by
  rw [← pow_two, d.rho_sq, zpow_natCast]

/-- The inverse of `rho` is again of the normal form `rho * tau ^ k`. -/
private lemma gq_rho_inv {P : Type*} [Group P] (d : Work.BrauerSuzuki.GenQuaternionData P) :
    d.rho⁻¹ = d.rho * d.tau ^ (-((2 ^ (d.n - 1) : ℕ) : ℤ)) := by
  have h2 : d.rho⁻¹ * d.tau ^ ((2 ^ (d.n - 1) : ℕ) : ℤ) = d.rho := by
    rw [← gq_rho_sq d, ← mul_assoc, inv_mul_cancel, one_mul]
  have h3 : d.rho⁻¹ = (d.rho⁻¹ * d.tau ^ ((2 ^ (d.n - 1) : ℕ) : ℤ)) *
      d.tau ^ (-((2 ^ (d.n - 1) : ℕ) : ℤ)) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [h3, h2]

/-- In a generalized quaternion group `d : GenQuaternionData P`, any element outside the cyclic
subgroup `⟨tau⟩` has square the central involution `tau ^ (2 ^ (n-1))`.  Follows from the normal
form together with
`(rho * tau^i) * (rho * tau^i) = (rho * tau^i * rho⁻¹) * (rho * rho) * tau^i
= tau ^ (-i) * tau ^ (2 ^ (n-1)) * tau ^ i = tau ^ (2 ^ (n-1))`. -/
theorem genQuaternionData_sq_eq_of_notMem (P : Type*) [Group P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) {g : P}
    (hg : g ∉ Subgroup.zpowers d.tau) : g ^ 2 = d.tau ^ (2 ^ (d.n - 1)) := by
  have key : ∀ x ∈ Subgroup.closure ({d.tau, d.rho} : Set P),
      x ∈ Subgroup.zpowers d.tau ∨ ∃ z : ℤ, x = d.rho * d.tau ^ z := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact Or.inl (Subgroup.mem_zpowers d.tau)
        · exact Or.inr ⟨0, by rw [zpow_zero, mul_one]⟩
    | one => exact Or.inl (Subgroup.one_mem _)
    | mul y z _ _ ihy ihz =>
        rcases ihy with hy | ⟨p, hp⟩
        · obtain ⟨p, hp⟩ := Subgroup.mem_zpowers_iff.mp hy
          rcases ihz with hz | ⟨q, hq⟩
          · obtain ⟨q, hq⟩ := Subgroup.mem_zpowers_iff.mp hz
            rw [← hp, ← hq, ← zpow_add]
            exact Or.inl (Subgroup.mem_zpowers_iff.mpr ⟨p + q, rfl⟩)
          · rw [← hp, hq]
            exact Or.inr ⟨-p + q, by rw [← mul_assoc, gq_move' d p, mul_assoc, ← zpow_add]⟩
        · rcases ihz with hz | ⟨q, hq⟩
          · obtain ⟨q, hq⟩ := Subgroup.mem_zpowers_iff.mp hz
            rw [hp, ← hq, mul_assoc, ← zpow_add]
            exact Or.inr ⟨p + q, rfl⟩
          · rw [hp, hq]
            exact Or.inl (by
              rw [show (d.rho * d.tau ^ p) * (d.rho * d.tau ^ q)
                    = (d.rho * d.tau ^ p * d.rho⁻¹) * (d.rho * d.rho) * d.tau ^ q from by group,
                  gq_conj d p, gq_rho_sq d, ← zpow_add, ← zpow_add]
              exact Subgroup.mem_zpowers_iff.mpr ⟨-p + ((2 ^ (d.n - 1) : ℕ) : ℤ) + q, rfl⟩)
    | inv y _ ihy =>
        rcases ihy with hy | ⟨p, hp⟩
        · obtain ⟨p, hp⟩ := Subgroup.mem_zpowers_iff.mp hy
          rw [← hp]
          exact Or.inl (Subgroup.mem_zpowers_iff.mpr ⟨-p, by rw [← zpow_neg]⟩)
        · rw [hp]
          exact Or.inr ⟨p - ((2 ^ (d.n - 1) : ℕ) : ℤ), by
            rw [mul_inv_rev, ← zpow_neg, gq_rho_inv d, ← mul_assoc, gq_move' d (-p), neg_neg,
                mul_assoc, ← zpow_add, sub_eq_add_neg]⟩
  have hg' : ∃ z : ℤ, g = d.rho * d.tau ^ z := by
    rcases key g (by rw [d.closure_eq_top]; exact Subgroup.mem_top g) with h | h
    · exact absurd h hg
    · exact h
  obtain ⟨z, hz⟩ := hg'
  rw [hz, pow_two]
  calc (d.rho * d.tau ^ z) * (d.rho * d.tau ^ z)
      = (d.rho * d.tau ^ z * d.rho⁻¹) * (d.rho * d.rho) * d.tau ^ z := by group
    _ = d.tau ^ (-z) * d.tau ^ ((2 ^ (d.n - 1) : ℕ) : ℤ) * d.tau ^ z := by
          rw [gq_conj d z, gq_rho_sq d]
    _ = d.tau ^ ((2 ^ (d.n - 1) : ℕ) : ℤ) := by
          rw [← zpow_add, ← zpow_add]
          congr 1
          ring
    _ = d.tau ^ (2 ^ (d.n - 1)) := by rw [zpow_natCast]

end Work.BrauerSuzuki.Quaternion
