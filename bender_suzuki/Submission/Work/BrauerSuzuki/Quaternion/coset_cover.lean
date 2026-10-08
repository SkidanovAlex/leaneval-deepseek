import Mathlib
import Submission.Work.BrauerSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

open Work.BrauerSuzuki

/-- In a generalized quaternion group `d : GenQuaternionData P`, the cosets of the cyclic
subgroup `A = ⟨τ⟩` are covered by `A` and `ρ · A`:  every element of `P` lies in `A` or in
the coset `ρ A`.

Proof:  the relations `ρ τ ρ⁻¹ = τ⁻¹` and `ρ ^ 2 = τ ^ (2 ^ (n-1)) ∈ A` show that the set
`A ∪ ρ · A` is closed under multiplication and inversion (it contains `1`), hence is a
subgroup `K` of `P`.  Since `τ ∈ K` and `ρ = ρ · 1 ∈ K` and `P = ⟨τ, ρ⟩`, we get `K = P`. -/
theorem coset_cover {P : Type*} [Group P]
    (d : Work.BrauerSuzuki.GenQuaternionData P) (g : P) :
    g ∈ Subgroup.zpowers d.tau ∨ ∃ h ∈ Subgroup.zpowers d.tau, g = d.rho * h := by
  let A : Subgroup P := Subgroup.zpowers d.tau
  have hA : ∀ x : P, x ∈ A ↔ ∃ z : ℤ, d.tau ^ z = x := fun x => Subgroup.mem_zpowers_iff
  -- conjugation by `ρ` inverts `τ`, hence inverts every power of `τ`
  have hconj : ∀ z : ℤ, d.rho * d.tau ^ z * d.rho⁻¹ = d.tau ^ (-z) := by
    intro z
    have h1 : (MulAut.conj d.rho) d.tau = d.tau⁻¹ := by
      rw [MulAut.conj_apply]; exact d.rho_conj
    have h2 : (MulAut.conj d.rho) (d.tau ^ z) = d.tau ^ (-z) := by
      rw [map_zpow, h1, inv_zpow, zpow_neg]
    rwa [MulAut.conj_apply] at h2
  -- `τ ^ z * ρ = ρ * τ ^ (-z)`
  have hcomm : ∀ z : ℤ, d.tau ^ z * d.rho = d.rho * d.tau ^ (-z) := by
    intro z
    have h := hconj (-z)
    have h3 : d.rho * d.tau ^ (-z) = d.tau ^ z * d.rho := by
      calc d.rho * d.tau ^ (-z) = d.rho * d.tau ^ (-z) * d.rho⁻¹ * d.rho := by group
        _ = d.tau ^ z * d.rho := by rw [h, neg_neg]
    rw [← h3]
  have hrho2 : d.rho ^ 2 = d.tau ^ ((2 ^ (d.n - 1) : ℕ) : ℤ) := by
    rw [d.rho_sq, zpow_natCast]
  have hrho2A : d.rho ^ 2 ∈ A := by
    rw [hrho2]; exact A.zpow_mem (Subgroup.mem_zpowers d.tau) _
  have hrho_inv : d.rho⁻¹ = d.rho * (d.rho ^ 2)⁻¹ := by group
  have hconjA : ∀ a : P, a ∈ A → d.rho * a * d.rho⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨i, hi⟩ := (hA a).mp ha
    rw [← hi, hconj i, zpow_neg]
  -- the set `A ∪ ρ · A` is a subgroup
  let K : Subgroup P :=
  { carrier := {x | x ∈ A ∨ ∃ h ∈ A, x = d.rho * h}
    one_mem' := Or.inl A.one_mem
    mul_mem' := by
      intro x y hx hy
      rcases hx with hx | ⟨a, ha, rfl⟩
      · rcases hy with hy | ⟨b, hb, rfl⟩
        · exact Or.inl (A.mul_mem hx hy)
        · obtain ⟨i, hi⟩ := (hA x).mp hx
          refine Or.inr ⟨d.tau ^ (-i) * b,
            A.mul_mem (A.zpow_mem (Subgroup.mem_zpowers d.tau) (-i)) hb, ?_⟩
          rw [← hi, ← mul_assoc, hcomm i, mul_assoc]
      · rcases hy with hy | ⟨b, hb, rfl⟩
        · exact Or.inr ⟨a * y, A.mul_mem ha hy, by rw [mul_assoc]⟩
        · refine Or.inl ?_
          rw [show (d.rho * a) * (d.rho * b) = a⁻¹ * d.rho ^ 2 * b from by
                rw [← hconjA a ha]; group]
          exact A.mul_mem (A.mul_mem (A.inv_mem ha) hrho2A) hb
    inv_mem' := by
      intro x hx
      rcases hx with hx | ⟨a, ha, rfl⟩
      · exact Or.inl (A.inv_mem hx)
      · refine Or.inr ⟨a * (d.rho ^ 2)⁻¹, A.mul_mem ha (A.inv_mem hrho2A), ?_⟩
        rw [mul_inv_rev, hrho_inv, ← mul_assoc,
            show a⁻¹ * d.rho = d.rho * a from by rw [← hconjA a ha]; group, mul_assoc] }
  have hτK : d.tau ∈ K := Or.inl (Subgroup.mem_zpowers d.tau)
  have hρK : d.rho ∈ K := Or.inr ⟨1, A.one_mem, by rw [mul_one]⟩
  have hclosure : Subgroup.closure ({d.tau, d.rho} : Set P) ≤ K := by
    rw [Subgroup.closure_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hτK
    · exact hρK
  have hg : g ∈ K := hclosure (by rw [d.closure_eq_top]; exact Subgroup.mem_top g)
  rcases hg with hg | ⟨h, hh, hgh⟩
  · exact Or.inl hg
  · exact Or.inr ⟨h, hh, hgh⟩

end Work.BrauerSuzuki.Quaternion
