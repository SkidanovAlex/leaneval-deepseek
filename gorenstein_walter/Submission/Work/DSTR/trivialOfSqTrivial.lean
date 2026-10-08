import Mathlib

namespace Work.DSTR

theorem trivialOfSqTrivial {F : Type*} [Group F] {D : Subgroup F} [D.Normal] (ξ : MulAut F)
    (hξ2 : ∀ x : F, ξ (ξ x) * x⁻¹ ∈ D) (hodd : Odd (orderOf ξ)) :
    ∀ x : F, ξ x * x⁻¹ ∈ D := by
  -- Since `orderOf ξ` is odd, `ξ` is a positive power of `ξ ^ 2`, namely
  -- `ξ = (ξ ^ 2) ^ (m + 1)` when `orderOf ξ = 2 * m + 1`.
  -- So it suffices to show that every positive even power of `ξ` moves each
  -- element `x` only by an element of `D`.
  have hiter : ∀ k : ℕ, ∀ x : F, (ξ ^ (2 * k)) x * x⁻¹ ∈ D := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      -- `(ξ ^ (2 * (k+1))) x = ξ (ξ ((ξ ^ (2 * k)) x))`
      have hz : (ξ ^ (2 * (k + 1))) x = ξ (ξ ((ξ ^ (2 * k)) x)) := by
        have h2k : 2 * (k + 1) = 2 + 2 * k := by ring
        rw [h2k, pow_add]
        simp [pow_two, MulAut.mul_apply]
      rw [hz]
      -- The element `y = (ξ ^ (2 * k)) x` satisfies `ξ (ξ y) ≡ y (mod D)`
      -- by `hξ2` and `y ≡ x (mod D)` by the inductive hypothesis.
      have h1 : ξ (ξ ((ξ ^ (2 * k)) x)) * ((ξ ^ (2 * k)) x)⁻¹ ∈ D := hξ2 _
      have h2 : (ξ ^ (2 * k)) x * x⁻¹ ∈ D := ih x
      have heq : ξ (ξ ((ξ ^ (2 * k)) x)) * x⁻¹
          = (ξ (ξ ((ξ ^ (2 * k)) x)) * ((ξ ^ (2 * k)) x)⁻¹)
            * ((ξ ^ (2 * k)) x * x⁻¹) := by
        group
      rw [heq]
      exact D.mul_mem h1 h2
  obtain ⟨k, hk⟩ := hodd
  have hpow : ξ ^ (2 * (k + 1)) = ξ := by
    have h1 : 2 * (k + 1) = orderOf ξ + 1 := by omega
    rw [h1, pow_succ, pow_orderOf_eq_one, one_mul]
  intro x
  have h := hiter (k + 1) x
  rwa [hpow] at h

end Work.DSTR
