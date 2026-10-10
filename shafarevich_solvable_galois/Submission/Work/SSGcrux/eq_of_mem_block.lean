import Mathlib.Tactic.Group
import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Submission.Work.SSGRoute.TPatom.blockSystemTransversal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGcrux

/-- **Two elements of the block system that lie in the same `H`-`D`-coset coincide.**

Let `H ⊴ Γ`, `D ≤ Γ`, `d ∈ D` of order exactly `f > 0` modulo `H` (spelled: `d ^ f ∈ H`,
`δ⁻¹ d ^ m ∈ H` for some `m` depending on `δ`, and `d ^ m ∉ H` for `0 < m < f`), and let
`X ⊆ Γ` be the set of block representatives of the partition of `Γ` into the blocks `x · ⟨d⟩ · H`
(`hpart`).  If `x ∈ X` and `x₀ ∈ X` and `x = a · x₀ · δ` with `a ∈ H` and `δ ∈ D`, then `x = x₀`. -/
theorem eq_of_mem_block {Γ : Type} [Group Γ] [Fintype Γ] [DecidableEq Γ]
    (H : Subgroup Γ) (hH : H.Normal) (D : Subgroup Γ) (d : ↥D) (f : ℕ) (hfpos : 0 < f)
    (hdH : ((d : Γ)) ^ f ∈ H)
    (hdgen : ∀ δ : ↥D, ∃ m : ℕ, ((δ : Γ))⁻¹ * (d : Γ) ^ m ∈ H)
    (hfmin : ∀ m : ℕ, 0 < m → m < f → ((d : Γ) ^ m) ∉ H)
    (X : Finset Γ)
    (hpart : ∀ γ : Γ, ∃! q : Γ × Fin f, q.1 ∈ X ∧ γ * (q.1 * (d : Γ) ^ (q.2 : ℕ))⁻¹ ∈ H)
    (x x₀ : Γ) (hx : x ∈ X) (hx₀ : x₀ ∈ X)
    (h : ∃ a ∈ H, ∃ δ : ↥D, x = a * x₀ * (δ : Γ)) : x = x₀ := by
  classical
  obtain ⟨a, ha, δ, hxδ⟩ := h
  obtain ⟨m, hm⟩ := hdgen δ
  -- `d` has exponent `f` modulo `H`, so we may replace `m` by `m % f`.
  have hm'lt : m % f < f := Nat.mod_lt m hfpos
  have hdec : m = f * (m / f) + m % f := (Nat.div_add_mod m f).symm
  have hpow : (d : Γ) ^ m = ((d : Γ) ^ f) ^ (m / f) * (d : Γ) ^ (m % f) := by
    conv_lhs => rw [hdec]
    rw [pow_add, pow_mul]
  have hv : ((d : Γ) ^ f) ^ (m / f) ∈ H := pow_mem hdH (m / f)
  -- Step 1: `(δ : Γ)⁻¹ * (d : Γ) ^ (m % f) ∈ H`.
  have h1 : (δ : Γ)⁻¹ * (d : Γ) ^ (m % f) ∈ H := by
    have h2 : (δ : Γ)⁻¹ * (((d : Γ) ^ f) ^ (m / f) * (d : Γ) ^ (m % f)) ∈ H := by
      rw [← hpow]; exact hm
    have hw : ((d : Γ) ^ (m % f))⁻¹ * ((d : Γ) ^ f) ^ (m / f) * (d : Γ) ^ (m % f) ∈ H := by
      simpa using hH.conj_mem (((d : Γ) ^ f) ^ (m / f)) hv ((d : Γ) ^ (m % f))⁻¹
    have heq : (δ : Γ)⁻¹ * (((d : Γ) ^ f) ^ (m / f) * (d : Γ) ^ (m % f))
        = ((δ : Γ)⁻¹ * (d : Γ) ^ (m % f))
          * (((d : Γ) ^ (m % f))⁻¹ * ((d : Γ) ^ f) ^ (m / f) * (d : Γ) ^ (m % f)) := by
      group
    rw [heq] at h2
    exact (Subgroup.mul_mem_cancel_right H hw).mp h2
  -- Step 2: `(δ : Γ) * ((d : Γ) ^ (m % f))⁻¹ ∈ H`.
  have h3 : (δ : Γ) * ((d : Γ) ^ (m % f))⁻¹ ∈ H := by
    have hconj : ((d : Γ) ^ (m % f)) * ((δ : Γ)⁻¹ * (d : Γ) ^ (m % f))⁻¹
        * ((d : Γ) ^ (m % f))⁻¹ ∈ H :=
      hH.conj_mem ((δ : Γ)⁻¹ * (d : Γ) ^ (m % f))⁻¹ (Subgroup.inv_mem H h1)
        ((d : Γ) ^ (m % f))
    have heq : ((d : Γ) ^ (m % f)) * ((δ : Γ)⁻¹ * (d : Γ) ^ (m % f))⁻¹
        * ((d : Γ) ^ (m % f))⁻¹ = (δ : Γ) * ((d : Γ) ^ (m % f))⁻¹ := by
      group
    rwa [heq] at hconj
  -- Step 3: `x` and `x₀ * d ^ (m % f)` lie in the same `H`-coset.
  have h4 : x * (x₀ * (d : Γ) ^ (m % f))⁻¹ ∈ H := by
    have hconj : x₀ * ((δ : Γ) * ((d : Γ) ^ (m % f))⁻¹) * x₀⁻¹ ∈ H := hH.conj_mem ((δ : Γ) * ((d : Γ) ^ (m % f))⁻¹) h3 x₀
    have hmul : a * (x₀ * ((δ : Γ) * ((d : Γ) ^ (m % f))⁻¹) * x₀⁻¹) ∈ H :=
      Subgroup.mul_mem H ha hconj
    have heq : a * (x₀ * ((δ : Γ) * ((d : Γ) ^ (m % f))⁻¹) * x₀⁻¹)
        = x * (x₀ * (d : Γ) ^ (m % f))⁻¹ := by
      rw [hxδ]; group
    rwa [heq] at hmul
  -- Step 4: uniqueness of the block coordinates forces `x = x₀`.
  have hA : (((x, (⟨0, hfpos⟩ : Fin f)) : Γ × Fin f).1 ∈ X ∧
      x * (((x, (⟨0, hfpos⟩ : Fin f)) : Γ × Fin f).1 *
        (d : Γ) ^ ((((x, (⟨0, hfpos⟩ : Fin f)) : Γ × Fin f).2 : ℕ)))⁻¹ ∈ H) := by
    refine ⟨hx, ?_⟩
    simp
  have hB : (((x₀, (⟨m % f, hm'lt⟩ : Fin f)) : Γ × Fin f).1 ∈ X ∧
      x * (((x₀, (⟨m % f, hm'lt⟩ : Fin f)) : Γ × Fin f).1 *
        (d : Γ) ^ ((((x₀, (⟨m % f, hm'lt⟩ : Fin f)) : Γ × Fin f).2 : ℕ)))⁻¹ ∈ H) := by
    refine ⟨hx₀, ?_⟩
    simpa using h4
  exact congrArg Prod.fst ((hpart x).unique hA hB)

end Work.SSGcrux
