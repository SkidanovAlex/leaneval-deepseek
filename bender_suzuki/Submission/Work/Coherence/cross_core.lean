import Mathlib
import Submission.Work.Coherence.irr_cfInner
import Submission.Work.Coherence.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Coherence.cross_core`

The cancellation lemma at the heart of the two-coherent-blocks argument: if two *distinct*
irreducible characters `χ₁ ≠ χ₂` and two *distinct* irreducible characters `ψ₁ ≠ ψ₂` satisfy the
2×2 signed coherence relation

`n₁ m₁ ⟪χ₁, ψ₁⟫ − n₁ m₂ ⟪χ₁, ψ₂⟫ − n₂ m₁ ⟪χ₂, ψ₁⟫ + n₂ m₂ ⟪χ₂, ψ₂⟫ = 0`

with all four coefficients `n₁, n₂, m₁, m₂` positive, then the "cross core" entry
`⟪χ₁, ψ₁⟫` already vanishes.

By `Work.Coherence.irr_cfInner` every entry of the `2 × 2` matrix `(⟪χᵢ, ψⱼ⟫)` lies in `{0, 1}`,
i.e. it is the indicator of the equality `χᵢ = ψⱼ`.  If `χ₁ = ψ₁` then two entries of the first
column already pin the matrix to a matching, so `χ₁ ≠ ψ₂` (because `ψ₁ ≠ ψ₂`) and `χ₂ ≠ ψ₁`
(because `χ₁ ≠ χ₂`); the relation then reads `n₁ m₁ + n₂ m₂ ε = 0` with `ε ∈ {0, 1}`, a sum of
non-negative terms whose first summand is strictly positive — impossible.  Hence `χ₁ ≠ ψ₁`, and
orthonormality gives `⟪χ₁, ψ₁⟫ = 0`.
-/

noncomputable section

open Classical

namespace Work.Coherence

theorem cross_core {G : Type*} [Group G] [Fintype G] {χ₁ χ₂ ψ₁ ψ₂ : G → ℂ}
    (hχ₁ : χ₁ ∈ Work.Coherence.Irr G) (hχ₂ : χ₂ ∈ Work.Coherence.Irr G)
    (hψ₁ : ψ₁ ∈ Work.Coherence.Irr G) (hψ₂ : ψ₂ ∈ Work.Coherence.Irr G)
    (hχ : χ₁ ≠ χ₂) (hψ : ψ₁ ≠ ψ₂)
    {n₁ n₂ m₁ m₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (heq : (n₁ : ℂ) * (m₁ : ℂ) * Work.Coherence.cfInner χ₁ ψ₁
        - (n₁ : ℂ) * (m₂ : ℂ) * Work.Coherence.cfInner χ₁ ψ₂
        - (n₂ : ℂ) * (m₁ : ℂ) * Work.Coherence.cfInner χ₂ ψ₁
        + (n₂ : ℂ) * (m₂ : ℂ) * Work.Coherence.cfInner χ₂ ψ₂ = 0) :
    Work.Coherence.cfInner χ₁ ψ₁ = 0 := by
  -- replace each inner product of irreducible characters by the indicator of equality
  rw [irr_cfInner hχ₁ hψ₁, irr_cfInner hχ₁ hψ₂, irr_cfInner hχ₂ hψ₁,
    irr_cfInner hχ₂ hψ₂] at heq
  rw [irr_cfInner hχ₁ hψ₁]
  by_cases h11 : χ₁ = ψ₁
  · -- the impossible case: `⟪χ₁, ψ₁⟫ = 1` forces the relation to be a positive number
    exfalso
    rw [ite_eq_left h11, ite_eq_right (fun h => hψ (h11.symm.trans h)),
      ite_eq_right (fun h => hχ (h.trans h11.symm).symm)] at heq
    by_cases h22 : χ₂ = ψ₂
    · rw [ite_eq_left h22] at heq
      simp only [mul_one, mul_zero, sub_zero] at heq
      have hbad : ((n₁ * m₁ + n₂ * m₂ : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination heq
      exact (Nat.cast_ne_zero.mpr (by positivity : (n₁ * m₁ + n₂ * m₂) ≠ 0)) hbad
    · rw [ite_eq_right h22] at heq
      simp only [mul_one, mul_zero, sub_zero, add_zero] at heq
      have hbad : ((n₁ * m₁ : ℕ) : ℂ) = 0 := by
        push_cast
        linear_combination heq
      exact (Nat.cast_ne_zero.mpr (by positivity : (n₁ * m₁) ≠ 0)) hbad
  · -- the surviving case: `χ₁ ≠ ψ₁`
    rw [ite_eq_right h11]

end Work.Coherence
