import Mathlib
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.principalChar_mem_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

/-!
The two "global" forms of the first orthogonality relation, read off from
`Work.CharCore.irr_orthonormal` (the normalised inner product of distinct irreducible
characters vanishes, and an irreducible character has inner product `1` with itself).
-/

/-- A non-principal irreducible character has vanishing sum over the group: this is the
orthogonality relation `⟨χ, 1⟩ = 0`, the principal character `1` being irreducible by
`Work.CharCore.principalChar_mem_Irr`. -/
theorem sum_apply_eq_zero_of_mem_Irr_of_ne_one {G : Type*} [Group G] [Fintype G]
    {χ : G → ℂ} (hχ : χ ∈ Irr G) (hne : χ ≠ fun _ : G => (1 : ℂ)) :
    ∑ g : G, χ g = 0 := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have h := irr_orthonormal χ (fun _ : G => (1 : ℂ)) hχ principalChar_mem_Irr
  have h' : (Fintype.card G : ℂ)⁻¹ * (∑ g : G, χ g) = 0 := by
    simpa [cfInner, hne] using h
  exact (mul_eq_zero.mp h').resolve_left (inv_ne_zero hcard)

/-- The sum of `|χ g|²` over a finite group, i.e. `∑_g χ g * conj (χ g)`, equals `|G|`: the
orthogonality relation `⟨χ, χ⟩ = 1`. -/
theorem sum_mul_star_eq_card_of_mem_Irr {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Irr G) :
    ∑ g : G, χ g * starRingEnd ℂ (χ g) = (Fintype.card G : ℂ) := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have h := irr_orthonormal χ χ hχ hχ
  have h' : (Fintype.card G : ℂ)⁻¹ * (∑ g : G, χ g * starRingEnd ℂ (χ g)) = 1 := by
    simpa [cfInner] using h
  calc (∑ g : G, χ g * starRingEnd ℂ (χ g))
      = (Fintype.card G : ℂ) *
          ((Fintype.card G : ℂ)⁻¹ * (∑ g : G, χ g * starRingEnd ℂ (χ g))) :=
        (mul_inv_cancel_left₀ hcard _).symm
    _ = (Fintype.card G : ℂ) * 1 := by rw [h']
    _ = (Fintype.card G : ℂ) := mul_one _

/-- **Step 9, global sums.** An irreducible complex character `χ` of a finite group `G` which
is not the principal character, and whose values are (the images of) integers `a g`, satisfies
`∑_g a g = 0` (orthogonality against the principal character) and `∑_g (a g)² = |G|` (the
norm of `χ` is `1`; since the values are real integers, `|χ g|² = (a g)²`). -/
theorem step9_global_sums {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} {a : G → ℤ}
    (hIrr : χ ∈ Work.CharCore.Irr G) (hne : χ ≠ (fun _ => (1 : ℂ)))
    (ha : ∀ g : G, χ g = (a g : ℂ)) :
    (∑ g : G, a g = 0) ∧ (∑ g : G, (a g) ^ 2 = Fintype.card G) := by
  -- the values of `χ` are fixed by complex conjugation, being integer valued
  have hconj : ∀ g : G, starRingEnd ℂ (χ g) = χ g := by
    intro g
    rw [ha g]
    simp
  have h0 : ∑ g : G, χ g = 0 := sum_apply_eq_zero_of_mem_Irr_of_ne_one hIrr hne
  have hS : ∑ g : G, χ g * starRingEnd ℂ (χ g) = (Fintype.card G : ℂ) :=
    sum_mul_star_eq_card_of_mem_Irr hIrr
  constructor
  · apply Int.cast_injective (α := ℂ)
    push_cast
    simpa [ha] using h0
  · apply Int.cast_injective (α := ℂ)
    push_cast
    calc ∑ g : G, ((a g : ℤ) : ℂ) ^ 2
        = ∑ g : G, χ g * starRingEnd ℂ (χ g) := by
          apply Finset.sum_congr rfl
          intro g _
          rw [hconj g, ha g]
          ring
      _ = (Fintype.card G : ℂ) := hS

end Work.CharCore
