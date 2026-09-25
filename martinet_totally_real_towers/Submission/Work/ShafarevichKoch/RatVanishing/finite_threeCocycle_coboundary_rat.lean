/-
Copyright: the martinet_totally_real_towers team.

# Every `3`-cocycle of a finite group with values in `ℚ` is a coboundary

**Module** `Submission.Work.ShafarevichKoch.RatVanishing.finite_threeCocycle_coboundary_rat`.

Let `Q` be a finite group and `c : Q → Q → Q → ℚ` an inhomogeneous `3`-cocycle for the trivial
action of `Q` on `ℚ`:

`c τ ρ υ - c (σ * τ) ρ υ + c σ (τ * ρ) υ - c σ τ (ρ * υ) + c σ τ ρ = 0`.

Then `c` is a coboundary: there is a `2`-cochain `x : Q → Q → ℚ` with

`x τ ρ - x (σ * τ) ρ + x σ (τ * ρ) - x σ τ = c σ τ ρ`.

Equivalently `H³(Q, ℚ) = 0`: `ℚ` is uniquely divisible, so one may average over the finite
group.  The explicit splitting is the classical one,

`x σ τ = - |Q|⁻¹ * ∑_{g : Q} c σ τ g`,

which is the exact analogue (one degree up) of `exists_coboundary_of_finite_twoCocycle_rat` in
`Submission.Work.ShafarevichKoch.RatVanishing.subsingleton_H1_H2_rat`.

The only computation is the pointwise identity obtained from the cocycle condition, after which
the summands telescope using that `g ↦ ρ * g` is a bijection of `Q`.
-/

import Mathlib

set_option linter.unusedVariables false

namespace Work.ShafarevichKoch.RatVanishing

/-- **Every `3`-cocycle of a finite group with values in `ℚ` is a coboundary.**  For a finite
group `Q` and an inhomogeneous `3`-cocycle `c` with values in `ℚ` (trivial action), the averaged
`2`-cochain `x σ τ = - |Q|⁻¹ * ∑_g c σ τ g` satisfies `δx = c`. -/
theorem finite_threeCocycle_coboundary_rat {Q : Type*} [Group Q] [Fintype Q]
    (c : Q → Q → Q → ℚ)
    (hc : ∀ σ τ ρ υ : Q, c τ ρ υ - c (σ * τ) ρ υ + c σ (τ * ρ) υ - c σ τ (ρ * υ) + c σ τ ρ = 0) :
    ∃ x : Q → Q → ℚ, ∀ σ τ ρ : Q, x τ ρ - x (σ * τ) ρ + x σ (τ * ρ) - x σ τ = c σ τ ρ := by
  classical
  -- the explicit cochain `x σ τ = -|Q|⁻¹ * ∑_g c σ τ g`
  let x : Q → Q → ℚ := fun σ τ => -((Fintype.card Q : ℚ))⁻¹ * ∑ g : Q, c σ τ g
  refine ⟨x, fun σ τ ρ => ?_⟩
  have hN : ((Fintype.card Q : ℚ)) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact (Fintype.card_pos_iff.mpr ⟨1⟩).ne'
  -- the pointwise identity coming from the cocycle condition
  have hstep : ∀ g : Q, c σ τ g - c σ (τ*ρ) g + c (σ*τ) ρ g - c τ ρ g
      = c σ τ g - c σ τ (ρ*g) + c σ τ ρ := by
    intro g
    linarith [hc σ τ ρ g]
  -- `g ↦ ρ * g` is a bijection, so the third slot may be relabelled
  have hreindex : (∑ g : Q, c σ τ (ρ*g)) = ∑ g : Q, c σ τ g :=
    Equiv.sum_comp (Equiv.mulLeft ρ) (fun g => c σ τ g)
  -- the averaged sums satisfy `S στ - S σ(τρ) + S (στ)ρ - S τρ = |Q| * c σ τ ρ`
  have hsum : (∑ g : Q, c σ τ g) - (∑ g : Q, c σ (τ*ρ) g) + (∑ g : Q, c (σ*τ) ρ g)
      - (∑ g : Q, c τ ρ g) = ((Fintype.card Q : ℚ)) * c σ τ ρ := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun g _ => hstep g), Finset.sum_add_distrib, Finset.sum_sub_distrib,
      hreindex]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hmain : ((Fintype.card Q : ℚ))⁻¹ * ((∑ g : Q, c σ τ g) - (∑ g : Q, c σ (τ*ρ) g)
      + (∑ g : Q, c (σ*τ) ρ g) - (∑ g : Q, c τ ρ g)) = c σ τ ρ := by
    rw [hsum, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  calc x τ ρ - x (σ*τ) ρ + x σ (τ*ρ) - x σ τ
      = ((Fintype.card Q : ℚ))⁻¹ * ((∑ g : Q, c σ τ g) - (∑ g : Q, c σ (τ*ρ) g)
          + (∑ g : Q, c (σ*τ) ρ g) - (∑ g : Q, c τ ρ g)) := by
        simp only [x]; ring
    _ = c σ τ ρ := hmain

end Work.ShafarevichKoch.RatVanishing
