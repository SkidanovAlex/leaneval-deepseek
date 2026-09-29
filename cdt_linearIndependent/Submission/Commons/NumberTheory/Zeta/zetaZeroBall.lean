import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# Zeros of the entire completion `riemannZeta₁` form a finite set in every closed ball

`riemannZeta₁ s = 1 + (s - 1) * riemannZeta₀ s` is the entire completion of `(s - 1) · ζ(s)`
at `s = 1`.  Away from `s = 1` we have `riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s`
(`riemannZeta_eq_inv_sub_mul`), so every zero of `riemannZeta₁` is a zero of `riemannZeta`.
Since Mathlib knows the zeros of `riemannZeta` form a closed discrete set
(`Mathlib.NumberTheory.LSeries.ZetaZeros`), the zeros of `riemannZeta₁` inside the compact
closed ball `Metric.closedBall 0 R` form a finite set, hence a `Finset`.
-/

namespace Commons.NumberTheory.Zeta


theorem zetaZeroBall (R : ℝ) (hR : 0 ≤ R) :
    ∃ s : Finset ℂ,
      ∀ ρ : ℂ, ρ ∈ s ↔ ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0 := by
  classical
  have _hR_nonneg : 0 ≤ R := hR
  let Z : Set ℂ := {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ riemannZeta₁ ρ = 0}
  have hsub : Z ⊆ Metric.closedBall (0 : ℂ) R ∩ riemannZetaZeros := by
    rintro ρ ⟨hball, hζ₁⟩
    exact ⟨hball, by
      rw [mem_riemannZetaZeros]
      by_cases hρ : ρ = 1
      · subst ρ
        exfalso
        exact zero_ne_one (hζ₁.symm.trans riemannZeta₁_one)
      · rw [riemannZeta_eq_inv_sub_mul hρ]
        simp [hζ₁]⟩
  have hZfin : Z.Finite := by
    have hcomp : (Metric.closedBall (0 : ℂ) R ∩ riemannZetaZeros).Finite :=
      (isCompact_closedBall (0 : ℂ) R).inter_riemannZetaZeros_finite
    exact hcomp.subset hsub
  refine ⟨hZfin.toFinset, ?_⟩
  intro ρ
  rw [Set.Finite.mem_toFinset]
  rfl

end Commons.NumberTheory.Zeta