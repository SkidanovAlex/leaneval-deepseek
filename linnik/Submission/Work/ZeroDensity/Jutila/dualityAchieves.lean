import Mathlib

namespace Work.ZeroDensity.Jutila

/-- **Finite-dimensional duality on `ι → ℂ` (the sup over the unit ball is attained).**

For a finite index type `ι` and `g : ι → ℂ` with `∑ i, ‖g i‖ ^ 2 > 0`, the Cauchy–Schwarz
duality between the standard norm `η ↦ (∑ i, ‖η i‖ ^ 2) ^ (1/2)` on `ι → ℂ` and the linear
functional `η ↦ ∑ i, η i * g i` is attained *inside* the unit ball: the vector
`η i = conj (g i) / √(∑ j, ‖g j‖ ^ 2)` has `∑ i, ‖η i‖ ^ 2 ≤ 1` and
`‖∑ i, η i * g i‖ ^ 2 = ∑ i, ‖g i‖ ^ 2`.  Equivalently, the operator norm of that functional
equals the `ℓ²` norm of `g` and is achieved. -/
lemma dualityAchieves {ι : Type*} [Fintype ι] (g : ι → ℂ)
    (hZ : 0 < ∑ i, ‖g i‖ ^ 2) :
    ∃ η : ι → ℂ, (∑ i, ‖η i‖ ^ 2) ≤ 1 ∧
      ‖∑ i, η i * g i‖ ^ 2 = ∑ i, ‖g i‖ ^ 2 := by
  classical
  -- The `ℓ²` mass of `g` and its square root.
  set S : ℝ := ∑ i, ‖g i‖ ^ 2 with hSdef
  have hSpos : 0 < S := hZ
  have hSnn : 0 ≤ S := le_of_lt hSpos
  have hSne : S ≠ 0 := ne_of_gt hSpos
  set r : ℝ := Real.sqrt S with hrdef
  have hrpos : 0 < r := Real.sqrt_pos.mpr hSpos
  have hr2 : r ^ 2 = S := Real.sq_sqrt hSnn
  -- Norm of the real `x` viewed in `ℂ`, for `x ≥ 0`.
  have hnormR : ∀ x : ℝ, 0 ≤ x → ‖(x : ℂ)‖ = x := by
    intro x hx
    rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs, abs_of_nonneg hx]
  -- The extremal weight.
  refine ⟨fun i => star (g i) / (r : ℂ), ?_, ?_⟩
  · -- It lies in the unit ball.
    have hterm : ∀ i, ‖star (g i) / (r : ℂ)‖ ^ 2 = ‖g i‖ ^ 2 / S := by
      intro i
      rw [norm_div, norm_star, hnormR r hrpos.le, div_pow, hr2]
    calc ∑ i, ‖star (g i) / (r : ℂ)‖ ^ 2
        = ∑ i, ‖g i‖ ^ 2 / S := Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (∑ i, ‖g i‖ ^ 2) / S := by rw [Finset.sum_div]
      _ = S / S := by rw [hSdef]
      _ = 1 := div_self hSne
      _ ≤ 1 := le_refl 1
  · -- It saturates the functional.
    have hterm_star : ∀ i, star (g i) * g i = ((‖g i‖ ^ 2 : ℝ) : ℂ) :=
      fun i => by push_cast; exact RCLike.conj_mul (g i)
    have hsumstar : ∑ i, star (g i) * g i = ((∑ i, ‖g i‖ ^ 2 : ℝ) : ℂ) := by
      calc ∑ i, star (g i) * g i
          = ∑ i, ((‖g i‖ ^ 2 : ℝ) : ℂ) := Finset.sum_congr rfl (fun i _ => hterm_star i)
        _ = ((∑ i, ‖g i‖ ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    have hsum : ∑ i, (star (g i) / (r : ℂ)) * g i = (S : ℂ) / (r : ℂ) := by
      calc ∑ i, (star (g i) / (r : ℂ)) * g i
          = ∑ i, (star (g i) * g i) / (r : ℂ) :=
              Finset.sum_congr rfl (fun i _ => div_mul_eq_mul_div _ _ _)
        _ = (∑ i, star (g i) * g i) / (r : ℂ) := by rw [Finset.sum_div]
        _ = ((∑ i, ‖g i‖ ^ 2 : ℝ) : ℂ) / (r : ℂ) := by rw [hsumstar]
        _ = (S : ℂ) / (r : ℂ) := by rw [hSdef]
    have hval : ‖(S : ℂ) / (r : ℂ)‖ ^ 2 = S := by
      rw [norm_div, hnormR S hSnn, hnormR r hrpos.le, div_pow, hr2]
      field_simp
    rw [hsum, hval, hSdef]

end Work.ZeroDensity.Jutila
