import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.chi_boundary_taylor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicPoissonAux` — the boundary-flatness (aliasing) toolkit of the cubic row

The cubic row `Work.BoseBoxFock.PotCubic` compares a **lattice** sum over the box's dual
lattice `(2π/ℓ)ℤ³` (the mode side) with a **continuum** position-space word (the `q3lowWord`
side).  Each Poisson/periodisation step of that comparison produces, besides the wanted
`d = 0` image, the *aliasing images* `d ≠ 0`.

Geometrically an aliasing image can only contribute when two points of the box are separated by
(nearly) a lattice vector `ℓ·v`, `‖v‖ ≥ 1`, within the range `ρ` of the potential — i.e. when
both points sit within `ρ` of the boundary of the bump's support `ball (0, ℓ/2)`.  The corpus bump
`Submission.BoseGases.chi` is **flat to all orders** at that boundary
(`Work.BoseFixB1.chi_boundary_taylor`), so each of the two factors contributes a superpolynomially
small `(ρ/ℓ)^N`: the aliasing images are killed.

This module contains exactly that geometric input, state-free and in the form in which the four
channels of the row use it:

* `chi_le_max_dist` — the flatness bound in the form `chi z ≤ C·(max 0 (1/2 − ‖z‖))^N`
  (the `max` removes the support hypothesis of `chi_boundary_taylor`);
* `half_sub_norm_le_of_alias` — the geometry: under the aliasing condition both `y` and `u` are
  within `ρ` of the boundary of `ball (ℓ/2)`;
* `chi_le_of_alias` (one factor) and `chi_mul_chi_le_of_alias` (two factors, channel (a)).

`κ`, the box side, the mode family and the state play no role here; the row's assembly applies
these to the `χ_Λ`-weighted integrands of its four channels.
-/

noncomputable section

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- **The flatness bound with the support condition removed.**  For every `N` there is `C ≥ 0`
with `chi z ≤ C·(max 0 (1/2 − ‖z‖))^N` for all `z`: inside the ball this is
`Work.BoseFixB1.chi_boundary_taylor`, outside it `chi` vanishes
(`Submission.BoseGases.chi_eq_zero_of_norm_gt`). -/
theorem chi_le_max_dist (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Ω,
      Submission.BoseGases.chi z ≤ C * (max 0 ((1 / 2 : ℝ) - ‖z‖)) ^ N := by
  obtain ⟨C, hCpos, hC⟩ := Work.BoseFixB1.chi_boundary_taylor N
  refine ⟨C, le_of_lt hCpos, fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ 1 / 2
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 / 2 - ‖z‖)]
    exact hC z hz
  · have h0 : Submission.BoseGases.chi z = 0 :=
      Submission.BoseGases.chi_eq_zero_of_norm_gt z (lt_of_not_ge hz)
    rw [h0]
    exact mul_nonneg (le_of_lt hCpos) (pow_nonneg (le_max_left _ _) N)

/-- **The aliasing geometry.**  If `y` and `u` both lie in the ball of radius `ℓ/2`, `‖v‖ ≥ 1`
and `‖y - u + ℓ•v‖ ≤ ρ`, then **both** `y` and `u` are within `ρ` of the boundary of that ball:
`ℓ/2 - ‖y‖ ≤ ρ` and `ℓ/2 - ‖u‖ ≤ ρ`.

Indeed `ℓ•v = (y - u + ℓ•v) + (u - y)` gives `ℓ‖v‖ ≤ ρ + ‖y‖ + ‖u‖`, and combining this with
`‖v‖ ≥ 1`, `‖y‖ ≤ ℓ/2` gives `ℓ/2 - ‖u‖ ≤ ρ`, while `‖u‖ ≤ ℓ/2` gives `ℓ/2 - ‖y‖ ≤ ρ`. -/
theorem half_sub_norm_le_of_alias {ℓ ρ : ℝ} (hℓ : 0 < ℓ) (hρ : 0 ≤ ρ) {v y u : Ω}
    (hv : 1 ≤ ‖v‖) (hy : ‖y‖ ≤ ℓ / 2) (hu : ‖u‖ ≤ ℓ / 2)
    (halias : ‖y - u + ℓ • v‖ ≤ ρ) :
    ℓ / 2 - ‖y‖ ≤ ρ ∧ ℓ / 2 - ‖u‖ ≤ ρ := by
  have h1 : ‖ℓ • v‖ ≤ ‖y - u + ℓ • v‖ + (‖y‖ + ‖u‖) := by
    have h2 : (y - u + ℓ • v) - (y - u) = ℓ • v := by abel
    calc ‖ℓ • v‖ = ‖(y - u + ℓ • v) - (y - u)‖ := by rw [h2]
      _ ≤ ‖y - u + ℓ • v‖ + ‖y - u‖ := norm_sub_le _ _
      _ ≤ ‖y - u + ℓ • v‖ + (‖y‖ + ‖u‖) := by
            have h3 := norm_sub_le y u
            linarith
  have h4 : ‖ℓ • v‖ = ℓ * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg hℓ.le]
  have hcore : ℓ ≤ ρ + ‖y‖ + ‖u‖ := by
    have : ℓ * 1 ≤ ℓ * ‖v‖ := mul_le_mul_of_nonneg_left hv hℓ.le
    linarith [h1, h4]
  constructor <;> linarith

/-- **The aliasing geometry, one factor.**  Under the hypotheses of `half_sub_norm_le_of_alias`
the flatness of `chi` at the boundary of `ball (ℓ/2)` gives `chi (ℓ⁻¹ • y) ≤ C·(ρ/ℓ)^N` (and the
same with `y ↦ u`). -/
theorem chi_le_of_alias (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃ℓ ρ : ℝ⦄, 0 < ℓ → 0 ≤ ρ → ∀ ⦃v : Ω⦄, 1 ≤ ‖v‖ →
      ∀ ⦃y u : Ω⦄, ‖y‖ ≤ ℓ / 2 → ‖u‖ ≤ ℓ / 2 → ‖y - u + ℓ • v‖ ≤ ρ →
        Submission.BoseGases.chi (ℓ⁻¹ • y) ≤ C * (ρ / ℓ) ^ N ∧
          Submission.BoseGases.chi (ℓ⁻¹ • u) ≤ C * (ρ / ℓ) ^ N := by
  obtain ⟨C, hCnn, hC⟩ := chi_le_max_dist N
  refine ⟨C, hCnn, ?_⟩
  intro ℓ ρ hℓ hρ v hv y u hy hu halias
  obtain ⟨hdy, hdu⟩ := half_sub_norm_le_of_alias hℓ hρ hv hy hu halias
  have hscale (z : Ω) : ‖ℓ⁻¹ • z‖ = ‖z‖ / ℓ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le), inv_mul_eq_div]
  have key : ∀ z : Ω, ℓ / 2 - ‖z‖ ≤ ρ → Submission.BoseGases.chi (ℓ⁻¹ • z) ≤ C * (ρ / ℓ) ^ N := by
    intro z hz
    have hstep := hC (ℓ⁻¹ • z)
    have harg : (1 / 2 : ℝ) - ‖ℓ⁻¹ • z‖ = (ℓ / 2 - ‖z‖) / ℓ := by
      rw [hscale z]
      field_simp
    rw [harg] at hstep
    have hle : (ℓ / 2 - ‖z‖) / ℓ ≤ ρ / ℓ := div_le_div_of_nonneg_right hz hℓ.le
    have hmax : max 0 ((ℓ / 2 - ‖z‖) / ℓ) ≤ ρ / ℓ := max_le (by positivity) hle
    calc Submission.BoseGases.chi (ℓ⁻¹ • z)
        ≤ C * (max 0 ((ℓ / 2 - ‖z‖) / ℓ)) ^ N := hstep
      _ ≤ C * (ρ / ℓ) ^ N :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_left _ _) hmax N) hCnn
  exact ⟨key y hdy, key u hdu⟩

/-- **The aliasing geometry, two factors.**  Both `y` and `u` are within `ρ` of the boundary of
`ball (ℓ/2)`, so both `chi`-factors are `O((ρ/ℓ)^N)`: the product is `O((ρ/ℓ)^{2N})`. -/
theorem chi_mul_chi_le_of_alias (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃ℓ ρ : ℝ⦄, 0 < ℓ → 0 ≤ ρ → ∀ ⦃v : Ω⦄, 1 ≤ ‖v‖ →
      ∀ ⦃y u : Ω⦄, ‖y‖ ≤ ℓ / 2 → ‖u‖ ≤ ℓ / 2 → ‖y - u + ℓ • v‖ ≤ ρ →
        Submission.BoseGases.chi (ℓ⁻¹ • y) * Submission.BoseGases.chi (ℓ⁻¹ • u)
          ≤ C * (ρ / ℓ) ^ (2 * N) := by
  obtain ⟨C, hCnn, hC⟩ := chi_le_of_alias N
  refine ⟨C * C, by positivity, ?_⟩
  intro ℓ ρ hℓ hρ v hv y u hy hu halias
  obtain ⟨hy', hu'⟩ := hC hℓ hρ hv hy hu halias
  have hρℓ : 0 ≤ ρ / ℓ := div_nonneg hρ hℓ.le
  calc Submission.BoseGases.chi (ℓ⁻¹ • y) * Submission.BoseGases.chi (ℓ⁻¹ • u)
      ≤ (C * (ρ / ℓ) ^ N) * (C * (ρ / ℓ) ^ N) :=
        mul_le_mul hy' hu' (Submission.BoseGases.chi_nonneg _) (mul_nonneg hCnn (pow_nonneg hρℓ N))
    _ = C * C * (ρ / ℓ) ^ (N + N) := by ring
    _ = C * C * (ρ / ℓ) ^ (2 * N) := by rw [← two_mul]

end Work.BoseBoxFock
