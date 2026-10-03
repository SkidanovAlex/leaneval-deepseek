import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.norm_exp_sub_one_sub_id_le_sharp
import Submission.Work.Pert.Lattice.two_mul_norm_alpha_le_norm_sigma
import Submission.Work.Pert.Lattice.norm_one_sub_exp_neg_two_pi_I_mul_le
import Submission.Work.Pert.Lattice.exp_neg_two_pi_I_mul_ne_one_of_lattice_pos

/-!
# PERT · `Work.Pert.lattice_dist_ge_of_tauC_le`

The lattice separation of the perturbation gates, in the `τ_f`-coordinates of Lemma A.1.5.
For a perturbation datum `(σ, u, α)` with `1 - σ u 0 = exp (2πi α)`, `‖α‖ ≤ 1/64` and
`1/2 ≤ ‖u‖ ≤ 2` on the ball of radius `rr`, every point `w` whose coordinate `τ := tauC σ α w`
lies in that ball and satisfies `‖τ‖ ≤ 5` is *away* from the lattice `α⁻¹ℤ` of `τ` (equivalently,
`α w` is at distance at least `‖α‖/20` from `ℤ`).

The mechanism is the identity

  `1 - σ / τ_f w = exp (-2πi α w)`  (`one_sub_sigma_div_tauC`, valid for `σ ≠ 0`),

read as a comparison of two first-order quantities: on the lattice itself (`α w ≈ k`) the right
side is `1 + 2πi (α w - k) + O(‖α w - k‖²)`, so `σ/τ_f w` is small; but the normalisation
`σ u 0 = 1 - exp (2πi α)` forces `‖σ‖ ≥ 2‖α‖`, so `‖σ/τ_f w‖ ≥ ‖σ‖/5 ≥ 2‖α‖/5`.  The two
estimates are incompatible as soon as `‖α w - k‖ < ‖α‖/20` (write `δ := α w - k`):

  `2‖α‖/5 ≤ ‖1 - exp (-2πi δ)‖ ≤ 2π‖δ‖ (1 + (29/48)‖δ‖) ≤ ‖α‖/3 < 2‖α‖/5`.

The three numerical ingredients are the sibling lemmas
`Work.Pert.Lattice.two_mul_norm_alpha_le_norm_sigma`,
`Work.Pert.Lattice.norm_one_sub_exp_neg_two_pi_I_mul_le` and
`Work.Pert.Lattice.exp_neg_two_pi_I_mul_ne_one_of_lattice_pos`.
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

/-- The elementary identity behind the normalisation of the gate hypotheses:
`1 - σ / τ_f w = exp (-2πi α w)` for `σ ≠ 0`.  (It fails for `σ = 0` and arbitrary `w`, whence the
hypothesis; when `exp (-2πi α w) = 1` both sides are `1`, because then `τ_f w = σ/0 = 0`.) -/
theorem one_sub_sigma_div_tauC {σ α w : ℂ} (hσ : σ ≠ 0) :
    1 - σ / tauC σ α w = Complex.exp (-(2 * Real.pi * Complex.I * α * w)) := by
  rw [tauC]
  field_simp
  ring

/-- **Lattice separation in `τ_f`-coordinates.**  If `τ_f w` lies in the ball where `u` is bounded
between `1/2` and `2`, is bounded by `5` in modulus, and `α w` is at positive distance from `ℤ`,
then that distance is at least `‖α‖/20`.

Contrapositive route, with `δ = α w - k` for an integer `k` closer than `‖α‖/20`: the identity
`1 - σ/τ_f w = exp (-2πi α w) = exp (-2πi δ)` gives `‖σ‖/‖τ_f w‖ = ‖1 - exp (-2πi δ)‖`; the left
side is at least `‖σ‖/5 ≥ 2‖α‖/5` (using `‖σ‖ ≥ 2‖α‖`, the sharp Taylor bound for `exp` at
`2πi α`, and `‖u 0‖ ≤ 2`), while the right side is at most
`2π‖δ‖ (1 + (29/48)‖δ‖) ≤ ‖α‖/3`.  Since `2/5 > 1/3`, this is absurd. -/
theorem lattice_dist_ge_of_tauC_le {rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {w : ℂ}
    (hα64 : ‖α‖ ≤ 1 / 64) (hσ : σ ≠ 0)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτ : Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (h5 : ‖Work.Pert.tauC σ α w‖ ≤ 5)
    (hd : 0 < ⨅ k : ℤ, dist (α * w) (k : ℂ)) :
    (1 / 20) * ‖α‖ ≤ ⨅ k : ℤ, dist (α * w) (k : ℂ) := by
  by_cases hα0 : α = 0
  · -- `α = 0` is immediate: the right side is an infimum of nonnegative numbers.
    rw [hα0, norm_zero, mul_zero]
    exact le_ciInf fun k => dist_nonneg
  · have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
    -- the ball containing `τ_f w` is nonempty, so `hu2` applies at `0`
    have hrr : 0 < rr := by
      have h := Metric.mem_ball.mp hτ
      linarith [dist_nonneg (x := tauC σ α w) (y := (0 : ℂ))]
    have hu0le : ‖u 0‖ ≤ 2 := (hu2 0 (Metric.mem_ball_self hrr)).2
    -- `‖σ‖` is comparable to `‖α‖` (normalisation `1 - σ u 0 = exp (2πi α)`)
    have hσlb : 2 * ‖α‖ ≤ ‖σ‖ :=
      Work.Pert.Lattice.two_mul_norm_alpha_le_norm_sigma hα64 hnorm hu0le
    -- `α w ∉ ℤ` (from `hd`), so `exp (-2πi α w) ≠ 1` and `τ_f w ≠ 0`
    have hEne : Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1 :=
      Work.Pert.Lattice.exp_neg_two_pi_I_mul_ne_one_of_lattice_pos (α := α) (w := w) hd
    have hτne : tauC σ α w ≠ 0 := by
      rw [tauC, div_ne_zero_iff]
      exact ⟨hσ, fun h => hEne (sub_eq_zero.mp h).symm⟩
    -- the identity `σ/τ = 1 - exp (-2πi α w)`
    have hId : 1 - σ / tauC σ α w
        = Complex.exp (-(2 * Real.pi * Complex.I * α * w)) := one_sub_sigma_div_tauC hσ
    have hdiv : σ / tauC σ α w
        = 1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w)) := by
      rw [← hId]; ring
    -- lower bound: `‖1 - exp (-2πi α w)‖ = ‖σ‖/‖τ‖ ≥ ‖σ‖/5 ≥ 2‖α‖/5`
    have hlow : (2 / 5) * ‖α‖
        ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * w))‖ := by
      rw [← hdiv, norm_div]
      have hτpos : 0 < ‖tauC σ α w‖ := norm_pos_iff.mpr hτne
      have h1 : ‖σ‖ / 5 ≤ ‖σ‖ / ‖tauC σ α w‖ :=
        div_le_div_of_nonneg_left (norm_nonneg σ) hτpos h5
      have h2 : (2 / 5) * ‖α‖ ≤ ‖σ‖ / 5 := by
        calc (2 / 5) * ‖α‖ = 2 * ‖α‖ / 5 := by ring
          _ ≤ ‖σ‖ / 5 := div_le_div_of_nonneg_right hσlb (by norm_num)
      exact le_trans h2 h1
    -- suppose some lattice point is closer than `‖α‖/20`
    by_contra hcon
    rw [not_le] at hcon
    have hcon' : (⨅ k : ℤ, dist (α * w) (k : ℂ)) < ‖α‖ / 20 := by
      have : (1 / 20) * ‖α‖ = ‖α‖ / 20 := by ring
      linarith
    obtain ⟨k, hk⟩ := exists_lt_of_ciInf_lt hcon'
    set δ : ℂ := α * w - (k : ℂ) with hδdef
    have hδle : ‖δ‖ ≤ ‖α‖ / 20 := by
      have h : ‖δ‖ = dist (α * w) (k : ℂ) := by rw [hδdef, dist_eq_norm]
      rw [h]
      exact le_of_lt hk
    -- upper bound: `exp (-2πi δ) = exp (-2πi α w)`, and `‖1 - exp (-2πi δ)‖ ≤ ‖α‖/3`
    have hup :=
      Work.Pert.Lattice.norm_one_sub_exp_neg_two_pi_I_mul_le (α := α) (δ := δ) hα64 hδle
    have hshift : Complex.exp (-(2 * Real.pi * Complex.I * δ))
        = Complex.exp (-(2 * Real.pi * Complex.I * α * w)) := by
      rw [hδdef]
      have hsplit : -(2 * Real.pi * Complex.I * (α * w - (k : ℂ)))
          = -(2 * Real.pi * Complex.I * α * w) + (k : ℤ) * (2 * Real.pi * Complex.I) := by
        ring
      rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hshift] at hup
    -- `2/5 ≤ 1/3`, contradiction
    have hcmp : (2 / 5 : ℝ) * ‖α‖ ≤ (1 / 3) * ‖α‖ := le_trans hlow hup
    nlinarith [hαpos, hcmp]

end

end Work.Pert
