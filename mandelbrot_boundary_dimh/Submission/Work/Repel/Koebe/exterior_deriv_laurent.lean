import Mathlib

/-!
# Term-by-term differentiation of the Laurent series of an exterior map

Let `c : ℕ → ℂ` be the Laurent coefficients at infinity of a function `g`:

  `g z - z = ∑' k, c k / z^k`   for `‖z‖ > 1`   (as a `HasSum`),

with the coefficient series absolutely summable at every radius `ρ > 1`:

  `Summable (fun k => ‖c k‖ / ρ^k)`   for every `ρ > 1`.

Then the Laurent series may be differentiated term by term on the exterior of the unit disc:

  `deriv g z - 1 = ∑' k, (-(k:ℂ) * c k) / z^(k+1)`   for `‖z‖ > 1`.

Note that no separate analyticity hypothesis on `g` is needed: the series itself defines an
analytic function there and `g` agrees with it on a neighbourhood of any point with `‖z‖ > 1`.

The proof fixes `z` with `1 < ρ < ‖z‖`, applies Weierstrass' theorem for series of holomorphic
functions (`Complex.differentiableOn_tsum_of_summable_norm`,
`Complex.hasSum_deriv_of_summable_norm`) to the terms `w ↦ c k / w^k` on the open set
`{w | ρ < ‖w‖}`, dominated by the summable sequence `‖c k‖ / ρ^k`, and identifies the derivative
of the sum function with `deriv g z - 1` using the local identity `∑' k, c k / w^k = g w - w`.
-/

namespace Work.Repel.Koebe

open Filter

/-- Pointwise derivative of `w ↦ cc / w ^ k` away from the origin:
`deriv (cc / w^k) z = -(k:ℂ) * cc / z ^ (k+1)`. -/
private lemma deriv_const_div_pow_aux (cc : ℂ) (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    deriv (fun w : ℂ => cc / w ^ k) z = -(k : ℂ) * cc / z ^ (k + 1) := by
  have hfun : (fun w : ℂ => cc / w ^ k) = fun w : ℂ => cc * w ^ (-(k : ℤ)) := by
    funext w
    rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [hfun, deriv_const_mul _ (differentiableAt_zpow.mpr (Or.inl hz)), deriv_zpow]
  have hm : (((-(k : ℤ) : ℤ)) : ℂ) = -(k : ℂ) := by push_cast; ring
  have hexp : (-(k : ℤ) - 1 : ℤ) = -((k + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hm, hexp, zpow_neg, zpow_natCast, div_eq_mul_inv, pow_succ]
  ring

theorem exterior_deriv_laurent {g : ℂ → ℂ} {c : ℕ → ℂ}
    (hexp : ∀ z : ℂ, 1 < ‖z‖ → HasSum (fun k : ℕ => c k / z ^ k) (g z - z))
    (hsum : ∀ ρ : ℝ, 1 < ρ → Summable (fun k : ℕ => ‖c k‖ / ρ ^ k)) :
    ∀ z : ℂ, 1 < ‖z‖ →
      HasSum (fun k : ℕ => (-(k : ℂ)) * c k / z ^ (k + 1)) (deriv g z - 1) := by
  intro z hz
  -- choose a radius `ρ` with `1 < ρ < ‖z‖`
  obtain ⟨ρ, hρ1, hρz⟩ : ∃ ρ : ℝ, 1 < ρ ∧ ρ < ‖z‖ := ⟨(1 + ‖z‖)/2, by linarith, by linarith⟩
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ1
  have hzne : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact absurd hz (by norm_num)
  -- the exterior `U = {w | ρ < ‖w‖}` is open and contains `z`
  have hUopen : IsOpen {w : ℂ | ρ < ‖w‖} := isOpen_Ioi.preimage continuous_norm
  have hzU : z ∈ {w : ℂ | ρ < ‖w‖} := hρz
  -- dominating summable sequence
  have hu : Summable (fun k : ℕ => ‖c k‖ / ρ ^ k) := hsum ρ hρ1
  -- each Laurent term is holomorphic on `U`
  have hFdiff : ∀ k : ℕ, DifferentiableOn ℂ (fun w : ℂ => c k / w ^ k) {w : ℂ | ρ < ‖w‖} := by
    intro k
    refine DifferentiableOn.div (differentiableOn_const (c k)) (differentiableOn_id.pow k) ?_
    intro w hw
    exact pow_ne_zero k (norm_pos_iff.mp (lt_trans hρpos hw))
  -- and dominated there by `‖c k‖ / ρ^k`
  have hFle : ∀ (k : ℕ) (w : ℂ), w ∈ {w : ℂ | ρ < ‖w‖} → ‖c k / w ^ k‖ ≤ ‖c k‖ / ρ ^ k := by
    intro k w hw
    rw [norm_div, norm_pow]
    gcongr
    exact le_of_lt hw
  -- Weierstrass: the sum of the series is holomorphic on `U`, hence at `z`
  have hSdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' k : ℕ, c k / w ^ k) {w : ℂ | ρ < ‖w‖} :=
    Complex.differentiableOn_tsum_of_summable_norm hu hFdiff hUopen hFle
  have hSz : DifferentiableAt ℂ (fun w : ℂ => ∑' k : ℕ, c k / w ^ k) z :=
    hSdiff.differentiableAt (hUopen.mem_nhds hzU)
  -- near `z` the sum is `g - id`
  have hEq : (fun w : ℂ => ∑' k : ℕ, c k / w ^ k) =ᶠ[nhds z] (fun w : ℂ => g w - w) := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    exact (hexp w (lt_trans hρ1 hw)).tsum_eq
  have h2 : (fun w : ℂ => (∑' k : ℕ, c k / w ^ k) + w) =ᶠ[nhds z] g := by
    filter_upwards [hEq] with w hw
    rw [hw]; ring
  -- hence the derivative of the sum function is `deriv g z - 1`
  have hderiv : deriv g z = deriv (fun w : ℂ => ∑' k : ℕ, c k / w ^ k) z + 1 := by
    rw [← h2.deriv_eq]
    rw [show (fun w : ℂ => (∑' k : ℕ, c k / w ^ k) + w)
        = (fun w : ℂ => ∑' k : ℕ, c k / w ^ k) + id from rfl]
    rw [deriv_add hSz differentiableAt_id, deriv_id]
  have hbr : deriv (fun w : ℂ => ∑' k : ℕ, c k / w ^ k) z = deriv g z - 1 := by
    rw [hderiv]; ring
  -- term-by-term differentiation
  have hW := Complex.hasSum_deriv_of_summable_norm (U := {w : ℂ | ρ < ‖w‖})
    (F := fun k : ℕ => fun w : ℂ => c k / w ^ k) (u := fun k : ℕ => ‖c k‖ / ρ ^ k)
    hu hFdiff hUopen hFle hzU
  rw [hbr] at hW
  refine hW.congr_fun (fun k => ?_)
  exact (deriv_const_div_pow_aux (c k) k hzne).symm

end Work.Repel.Koebe
