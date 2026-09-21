import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# The odd first-row identity with a pointwise envelope hypothesis

`(Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 / √(σ-s)` equals minus
the sum of the `(n+1)`-st iterated derivatives of the moment integrand at the
two section endpoints.

This is the sibling identity `Kvec_div_sqrt_eq` of
`Submission.Work.OddVolterra.RowIdentity.odd_iteratedDeriv_momentF_eq_abel`,
but with the envelope relations `f (y u) = u * y u + h u` and
`f (-(x u)) = -(u * (-(x u)) + h u)` required only at the single point
`u = σ` (the form needed when the envelope is only known on `u ∈ (0,1]`).

Every ingredient only ever uses the envelope relation at `σ`, so the same
proof goes through; we reproduce the needed helper lemmas here with the
weaker hypotheses.
-/

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

variable {h x y f : ℝ → ℝ}

/-! ## The frozen-line identification at an endpoint -/

/-- At an endpoint where `f` and the `σ`-frozen line agree in square, the
`σ`-frozen radicand agrees with the true one. -/
theorem psi_line_eq_of_sq_pt {h f g : ℝ → ℝ} {σ : ℝ}
    (hg : (line h σ (g σ)) ^ 2 = (f (g σ)) ^ 2) (u : ℝ) :
    psi h (fun t => line h σ t) u (g σ) = psi h f u (g σ) := by
  simp only [psi]
  rw [hg]

/-! ## The kernel denominator and the `1/√(σ-s)` normalization -/

/-- `Kden · √(σ-s) = √ψ` on the section. -/
theorem Kden_mul_sqrt_pt {h f : ℝ → ℝ} {s σ t : ℝ} (hsσ : s < σ)
    (hfac : psi h f s t = (σ - s) * ((t + hquot h s σ) * (line h σ t + line h s t)))
    (hpos : 0 ≤ psi h f s t) :
    Kden h s σ t * Real.sqrt (σ - s) = Real.sqrt (psi h f s t) := by
  have hspos : 0 < σ - s := sub_pos.mpr hsσ
  have hnum : 0 ≤ (t + hquot h s σ) * (line h σ t + line h s t) := by
    have h2 : 0 ≤ (σ - s) * ((t + hquot h s σ) * (line h σ t + line h s t)) := by
      rw [← hfac]; exact hpos
    exact (mul_nonneg_iff_of_pos_left hspos).mp h2
  rw [Kden, hfac, Real.sqrt_mul hspos.le, mul_comm]

/-- The normalisation `K₁(s,σ,t)/√(σ-s) = J₁(s,σ,t)/√ψ(s,t)`. -/
theorem K1_div_sqrt_pt {n : ℕ} {h f : ℝ → ℝ} {s σ t : ℝ} (hsσ : s < σ)
    (hfac : psi h f s t = (σ - s) * ((t + hquot h s σ) * (line h σ t + line h s t)))
    (hpos : 0 < psi h f s t) :
    K1 n h s σ t / Real.sqrt (σ - s) = J1 n h s σ t / Real.sqrt (psi h f s t) := by
  have hden := Kden_mul_sqrt_pt hsσ hfac (le_of_lt hpos)
  rw [K1, div_div, hden]

/-- `J₁` at a section endpoint is the (frozen) iterated derivative times `√ψ`. -/
theorem J1_eq_pt {n : ℕ} {h f g : ℝ → ℝ} {σ : ℝ}
    (hg : (line h σ (g σ)) ^ 2 = (f (g σ)) ^ 2) {s : ℝ} (hσ : σ ≠ s) :
    J1 n h s σ (g σ)
      = iteratedDeriv (n + 1)
          (fun u : ℝ => psi h f u (g σ) ^ n * Real.sqrt (psi h f u (g σ))) s
        * Real.sqrt (psi h f s (g σ)) := by
  rw [J1, if_neg hσ]
  have hfun : (fun u : ℝ => psi h (fun t' => line h σ t') u (g σ) ^ n *
        Real.sqrt (psi h (fun t' => line h σ t') u (g σ)))
      = fun u : ℝ => psi h f u (g σ) ^ n * Real.sqrt (psi h f u (g σ)) := by
    funext u
    rw [psi_line_eq_of_sq_pt hg u]
  have harg : psi h (fun t' => line h σ t') s (g σ) = psi h f s (g σ) :=
    psi_line_eq_of_sq_pt hg s
  rw [hfun, harg]

/-- `J₁/√ψ` at a section endpoint is the iterated derivative of the moment
integrand, with the true `f`. -/
theorem J1_div_sqrt_eq_pt {n : ℕ} {h f g : ℝ → ℝ} {σ : ℝ}
    (hg : (line h σ (g σ)) ^ 2 = (f (g σ)) ^ 2) {s : ℝ} (hσ : σ ≠ s)
    (hpos : 0 < psi h f s (g σ)) :
    J1 n h s σ (g σ) / Real.sqrt (psi h f s (g σ))
      = iteratedDeriv (n + 1)
          (fun u : ℝ => psi h f u (g σ) ^ n * Real.sqrt (psi h f u (g σ))) s := by
  rw [J1_eq_pt hg hσ]
  have hne : Real.sqrt (psi h f s (g σ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  field_simp

/-! ## The endpoint factorisations (envelope relation only at `σ`) -/

/-- For the right endpoint,
`ψ(s, y σ) = (σ - s) · (y σ + H(s,σ)) · (L(σ, y σ) + L(s, y σ))`. -/
theorem psi_y_factor_pt {h f y : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {σ : ℝ}
    (hxy : f (y σ) = σ * y σ + h σ) (s : ℝ) :
    psi h f s (y σ)
      = (σ - s) * ((y σ + hquot h s σ) * (line h σ (y σ) + line h s (y σ))) := by
  have hkey : psi h f s (y σ) = (σ * y σ + h σ) ^ 2 - (s * y σ + h s) ^ 2 := by
    rw [psi, line, hxy]
  rw [hkey]
  have hq : h σ - h s = (σ - s) * hquot h s σ := sub_mul_hquot hh s σ
  calc (σ * y σ + h σ) ^ 2 - (s * y σ + h s) ^ 2
      = ((σ - s) * y σ + (h σ - h s)) * ((σ + s) * y σ + (h σ + h s)) := by ring
    _ = ((σ - s) * y σ + (σ - s) * hquot h s σ) * ((σ + s) * y σ + (h σ + h s)) := by
          rw [hq]
    _ = (σ - s) * ((y σ + hquot h s σ) *
          ((σ * y σ + h σ) + (s * y σ + h s))) := by ring
    _ = (σ - s) * ((y σ + hquot h s σ) * (line h σ (y σ) + line h s (y σ))) := by
          rw [line, line]

/-- The same for the left endpoint. -/
theorem psi_negx_factor_pt {h f x : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {σ : ℝ}
    (hxy : f (-(x σ)) = -(σ * (-(x σ)) + h σ)) (s : ℝ) :
    psi h f s (-(x σ))
      = (σ - s) * ((-(x σ) + hquot h s σ) * (line h σ (-(x σ)) + line h s (-(x σ)))) := by
  have hkey : psi h f s (-(x σ)) = (σ * (-(x σ)) + h σ) ^ 2 - (s * (-(x σ)) + h s) ^ 2 := by
    rw [psi, line, hxy]
    ring
  rw [hkey]
  have hq : h σ - h s = (σ - s) * hquot h s σ := sub_mul_hquot hh s σ
  calc (σ * (-(x σ)) + h σ) ^ 2 - (s * (-(x σ)) + h s) ^ 2
      = ((σ - s) * (-(x σ)) + (h σ - h s)) * ((σ + s) * (-(x σ)) + (h σ + h s)) := by ring
    _ = ((σ - s) * (-(x σ)) + (σ - s) * hquot h s σ) *
          ((σ + s) * (-(x σ)) + (h σ + h s)) := by rw [hq]
    _ = (σ - s) * ((-(x σ) + hquot h s σ) *
          ((σ * (-(x σ)) + h σ) + (s * (-(x σ)) + h s))) := by ring
    _ = (σ - s) * ((-(x σ) + hquot h s σ) *
          (line h σ (-(x σ)) + line h s (-(x σ)))) := by rw [line, line]

/-! ## Positivity of the radicand at the endpoints (from `hKden`) -/

theorem psi_y_pos_pt {h f y : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {σ : ℝ}
    (hxy : f (y σ) = σ * y σ + h σ) {s : ℝ} (hsσ : s < σ)
    (hK : 0 < (y σ + hquot h s σ) * (line h σ (y σ) + line h s (y σ))) :
    0 < psi h f s (y σ) := by
  rw [psi_y_factor_pt hh hxy s]
  exact mul_pos (sub_pos.mpr hsσ) hK

theorem psi_negx_pos_pt {h f x : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {σ : ℝ}
    (hxy : f (-(x σ)) = -(σ * (-(x σ)) + h σ)) {s : ℝ} (hsσ : s < σ)
    (hK : 0 < (-(x σ) + hquot h s σ) * (line h σ (-(x σ)) + line h s (-(x σ)))) :
    0 < psi h f s (-(x σ)) := by
  rw [psi_negx_factor_pt hh hxy s]
  exact mul_pos (sub_pos.mpr hsσ) hK

/-! ## The row identity -/

/-- The `0`-th component of the kernel `Kvec`, divided by `√(σ-s)`, is minus the sum of the
`(n+1)`-st derivatives of the moment integrand at the two section endpoints, for `σ > s`:
`(Kvec n h s σ (xσ) (yσ) (x'σ) (y'σ)) 0 / √(σ-s)
 = -(∂_u^{n+1}(ψ(u,yσ)^{n+1/2})|_s · y'σ + ∂_u^{n+1}(ψ(u,-xσ)^{n+1/2})|_s · x'σ)`.

This is `Kvec_div_sqrt_eq` of the sibling file
`Submission.Work.OddVolterra.RowIdentity.odd_iteratedDeriv_momentF_eq_abel` (which is sorry-free),
but with the envelope hypotheses `f (y u) = u*y u + h u` and `f (-(x u)) = -(u*(-(x u)) + h u)`
imposed only at the single point `u = σ` (the sibling imposes them for all `u`), which is the
form needed when the envelope is only known on `u ∈ (0,1]`.  The proof is the sibling's: write
`Kvec`'s first component via `K1`, use `K1_div_sqrt`/`Kden_mul_sqrt` and `psi_y_factor`,
`psi_negx_factor`, `J1_div_sqrt_eq` (each of which only ever uses the envelope relation at `σ`),
then simplify.  Definitions `Kvec`, `K1`, `J1`, `psi`, `line`, `hquot` are in
`Submission.Work.OddVolterra.Defs`. -/
theorem kvec_zero_div_sqrt_eq (n : ℕ) {h x y f : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {s σ : ℝ} (hsσ : s < σ)
    (hy : f (y σ) = σ * y σ + h σ) (hx : f (-(x σ)) = -(σ * (-(x σ)) + h σ))
    (hKy : 0 < (y σ + hquot h s σ) * (line h σ (y σ) + line h s (y σ)))
    (hKx : 0 < (-(x σ) + hquot h s σ) * (line h σ (-(x σ)) + line h s (-(x σ)))) :
    (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 0 / Real.sqrt (σ - s)
      = -((iteratedDeriv (n + 1)
              (fun u : ℝ => psi h f u (y σ) ^ n * Real.sqrt (psi h f u (y σ))) s) * deriv y σ
          + (iteratedDeriv (n + 1)
              (fun u : ℝ => psi h f u (-(x σ)) ^ n * Real.sqrt (psi h f u (-(x σ)))) s)
            * deriv x σ) := by
  have hy' : 0 < psi h f s (y σ) := psi_y_pos_pt hh hy hsσ hKy
  have hx' : 0 < psi h f s (-(x σ)) := psi_negx_pos_pt hh hx hsσ hKx
  have hfy := psi_y_factor_pt hh hy s
  have hfx := psi_negx_factor_pt hh hx s
  have h1 := K1_div_sqrt_pt (n := n) (h := h) (f := f) (s := s) (σ := σ) (t := y σ) hsσ hfy hy'
  have h2 := K1_div_sqrt_pt (n := n) (h := h) (f := f) (s := s) (σ := σ) (t := -(x σ))
    hsσ hfx hx'
  have hsqy : (line h σ (y σ)) ^ 2 = (f (y σ)) ^ 2 := by rw [line, hy]
  have hsqx : (line h σ (-(x σ))) ^ 2 = (f (-(x σ))) ^ 2 := by
    rw [line, hx]; ring
  have h3 := J1_div_sqrt_eq_pt (n := n) (h := h) (f := f) (g := y) (σ := σ) hsqy
    (ne_of_gt hsσ) hy'
  have h4 := J1_div_sqrt_eq_pt (n := n) (h := h) (f := f) (g := fun u => -(x u)) (σ := σ)
    hsqx (ne_of_gt hsσ) hx'
  have hIx : K1 n h s σ (-(x σ)) / Real.sqrt (σ - s)
      = iteratedDeriv (n + 1)
          (fun u : ℝ => psi h f u (-(x σ)) ^ n * Real.sqrt (psi h f u (-(x σ)))) s := by
    rw [h2, h4]
  have hIy : K1 n h s σ (y σ) / Real.sqrt (σ - s)
      = iteratedDeriv (n + 1)
          (fun u : ℝ => psi h f u (y σ) ^ n * Real.sqrt (psi h f u (y σ))) s := by
    rw [h1, h3]
  simp only [Kvec, Matrix.cons_val_zero]
  rw [show (-(K1 n h s σ (-(x σ)) * deriv x σ + K1 n h s σ (y σ) * deriv y σ))
        / Real.sqrt (σ - s)
      = -((K1 n h s σ (-(x σ)) / Real.sqrt (σ - s)) * deriv x σ)
        - ((K1 n h s σ (y σ) / Real.sqrt (σ - s)) * deriv y σ) by ring]
  rw [hIx, hIy]
  ring

end

end Work.OddVolterra.RowIdentity
