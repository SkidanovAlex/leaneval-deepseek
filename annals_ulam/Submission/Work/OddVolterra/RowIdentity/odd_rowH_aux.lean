import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.window_iteratedDeriv_of_eventually_pos
import Submission.Work.Analysis.Abel.integral_moving_split_local
import Submission.Work.OddVolterra.RowIdentity.kvec_zero_div_sqrt_eq
import Submission.Work.OddVolterra.RowIdentity.yend_iteratedDeriv_eq_rpow
import Submission.Work.OddVolterra.RowIdentity.contDiff_trunc_pow_sqrt

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Commons.Geometry.Ulam (profileX semicircle)

noncomputable section

/-!
# The odd centroid-moment row identity

This file proves `Work.OddVolterra.RowIdentity.odd_rowH`, the second (centroid)
row of the odd transition-slope system: the `n`-th derivative of the centroid
moment integral equals the fixed-window term `E2` plus the Abel transform of the
second kernel `Kvec … 1`.
-/

/-! ## The endpoint factors of the frozen radicand -/

/-- The `y`-endpoint factor of the frozen radicand: `ψ(u,yσ) = (σ-u)·Qy(u,σ)`. -/
def QyH (h y : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (y σ + hquot h u σ) * (line h σ (y σ) + line h u (y σ))

/-- The `-x`-endpoint factor of the frozen radicand: `ψ(u,-xσ) = (σ-u)·Qx(u,σ)`. -/
def QxH (h x : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (-(x σ) + hquot h u σ) * (line h σ (-(x σ)) + line h u (-(x σ)))

/-- The globally smooth auxiliary radicand `1 - t² - (ut + h u)²`; it agrees with
`psi h semicircle u t` for `|t| ≤ 1`. -/
def PsiH (h : ℝ → ℝ) (u t : ℝ) : ℝ := 1 - t ^ 2 - line h u t ^ 2

/-- The coefficient of the swept integral for the centroid row. -/
def AH (n : ℕ) (h x y : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (QyH h y u σ) ^ ((n : ℝ) - 1 / 2) * lineSlope h u (y σ) * (-(deriv y σ)) +
    (QxH h x u σ) ^ ((n : ℝ) - 1 / 2) * lineSlope h u (-(x σ)) * (-(deriv x σ))

/-! ## The centroid integrand at the two section endpoints -/

/-- The cast `(n-1) + 1/2 = n - 1/2` in `ℝ`. -/
theorem cast_sub_half {n : ℕ} (hn : 1 ≤ n) : (((n - 1 : ℕ) : ℝ) + 1 / 2) = (n : ℝ) - 1 / 2 := by
  push_cast [Nat.cast_sub hn]
  ring

/-- Pointwise identification of the centroid integrand at the right endpoint with
the product of the two half-integer powers of the factors of `ψ`. -/
theorem centroidIntegrand_y_eq_rpow {n : ℕ} (hn : 1 ≤ n) {h f y : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {u σ : ℝ} (huσ : u ≤ σ) (hQ : 0 ≤ QyH h y u σ) (hy : f (y σ) = σ * y σ + h σ) :
    centroidIntegrand n h f u (y σ)
      = (σ - u) ^ ((n : ℝ) - 1 / 2) * (QyH h y u σ) ^ ((n : ℝ) - 1 / 2) *
        lineSlope h u (y σ) := by
  have hfac : psi h f u (y σ) = (σ - u) * QyH h y u σ := by
    rw [psi_y_factor_pt hh hy u]; rfl
  rw [centroidIntegrand, pow_mul_sqrt_eq_rpow (n - 1) (psi h f u (y σ)), hfac,
    Real.mul_rpow (sub_nonneg.mpr huσ) hQ, cast_sub_half hn]

/-- The same at the left endpoint. -/
theorem centroidIntegrand_negx_eq_rpow {n : ℕ} (hn : 1 ≤ n) {h f x : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {u σ : ℝ} (huσ : u ≤ σ) (hQ : 0 ≤ QxH h x u σ) (hx : f (-(x σ)) = -(σ * (-(x σ)) + h σ)) :
    centroidIntegrand n h f u (-(x σ))
      = (σ - u) ^ ((n : ℝ) - 1 / 2) * (QxH h x u σ) ^ ((n : ℝ) - 1 / 2) *
        lineSlope h u (-(x σ)) := by
  have hfac : psi h f u (-(x σ)) = (σ - u) * QxH h x u σ := by
    rw [psi_negx_factor_pt hh hx u]; rfl
  rw [centroidIntegrand, pow_mul_sqrt_eq_rpow (n - 1) (psi h f u (-(x σ))), hfac,
    Real.mul_rpow (sub_nonneg.mpr huσ) hQ, cast_sub_half hn]

/-- The pointwise form of the swept integrand. -/
theorem swept_pointwise {n : ℕ} (hn : 1 ≤ n) {h f x y : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {u σ : ℝ} (huσ : u ≤ σ) (hQy : 0 ≤ QyH h y u σ) (hQx : 0 ≤ QxH h x u σ)
    (hy : f (y σ) = σ * y σ + h σ) (hx : f (-(x σ)) = -(σ * (-(x σ)) + h σ)) :
    centroidIntegrand n h f u (y σ) * (-(deriv y σ)) +
        centroidIntegrand n h f u (-(x σ)) * (-(deriv x σ))
      = (σ - u) ^ ((n : ℝ) - 1 / 2) * AH n h x y u σ := by
  rw [centroidIntegrand_y_eq_rpow (n := n) hn hh huσ hQy hy,
    centroidIntegrand_negx_eq_rpow (n := n) hn hh huσ hQx hx, AH]
  ring

/-! ## The second Abel kernel at the section endpoints -/

/-- The normalisation `K₂(s,σ,t)/√(σ-s) = J₂(s,σ,t)/√ψ(s,t)`. -/
theorem K2_div_sqrt_pt {n : ℕ} {h f : ℝ → ℝ} {s σ t : ℝ} (hsσ : s < σ)
    (hfac : psi h f s t = (σ - s) * ((t + hquot h s σ) * (line h σ t + line h s t)))
    (hpos : 0 < psi h f s t) :
    K2 n h s σ t / Real.sqrt (σ - s) = J2 n h s σ t / Real.sqrt (psi h f s t) := by
  have hden := Kden_mul_sqrt_pt hsσ hfac (le_of_lt hpos)
  rw [K2, div_div, hden]

/-- `J₂` at a section endpoint is the (frozen) iterated derivative of the centroid
integrand times `√ψ`. -/
theorem J2_eq_pt {n : ℕ} {h f g : ℝ → ℝ} {σ : ℝ}
    (hg : (line h σ (g σ)) ^ 2 = (f (g σ)) ^ 2) {s : ℝ} (hσ : σ ≠ s) :
    J2 n h s σ (g σ)
      = iteratedDeriv n
          (fun u : ℝ => psi h f u (g σ) ^ (n - 1) * Real.sqrt (psi h f u (g σ)) *
            lineSlope h u (g σ)) s
        * Real.sqrt (psi h f s (g σ)) := by
  rw [J2, if_neg hσ]
  have hfun : (fun u : ℝ => psi h (fun t' => line h σ t') u (g σ) ^ (n - 1) *
        Real.sqrt (psi h (fun t' => line h σ t') u (g σ)) * lineSlope h u (g σ))
      = fun u : ℝ => psi h f u (g σ) ^ (n - 1) * Real.sqrt (psi h f u (g σ)) *
          lineSlope h u (g σ) := by
    funext u
    rw [psi_line_eq_of_sq_pt hg u]
  have harg : psi h (fun t' => line h σ t') s (g σ) = psi h f s (g σ) :=
    psi_line_eq_of_sq_pt hg s
  rw [hfun, harg]

/-- `J₂/√ψ` at a section endpoint is the iterated derivative of the centroid integrand. -/
theorem J2_div_sqrt_eq_pt {n : ℕ} {h f g : ℝ → ℝ} {σ : ℝ}
    (hg : (line h σ (g σ)) ^ 2 = (f (g σ)) ^ 2) {s : ℝ} (hσ : σ ≠ s)
    (hpos : 0 < psi h f s (g σ)) :
    J2 n h s σ (g σ) / Real.sqrt (psi h f s (g σ))
      = iteratedDeriv n
          (fun u : ℝ => psi h f u (g σ) ^ (n - 1) * Real.sqrt (psi h f u (g σ)) *
            lineSlope h u (g σ)) s := by
  rw [J2_eq_pt hg hσ]
  have hne : Real.sqrt (psi h f s (g σ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  field_simp

/-- The `1`-st component of the kernel `Kvec`, divided by `√(σ-s)`, is minus the sum of the
`n`-th derivatives of the centroid integrand at the two section endpoints, for `σ > s`. -/
theorem kvec_one_div_sqrt_eq {n : ℕ} (hn : 1 ≤ n) {h x y f : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    {s σ : ℝ} (hsσ : s < σ)
    (hy : f (y σ) = σ * y σ + h σ) (hx : f (-(x σ)) = -(σ * (-(x σ)) + h σ))
    (hKy : 0 < (y σ + hquot h s σ) * (line h σ (y σ) + line h s (y σ)))
    (hKx : 0 < (-(x σ) + hquot h s σ) * (line h σ (-(x σ)) + line h s (-(x σ)))) :
    (Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) 1 / Real.sqrt (σ - s)
      = -((iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (y σ)) s) * deriv y σ
          + (iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (-(x σ))) s)
            * deriv x σ) := by
  have hKy' : 0 < QyH h y s σ := hKy
  have hKx' : 0 < QxH h x s σ := hKx
  have hy' : 0 < psi h f s (y σ) := psi_y_pos_pt hh hy hsσ hKy'
  have hx' : 0 < psi h f s (-(x σ)) := psi_negx_pos_pt hh hx hsσ hKx'
  have hfy : psi h f s (y σ)
      = (σ - s) * ((y σ + hquot h s σ) * (line h σ (y σ) + line h s (y σ))) :=
    psi_y_factor_pt hh hy s
  have hfx : psi h f s (-(x σ))
      = (σ - s) * ((-(x σ) + hquot h s σ) * (line h σ (-(x σ)) + line h s (-(x σ)))) :=
    psi_negx_factor_pt hh hx s
  have h1 := K2_div_sqrt_pt (n := n) (h := h) (f := f) (s := s) (σ := σ) (t := y σ) hsσ hfy hy'
  have h2 := K2_div_sqrt_pt (n := n) (h := h) (f := f) (s := s) (σ := σ) (t := -(x σ))
    hsσ hfx hx'
  have hsqy : (line h σ (y σ)) ^ 2 = (f (y σ)) ^ 2 := by rw [line, hy]
  have hsqx : (line h σ (-(x σ))) ^ 2 = (f (-(x σ))) ^ 2 := by
    rw [line, hx]; ring
  have h3 := J2_div_sqrt_eq_pt (n := n) (h := h) (f := f) (g := y) (σ := σ) hsqy
    (ne_of_gt hsσ) hy'
  have h4 := J2_div_sqrt_eq_pt (n := n) (h := h) (f := f) (g := fun u => -(x u)) (σ := σ)
    hsqx (ne_of_gt hsσ) hx'
  have hIx : K2 n h s σ (-(x σ)) / Real.sqrt (σ - s)
      = iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (-(x σ))) s := by
    rw [h2, h4]
    rfl
  have hIy : K2 n h s σ (y σ) / Real.sqrt (σ - s)
      = iteratedDeriv n (fun u : ℝ => centroidIntegrand n h f u (y σ)) s := by
    rw [h1, h3]
    rfl
  simp only [Kvec, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [show (-(K2 n h s σ (-(x σ)) * deriv x σ + K2 n h s σ (y σ) * deriv y σ))
        / Real.sqrt (σ - s)
      = -((K2 n h s σ (-(x σ)) / Real.sqrt (σ - s)) * deriv x σ)
        - ((K2 n h s σ (y σ) / Real.sqrt (σ - s)) * deriv y σ) by ring]
  rw [hIx, hIy]
  ring


/-- The integrand of the swept integral of the centroid row. -/
def WintH (n : ℕ) (h x y : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (σ - u) ^ ((n : ℝ) - 1 / 2) * AH n h x y u σ

/-- The swept integral of the centroid row. -/
def WWH (n : ℕ) (h x y : ℝ → ℝ) (u : ℝ) : ℝ := ∫ σ in u..1, WintH n h x y u σ

/-- The fixed-window part of the centroid moment. -/
def AAfH (n : ℕ) (h f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ t in (-(profileX 1))..(profileX 1), centroidIntegrand n h f u t


end

end Work.OddVolterra.RowIdentity
