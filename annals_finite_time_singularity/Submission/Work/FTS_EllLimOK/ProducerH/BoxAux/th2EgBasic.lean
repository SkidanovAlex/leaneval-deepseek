import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.vopRated

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Elementary angular facts -/

/-- `sin(2θ) ≤ 2·min θ (π/2-θ)` for `θ ∈ (0,π/2)`. -/
theorem sin_two_le_two_min {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.sin (2 * θ) ≤ 2 * min θ (π / 2 - θ) := by
  have h1 : Real.sin (2 * θ) ≤ 2 * θ := by
    have h := Real.sin_le (by linarith [hθ.1] : (0 : ℝ) ≤ 2 * θ)
    linarith [h]
  have h2 : Real.sin (2 * θ) ≤ 2 * (π / 2 - θ) := by
    have hπ : 0 ≤ Real.pi - 2 * θ := by linarith [hθ.2]
    have h := Real.sin_le hπ
    have heq : Real.sin (2 * θ) = Real.sin (Real.pi - 2 * θ) := by
      rw [Real.sin_pi_sub]
    rw [heq]
    linarith [h]
  rcases le_total θ (π / 2 - θ) with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

/-- `m(θ) ≤ m(θ)^β` for `θ ∈ (0,π/2)` and `β ≤ 1` (the `min` is at most `π/4 ≤ 1`). -/
theorem min_rpow_ge_self {β θ : ℝ} (hβ : β ≤ 1) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    min θ (π / 2 - θ) ≤ (min θ (π / 2 - θ)) ^ β := by
  have hm0 : 0 < min θ (π / 2 - θ) := lt_min hθ.1 (by linarith [hθ.2])
  have hm1 : min θ (π / 2 - θ) ≤ 1 := by
    rcases le_total θ (π / 2 - θ) with h | h
    · rw [min_eq_left h]; nlinarith [hθ.2, Real.pi_lt_four]
    · rw [min_eq_right h]; nlinarith [h, Real.pi_lt_four]
  calc min θ (π / 2 - θ) = (min θ (π / 2 - θ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ (min θ (π / 2 - θ)) ^ β :=
        Real.rpow_le_rpow_of_exponent_ge hm0 hm1 hβ

/-- `x ≤ x^β` for `0 < x ≤ 1` and `β ≤ 1`. -/
theorem self_le_rpow {β x : ℝ} (hβ : β ≤ 1) (hx0 : 0 < x) (hx1 : x ≤ 1) : x ≤ x ^ β := by
  calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
    _ ≤ x ^ β := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hβ

/-- `tan θ ≤ 2θ` for `θ ∈ (0,π/4]`. -/
theorem tan_le_two_mul {θ : ℝ} (hθ0 : 0 < θ) (hθ4 : θ ≤ Real.pi / 4) :
    Real.tan θ ≤ 2 * θ := by
  have hcos : (1 : ℝ) / 2 ≤ Real.cos θ := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := θ)
    have h2 : θ ^ 2 ≤ (Real.pi / 4) ^ 2 := by nlinarith [hθ4, hθ0]
    nlinarith [h1, h2, Real.pi_lt_four, Real.pi_pos, sq_nonneg θ]
  have hcpos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hθ4, Real.pi_pos]⟩
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcpos]
  nlinarith [Real.sin_le (le_of_lt hθ0), hcos, hθ0]

/-- `(1-sin θ)/cos θ ≤ cos θ` on `(0,π/2)`. -/
theorem one_sub_sin_div_cos_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (1 - Real.sin θ) / Real.cos θ ≤ Real.cos θ := by
  have hc : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1.le, by linarith [hθ.2, Real.pi_pos]⟩
  rw [div_le_iff₀ hc]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- `cos θ ≤ π/2 - θ` on `(0,π/2)`. -/
theorem cos_le_pi_div_two_sub {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    Real.cos θ ≤ Real.pi / 2 - θ := by
  have h := Real.sin_le (show (0 : ℝ) ≤ Real.pi / 2 - θ by linarith [hθ.2])
  rwa [Real.sin_pi_div_two_sub] at h

/-- The two one-sided Gronwall bounds of `vopRated` combine into `|f θ| ≤ 2K·min θ (π/2-θ)`. -/
theorem vop_two_sided_le_min {K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ}
    (h1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |f θ| ≤ K * (Real.sin θ / Real.cos θ))
    (h2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |f θ| ≤ K * ((1 - Real.sin θ) / Real.cos θ)) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |f θ| ≤ 2 * K * min θ (π / 2 - θ) := by
  intro θ hθ
  rcases le_total θ (π / 2 - θ) with h | h
  · rw [min_eq_left h]
    have hθ4 : θ ≤ Real.pi / 4 := by linarith
    have hb := h1 θ hθ
    have ht := tan_le_two_mul hθ.1 hθ4
    have htan : Real.sin θ / Real.cos θ ≤ 2 * θ := by
      rwa [← Real.tan_eq_sin_div_cos]
    calc |f θ| ≤ K * (Real.sin θ / Real.cos θ) := hb
      _ ≤ K * (2 * θ) := mul_le_mul_of_nonneg_left htan hK
      _ = 2 * K * θ := by ring
  · rw [min_eq_right h]
    have hb := h2 θ hθ
    have hle := one_sub_sin_div_cos_le hθ
    have hcos := cos_le_pi_div_two_sub hθ
    have hpos : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    calc |f θ| ≤ K * ((1 - Real.sin θ) / Real.cos θ) := hb
      _ ≤ K * Real.cos θ := mul_le_mul_of_nonneg_left hle hK
      _ ≤ K * (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_left hcos hK
      _ ≤ 2 * K * (Real.pi / 2 - θ) := by nlinarith [hK, hpos]

/-- `D_z^j` is linear in the function: `D_z^j (f + g) = D_z^j f + D_z^j g` on the open
quadrant, for `f, g` smooth there. -/
theorem dzIter_add_eqOn {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    ∀ j : ℕ, ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.DzIter j (fun z θ => f z θ + g z θ) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  intro j
  induction j with
  | zero => intro z hz θ hθ; rfl
  | succ k ih =>
      intro z hz θ hθ
      have hdf : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter k f z' θ) z :=
        (((hf.DzIter k).curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero)
          |>.differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hdg : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter k g z' θ) z :=
        (((hg.DzIter k).curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero)
          |>.differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hev : (fun z' => Work.Spaces.DzIter k (fun z θ => f z θ + g z θ) z' θ)
          =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter k f z' θ + Work.Spaces.DzIter k g z' θ) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hz)
          (fun z' hz' => ih z' hz' θ hθ)
      show z * deriv (fun z' => Work.Spaces.DzIter k (fun z θ => f z θ + g z θ) z' θ) z
        = z * deriv (fun z' => Work.Spaces.DzIter k f z' θ) z
          + z * deriv (fun z' => Work.Spaces.DzIter k g z' θ) z
      rw [hev.deriv_eq]
      change z * deriv ((fun z' => Work.Spaces.DzIter k f z' θ)
        + fun z' => Work.Spaces.DzIter k g z' θ) z = _
      rw [deriv_add hdf hdg]
      ring

/-! ## The `V`-slot jets of `Φ̃` are bounded by `Xn₆` -/

end Work.FTS_EllLimOK.ProducerH.BoxAux
