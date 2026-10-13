import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.I1cb.ftc_open_interval
import Submission.Work.FTS.EllipticEst.H2W.I1cb.boundary_vanish_left
import Submission.Work.FTS.EllipticEst.H2W.I1cb.boundary_vanish_right
import Submission.Work.FTS.H2.STBasic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `θ`-integration by parts of the cross term of `I₁`

With `η ∈ (0,1)` and a function `v` of class `C¹` on the *open* interval `(0,π/2)` (no
closed-interval regularity, and no hypothesis on the endpoint values of `v` — this is what the
almost-everywhere class `H2W.Ae.AeData` supplies), the identity

```
∫_θ v · v' · cos(2θ) · sin(2θ)^{-1-η}
  = ∫_θ v² · sin(2θ)^{-η} + (1+η) · ∫_θ v² · cos²(2θ) · sin(2θ)^{-2-η}
```

holds, where all integrals are over `(0,π/2)` (`v' = deriv v`).

This is the third step of the paper's chain for the `I₁` lower bound (Elgindi, Annals **194**
(2021), tex 873–890): with `U = z∂_zu` it says `CROSS = ⟨U,U⟩ + (1+η)N`, which combined with the
`z`-IBP (`SlotA.I1_z_ibp_open`) and the `θ`-IBP of the mixed term
(`H2W.I1_cross_bookkeeping`, `T₂ = -Pp + 2η·CROSS`) gives the identity

`⟨z²∂_zzu, ∂_θ²u⟩ = Pp - 2η⟨U,U⟩ - 2η(1+η)N - ⟨U, cw·∂_θ²u⟩`

consumed by the algebraic core `H2W.Ae.i1Lower_algebra_eta`.

## Route

Write `P θ := v θ² · cos(2θ) · sin(2θ)^{-1-η}`, whose derivative on `(0,π/2)` is exactly

`2·(v v' cos(2θ) sin(2θ)^{-1-η}) - 2·(v² sin(2θ)^{-η}) - 2(1+η)·(v² cos²(2θ) sin(2θ)^{-2-η})`.

The integrability of that derivative puts us in the hypotheses of `I1cb.ftc_open_interval`: `P`
has one-sided limits `fa` at `0⁺`, `fb` at `π/2⁻`, and `∫ P' = fb - fa`.  Both limits vanish by
*integrability*: near `θ = 0` (resp. `π/2`) one has `|cos 2θ| ≥ 1/2`, hence `|cos 2θ| ≤ 2 cos²2θ`
and therefore `|P θ| ≤ 2·sin(2θ)·|v² cos²(2θ) sin(2θ)^{-2-η}|`, while
`v² cos²(2θ) sin(2θ)^{-2-η}` is integrable near the endpoint by `hintN`; so a non-zero limit
would make a `1/θ`-like function integrable (`I1cb.boundary_vanish_left` / `_right`).  Hence
`∫ P' = 0`, and splitting the integral of `P'` against the three integrable pieces gives the
identity.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.SlotA

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "Iθo" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- The primitive `P θ = v θ² cos(2θ) sin(2θ)^{-1-η}`. -/
private def cP (η : ℝ) (v : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => v θ ^ 2 * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η)

/-- Its derivative. -/
private def cP' (η : ℝ) (v : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => 2 * (v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η))
    - 2 * (v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
    - 2 * (1 + η) * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η))

/-- **The pointwise derivative of the primitive.** -/
private theorem cP_hasDerivAt (η : ℝ) (v : ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Iθo)
    (hv : HasDerivAt v (deriv v θ) θ) :
    HasDerivAt (cP η v) (cP' η v θ) θ := by
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hv2 : HasDerivAt (fun t : ℝ => v t ^ 2) (2 * v θ * deriv v θ) θ := by
    have h := hv.pow 2
    have h2 : (2 : ℕ) * v θ ^ (2 - 1) * deriv v θ = 2 * v θ * deriv v θ := by norm_num
    exact h.congr_deriv h2
  have hc : HasDerivAt (fun t : ℝ => Real.cos (2 * t)) (-2 * Real.sin (2 * θ)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2 := (Real.hasDerivAt_cos (2 * θ)).comp θ h1
    have h3 : (-Real.sin (2 * θ)) * 2 = -2 * Real.sin (2 * θ) := by ring
    exact h2.congr_deriv h3
  have hs' : HasDerivAt (fun t : ℝ => (Real.sin (2 * t)) ^ (-1 - η))
      (2 * Real.cos (2 * θ) * (-1 - η) * (Real.sin (2 * θ)) ^ (-2 - η)) θ := by
    have h := Work.FTS.H2.hasDerivAt_sin_rpow (-1 - η) θ hθ
    rw [show (-1 - η) - 1 = (-2 - η) by ring] at h
    exact h
  have h := (hv2.mul hc).mul hs'
  refine h.congr_deriv ?_
  have hkey : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η)
      = (Real.sin (2 * θ)) ^ (-η) := by
    rw [show (-η) = 1 + (-1 - η) by ring, Real.rpow_add hspos, Real.rpow_one]
  simp only [Pi.mul_apply, cP']
  rw [← hkey]
  ring

/-- The pointwise bound of the primitive by `2·sin(2θ)·(v² cos²(2θ) sin(2θ)^{-2-η})`, valid
whenever `|cos 2θ| ≤ 2 cos²(2θ)` (which holds near both endpoints of `(0,π/2)`). -/
private theorem abs_cP_le (η : ℝ) (v : ℝ → ℝ) {θ : ℝ} (hspos : 0 < Real.sin (2 * θ))
    (hca : |Real.cos (2 * θ)| ≤ 2 * (Real.cos (2 * θ)) ^ 2) :
    |cP η v θ| ≤ 2 * Real.sin (2 * θ)
      * |v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)| := by
  have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-1 - η) := Real.rpow_nonneg hspos.le _
  have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-2 - η) := Real.rpow_nonneg hspos.le _
  have hmul : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-2 - η)
      = (Real.sin (2 * θ)) ^ (-1 - η) := by
    rw [show (-1 - η) = 1 + (-2 - η) by ring, Real.rpow_add hspos, Real.rpow_one]
  have hgoal : |cP η v θ| = v θ ^ 2 * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-1 - η) := by
    simp only [cP]
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_nonneg h1]
  rw [hgoal, ← hmul]
  have hrhs : 2 * Real.sin (2 * θ)
      * |v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)|
      = 2 * Real.sin (2 * θ) * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-2 - η)) := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h2)]
  rw [hrhs]
  have hsin2 : 0 ≤ Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-2 - η) := mul_nonneg hspos.le h2
  calc v θ ^ 2 * |Real.cos (2 * θ)| * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-2 - η))
      = (v θ ^ 2 * |Real.cos (2 * θ)|)
          * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-2 - η)) := by ring
    _ ≤ (2 * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2))
          * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-2 - η)) := by
        refine mul_le_mul_of_nonneg_right ?_ hsin2
        nlinarith [hca, sq_nonneg (v θ)]
    _ = 2 * Real.sin (2 * θ)
          * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)) := by ring

/-- **The `θ`-integration by parts of the cross term of `I₁`.** -/
theorem cross_theta_ibp (η : ℝ) (hη : 0 < η) (hη1 : η < 1) (v : ℝ → ℝ)
    (hv : ∀ θ ∈ Iθo, HasDerivAt v (deriv v θ) θ)
    (hintA : MeasureTheory.IntegrableOn (fun θ => v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) Iθo)
    (hintC : MeasureTheory.IntegrableOn
      (fun θ => v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η)) Iθo)
    (hintN : MeasureTheory.IntegrableOn
      (fun θ => v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)) Iθo) :
    (∫ θ in Iθo, v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η))
      = (∫ θ in Iθo, v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        + (1 + η) * (∫ θ in Iθo,
            v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)) := by
  -- ## integrability of the derivative of the primitive
  have hintD : MeasureTheory.IntegrableOn (cP' η v) Iθo := by
    have h1 : MeasureTheory.IntegrableOn
        (fun θ => 2 * (v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η))) Iθo :=
      hintC.const_mul 2
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (2 : ℝ) * (v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))) Iθo :=
      hintA.const_mul 2
    have h3 : MeasureTheory.IntegrableOn
        (fun θ => (2 * (1 + η)) * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (-2 - η))) Iθo :=
      hintN.const_mul (2 * (1 + η))
    exact ((h1.sub h2).sub h3)
  -- ## the fundamental theorem of calculus for the primitive
  obtain ⟨fa, fb, hta, htb, hftc⟩ :=
    Work.FTS.EllipticEst.H2W.I1cb.ftc_open_interval (f := cP η v) (f' := cP' η v)
      (by positivity : (0 : ℝ) < Real.pi / 2) (fun θ hθ => cP_hasDerivAt η v hθ (hv θ hθ))
      hintD
  -- ## the two limits of the primitive vanish
  have hGNleft : MeasureTheory.IntegrableOn
      (fun θ => v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η))
      (Set.Ioo (0 : ℝ) (Real.pi / 6)) :=
    hintN.mono_set (fun x hx => ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
  have hGNright : MeasureTheory.IntegrableOn
      (fun θ => v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η))
      (Set.Ioo (Real.pi / 3) (Real.pi / 2)) :=
    hintN.mono_set (fun x hx => ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
  have hbd0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 6),
      |cP η v θ| ≤ 2 * Real.sin (2 * θ)
        * |v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)| := by
    intro θ hθ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hcos : (1 / 2 : ℝ) ≤ Real.cos (2 * θ) := by
      have h2θ0 : (0 : ℝ) ≤ 2 * θ := by linarith [hθ.1]
      have h2θ1 : 2 * θ ≤ Real.pi / 3 := by linarith [hθ.2]
      have h := Real.cos_le_cos_of_nonneg_of_le_pi h2θ0 (by linarith [Real.pi_pos]) h2θ1
      rwa [Real.cos_pi_div_three] at h
    have hca : |Real.cos (2 * θ)| ≤ 2 * (Real.cos (2 * θ)) ^ 2 := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ Real.cos (2 * θ))]
      nlinarith [hcos]
    exact abs_cP_le η v hspos hca
  have hbdπ : ∀ θ ∈ Set.Ioo (Real.pi / 3) (Real.pi / 2),
      |cP η v θ| ≤ 2 * Real.sin (2 * θ)
        * |v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)| := by
    intro θ hθ
    have hspos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos])
    have hcos : Real.cos (2 * θ) ≤ -(1 / 2 : ℝ) := by
      have h2θ0 : (0 : ℝ) ≤ 2 * Real.pi / 3 := by positivity
      have h2θ1 : 2 * θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
      have h2θ2 : 2 * Real.pi / 3 ≤ 2 * θ := by linarith [hθ.1, Real.pi_pos]
      have h := Real.cos_le_cos_of_nonneg_of_le_pi h2θ0 h2θ1 h2θ2
      have h2 : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
        rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
          Real.cos_pi_div_three]
      rwa [h2] at h
    have hca : |Real.cos (2 * θ)| ≤ 2 * (Real.cos (2 * θ)) ^ 2 := by
      rw [abs_of_nonpos (by linarith : Real.cos (2 * θ) ≤ 0)]
      nlinarith [hcos]
    exact abs_cP_le η v hspos hca
  have hfa : fa = 0 :=
    Work.FTS.EllipticEst.H2W.I1cb.boundary_vanish_left (F := cP η v)
      (G := fun θ => v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η))
      (c := fa) (d := Real.pi / 6) (C := 2) (by linarith [Real.pi_pos]) (by norm_num) hta hbd0 hGNleft
  have hfb : fb = 0 :=
    Work.FTS.EllipticEst.H2W.I1cb.boundary_vanish_right (F := cP η v)
      (G := fun θ => v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η))
      (c := fb) (d := Real.pi / 3) (C := 2) (by linarith [Real.pi_pos]) (by norm_num) htb hbdπ hGNright
  have hzero : (∫ θ in Iθo, cP' η v θ) = 0 := by
    rw [hftc, hfa, hfb, sub_zero]
  -- ## split the integral of `P'`
  -- ## named pieces and the splitting of the integral of `P'`
  set F : ℝ → ℝ := fun θ =>
    2 * (v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η)) with hF
  set G : ℝ → ℝ := fun θ => 2 * (v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) with hG
  set H : ℝ → ℝ := fun θ => 2 * (1 + η) * (v θ ^ 2 * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-2 - η)) with hH
  have hFi : MeasureTheory.IntegrableOn F Iθo := by rw [hF]; exact hintC.const_mul 2
  have hGi : MeasureTheory.IntegrableOn G Iθo := by rw [hG]; exact hintA.const_mul 2
  have hHi : MeasureTheory.IntegrableOn H Iθo := by rw [hH]; exact hintN.const_mul (2 * (1 + η))
  have hsplit : (∫ θ in Iθo, cP' η v θ)
      = 2 * (∫ θ in Iθo, v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η))
        - 2 * (∫ θ in Iθo, v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η))
        - 2 * (1 + η) * (∫ θ in Iθo,
            v θ ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (-2 - η)) := by
    have heq : (∫ θ in Iθo, cP' η v θ) = ∫ θ in Iθo, F θ - G θ - H θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      simp only [cP', hF, hG, hH]
    have hFG : (∫ θ in Iθo, F θ - G θ) = (∫ θ in Iθo, F θ) - (∫ θ in Iθo, G θ) :=
      MeasureTheory.integral_sub hFi hGi
    have hFGH : (∫ θ in Iθo, F θ - G θ - H θ)
        = (∫ θ in Iθo, F θ - G θ) - (∫ θ in Iθo, H θ) :=
      MeasureTheory.integral_sub (hFi.sub hGi) hHi
    have hF' : (∫ θ in Iθo, F θ)
        = 2 * (∫ θ in Iθo,
            v θ * deriv v θ * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-1 - η)) := by
      rw [hF]
      exact MeasureTheory.integral_const_mul 2 _
    have hG' : (∫ θ in Iθo, G θ)
        = 2 * (∫ θ in Iθo, v θ ^ 2 * (Real.sin (2 * θ)) ^ (-η)) := by
      rw [hG]
      exact MeasureTheory.integral_const_mul 2 _
    have hH' : (∫ θ in Iθo, H θ)
        = 2 * (1 + η) * (∫ θ in Iθo, v θ ^ 2 * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (-2 - η)) := by
      rw [hH]
      exact MeasureTheory.integral_const_mul (2 * (1 + η)) _
    rw [heq, hFGH, hFG, hF', hG', hH']
  linarith [hzero, hsplit]

end Work.FTS.EllipticEst.H2W.SlotA
