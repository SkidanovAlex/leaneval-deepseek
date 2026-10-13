/-
# The finite-interval `z`-integration by parts for `D_θ f`

This file proves `Work.Coercivity.dth_slice_z_ibp`: for `u = D_θ f` with `SmoothNbhd f`,
`R > 0` and `θ ∈ Iθ`, and assuming that `u·w` and `𝓛u·u·w²` are bounded on `(0,R)` (this is
what makes the boundary term at `z = 0` vanish and the derivative of the boundary term
integrable), one has

  `∫_0^R 𝓛u · u · w² = ½ ∫_0^R (u w)² + ½ R (u(R) w(R))²`.

The pointwise identity behind it is the `z`-integration by parts of §6 of Elgindi's paper,

  `𝓛u · u · w² = (u w)² + ½ z ∂_z((u w)²)`,

i.e. with `G(z) = z (u(z)w(z))²`,

  `𝓛u · u · w² = ½ (u w)² + ½ G'(z)`.

The boundedness hypotheses give `G(z) → 0` as `z → 0⁺` (`hb1`) and that `G'` is bounded
(hence integrable) on `(0,R)` (`hb2`), so the fundamental theorem of calculus on `[0,R]`
yields `∫_0^R G' = G(R) - G(0) = R (u(R)w(R))²`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.Coercivity.pz_mul_w
import Submission.Work.Coercivity.L_mul_w_deriv
import Submission.Work.Coercivity.l_self_w_sq_eq
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HardyZ
import Submission.Work.Coercivity.integrableOn_zw_sq_finite
import Submission.Work.Coercivity.continuousOn_zw_sq_finite

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## The pointwise identity `𝓛u · u · w² = (u w)² + ½ z ∂_z((u w)²)` -/

/-- The pointwise identity behind the `z`-integration by parts: for a function `u` whose
`θ`-slice is differentiable at `z > 0` with derivative `pz u z θ` (e.g. every slice of a
`SmoothNbhd` function at `z > 0`),

  `𝓛u · u · w² = (u w)² + ½ z ∂_z((u w)²)`.

This is `l_self_w_sq_eq` with the differentiability hypothesis extracted, so that it
applies without the full integrability package `IBP u`. -/
theorem L_self_w_sq_hasDerivAt {u : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hf : HasDerivAt (fun z' => u z' θ) (Spaces.pz u z θ) z) :
    L u z θ * u z θ * Spaces.w z ^ 2
      = (u z θ * Spaces.w z) ^ 2
        + (1 / 2) * (z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z) := by
  have hLw : L u z θ * Spaces.w z
      = u z θ * Spaces.w z + z * Spaces.pz (fun z θ => u z θ * Spaces.w z) z θ :=
    L_mul_w_deriv hz hf
  have hgw : DifferentiableAt ℝ (fun z' => u z' θ * Spaces.w z') z :=
    (hf.mul (hasDerivAt_w (ne_of_gt hz))).differentiableAt
  have hgsq : deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z
      = 2 * (u z θ * Spaces.w z) * Spaces.pz (fun z θ => u z θ * Spaces.w z) z θ := by
    have h1 := (hgw.hasDerivAt).pow 2
    have h2 : deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z
        = 2 * (u z θ * Spaces.w z) ^ (2 - 1) * deriv (fun z' => u z' θ * Spaces.w z') z :=
      h1.deriv
    rw [h2]
    simp only [Nat.reduceSub, pow_one]
    rfl
  have hkey : L u z θ * u z θ * Spaces.w z ^ 2
      = (L u z θ * Spaces.w z) * (u z θ * Spaces.w z) := by ring
  rw [hkey, hLw, hgsq]
  ring


/-! ## The derivative of the boundary term `G(z) = z (u w)²` -/

/-- `G(z) = z (u(z,θ) w(z))²` is differentiable at `z > 0` for a `SmoothNbhd` function `u`. -/
theorem hasDerivAt_zw_sq_b {u : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd u)
    {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => z' * (u z' θ * Spaces.w z') ^ 2)
      (deriv (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z) z := by
  have hu : HasDerivAt (fun z' => u z' θ) (Spaces.pz u z θ) z :=
    Spaces.hardyZ_hasDerivAt_slice u hsm hθ (by simp only [Set.mem_Ioi]; linarith)
  have hw : HasDerivAt Spaces.w (-2 * (1 + z) / z ^ 3) z := hasDerivAt_w (ne_of_gt hz)
  have hgw : DifferentiableAt ℝ (fun z' => u z' θ * Spaces.w z') z := (hu.mul hw).differentiableAt
  have hsq : DifferentiableAt ℝ (fun z' => (u z' θ * Spaces.w z') ^ 2) z := hgw.pow 2
  have hG : DifferentiableAt ℝ (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z :=
    (differentiableAt_id (x := z)).mul hsq
  exact hG.hasDerivAt

/-- The product rule for the boundary term:
`∂_z (z (u w)²) = (u w)² + z ∂_z((u w)²)` at `z > 0`. -/
theorem deriv_zw_sq_finite {u : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd u)
    {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) {z : ℝ} (hz : 0 < z) :
    deriv (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z
      = (u z θ * Spaces.w z) ^ 2 + z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z := by
  have hu : HasDerivAt (fun z' => u z' θ) (Spaces.pz u z θ) z :=
    Spaces.hardyZ_hasDerivAt_slice u hsm hθ (by simp only [Set.mem_Ioi]; linarith)
  have hw : HasDerivAt Spaces.w (-2 * (1 + z) / z ^ 3) z := hasDerivAt_w (ne_of_gt hz)
  have hgw : DifferentiableAt ℝ (fun z' => u z' θ * Spaces.w z') z := (hu.mul hw).differentiableAt
  have hsq : DifferentiableAt ℝ (fun z' => (u z' θ * Spaces.w z') ^ 2) z := hgw.pow 2
  have h1 : HasDerivAt (fun z' : ℝ => z') 1 z := by
    convert hasDerivAt_id z using 2 <;> rfl
  have h2 := h1.mul hsq.hasDerivAt
  have h3 : deriv (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) z
      = 1 * (u z θ * Spaces.w z) ^ 2
        + z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z := by
    convert h2.deriv using 1
  rw [h3]; ring

/-- `HasDerivAt` form of `deriv_zw_sq_finite`, with the derivative written out.  (This is
`deriv_zw_sq_integral.hasDerivAt_zw_sq` without the integrability package `IBP u`.) -/
theorem hasDerivAt_zw_sq_smooth {u : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd u)
    {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => z' * (u z' θ * Spaces.w z') ^ 2)
      ((u z θ * Spaces.w z) ^ 2 + z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z) z := by
  rw [← deriv_zw_sq_finite hsm hθ hz]
  exact hasDerivAt_zw_sq_b hsm hθ hz

/-! ## The finite-interval integration by parts -/

theorem dth_slice_z_ibp (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) (R : ℝ) (hR : 0 < R)
    {θ : ℝ} (hθ : θ ∈ Spaces.Iθ)
    (hb1 : ∃ C : ℝ, ∀ z ∈ Set.Ioo 0 R, |Spaces.Dth f z θ * Spaces.w z| ≤ C)
    (hb2 : ∃ C : ℝ, ∀ z ∈ Set.Ioo 0 R, |L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2| ≤ C) :
    ∫ z in Set.Icc 0 R, L (Spaces.Dth f) z θ * Spaces.Dth f z θ * Spaces.w z ^ 2
      = (1 / 2) * (∫ z in Set.Icc 0 R, (Spaces.Dth f z θ * Spaces.w z) ^ 2)
        + (1 / 2) * (R * (Spaces.Dth f R θ * Spaces.w R) ^ 2) := by
  set u := Spaces.Dth f with hu
  have hsm' : Spaces.SmoothNbhd u := by rw [hu]; exact Spaces.SmoothNbhd.Dth hsm
  have hbd := integrableOn_zw_sq_finite (u := u) hsm' hR hθ hb1 hb2
  obtain ⟨hh, hL⟩ := hbd
  -- `φ` is the derivative of the boundary term `G(z) = z (u w)²`
  set φ : ℝ → ℝ :=
    fun z => (u z θ * Spaces.w z) ^ 2 + z * deriv (fun z' => (u z' θ * Spaces.w z') ^ 2) z
    with hφdef
  -- `ψ = 2 𝓛u·u·w² - (u w)²` agrees with `φ` on `(0,R)`, and is integrable by `hb2`
  set ψ : ℝ → ℝ :=
    fun z => 2 * (L u z θ * u z θ * Spaces.w z ^ 2) - (u z θ * Spaces.w z) ^ 2 with hψdef
  have hψicc : IntegrableOn ψ (Set.Icc 0 R) := by
    rw [hψdef]
    exact MeasureTheory.Integrable.sub (MeasureTheory.Integrable.const_mul hL 2) hh
  have hψioo : IntegrableOn ψ (Set.Ioo 0 R) :=
    (integrableOn_Icc_iff_integrableOn_Ioo (f := ψ) (a := 0) (b := R)).mp hψicc
  have hφioo : IntegrableOn φ (Set.Ioo 0 R) := by
    refine hψioo.congr_fun (fun z hz => ?_) measurableSet_Ioo
    rw [hφdef, hψdef]
    beta_reduce
    have hf : HasDerivAt (fun z' => u z' θ) (Spaces.pz u z θ) z :=
      Spaces.hardyZ_hasDerivAt_slice u hsm' hθ (by simp only [Set.mem_Ioi]; linarith [hz.1])
    have h := L_self_w_sq_hasDerivAt (u := u) hz.1 hf
    rw [h]; ring
  have hφicc : IntegrableOn φ (Set.Icc 0 R) :=
    (integrableOn_Icc_iff_integrableOn_Ioo (f := φ) (a := 0) (b := R)).mpr hφioo
  -- continuity of the boundary term on `[0,R]` and its derivative on `(0,R)`
  have hcontG : ContinuousOn (fun z => z * (u z θ * Spaces.w z) ^ 2) (Set.Icc 0 R) :=
    continuousOn_zw_sq_finite (u := u) hsm' hR hθ hb1
  have hderivG : ∀ z ∈ Set.Ioo 0 R,
      HasDerivAt (fun z' => z' * (u z' θ * Spaces.w z') ^ 2) (φ z) z := by
    intro z hz
    rw [hφdef]
    exact hasDerivAt_zw_sq_smooth (u := u) hsm' hθ hz.1
  have hint : IntervalIntegrable φ volume 0 R :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR.le).mpr hφicc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hcontG hderivG hint
  have hconv : ∫ z in Set.Icc 0 R, φ z = ∫ z in (0 : ℝ)..R, φ z := by
    rw [intervalIntegral.integral_of_le hR.le]
    exact MeasureTheory.integral_Icc_eq_integral_Ioc
  -- the fundamental theorem of calculus gives the value of `∫ φ`
  have hFTV : ∫ z in Set.Icc 0 R, φ z = R * (u R θ * Spaces.w R) ^ 2 := by
    rw [hconv, hftc]
    simp
  -- rewrite the left-hand integrand pointwise
  have hcongr : ∫ z in Set.Icc 0 R, L u z θ * u z θ * Spaces.w z ^ 2
      = ∫ z in Set.Icc 0 R, ((1 / 2) * (u z θ * Spaces.w z) ^ 2 + (1 / 2) * φ z) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
    rcases eq_or_lt_of_le hz.1 with hz0 | hzpos
    · rw [← hz0, hφdef]
      beta_reduce
      simp [Spaces.w]
    · rw [hφdef]
      beta_reduce
      have hf : HasDerivAt (fun z' => u z' θ) (Spaces.pz u z θ) z :=
        Spaces.hardyZ_hasDerivAt_slice u hsm' hθ (by simp only [Set.mem_Ioi]; linarith)
      have h := L_self_w_sq_hasDerivAt (u := u) hzpos hf
      rw [h]; ring
  rw [hcongr, MeasureTheory.integral_add (MeasureTheory.Integrable.const_mul hh (1 / 2))
    (MeasureTheory.Integrable.const_mul hφicc (1 / 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hFTV]

end Work.Coercivity
