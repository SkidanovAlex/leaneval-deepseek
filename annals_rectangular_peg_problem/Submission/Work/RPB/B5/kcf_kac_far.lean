import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappa_shape_basic
import Submission.Work.RPB.B5.kA0_spec
import Submission.Work.RPB.B5.noL_far_flux

/-!
# B5: the phase `kac` is `t` on the far region `σ ≥ 2δ`

On the far region `σ ≥ 2δ` the collar `kgam` collapses to the rescaled unit circle

`kgam τ σ t = (√(2+2σ)) · exp ((t - π/2) I)`,

independently of `τ`, because there `krpf = 0`, `kphc = -(π/2 + 2πk)`, `kblf = 1` and `kg = 1`.
The flux integrand `ω_ℂ (∂_σ kgam, ∂_t kgam)` is therefore `deriv krd σ · krd σ = 1`, and the
phase constant `kA0` vanishes by `kA0_far_zero`; the fundamental theorem of calculus then gives
`kac τ σ t = ∫_0^t 1 = t`.

The three ingredients (`∂_σ`, `∂_t`, and the algebraic identity for `ω_ℂ` on a unit-modulus
exponential) are exactly the corresponding facts of the sibling no-`L` route
(`noL_far_flux`), whose collar agrees with `kgam` on `σ ≥ δ`; the bridge is
`ksb_kgam_far`/`ksb_kshape_far`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Elementary bridges to the no-`L` computation -/

/-- On the far region `σ ≥ 2δ` the phase offset `kphc` has reached `-(π/2 + 2πk)`, so the
corresponding exponential is the rotation by `-π/2`. -/
theorem kexp_kphc_far {δ : ℝ} (hδ : 0 < δ) (k : ℤ) {σ : ℝ} (hσ : 2 * δ ≤ σ) (u : ℝ) :
    Complex.exp (((u : ℂ) - (Real.pi : ℂ) / 2) * Complex.I)
      = Complex.exp (((u + kphc δ k σ : ℝ) : ℂ) * Complex.I) := by
  rw [ksb_kphc_far k hδ hσ]
  have h2 : ((u + (-(Real.pi / 2 + 2 * Real.pi * k)) : ℝ) : ℂ) * Complex.I
      = ((u : ℂ) - (Real.pi : ℂ) / 2) * Complex.I
        + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `deriv krd σ = 1 / krd σ`. -/
theorem kderiv_krd {σ : ℝ} (hσ : -1 < σ) : deriv krd σ = 1 / krd σ :=
  fluxAux_deriv_rd hσ

/-- The `σ`-derivative of the far family, on the region `σ ≥ 2δ`. -/
theorem kderiv_far_sigma (CI : Work.RPV.CurveIsotopy) {δ : ℝ} (hδ : 0 < δ) (k : ℤ)
    {τ σ u : ℝ} (hσ : 2 * δ ≤ σ) :
    deriv (fun s : ℝ => kfsh CI δ k τ s u) σ
      = ((deriv krd σ : ℝ) : ℂ) * Complex.exp (((u + kphc δ k σ : ℝ) : ℂ) * Complex.I) :=
  fluxAux_sigma_deriv CI hδ k hσ

/-- The `t`-derivative of the `τ = 0` slice of the far family. -/
theorem kderiv_far_t (CI : Work.RPV.CurveIsotopy) (δ : ℝ) (k : ℤ) (σ u : ℝ) :
    deriv (fun s : ℝ => (krd σ : ℂ) * CI.c 0 (s + kphc δ k σ)) u
      = (krd σ : ℂ) *
          (Complex.exp (((u + kphc δ k σ : ℝ) : ℂ) * Complex.I) * Complex.I) :=
  fluxAux_t_deriv CI δ k σ u

/-! ## The two derivatives of `kgam` at the far end -/

/-- On `σ ≥ 2δ` the collar `kgam` coincides with the far family `kfsh` in a whole neighbourhood of
`σ` (since `σ > δ`), so its `σ`-derivative is that of `kfsh`. -/
theorem kgam_far_sigma_deriv (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) {τ σ u : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hσ : 2 * δ ≤ σ) :
    deriv (fun s : ℝ => kgam CI W ρh δ k τ s u) σ
      = ((deriv krd σ : ℝ) : ℂ) * Complex.exp (((u + kphc δ k σ : ℝ) : ℂ) * Complex.I) := by
  have hδσ : δ < σ := by linarith
  have hev : Filter.EventuallyEq (nhds σ) (fun s : ℝ => kgam CI W ρh δ k τ s u)
      (fun s : ℝ => kfsh CI δ k τ s u) :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hδσ)
      (fun s hs => by
        show kgam CI W ρh δ k τ s u = kfsh CI δ k τ s u
        rw [ksb_kgam_far CI W ρh hδ k hτ (le_of_lt hs),
          ksb_kshape_eq_kfsh CI W ρh hδ (le_of_lt hs) k τ u])
  rw [hev.deriv_eq]
  exact kderiv_far_sigma CI hδ k hσ

/-- On `σ ≥ 2δ` the collar `kgam` is identically the far family (on the `τ = 0` slice of the
isotopy), so its `t`-derivative is that of `krd σ · CI.c 0 (· + kphc δ k σ)`. -/
theorem kgam_far_t_deriv (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) {τ σ u : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hσ : 2 * δ ≤ σ) :
    deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) u
      = (krd σ : ℂ) *
          (Complex.exp (((u + kphc δ k σ : ℝ) : ℂ) * Complex.I) * Complex.I) := by
  have hfun : (fun s : ℝ => kgam CI W ρh δ k τ σ s)
      = fun s : ℝ => (krd σ : ℂ) * CI.c 0 (s + kphc δ k σ) := by
    funext s
    rw [ksb_kgam_far CI W ρh hδ k hτ (by linarith : δ ≤ σ),
      ksb_kshape_far CI W ρh δ k hδ hσ]
    congr 1
    rw [CI.start]
    exact kexp_kphc_far hδ k hσ s
  rw [hfun]
  exact kderiv_far_t CI δ k σ u

/-! ## The flux integrand on the far region -/

/-- On the far region `σ ≥ 2δ` the flux integrand `ω_ℂ (∂_σ kgam, ∂_t kgam)` is identically `1`:
both derivatives are of the form `x · E` and `y · (E · I)` with `‖E‖ = 1`, and
`x = deriv krd σ = 1 / krd σ`, `y = krd σ`. -/
theorem kac_far_integrand (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, 2 * δ ≤ σ → ∀ u : ℝ,
      Work.RPV.ωC (deriv (fun s : ℝ => kgam CI W ρh δ k τ s u) σ)
        (deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) u) = 1 := by
  intro τ hτ σ hσ u
  have hσpos : (-1 : ℝ) < σ := by linarith
  have hA := kgam_far_sigma_deriv CI W ρh hδ k hτ hσ (u := u)
  have hB := kgam_far_t_deriv CI W ρh hδ k hτ hσ (u := u)
  rw [hA, hB]
  rw [fluxAux_omegaC_far (deriv krd σ) (krd σ)
    (Complex.exp (((u + kphc δ k σ : ℝ) : ℂ) * Complex.I))
    (Complex.norm_exp_ofReal_mul_I (u + kphc δ k σ))]
  rw [kderiv_krd hσpos]
  exact one_div_mul_cancel (ne_of_gt (ksb_krd_pos σ (by linarith)))

/-! ## The main statement -/

theorem kcf_kac_far (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℤ) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ σ : ℝ, 2 * δ ≤ σ → ∀ t : ℝ,
      Work.RPB.B5.kac CI W ρh δ k τ σ t = t := by
  intro τ hτ σ hσ t
  have hint : (∫ u in (0 : ℝ)..t,
        Work.RPV.ωC (deriv (fun s : ℝ => kgam CI W ρh δ k τ s u) σ)
          (deriv (fun s : ℝ => kgam CI W ρh δ k τ σ s) u)) = t := by
    rw [intervalIntegral.integral_congr
      (fun u _ => kac_far_integrand CI W ρh hδ k τ hτ σ hσ u)]
    simp
  rw [ksb_kac_apply, kA0_far_zero W ρh δ hδ k τ σ hσ, hint]
  ring

end Work.RPB.B5
