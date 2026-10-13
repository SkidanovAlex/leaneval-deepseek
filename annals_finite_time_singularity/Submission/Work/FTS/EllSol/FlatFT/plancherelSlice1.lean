/-
Copyright: work module for the Elgindi finite-time singularity project.

# Plancherel for the `t`-Fourier slice, first order

`Work.FTS.EllSol.FlatFT.plancherelSlice1`:
`∫ ξ, ‖slice1 h ξ‖ ^ 2 = ∫ t, ‖h t‖ ^ 2` for `h` continuous with compact support.

Here `slice1 h ξ = ∫ t, h t * exp (-(2π I ξ t))` is the (Mathlib-convention) Fourier transform
`𝓕 h ξ = ∫ t, 𝐞 (-⟪t, ξ⟫) • h t`; the two differ only by the commutativity of the product in
`ℂ` (`slice1_eq_fourier`).

The proof decomposes as follows.

* `slice1_eq_fourier` : `slice1 h ξ = 𝓕 h ξ` (pointwise).
* `lp_norm_sq_eq_integral` : for `f : Lp ℂ 2 volume`, `‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2`.  This is
  `Lp.norm_def` combined with `MemLp.eLpNorm_eq_integral_rpow_norm`.
* `fourier_lp_pairing` : the self-adjointness of the Fourier transform between the `L²` class of
  `h` and a Schwartz test function `ψ`,
  `∫ x, ψ x • 𝓕 (toLp h) x = ∫ x, 𝓕 ψ x • h x`.
  It is read off from Mathlib's tempered distribution identity
  `Lp.fourier_toTemperedDistribution_eq` (`𝓕 (toLp h) ψ = (toLp h) (𝓕 ψ)`).
* `fourier_lp_ae_eq` : the `L²` Fourier transform of an `L¹ ∩ L²` function is a.e. equal to its
  pointwise Fourier transform.  This is the crucial identification: the pairings with Schwartz
  test functions determine the `L²` class, and Mathlib's
  `ae_eq_of_integral_contDiff_smul_eq` converts the resulting identity against all smooth
  compactly supported test functions into an a.e. equality.
* the target theorem then combines these with Plancherel at the `L²` level,
  `Lp.norm_fourier_eq : ‖𝓕 f‖ = ‖f‖`.
-/
import Mathlib.Analysis.Fourier.LpSpace
import Submission.Work.FTS.EllSol.FlatFT.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory
open scoped FourierTransform

namespace Work.FTS.EllSol.FlatFT

noncomputable section

set_option maxHeartbeats 800000

/-- `slice1 h ξ` is the pointwise Fourier transform `𝓕 h ξ` (Mathlib's convention). -/
theorem slice1_eq_fourier (h : ℝ → ℂ) (ξ : ℝ) : slice1 h ξ = 𝓕 h ξ := by
  rw [Real.fourier_eq']
  rw [slice1]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Real.inner_apply, smul_eq_mul]
  have hexp : -(2 * (Real.pi : ℂ) * Complex.I * ξ * (t : ℂ))
      = ↑(-2 * Real.pi * (t * ξ)) * Complex.I := by
    push_cast
    ring
  rw [hexp]
  ring

/-- The `L²` norm of an `L²` function of one real variable, as an integral. -/
theorem lp_norm_sq_eq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ ξ : ℝ, ‖(f : ℝ → ℂ) ξ‖ ^ 2 := by
  have hmem : MemLp (f : ℝ → ℂ) 2 (volume : Measure ℝ) := Lp.memLp f
  have hnorm : ‖f‖ = Real.sqrt (∫ ξ : ℝ, ‖(f : ℝ → ℂ) ξ‖ ^ 2) := by
    rw [Lp.norm_def, hmem.eLpNorm_eq_integral_rpow_norm (p := 2) (μ := volume)
      (by norm_num) (by norm_num)]
    rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num
  rw [hnorm, Real.sq_sqrt (integral_nonneg (fun _ => by positivity))]

/-- The pairing identity behind Plancherel for `L¹ ∩ L²` functions: the `L²` Fourier transform
of the class of `h` is self-adjoint against Schwartz test functions. -/
theorem fourier_lp_pairing {h : ℝ → ℂ} (h2 : MemLp h 2 (volume : Measure ℝ))
    (ψ : SchwartzMap ℝ ℂ) :
    ∫ x : ℝ, (ψ : ℝ → ℂ) x • (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) x
      = ∫ x : ℝ, (𝓕 (ψ : ℝ → ℂ)) x • h x := by
  have hdist := Lp.fourier_toTemperedDistribution_eq (h2.toLp h)
  have happ := congrArg (fun T : TemperedDistribution ℝ ℂ => T ψ) hdist
  rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at happ
  rw [← happ]
  apply integral_congr_ae
  filter_upwards [h2.coeFn_toLp] with x hx
  rw [hx]
  simp only [SchwartzMap.fourier_coe]

/-- The `L²` Fourier transform of an `L¹ ∩ L²` function is, almost everywhere, its pointwise
Fourier transform. -/
theorem fourier_lp_ae_eq {h : ℝ → ℂ} (h1 : Integrable h) (h2 : MemLp h 2 (volume : Measure ℝ)) :
    ((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 h := by
  have hFmem : MemLp (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) 2 volume :=
    Lp.memLp _
  have hFcont : Continuous (𝓕 h) :=
    VectorFourier.fourierIntegral_continuous (e := Real.fourierChar) (μ := volume)
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner h1
  refine ae_eq_of_integral_contDiff_smul_eq (hFmem.locallyIntegrable (by norm_num))
    (hFcont.locallyIntegrable) ?_
  intro g hg hgsupp
  have hof : ContDiff ℝ (↑(⊤ : ℕ∞)) (⇑Complex.ofRealCLM) := Complex.ofRealCLM.contDiff
  have hgC : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => (g x : ℂ)) := hof.comp hg
  have hsuppC : HasCompactSupport (fun x : ℝ => (g x : ℂ)) := hgsupp.comp_left Complex.ofReal_zero
  let ψ : SchwartzMap ℝ ℂ := hsuppC.toSchwartzMap hgC
  have hψx : ∀ x : ℝ, ψ x = (g x : ℂ) := fun x => rfl
  have hpair := fourier_lp_pairing h2 ψ
  have hself : ∫ x : ℝ, (𝓕 h) x • (ψ : ℝ → ℂ) x
      = ∫ x : ℝ, h x • (𝓕 (ψ : ℝ → ℂ)) x := by
    have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
      (μ := volume) (ν := volume) (L := innerₗ ℝ) (f := h) (g := (ψ : ℝ → ℂ))
      Real.continuous_fourierChar continuous_inner h1 ψ.integrable
    rw [flip_innerₗ] at h
    exact h
  have hcomm1 : ∫ x : ℝ, (𝓕 (ψ : ℝ → ℂ)) x • h x = ∫ x : ℝ, h x • (𝓕 (ψ : ℝ → ℂ)) x := by
    apply integral_congr_ae
    filter_upwards with x
    exact mul_comm _ _
  have hgψ : ∫ x : ℝ, g x • (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) x
      = ∫ x : ℝ, (ψ : ℝ → ℂ) x •
          (((𝓕 (h2.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hψx x, Complex.coe_smul]
  have hψg : ∫ x : ℝ, (𝓕 h) x • (ψ : ℝ → ℂ) x = ∫ x : ℝ, g x • (𝓕 h) x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hψx x]
    exact mul_comm _ _
  exact hgψ.trans (hpair.trans (hcomm1.trans (hself.symm.trans hψg)))

/-- **Plancherel's theorem for the first `t`-Fourier slice.**  For a continuous compactly
supported `h : ℝ → ℂ` the `L²` norm of `slice1 h` (the Fourier transform in `t`) equals the `L²`
norm of `h`. -/
theorem plancherelSlice1 (h : ℝ → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) :
    ∫ ξ : ℝ, ‖Work.FTS.EllSol.FlatFT.slice1 h ξ‖ ^ 2 = ∫ t : ℝ, ‖h t‖ ^ 2 := by
  have hInt : Integrable h := hh.integrable_of_hasCompactSupport hs
  have hMem : MemLp h 2 (volume : Measure ℝ) := hh.memLp_of_hasCompactSupport hs
  have hae := fourier_lp_ae_eq hInt hMem
  have hstep : ∫ ξ : ℝ, ‖slice1 h ξ‖ ^ 2
      = ∫ ξ : ℝ, ‖(((𝓕 (hMem.toLp h) : Lp ℂ 2 (volume : Measure ℝ))) : ℝ → ℂ) ξ‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hae] with ξ hξ
    rw [slice1_eq_fourier h ξ, ← hξ]
  rw [hstep, ← lp_norm_sq_eq_integral (𝓕 (hMem.toLp h)), Lp.norm_fourier_eq,
    lp_norm_sq_eq_integral (hMem.toLp h)]
  apply integral_congr_ae
  filter_upwards [hMem.coeFn_toLp] with t ht
  rw [ht]

end

end Work.FTS.EllSol.FlatFT
