/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the self-pairing of `L₀`

Elgindi, Annals 194 (3) 2021, §'Elliptic Regularity Estimates'.  The `α = 0` part of the
elliptic operator (PolarBSL) is

  `L₀(Ψ)(z,θ) = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`   (`Work.Elliptic.Lzero`),

whose coefficient `tan θ` blows up at `θ = π/2`.  Individual summands of `L₀` are therefore
*not* integrable against `Ψ` on the angular interval `Iθ = [0,π/2]`: e.g. the term
`(∂_θ tan θ) Ψ · Ψ = Ψ²/cos²θ` grows like `1/(π/2-θ)` at the right endpoint when
`Ψ(·,π/2) ≠ 0`.  The point of this file is that, **assuming `Ψ(z,π/2) = 0` for every `z`**
(so that `Ψ` vanishes at least to first order at `θ = π/2`, which is exactly the Dirichlet
condition of the problem), the *product* `θ ↦ L₀(Ψ)(z,θ) · Ψ(z,θ)` is integrable on `Iθ`.

## The argument

For `f = Ψ z`, and on the open interval `(0,π/2)` where `cos θ ≠ 0`, expanding `L₀` and using
`tan θ = sin θ / cos θ` gives the *purely algebraic* identity

  `L₀(Ψ)(z,θ) · f(θ)
      = -(f''θ)·f(θ) + (f(θ)/cos θ)² + sin θ · (f(θ)/cos θ) · f'(θ) - 6 f(θ)²`,

in which the singular terms of `L₀` have been recombined: the dangerous `f(θ)/cos²θ · f(θ)`
became `(f(θ)/cos θ)²`, whose boundedness at `π/2` is exactly `exists_bound_div_cos`
(`f/cos` is bounded because `f(π/2) = 0`), and `tan θ · f'(θ) · f(θ)` became
`sin θ · (f(θ)/cos θ) · f'(θ)`, bounded by `Cb · sup|f'|`.

`SmoothNbhd Ψ` makes `f` smooth on an *open* neighbourhood of `[0,π/2]`, so `f`, `f'` and `f''`
are all continuous on the compact `Iθ` (finite supremum bound), and each of the four terms of
the right hand side is bounded on `Iθ` and a.e. strongly measurable.  Since the two endpoints of
`Iθ` are null and `Iθ` has finite measure, `IntegrableOn.of_bound` gives the integrability of
any function that agrees with the right hand side a.e. (here: on `(0,π/2)`) and is bounded.

This is the integrability input used when splitting `∫_θ (L₀(Ψ)) Ψ` in the radial energy
estimates; it is stated for the `SmoothNbhd` class (smoothness on a neighbourhood of the closed
quadrant together with vanishing at `θ = π/2`) because that is what the callers have.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.Lzero_orthogonal
import Submission.Work.FTS.EllipticEst.exists_bound_div_cos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Auxiliary

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- **The self-pairing of `L₀` is integrable on the angular interval.**  If `Ψ` is smooth on an
open neighbourhood of the closed quadrant `[0,∞) × [0,π/2]` and vanishes on the angular boundary
`θ = π/2`, then for every `z > -1` the function `θ ↦ L₀(Ψ)(z,θ) · Ψ(z,θ)` is integrable on
`Iθ = [0,π/2]`.  (The hypothesis `z > -1` puts the slice `{z} × Iθ` inside the smoothness
region of `Ψ`.)  The apparent `tan`-singularity of `L₀` at `θ = π/2` cancels against the
vanishing of `Ψ` there; see the module header. -/
theorem Lzero_self_integrable_fts (Ψ : ℝ → ℝ → ℝ) (hsm : Work.Spaces.SmoothNbhd Ψ)
    (h1 : ∀ z, Ψ z (Real.pi / 2) = 0) {z : ℝ} (hz : z ∈ Set.Ioi (-1)) :
    MeasureTheory.IntegrableOn (fun θ => Work.Elliptic.Lzero Ψ z θ * Ψ z θ) Work.Spaces.Iθ := by
  -- the slice is smooth on an open neighbourhood of `[0, π/2]`
  have hsubV : Set.Icc (0 : ℝ) (π / 2) ⊆ Set.Ioo (-1) (π / 2 + 1) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsliceV : ContDiffOn ℝ ⊤ (fun θ : ℝ => Ψ z θ) (Set.Ioo (-1) (π / 2 + 1)) := by
    have hp : ContDiffOn ℝ ⊤ (fun θ : ℝ => (z, θ)) (Set.Ioo (-1) (π / 2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo (-1) (π / 2 + 1))
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) := fun θ hθ => ⟨hz, hθ⟩
    have h := hsm.comp hp hmap
    simpa [Function.comp_def, Function.uncurry] using h
  have hf_cont : ContinuousOn (fun θ : ℝ => Ψ z θ) Work.Spaces.Iθ :=
    hsliceV.continuousOn.mono hsubV
  have hd1V : ContDiffOn ℝ ⊤ (deriv (fun θ : ℝ => Ψ z θ)) (Set.Ioo (-1) (π / 2 + 1)) :=
    hsliceV.deriv_of_isOpen isOpen_Ioo le_top
  have hd2V : ContDiffOn ℝ ⊤ (deriv (deriv (fun θ : ℝ => Ψ z θ))) (Set.Ioo (-1) (π / 2 + 1)) :=
    hd1V.deriv_of_isOpen isOpen_Ioo le_top
  have hdf_cont : ContinuousOn (deriv (fun θ : ℝ => Ψ z θ)) Work.Spaces.Iθ :=
    hd1V.continuousOn.mono hsubV
  have hdd_cont : ContinuousOn (deriv (deriv (fun θ : ℝ => Ψ z θ))) Work.Spaces.Iθ :=
    hd2V.continuousOn.mono hsubV
  -- uniform bounds for `Ψ z`, `∂_θ(Ψ z)` and `∂_θθ(Ψ z)` on the compact `Iθ`
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hdf_cont
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hdd_cont
  have h2 : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (π / 2)) :=
    (hsliceV.mono hsubV).of_le (by norm_num)
  -- the vanishing of `Ψ` at `θ = π/2` makes `θ ↦ Ψ(z,θ)/cos θ` bounded
  obtain ⟨Cb, hCb0, hCb⟩ :=
    Work.FTS.EllipticEst.exists_bound_div_cos (fun θ : ℝ => Ψ z θ) h2 (h1 z)
  set Mf' : ℝ := max Mf 0 with hMf'def
  set M1' : ℝ := max M1 0 with hM1'def
  set M2' : ℝ := max M2 0 with hM2'def
  have hMf'0 : 0 ≤ Mf' := le_max_right _ _
  have hM1'0 : 0 ≤ M1' := le_max_right _ _
  have hM2'0 : 0 ≤ M2' := le_max_right _ _
  have hf_b : ∀ x ∈ Work.Spaces.Iθ, |Ψ z x| ≤ Mf' := by
    intro x hx
    have h := hMf x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have hd1_b : ∀ x ∈ Work.Spaces.Iθ, |deriv (fun θ : ℝ => Ψ z θ) x| ≤ M1' := by
    intro x hx
    have h := hM1 x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  have hd2_b : ∀ x ∈ Work.Spaces.Iθ, |deriv (deriv (fun θ : ℝ => Ψ z θ)) x| ≤ M2' := by
    intro x hx
    have h := hM2 x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  -- the algebraic rewriting of `L₀(Ψ) · Ψ` on the open quadrant
  have hpoint : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Elliptic.Lzero Ψ z θ * Ψ z θ
        = -(deriv (deriv (fun s : ℝ => Ψ z s)) θ) * Ψ z θ
          + (Ψ z θ / Real.cos θ) ^ 2
          + Real.sin θ * (Ψ z θ / Real.cos θ) * deriv (fun s : ℝ => Ψ z s) θ
          - 6 * (Ψ z θ) ^ 2 := by
    intro θ hθ
    have hcos : Real.cos θ ≠ 0 := by
      have hmem : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
      exact ne_of_gt (Real.cos_pos_of_mem_Ioo hmem)
    have hca : ContDiffAt ℝ ⊤ (fun s : ℝ => Ψ z s) θ :=
      hsliceV.contDiffAt (isOpen_Ioo.mem_nhds (hsubV ⟨hθ.1.le, hθ.2.le⟩))
    have hd : DifferentiableAt ℝ (fun s : ℝ => Ψ z s) θ := hca.differentiableAt (by simp)
    have htan : HasDerivAt (fun s : ℝ => Real.tan s * Ψ z s)
        (1 / Real.cos θ ^ 2 * Ψ z θ + Real.tan θ * deriv (fun s : ℝ => Ψ z s) θ) θ :=
      (Real.hasDerivAt_tan hcos).mul hd.hasDerivAt
    rw [Work.Elliptic.Lzero_eq_deriv, htan.deriv, Real.tan_eq_sin_div_cos]
    field_simp
    ring
  -- the a.e. bounded majorant
  set R : ℝ → ℝ := fun θ => -(deriv (deriv (fun s : ℝ => Ψ z s)) θ) * Ψ z θ
      + (Ψ z θ / Real.cos θ) ^ 2
      + Real.sin θ * (Ψ z θ / Real.cos θ) * deriv (fun s : ℝ => Ψ z s) θ
      - 6 * (Ψ z θ) ^ 2 with hRdef
  have hR_eq : ∀ θ : ℝ, R θ = -(deriv (deriv (fun s : ℝ => Ψ z s)) θ) * Ψ z θ
      + (Ψ z θ / Real.cos θ) ^ 2
      + Real.sin θ * (Ψ z θ / Real.cos θ) * deriv (fun s : ℝ => Ψ z s) θ
      - 6 * (Ψ z θ) ^ 2 := fun θ => rfl
  have hae : (fun θ => Work.Elliptic.Lzero Ψ z θ * Ψ z θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ] R := by
    show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), Work.Elliptic.Lzero Ψ z θ * Ψ z θ = R θ
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    have h1' : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by rw [MeasureTheory.ae_iff]; simp
    have h2' : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ π / 2 := by rw [MeasureTheory.ae_iff]; simp
    filter_upwards [h1', h2'] with θ hθ0 hθ2 hθmem
    rw [hR_eq θ]
    exact hpoint θ ⟨lt_of_le_of_ne hθmem.1 (Ne.symm hθ0), lt_of_le_of_ne hθmem.2 hθ2⟩
  -- a.e. strong measurability of the majorant
  have hf_aem : AEMeasurable (fun θ : ℝ => Ψ z θ) (volume.restrict Work.Spaces.Iθ) :=
    hf_cont.aemeasurable measurableSet_Icc
  have hdf_aem : AEMeasurable (deriv (fun θ : ℝ => Ψ z θ)) (volume.restrict Work.Spaces.Iθ) :=
    hdf_cont.aemeasurable measurableSet_Icc
  have hdd_aem : AEMeasurable (deriv (deriv (fun θ : ℝ => Ψ z θ)))
      (volume.restrict Work.Spaces.Iθ) := hdd_cont.aemeasurable measurableSet_Icc
  have hdiv_aem : AEMeasurable (fun θ : ℝ => Ψ z θ / Real.cos θ)
      (volume.restrict Work.Spaces.Iθ) := hf_aem.div Real.measurable_cos.aemeasurable
  have hR_aem : AEMeasurable R (volume.restrict Work.Spaces.Iθ) := by
    have hA : AEMeasurable (fun θ : ℝ => -(deriv (deriv (fun s : ℝ => Ψ z s)) θ) * Ψ z θ)
        (volume.restrict Work.Spaces.Iθ) := hdd_aem.neg.mul hf_aem
    have hB : AEMeasurable (fun θ : ℝ => (Ψ z θ / Real.cos θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) := hdiv_aem.pow_const 2
    have hC : AEMeasurable (fun θ : ℝ => Real.sin θ * (Ψ z θ / Real.cos θ)
        * deriv (fun s : ℝ => Ψ z s) θ) (volume.restrict Work.Spaces.Iθ) :=
      (Real.measurable_sin.aemeasurable.mul hdiv_aem).mul hdf_aem
    have hD : AEMeasurable (fun θ : ℝ => 6 * (Ψ z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
      (hf_aem.pow_const 2).const_mul 6
    have hsum : AEMeasurable (fun θ : ℝ => -(deriv (deriv (fun s : ℝ => Ψ z s)) θ) * Ψ z θ
        + (Ψ z θ / Real.cos θ) ^ 2
        + Real.sin θ * (Ψ z θ / Real.cos θ) * deriv (fun s : ℝ => Ψ z s) θ
        - 6 * (Ψ z θ) ^ 2) (volume.restrict Work.Spaces.Iθ) := ((hA.add hB).add hC).sub hD
    simpa only [hR_eq] using hsum
  -- the uniform bound of the majorant
  have hR_bound : ∀ θ ∈ Work.Spaces.Iθ,
      |R θ| ≤ M2' * Mf' + Cb ^ 2 + Cb * M1' + 6 * Mf' ^ 2 := by
    intro θ hθ
    rw [hR_eq θ]
    have hA : |-(deriv (deriv (fun s : ℝ => Ψ z s)) θ) * Ψ z θ| ≤ M2' * Mf' := by
      rw [abs_mul, abs_neg]
      exact mul_le_mul (hd2_b θ hθ) (hf_b θ hθ) (abs_nonneg _) hM2'0
    have hB : |(Ψ z θ / Real.cos θ) ^ 2| ≤ Cb ^ 2 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hCb θ hθ) 2
    have hC : |Real.sin θ * (Ψ z θ / Real.cos θ) * deriv (fun s : ℝ => Ψ z s) θ|
        ≤ Cb * M1' := by
      rw [abs_mul, abs_mul]
      calc |Real.sin θ| * |Ψ z θ / Real.cos θ| * |deriv (fun s : ℝ => Ψ z s) θ|
          ≤ 1 * Cb * M1' := by
            refine mul_le_mul (mul_le_mul (Real.abs_sin_le_one θ) (hCb θ hθ) (abs_nonneg _)
              (by norm_num)) (hd1_b θ hθ) (abs_nonneg _) ?_
            positivity
        _ = Cb * M1' := by ring
    have hD : |6 * (Ψ z θ) ^ 2| ≤ 6 * Mf' ^ 2 := by
      rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hf_b θ hθ) 2)
        (by norm_num)
    rw [abs_le] at hA hB hC hD ⊢
    constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2, hD.1, hD.2]
  -- conclude by `of_bound` and transfer along the a.e. identity
  have hR_int : MeasureTheory.IntegrableOn R Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.of_bound isCompact_Icc.measure_lt_top
      hR_aem.aestronglyMeasurable (M2' * Mf' + Cb ^ 2 + Cb * M1' + 6 * Mf' ^ 2) ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine Eventually.of_forall (fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    exact hR_bound θ hθ
  exact hR_int.congr_fun_ae hae.symm

end Work.FTS.EllipticEst.Auxiliary
