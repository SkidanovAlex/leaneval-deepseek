/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/Jeps_contDiffOn.lean` — E1: `J_ε` smooths

The target of this file is `Jeps_contDiffOn`: the log-coordinate mollifier `J_ε` of
`Submission/Work/FTS/StrongEps/Basic.lean` sends *any* locally integrable profile to a profile
which is `C^n` on the open quadrant `Quad` `(0,∞) × (0,π/2)`, for every `n`.

The proof is the standard convolution argument, carried out in the log coordinates
`s = log z`, `ζ = log tan θ`:

* on `Quad`, `J_ε f` equals the convolution `Jker ρ ε ⋆ logPull f` evaluated at `(s, ζ)`
  (`Jeps_eq_conv`); this is `logPull_shift`, the statement that the two shifts `zShift`/`thShift`
  of the kernel are the translations `s ↦ s - p₁`, `ζ ↦ ζ - p₂`;
* `Jker ρ ε = ε⁻² · ρ (ε⁻¹ • ·)` is `C^n` (`contDiff_Jker`) and compactly supported
  (`hasCompactSupport_Jker`, from the support condition in `IsSmoothKernel`), while `logPull f`
  is locally integrable by hypothesis; hence the convolution is `C^n`
  (`HasCompactSupport.contDiff_convolution_left`);
* the log-coordinate map `p ↦ (log p.1, log (tan p.2))` is `C^∞` on `Quad`
  (`contDiffOn_logMap`), so the composite is `C^n` on `Quad`.

This is the smoothing half of **E1** of the design; the weight bounds (the fact that the same
construction is bounded on the weighted norms, uniformly in `ε`) live in the `E1`-modules
`wt*_shift_le.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Convolution
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-! ## The kernel `Jker ρ ε` -/

/-- The rescaled kernel `Jker ρ ε` is `C^n` as soon as `ρ` is. -/
theorem contDiff_Jker (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) (ε : ℝ) (n : ℕ) :
    ContDiff ℝ n (Jker ρ ε) := by
  have h1 : ContDiff ℝ n (fun p : ℝ × ℝ => ρ (ε⁻¹ • p)) :=
    (hρ.smooth n).comp (ContDiff.const_smul (ε⁻¹) (contDiff_id (n := (n : WithTop ℕ∞))))
  have h2 : ContDiff ℝ n (fun p : ℝ × ℝ => (ε⁻¹ ^ 2) * ρ (ε⁻¹ • p)) := by
    simpa only [smul_eq_mul] using h1.const_smul (ε⁻¹ ^ 2)
  exact h2

/-- The rescaled kernel `Jker ρ ε` is compactly supported: its support is contained in the
square of half-side `|ε|` (the support condition `IsMollKernel.support` holds on the closed unit
ball). -/
theorem hasCompactSupport_Jker (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (Jker ρ ε) := by
  refine HasCompactSupport.intro (K := Set.Icc (-|ε|) |ε| ×ˢ Set.Icc (-|ε|) |ε|)
    (isCompact_Icc.prod isCompact_Icc) ?_
  rintro ⟨x1, x2⟩ hx
  have hx' : ¬(-|ε| ≤ x1 ∧ x1 ≤ |ε|) ∨ ¬(-|ε| ≤ x2 ∧ x2 ≤ |ε|) := by
    simpa only [Set.mem_prod, Set.mem_Icc, not_and_or] using hx
  have aux : ∀ y : ℝ, ¬(-|ε| ≤ y ∧ y ≤ |ε|) → |ε| < |y| := by
    intro y hy
    rw [not_and_or, not_le, not_le] at hy
    rcases hy with h | h
    · have hy0 : y < 0 := by linarith [abs_nonneg ε, h]
      have : |y| = -y := abs_of_neg hy0
      linarith
    · have hy0 : 0 < y := by linarith [abs_nonneg ε, h]
      have : |y| = y := abs_of_nonneg hy0.le
      linarith
  have hbig : |ε| < |x1| ∨ |ε| < |x2| := by
    rcases hx' with h | h
    · exact Or.inl (aux x1 h)
    · exact Or.inr (aux x2 h)
  have habs_aux : ∀ y : ℝ, |ε| < |y| → (1 : ℝ) < (ε⁻¹ * y) ^ 2 := by
    intro y hy
    have h1 : (1 : ℝ) < |ε⁻¹ * y| := by
      rw [abs_mul, abs_inv, abs_of_pos hε, ← inv_mul_cancel₀ (ne_of_gt hε)]
      simpa [abs_of_pos hε] using mul_lt_mul_of_pos_left hy (inv_pos.mpr hε)
    have h2 : ((1 : ℝ)) ^ 2 < (ε⁻¹ * y) ^ 2 := by
      rw [sq_lt_sq]
      simpa using h1
    simpa using h2
  have hρ0 : ρ (ε⁻¹ • (x1, x2)) = 0 := by
    by_contra hne
    have hle := hρ.moll.support _ hne
    simp only [Prod.smul_mk, smul_eq_mul] at hle
    have hsum : (1 : ℝ) < (ε⁻¹ * x1) ^ 2 + (ε⁻¹ * x2) ^ 2 := by
      rcases hbig with h | h
      · nlinarith [habs_aux x1 h, sq_nonneg (ε⁻¹ * x2)]
      · nlinarith [habs_aux x2 h, sq_nonneg (ε⁻¹ * x1)]
    exact absurd hle (not_le.mpr hsum)
  simp only [Jker, hρ0, mul_zero]

/-! ## The log-coordinate map -/

/-- The log-coordinate map `p ↦ (log p.1, log (tan p.2))` is `C^∞` on the open quadrant. -/
theorem contDiffOn_logMap (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => (sOf p.1, zetaOf p.2)) Quad := by
  have htan : ContDiffOn ℝ n Real.tan (Set.Ioo 0 (π / 2)) := fun x hx =>
    (Real.contDiffAt_tan.mpr (ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩))).contDiffWithinAt
  refine ContDiffOn.prodMk ?_ ?_
  · exact Real.contDiffOn_log.comp contDiffOn_fst (fun p hp => by simpa using hp.1.ne')
  · exact Real.contDiffOn_log.comp (htan.comp contDiffOn_snd (fun p hp => hp.2))
      (fun p hp => by
        simp only [mem_compl_iff, mem_singleton_iff]
        exact ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two hp.2.1 hp.2.2))

/-! ## `J_ε` is the convolution in the log coordinates -/

/-- On the open quadrant, `J_ε f` is the convolution of `logPull f` with the kernel `Jker ρ ε`,
evaluated at the log coordinates `(s, ζ) = (log z, log tan θ)`. -/
theorem Jeps_eq_conv (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Jeps ρ ε f z θ
      = (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f) (sOf z, zetaOf θ) := by
  rw [Jeps_eq_integral ρ ε f hz hθ, MeasureTheory.convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [show (sOf z, zetaOf θ) - p = (sOf z - p.1, zetaOf θ - p.2) from Prod.mk_sub_mk _ _ _ _,
    ← logPull_shift f hz hθ]

/-! ## The main statement -/

theorem Jeps_contDiffOn (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : MeasureTheory.LocallyIntegrable (logPull f) volume) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Jeps ρ ε f)) Quad := by
  intro n
  have hconv : ContDiff ℝ n
      (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f) :=
    (hasCompactSupport_Jker ρ hρ hε).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (contDiff_Jker ρ hρ ε n) hf
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ =>
        (Jker ρ ε ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] logPull f) (sOf p.1, zetaOf p.2))
      Quad :=
    hconv.comp_contDiffOn (contDiffOn_logMap n)
  refine hcomp.congr (fun p hp => ?_)
  exact Jeps_eq_conv ρ ε f hp.1 hp.2

end Work.FTS.StrongEps
