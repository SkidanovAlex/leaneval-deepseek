/-
Work module for the Elgindi finite-time singularity project.

# The pointwise Agmon inequality on a single angular slice, light weight

For `0 < α ≤ 1/4` and `f : ℝ → ℝ` of class `C²` on the open interval `(0, π/2)`, with the two
endpoint traces `f → 0` at `0⁺` and at `(π/2)⁻`, and with the weighted second derivative
`(f'')² sin(2θ)^{2-γ(α)}` integrable, one has

  `∫_θ (f')² σ ≤ -∫_θ f f'' σ`,   `σ = sin(2θ)^{2-γ(α)}`,  `γ(α) = 1 + α/10`.

This is the `μ`-weight slice Agmon inequality consumed by the level-`2` core slot
(`VopGen.coreASlot11`): it is the sharp (one-`√`-free) form of the interpolation, valid because
the light weight `σ` is *concave* on `(0, π/2)`.

## Proof

Write `a := 2 - γ(α) ∈ (0,1)`.  The double angular integration by parts for the light weight
(`TT.slice_ibp_light`, the already-proved generic brick) gives, whenever its five integrability
and four boundary clauses hold,

  `∫ (f')²σ = -∫ f f''σ - 2a ∫ f²σ - 2a(1-a) ∫ f²cos²(2θ) sin(2θ)^{a-2}`,

and the last two terms are `≤ 0` because their integrands are nonnegative and `0 < a < 1`.  The
side conditions (`σψ'²`, `σψ''ψ`, `σ'ψψ'`, `σψ²`, `σ''ψ²`-type integrability and the vanishing of
`ψψ'σ` and `ψ²σ'` at both endpoints) are *not* hypotheses here: they are derived from
`f → 0` at the endpoints and `(f'')²σ ∈ L¹`, exactly as in the sibling
`InterpJumpAux.sliceAgmonVanishing` (recall that `env` of that file also contains
`exists_deriv_abs_bound`, which bounds `|f'|` by a constant `M` on `(0,π/2)`, and the two value
bounds `|f θ| ≤ M θ`, `|f θ| ≤ M (π/2 - θ)`, whence `|f θ| ≤ M sin(2θ)`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Prop.mixedSlotInterpEta
import Submission.Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.sliceAgmonVanishing
import Submission.Work.FTS.EllipticEst.TT.sliceIBPLight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC.VopGen

open MeasureTheory Set Filter
open scoped Real Topology

/-- The light angular weight of the `μ`-slot: `σ = TT.sigR (2 - γ(α))`. -/
local notation "𝔰[" α "]" => Work.FTS.EllipticEst.TT.sigR (2 - Work.Spaces.gam α)

/-- The derivative of the light angular weight: `σ' = TT.sigDR (2 - γ(α))`. -/
local notation "𝔡[" α "]" => Work.FTS.EllipticEst.TT.sigDR (2 - Work.Spaces.gam α)

/-! ## Elementary facts about the weight -/

lemma sigR_gam_pos (α θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) : 0 < 𝔰[α] θ := by
  simpa only [Work.FTS.EllipticEst.TT.sigR, Work.FTS.EllipticEst.TT.sigA,
    Work.FTS.EllipticEst.Cores.sigA]
    using Work.FTS.EllipticEst.Cores.sigA_pos' (α := α) hθ

lemma sigR_gam_nonneg (α θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ 𝔰[α] θ := by
  simpa only [Work.FTS.EllipticEst.TT.sigR, Work.FTS.EllipticEst.TT.sigA]
    using Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ

/-- `|σ'| ≤ 2a sin(2θ)^{a-1}` on the open interval. -/
lemma sigDR_gam_abs_le {α y : ℝ} (hα1 : α ≤ 1) (hSp : 0 < Real.sin (2 * y)) :
    |𝔡[α] y| ≤ 2 * (2 - Work.Spaces.gam α) * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  rw [Work.FTS.EllipticEst.TT.sigDR_apply, abs_mul, abs_mul,
    abs_of_pos (show (0:ℝ) < 2 * (2 - Work.Spaces.gam α) by linarith),
    abs_of_nonneg (Real.rpow_nonneg hSp.le _)]
  have hc : |Real.cos (2 * y)| ≤ 1 := Real.abs_cos_le_one _
  have h2 : 2 * (2 - Work.Spaces.gam α) * |Real.cos (2 * y)| ≤ 2 * (2 - Work.Spaces.gam α) := by
    simpa using mul_le_mul_of_nonneg_left hc (show (0:ℝ) ≤ 2 * (2 - Work.Spaces.gam α) by linarith)
  exact mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hSp.le _)

/-- `σ'(π/2 - y) = -σ'(y)`, hence equal absolute values. -/
lemma sigDR_gam_abs_reflect {α y : ℝ} : |𝔡[α] (Real.pi / 2 - y)| = |𝔡[α] y| := by
  have hsinref : Real.sin (2 * (Real.pi / 2 - y)) = Real.sin (2 * y) := by
    rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.sin_pi_sub]
  have hcref : Real.cos (2 * (Real.pi / 2 - y)) = -Real.cos (2 * y) := by
    rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.cos_pi_sub]
  simp only [Work.FTS.EllipticEst.TT.sigDR]
  rw [hsinref, hcref]
  have heq : ((2 * (2 - Work.Spaces.gam α)) * (-Real.cos (2 * y)))
      * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)
      = -(((2 * (2 - Work.Spaces.gam α)) * Real.cos (2 * y))
        * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)) := by ring
  rw [heq, abs_neg]

lemma sigDR_gam_continuousOn (α : ℝ) : ContinuousOn (𝔡[α]) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hp : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hsin.rpow_const (fun x hx => Or.inl (ne_of_gt
      (Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hx)))
  have hcont : ContinuousOn (fun θ : ℝ => (2 * (2 - Work.Spaces.gam α)) * Real.cos (2 * θ)
      * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1)) (Set.Ioo 0 (Real.pi / 2)) :=
    (continuousOn_const.mul hcos).mul hp
  refine hcont.congr ?_
  intro x hx
  simp only [Work.FTS.EllipticEst.TT.sigDR_apply]

/-- Domination by an integrable function gives integrability on the open interval. -/
lemma integrableOn_Ioo_of_le {g D : ℝ → ℝ}
    (hD : IntegrableOn D (Set.Ioo 0 (Real.pi / 2)))
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |g θ| ≤ D θ) :
    IntegrableOn g (Set.Ioo 0 (Real.pi / 2)) := by
  refine MeasureTheory.Integrable.mono' hD (hg.aestronglyMeasurable measurableSet_Ioo) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  rw [Real.norm_eq_abs]
  exact hbound θ hθ

/-! ## The boundary limits

Both boundary products `f f' σ` and `f² σ'` are `O(sin(2θ)^{1+a})` near the endpoints, hence tend
to `0`. -/

/-- `f f' σ → 0` at `0⁺`. -/
lemma tendsto_ff'_sigR_zero {α M : ℝ} {f : ℝ → ℝ} (hα1 : α ≤ 1) (hMnn : 0 ≤ M)
    (hfS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hdS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) :
    Filter.Tendsto (fun t : ℝ => f t * deriv f t * 𝔰[α] t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  refine Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.tendsto_zero_of_abs_le_eventually
    (A := M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)))
    (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4) (by linarith) (by linarith [Real.pi_pos]) ?_
  intro y hy
  have hyO : y ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
  have hSp : 0 < Real.sin (2 * y) := Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hyO
  have hSle : Real.sin (2 * y) ≤ 2 * y := Real.sin_le (by linarith [hy.1])
  have hchain : |f y * deriv f y * 𝔰[α] y|
      ≤ M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sigR_gam_pos α y hyO).le]
    calc |f y| * |deriv f y| * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α)
        ≤ (M * Real.sin (2 * y)) * M * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α) :=
          mul_le_mul (mul_le_mul (hfS y hyO) (hdS y hyO) (abs_nonneg _)
            (mul_nonneg hMnn hSp.le)) le_rfl (Real.rpow_nonneg hSp.le _)
            (mul_nonneg (mul_nonneg hMnn hSp.le) hMnn)
      _ = M * M * ((Real.sin (2 * y)) * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α)) := by ring
      _ = M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
          rw [← Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.rpow_one_add hSp]
  calc |f y * deriv f y * 𝔰[α] y|
        ≤ M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := hchain
    _ ≤ M * M * (2 * y) ^ (1 + (2 - Work.Spaces.gam α)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.rpow_le_rpow hSp.le hSle (by linarith)
    _ = M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)) * y ^ (1 + (2 - Work.Spaces.gam α)) := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hy.1)]; ring

/-- `f f' σ → 0` at `(π/2)⁻`. -/
lemma tendsto_ff'_sigR_zero_right {α M : ℝ} {f : ℝ → ℝ} (hα1 : α ≤ 1) (hMnn : 0 ≤ M)
    (hfS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ))
    (hdS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) :
    Filter.Tendsto (fun t : ℝ => f t * deriv f t * 𝔰[α] t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  refine Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.tendsto_zero_of_abs_le_eventually_right
    (A := M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)))
    (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4) (by linarith) (by linarith [Real.pi_pos]) ?_
  intro y hy
  have hyO : Real.pi / 2 - y ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [hy.2, Real.pi_pos], by linarith [hy.1]⟩
  have hSy : 0 < Real.sin (2 * y) :=
    Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
  have hSle : Real.sin (2 * y) ≤ 2 * y := Real.sin_le (by linarith [hy.1])
  have hsinref : Real.sin (2 * (Real.pi / 2 - y)) = Real.sin (2 * y) := by
    rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.sin_pi_sub]
  have hsref : 𝔰[α] (Real.pi / 2 - y) = 𝔰[α] y := by
    simp only [Work.FTS.EllipticEst.TT.sigR]
    rw [hsinref]
  have hfθ : |f (Real.pi / 2 - y)| ≤ M * Real.sin (2 * y) := by
    have h := hfS (Real.pi / 2 - y) hyO
    rwa [hsinref] at h
  have hchain : |f (Real.pi / 2 - y) * deriv f (Real.pi / 2 - y) * 𝔰[α] (Real.pi / 2 - y)|
      ≤ M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sigR_gam_pos α _ hyO).le, hsref]
    calc |f (Real.pi / 2 - y)| * |deriv f (Real.pi / 2 - y)|
          * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α)
        ≤ (M * Real.sin (2 * y)) * M * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α) :=
          mul_le_mul (mul_le_mul hfθ (hdS _ hyO) (abs_nonneg _) (mul_nonneg hMnn hSy.le))
            le_rfl (Real.rpow_nonneg hSy.le _) (mul_nonneg (mul_nonneg hMnn hSy.le) hMnn)
      _ = M * M * ((Real.sin (2 * y)) * (Real.sin (2 * y)) ^ (2 - Work.Spaces.gam α)) := by ring
      _ = M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
          rw [← Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.rpow_one_add hSy]
  calc |f (Real.pi / 2 - y) * deriv f (Real.pi / 2 - y) * 𝔰[α] (Real.pi / 2 - y)|
        ≤ M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := hchain
    _ ≤ M * M * (2 * y) ^ (1 + (2 - Work.Spaces.gam α)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.rpow_le_rpow hSy.le hSle (by linarith)
    _ = M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)) * y ^ (1 + (2 - Work.Spaces.gam α)) := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hy.1)]; ring

/-- `f² σ' → 0` at `0⁺`. -/
lemma tendsto_sq_sigDR_zero {α M : ℝ} {f : ℝ → ℝ} (hα1 : α ≤ 1) (hMnn : 0 ≤ M)
    (hfS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) :
    Filter.Tendsto (fun t : ℝ => f t ^ 2 * 𝔡[α] t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  have hpne : 2 - Work.Spaces.gam α ≠ 0 := ne_of_gt hp0
  have hA : (0:ℝ) ≤ 2 * (2 - Work.Spaces.gam α) * M * M := by
    have h1 : 0 ≤ M * M := mul_nonneg hMnn hMnn
    nlinarith [hp0, h1]
  refine Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.tendsto_zero_of_abs_le_eventually
    (A := 2 * (2 - Work.Spaces.gam α) * M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)))
    (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4) (by linarith) (by linarith [Real.pi_pos]) ?_
  intro y hy
  have hyO : y ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
  have hSp : 0 < Real.sin (2 * y) := Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hyO
  have hSle : Real.sin (2 * y) ≤ 2 * y := Real.sin_le (by linarith [hy.1])
  have hu2 : (f y) ^ 2 ≤ (M * Real.sin (2 * y)) ^ 2 := by
    have h0' : (0:ℝ) ≤ |f y| := abs_nonneg _
    calc (f y) ^ 2 = |f y| ^ 2 := (sq_abs (f y)).symm
      _ ≤ (M * Real.sin (2 * y)) ^ 2 := pow_le_pow_left₀ h0' (hfS y hyO) 2
  have hpow : (Real.sin (2 * y)) ^ 2 * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)
      = (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [show (Real.sin (2 * y)) ^ 2 = Real.sin (2 * y) * Real.sin (2 * y) by ring, mul_assoc,
      Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.mul_rpow_sub_one hSp hpne,
      ← Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.rpow_one_add hSp]
  have hbound : |f y ^ 2 * 𝔡[α] y|
      ≤ 2 * (2 - Work.Spaces.gam α) * M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (f y))]
    calc (f y) ^ 2 * |𝔡[α] y|
        ≤ (M * Real.sin (2 * y)) ^ 2
            * (2 * (2 - Work.Spaces.gam α) * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)) :=
          mul_le_mul hu2 (sigDR_gam_abs_le hα1 hSp) (abs_nonneg _) (sq_nonneg _)
      _ = 2 * (2 - Work.Spaces.gam α) * M * M
            * ((Real.sin (2 * y)) ^ 2 * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)) := by ring
      _ = 2 * (2 - Work.Spaces.gam α) * M * M
            * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by rw [hpow]
  calc |f y ^ 2 * 𝔡[α] y|
        ≤ 2 * (2 - Work.Spaces.gam α) * M * M
            * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := hbound
    _ ≤ 2 * (2 - Work.Spaces.gam α) * M * M * (2 * y) ^ (1 + (2 - Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hSp.le hSle (by linarith)) hA
    _ = 2 * (2 - Work.Spaces.gam α) * M * M * 2 ^ (1 + (2 - Work.Spaces.gam α))
          * y ^ (1 + (2 - Work.Spaces.gam α)) := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hy.1)]; ring

/-- `f² σ' → 0` at `(π/2)⁻`. -/
lemma tendsto_sq_sigDR_zero_right {α M : ℝ} {f : ℝ → ℝ} (hα1 : α ≤ 1) (hMnn : 0 ≤ M)
    (hfS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * Real.sin (2 * θ)) :
    Filter.Tendsto (fun t : ℝ => f t ^ 2 * 𝔡[α] t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
  have hp0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  have hpne : 2 - Work.Spaces.gam α ≠ 0 := ne_of_gt hp0
  have hA : (0:ℝ) ≤ 2 * (2 - Work.Spaces.gam α) * M * M := by
    have h1 : 0 ≤ M * M := mul_nonneg hMnn hMnn
    nlinarith [hp0, h1]
  refine Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.tendsto_zero_of_abs_le_eventually_right
    (A := 2 * (2 - Work.Spaces.gam α) * M * M * 2 ^ (1 + (2 - Work.Spaces.gam α)))
    (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4) (by linarith) (by linarith [Real.pi_pos]) ?_
  intro y hy
  have hyO : Real.pi / 2 - y ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [hy.2, Real.pi_pos], by linarith [hy.1]⟩
  have hSy : 0 < Real.sin (2 * y) :=
    Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
  have hSle : Real.sin (2 * y) ≤ 2 * y := Real.sin_le (by linarith [hy.1])
  have hsinref : Real.sin (2 * (Real.pi / 2 - y)) = Real.sin (2 * y) := by
    rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.sin_pi_sub]
  have hfθ : |f (Real.pi / 2 - y)| ≤ M * Real.sin (2 * y) := by
    have h := hfS (Real.pi / 2 - y) hyO
    rwa [hsinref] at h
  have hu2 : (f (Real.pi / 2 - y)) ^ 2 ≤ (M * Real.sin (2 * y)) ^ 2 := by
    have h0' : (0:ℝ) ≤ |f (Real.pi / 2 - y)| := abs_nonneg _
    calc (f (Real.pi / 2 - y)) ^ 2 = |f (Real.pi / 2 - y)| ^ 2 := (sq_abs _).symm
      _ ≤ (M * Real.sin (2 * y)) ^ 2 := pow_le_pow_left₀ h0' hfθ 2
  have hdr : |𝔡[α] (Real.pi / 2 - y)|
      ≤ 2 * (2 - Work.Spaces.gam α) * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1) := by
    rw [sigDR_gam_abs_reflect]; exact sigDR_gam_abs_le hα1 hSy
  have hpow : (Real.sin (2 * y)) ^ 2 * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)
      = (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [show (Real.sin (2 * y)) ^ 2 = Real.sin (2 * y) * Real.sin (2 * y) by ring, mul_assoc,
      Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.mul_rpow_sub_one hSy hpne,
      ← Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux.rpow_one_add hSy]
  have hbound : |f (Real.pi / 2 - y) ^ 2 * 𝔡[α] (Real.pi / 2 - y)|
      ≤ 2 * (2 - Work.Spaces.gam α) * M * M * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (f (Real.pi / 2 - y)))]
    calc (f (Real.pi / 2 - y)) ^ 2 * |𝔡[α] (Real.pi / 2 - y)|
        ≤ (M * Real.sin (2 * y)) ^ 2
            * (2 * (2 - Work.Spaces.gam α) * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)) :=
          mul_le_mul hu2 hdr (abs_nonneg _) (sq_nonneg _)
      _ = 2 * (2 - Work.Spaces.gam α) * M * M
            * ((Real.sin (2 * y)) ^ 2 * (Real.sin (2 * y)) ^ ((2 - Work.Spaces.gam α) - 1)) := by ring
      _ = 2 * (2 - Work.Spaces.gam α) * M * M
            * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := by rw [hpow]
  calc |f (Real.pi / 2 - y) ^ 2 * 𝔡[α] (Real.pi / 2 - y)|
        ≤ 2 * (2 - Work.Spaces.gam α) * M * M
            * (Real.sin (2 * y)) ^ (1 + (2 - Work.Spaces.gam α)) := hbound
    _ ≤ 2 * (2 - Work.Spaces.gam α) * M * M * (2 * y) ^ (1 + (2 - Work.Spaces.gam α)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hSy.le hSle (by linarith)) hA
    _ = 2 * (2 - Work.Spaces.gam α) * M * M * 2 ^ (1 + (2 - Work.Spaces.gam α))
          * y ^ (1 + (2 - Work.Spaces.gam α)) := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hy.1)]; ring


end Work.FTS.ClassC.VopGen
