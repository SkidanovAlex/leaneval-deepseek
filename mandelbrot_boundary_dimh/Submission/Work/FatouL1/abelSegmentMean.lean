import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# FATOU-L1: the integrated Abel relation along a segment (`abelSegmentMean`)

If `Φ` is a holomorphic Fatou coordinate on the region `𝒬 = MandelDim.Qreg b₁ b₂`, i.e.
`Φ (F z) = Φ z + 1` whenever `z` and `F z` lie in `𝒬`, and the whole straight segment from `z`
to `F z` stays in `𝒬`, then the fundamental theorem of calculus applied to `Φ` along that
segment gives

`(F z - z) * ∫₀¹ (deriv Φ) (z + t • (F z - z)) dt = Φ (F z) - Φ z = 1`.

The auxiliary lemma `integral_deriv_segment` below is the field-free (indeed, hypothesis-free
apart from openness of the domain) statement of the first equality: the integral of the complex
derivative along a segment is the increment of the primitive.
-/

open Set MeasureTheory

set_option linter.unusedVariables false

namespace Work.FatouL1

noncomputable section

/-- **The fundamental theorem of calculus along a segment.**  For a holomorphic `Φ` on an open
set `U` and points `z`, `w` such that the whole segment `t ↦ z + t • (w - z)`, `t ∈ [0,1]`, lies
in `U`,

`∫₀¹ (deriv Φ) (z + t • (w - z)) * (w - z) dt = Φ w - Φ z`.

(The chain rule gives `(Φ ∘ γ)' = (deriv Φ ∘ γ) · γ'` with `γ' = w - z`, and
`intervalIntegral.integral_eq_sub_of_hasDerivAt` integrates it.) -/
lemma integral_deriv_segment {U : Set ℂ} (hU : IsOpen U) {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ U) {z w : ℂ}
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → z + t • (w - z) ∈ U) :
    ∫ t in (0:ℝ)..1, deriv Φ (z + t • (w - z)) * (w - z) = Φ w - Φ z := by
  -- the segment stays in `U` (in the form `uIcc` used by the FTC lemmas)
  have hmem : ∀ t ∈ Set.uIcc (0:ℝ) 1, z + t • (w - z) ∈ U := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hseg t ht
  -- `Φ` is holomorphic on the open set `U`, hence its derivative is continuous there
  have hderivΦcont : ContinuousOn (deriv Φ) U :=
    (hΦd.contDiffOn hU).continuousOn_deriv_of_isOpen hU le_rfl
  -- the parametrisation of the segment and its derivative
  have hγ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => z + s • (w - z)) (w - z) t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const (w - z)).const_add z
  -- the chain rule
  have hcomp : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => Φ (z + s • (w - z))) (deriv Φ (z + t • (w - z)) * (w - z)) t := by
    intro t ht
    have hΦat : DifferentiableAt ℂ Φ (z + t • (w - z)) :=
      hΦd.differentiableAt (hU.mem_nhds (hmem t ht))
    exact (hΦat.hasDerivAt).comp t (hγ t)
  -- continuity of the integrand on the interval (so that it is interval integrable)
  have hcont : ContinuousOn (fun s : ℝ => deriv Φ (z + s • (w - z)) * (w - z))
      (Set.uIcc (0:ℝ) 1) := by
    intro t ht
    have h1 : ContinuousAt (deriv Φ) (z + t • (w - z)) :=
      hderivΦcont.continuousAt (hU.mem_nhds (hmem t ht))
    have h2 : ContinuousAt (fun s : ℝ => z + s • (w - z)) t := (hγ t).continuousAt
    have h3 : ContinuousAt (fun s : ℝ => deriv Φ (z + s • (w - z))) t :=
      ContinuousAt.comp (x := t) (f := fun s : ℝ => z + s • (w - z)) h1 h2
    exact h3.continuousWithinAt.mul_const (w - z)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hcomp hcont.intervalIntegrable
  have h1 : Φ (z + (1:ℝ) • (w - z)) = Φ w := by
    simp only [one_smul]
    congr 1
    ring
  have h0 : Φ (z + (0:ℝ) • (w - z)) = Φ z := by
    simp
  rw [hFTC, h1, h0]

/-- **`Qreg b₁ b₂` is open** (each defining condition is a strict inequality for a continuous
function, and there are only finitely many of them, `b₁`, `b₂` being `Option`s). -/
lemma isOpen_Qreg_local (b₁ b₂ : Option ℂ) : IsOpen (MandelDim.Qreg b₁ b₂) := by
  have h1 : ∀ a : ℂ, IsOpen {z : ℂ | -|(z - a).im| < (z - a).re} := fun a =>
    isOpen_lt (by fun_prop) (by fun_prop)
  have h2 : ∀ b : ℂ, IsOpen {z : ℂ | (z - b).re < |(z - b).im|} := fun b =>
    isOpen_lt (by fun_prop) (by fun_prop)
  rcases b₁ with _ | a <;> rcases b₂ with _ | b
  · convert isOpen_univ using 1; ext z; simp [MandelDim.Qreg]
  · convert h2 b using 1; ext z; simp [MandelDim.Qreg]
  · convert h1 a using 1; ext z; simp [MandelDim.Qreg]
  · convert (h1 a).inter (h2 b) using 1
    ext z; simp [MandelDim.Qreg]

theorem abelSegmentMean {b₁ b₂ : Option ℂ} {F Φ : ℂ → ℂ}
    (hFd : DifferentiableOn ℂ F (MandelDim.Qreg b₁ b₂))
    (hΦd : DifferentiableOn ℂ Φ (MandelDim.Qreg b₁ b₂))
    (hAbel : ∀ z ∈ MandelDim.Qreg b₁ b₂, F z ∈ MandelDim.Qreg b₁ b₂ → Φ (F z) = Φ z + 1)
    {z : ℂ} (hz : z ∈ MandelDim.Qreg b₁ b₂) (hzF : F z ∈ MandelDim.Qreg b₁ b₂)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → z + t • (F z - z) ∈ MandelDim.Qreg b₁ b₂) :
    (F z - z) * (∫ t in (0:ℝ)..1, deriv Φ (z + t • (F z - z))) = 1 := by
  have hQopen : IsOpen (MandelDim.Qreg b₁ b₂) := isOpen_Qreg_local b₁ b₂
  -- the FTC along the segment, with the Abel relation producing the increment `1`
  have hmain : ∫ t in (0:ℝ)..1, deriv Φ (z + t • (F z - z)) * (F z - z) = 1 := by
    rw [integral_deriv_segment hQopen hΦd hseg, hAbel z hz hzF]
    ring
  -- pull the constant `F z - z` out of the integral
  have h2 : (∫ t in (0:ℝ)..1, deriv Φ (z + t • (F z - z))) * (F z - z) = 1 := by
    rw [← intervalIntegral.integral_mul_const]
    exact hmain
  rw [mul_comm]
  exact h2

end

end Work.FatouL1
