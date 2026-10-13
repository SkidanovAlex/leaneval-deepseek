/-
Work module for the Elgindi finite-time singularity project.

# Definitions for the honest-class mixed interpolation `mixedInterp`

The target lemma `Work.FTS.EllipticEst.HonGaps.mixedInterp` asserts that for honest data
`Hon α F Ψ` (plus the honesties of `z∂_zΨ` and of the mixed derivative `z∂_θ∂_zΨ`) one has

  `IP M M ≤ C (IP A A + IP B B + IP G G)`,  `M = z∂_θ∂_zΨ`, `A = z²∂²_zzΨ`, `B = ∂²_θθΨ`,
  `G = z∂_zΨ`,  `IP g h = ∫_z ∫_θ g h w²σ`,  `σ θ = sin(2θ)^{-η}`.

The proof follows the paper's two integrations by parts, carried out in the honest class with a
*θ-cut-off* `ψ_ε` and a *z-cut-off* `χ_N`.  The needed objects are defined here.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.HonGaps

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- The angular cut-off `ψ_ε`: smooth, `= 0` off `(ε, π/2-ε)`, `= 1` on `[2ε, π/2-2ε]`,
valued in `[0,1]`. -/
def psiCut (ε θ : ℝ) : ℝ :=
  Real.smoothTransition (θ / ε - 1) * Real.smoothTransition ((Real.pi / 2 - θ) / ε - 1)

/-- The angular weight `σ θ = sin(2θ)^{-η}`. -/
def sigS (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))

theorem sigS_eq_angSecond (θ : ℝ) : sigS θ = AngSecond.sig θ := rfl

theorem angSecond_IP_eq (g h : ℝ → ℝ → ℝ) :
    AngSecond.IP g h = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      g z θ * h z θ * (Work.Spaces.w z) ^ 2 * sigS θ := by
  rw [AngSecond.IP]
  refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  rw [sigS_eq_angSecond]
  rfl

theorem psiCut_zero_of_le {ε θ : ℝ} (hε : 0 < ε) (h : θ ≤ ε) : psiCut ε θ = 0 := by
  have h1 : θ / ε - 1 ≤ 0 := by
    have : θ / ε ≤ 1 := by
      rw [div_le_iff₀ hε]; linarith
    linarith
  rw [psiCut, Real.smoothTransition.zero_of_nonpos h1, zero_mul]

theorem psiCut_zero_of_ge {ε θ : ℝ} (hε : 0 < ε) (h : Real.pi / 2 - ε ≤ θ) :
    psiCut ε θ = 0 := by
  have h2 : (Real.pi / 2 - θ) / ε - 1 ≤ 0 := by
    have : (Real.pi / 2 - θ) / ε ≤ 1 := by
      rw [div_le_iff₀ hε]; linarith
    linarith
  rw [psiCut, Real.smoothTransition.zero_of_nonpos h2, mul_zero]

theorem psiCut_nonneg (ε θ : ℝ) : 0 ≤ psiCut ε θ :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem psiCut_le_one (ε θ : ℝ) : psiCut ε θ ≤ 1 := by
  have h1 := Real.smoothTransition.le_one (θ / ε - 1)
  have h2 := Real.smoothTransition.le_one ((Real.pi / 2 - θ) / ε - 1)
  have h2' := Real.smoothTransition.nonneg ((Real.pi / 2 - θ) / ε - 1)
  calc psiCut ε θ = Real.smoothTransition (θ / ε - 1)
        * Real.smoothTransition ((Real.pi / 2 - θ) / ε - 1) := rfl
    _ ≤ 1 * 1 := mul_le_mul h1 h2 h2' (by norm_num)
    _ = 1 := by ring

/-- The mixed term of the target. -/
def mixTerm (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ

/-- The `A`-term `z²∂²_zzΨ` of the target. -/
def qTerm (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ

/-- The `G`-term `z∂_zΨ` of the target. -/
def gTerm (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.Dz Ψ

/-- The `B`-term `∂²_θθΨ` of the target. -/
def bTerm (Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ

/-- The cut mixed functional `∫_z χ²w² ∫_θ σ ψ² (z∂_θ∂_zΨ)²`. -/
def truncMix (χ : ℝ → ℝ) (ε : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (χ z) ^ 2 * (Work.Spaces.w z) ^ 2
    * ∫ θ in Work.Spaces.Iθ, sigS θ * (psiCut ε θ) ^ 2 * (mixTerm Ψ z θ) ^ 2

/-- The cut angular functional `∫_z χ²w² ∫_θ σ ψ² (∂²_θθΨ)²`. -/
def truncTT (χ : ℝ → ℝ) (ε : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (χ z) ^ 2 * (Work.Spaces.w z) ^ 2
    * ∫ θ in Work.Spaces.Iθ, sigS θ * (psiCut ε θ) ^ 2 * (bTerm Ψ z θ) ^ 2

/-- The cut radial functional `∫_z χ²w² ∫_θ σ ψ² (z²∂²_zzΨ)²`. -/
def truncQQ (χ : ℝ → ℝ) (ε : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (χ z) ^ 2 * (Work.Spaces.w z) ^ 2
    * ∫ θ in Work.Spaces.Iθ, sigS θ * (psiCut ε θ) ^ 2 * (qTerm Ψ z θ) ^ 2

/-- The cut `G`-functional `∫_z χ²w² ∫_θ σ ψ² (z∂_zΨ)²`. -/
def truncGG (χ : ℝ → ℝ) (ε : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (χ z) ^ 2 * (Work.Spaces.w z) ^ 2
    * ∫ θ in Work.Spaces.Iθ, sigS θ * (psiCut ε θ) ^ 2 * (gTerm Ψ z θ) ^ 2

/-- The layer error functional, `∫_z χ²w²` times the mass of `σ(z∂_θ∂_zΨ)²` on the two
`ψ`-layers. -/
def truncLay (χ : ℝ → ℝ) (ε : ℝ) (Ψ : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Work.Spaces.Iz, (χ z) ^ 2 * (Work.Spaces.w z) ^ 2
    * ((∫ θ in Set.Ioo (0 : ℝ) (min (2 * ε) (Real.pi / 2)),
          sigS θ * (mixTerm Ψ z θ) ^ 2)
      + (∫ θ in Set.Ioo (max (Real.pi / 2 - 2 * ε) 0) (Real.pi / 2),
          sigS θ * (mixTerm Ψ z θ) ^ 2))

end Work.FTS.EllipticEst.HonGaps
