/-
# Smoothness (analyticity) of the radial factor `F_rad` of the `D_z`-commutator

The `D_z`-commutator defect `E₂ = D_z 𝓛_Γ^T f - 𝓛_Γ^T(D_z f)` of Elgindi, *Finite-time
singularity formation for `C^{1,α}` solutions to the incompressible Euler equations on
`ℝ³`*, Annals **194** (3) 2021, splits as

  `E₂(z,θ) = mm(z)·f(z,θ) + (3/2)·mm(z)·D_θf(z,θ) + (Γ(θ)/c)·G(z)`

(`Work.Coercivity.CommutZ.CommutZ_pointwise_E2`), where the *radial* profile `G` is

  `G(z) = cfac(z)·L₁₂(f)(z) + z q'(z)·L₁₂(Transport f)(0) - q(z)·L₁₂(Transport(D_z f))(0)`

(`Work.Coercivity.CommutZ.Gfun`) with the rational coefficients

  `cfac(z) = -2z(1-z)/(1+z)³`, `z q'(z) = 2z²(2-z)/(1+z)⁴`, `q(z) = 2z²/(1+z)³`.

Divided by the constant `c = c(α)` this is the radial factor
`F_rad α f = G(·)/c α` (`Work.Coercivity.CommutZ.Frad`) of the `Γ`-term, and this module
proves that `F_rad α f` — like `L₁₂(f)` itself — is real-analytic on `(0,∞)`.

Note that in this Mathlib the order `⊤` of `ContDiffOn` is the **analytic** order `ω`
(`ContDiffOn ℝ ⊤ f s ↔ AnalyticOn ℝ f s` for open `s`), so the statement below says that
both functions are real-analytic on `(0,∞)`.

The proof is a two-line assembly of facts already in the workspace: `L₁₂(f)` is analytic
on `(0,∞)` by `Work.Coercivity.L12f_contDiffOn` (module `F1F2_smooth`), and the three
rational profiles are analytic there because their denominators `(1+z)^3`, `(1+z)^4` do
not vanish for `z > 0`; then use the closure of `ContDiffOn` under products and sums, and
divide by the constant `c α`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.CommutZBase
import Submission.Work.Coercivity.F1F2_smooth

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

namespace CommutZ

/-! ## Analyticity of the three rational profiles -/

/-- `cfac(z) = -2z(1-z)/(1+z)³` is real-analytic on `(0,∞)`. -/
theorem cfac_contDiffOn : ContDiffOn ℝ ⊤ cfac (Set.Ioi 0) := by
  unfold cfac
  refine ContDiffOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
  have hz' : (0 : ℝ) < z := hz
  positivity

/-- `z q'(z) = 2z²(2-z)/(1+z)⁴` is real-analytic on `(0,∞)`. -/
theorem zdq_contDiffOn : ContDiffOn ℝ ⊤ zdq (Set.Ioi 0) := by
  unfold zdq
  refine ContDiffOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
  have hz' : (0 : ℝ) < z := hz
  positivity

/-- `q(z) = 2z²/(1+z)³` is real-analytic on `(0,∞)`. -/
theorem qfun_contDiffOn : ContDiffOn ℝ ⊤ qfun (Set.Ioi 0) := by
  unfold qfun
  refine ContDiffOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
  have hz' : (0 : ℝ) < z := hz
  positivity

/-! ## Analyticity of the `z`-profile `G` -/

/-- The radial profile `G`, being a sum of products of an analytic rational profile with
either `L₁₂(f)` or a constant, is real-analytic on `(0,∞)`. -/
theorem Gfun_contDiffOn (f : ℝ → ℝ → ℝ) (hf : Spaces.SmoothNbhd f)
    (hint : IntegrableOn (FM.L12dens Spaces.K f) (Set.Ioi 0)) :
    ContDiffOn ℝ ⊤ (Gfun f) (Set.Ioi 0) := by
  have hL : ContDiffOn ℝ ⊤ (fun z => L12f f z) (Set.Ioi 0) := L12f_contDiffOn f hf hint
  have h1 : ContDiffOn ℝ ⊤ (fun z => cfac z * L12f f z) (Set.Ioi 0) :=
    cfac_contDiffOn.mul hL
  have h2 : ContDiffOn ℝ ⊤ (fun z => zdq z * Lam1 f) (Set.Ioi 0) :=
    zdq_contDiffOn.mul contDiffOn_const
  have h3 : ContDiffOn ℝ ⊤ (fun z => qfun z * Lam2 f) (Set.Ioi 0) :=
    qfun_contDiffOn.mul contDiffOn_const
  show ContDiffOn ℝ ⊤ (fun z => cfac z * L12f f z + zdq z * Lam1 f - qfun z * Lam2 f)
    (Set.Ioi 0)
  exact (h1.add h2).sub h3

end CommutZ

/-! ## The main statement -/

theorem CommutZ_Frad_smooth (α : ℝ) (hc : Work.Spaces.c α ≠ 0) (f : ℝ → ℝ → ℝ)
    (hf : Work.Spaces.SmoothNbhd f)
    (hint : MeasureTheory.IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0)) :
    ContDiffOn ℝ ⊤ (fun z => Work.Coercivity.L12f f z) (Set.Ioi 0)
      ∧ ContDiffOn ℝ ⊤ (Work.Coercivity.CommutZ.Frad α f) (Set.Ioi 0) := by
  have hL : ContDiffOn ℝ ⊤ (fun z => L12f f z) (Set.Ioi 0) := L12f_contDiffOn f hf hint
  refine ⟨hL, ?_⟩
  have hG : ContDiffOn ℝ ⊤ (CommutZ.Gfun f) (Set.Ioi 0) :=
    CommutZ.Gfun_contDiffOn f hf hint
  -- `F_rad α f = Gfun f / c α`, and the denominator is the non-zero constant `c α`
  have hdiv : ContDiffOn ℝ ⊤ (fun z => CommutZ.Gfun f z / Spaces.c α) (Set.Ioi 0) :=
    ContDiffOn.div hG contDiffOn_const (fun _ _ => hc)
  exact hdiv

end Work.Coercivity
