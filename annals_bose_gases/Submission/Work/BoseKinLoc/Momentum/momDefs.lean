import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.cubFT_defs
import Submission.Work.BoseKinLoc.NeuFrac.plancherel_pconv_schwartz
import Submission.Work.OneBodyKin.integral_bsMean_sq_eq_symbol
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.momDefs` — definitions for the exact `u`-average of `momForm`

FS `eq:Q1Qslide` computes the `u`-average of the sliding mean-free box family.  The proof works
with the following objects, all at the box `x + acube ℓ` (side `ℓ`, centred at `x`):

* `boxFTfun ℓ p ψ x = ∫_{z ∈ acube ℓ} e^{-i⟪p,z⟫} ψ(x+z) dz` — the `p`-Fourier transform of `ψ`
  localised to the box centred at `x`;
* `boxMeanR ℓ ψ x = ℓ⁻³ ∫_{z ∈ acube ℓ} ψ(x+z) dz` — the box mean of `ψ`;
* `PsiC ℓ p ψ = boxFTfun ℓ p ψ − boxMeanR ℓ ψ · boxHat ℓ p` — the mean-free combination;
* `Bh ℓ q p = boxHat ℓ (q−p) − ℓ⁻³ boxHat ℓ p · boxHat ℓ q` — FS's sliding symbol;
* `statU ℓ u ψ = 1_{Λ(u)}(ψ − m_u)` — the complexified mean-free box state.

These are kept in a separate (stable) module because several independent lemmas about them are
proved in parallel.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `p`-Fourier transform of `ψ` restricted to the box `x + acube ℓ`. -/
noncomputable def boxFTfun (ℓ : ℝ) (p : ℝ³) (ψ : ℝ³ → ℝ) : ℝ³ → ℂ :=
  fun x => ∫ z in acube ℓ, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (ψ (x + z) : ℂ)

/-- The box mean of `ψ` over `x + acube ℓ`. -/
noncomputable def boxMeanR (ℓ : ℝ) (ψ : ℝ³ → ℝ) : ℝ³ → ℝ :=
  fun x => (ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, ψ (x + z)

/-- The mean-free localised state in `x`-space whose Fourier transform is
`fhat ψ q · Bh ℓ q p`. -/
noncomputable def PsiC (ℓ : ℝ) (p : ℝ³) (ψ : ℝ³ → ℝ) : ℝ³ → ℂ :=
  fun x => boxFTfun ℓ p ψ x
    - (boxMeanR ℓ ψ x : ℂ) * (Work.OneBodyKin.boxHat ℓ p : ℂ)

/-- FS's sliding symbol `θ̂(q−p) − θ̂(p)θ̂(q)` in the `boxHat` normalisation. -/
noncomputable def Bh (ℓ : ℝ) (q p : ℝ³) : ℝ :=
  Work.OneBodyKin.boxHat ℓ (q - p)
    - (ℓ ^ 3)⁻¹ * Work.OneBodyKin.boxHat ℓ p * Work.OneBodyKin.boxHat ℓ q

/-- The complexified mean-free box state `1_{Λ(u)}(ψ − m_u)`. -/
noncomputable def statU (ℓ : ℝ) (u : ℝ³) (ψ : ℝ³ → ℝ) : ℝ³ → ℂ :=
  fun x => (Work.BoseKinLoc.indU ℓ u x : ℂ) * (Work.BoseKinLoc.Qfree ℓ u ψ x : ℂ)

/-- The symbol appearing on the right-hand side of `momForm_u_integral`. -/
noncomputable def msym (ℓ d : ℝ) (s : ℝ³) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ w in {q : ℝ³ | (d ^ 2)⁻¹ < ‖q‖},
      (cubFT (w - ℓ • s) - cubFT (ℓ • s) * cubFT w) ^ 2

end Work.BoseKinLoc.Momentum
