/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise bound of order `≤ 2` in the interior class `SmoothQuad`

`T2Qaux.supQ_T2Q` is the `SmoothQuad` form of Elgindi's Corollary `SecondDerivativesBounded`
(tex 1094) needed by the `D_z`-transport estimate `Work.FTS.H2.T2Q`:

  `|D_z^b D_θ^a f(z,θ)| ≤ C/√(γ-1) · |f|_{ℋ⁴}`   (`a + b ≤ 2`, `z > 0`, `0 < θ < π/2`)

for `f` smooth on the open quadrant, of class `ℋ⁴` and with `DecayAll 4`.

It is deduced from the already proved *squared* form `Work.H2.T1Q.PwBdQ` (which is proved in
`Submission/Work/H2/T1Q/PwBdQ.lean`, sorry-free, for exactly this class) by taking square
roots and using `HkNorm = √(HkSq)`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.H2.T1Q.PwBdQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.T2Qaux

set_option autoImplicit false

open Work.Spaces

/-- **Elgindi's `SecondDerivativesBounded` in the interior class.**  For `0 < α ≤ 1` and `f`
`C^∞` on the open quadrant with `DecayAll 4 f` and honest `ℋ⁴` norm,

  `|D_z^bD_θ^a f(z,θ)| ≤ C/√(γ-1) · |f|_{ℋ⁴}`

for every `a + b ≤ 2` and every point of the open quadrant. -/
theorem supQ_T2Q : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ), 0 < α → α ≤ 1 →
    a + b ≤ 2 → Work.FTS.LocData.SmoothQuad f → Work.Spaces.DecayAll 4 f →
    Work.Spaces.HkMem α 4 f →
    ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.mixed b a f z θ| ≤ C / Real.sqrt (Work.Spaces.gam α - 1)
        * Work.Spaces.HkNorm α 4 f := by
  obtain ⟨C0, hC0pos, hPw⟩ := Work.H2.T1Q.PwBdQ
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro α f b a hα hα1 hab hsq hdec hmem z hz θ hθ
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hsq0 : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
  have hbnd := (hPw α f hα hα1 hsq hdec hmem).bound b a hab z hz θ hθ.1 hθ.2
  -- take square roots
  have h1 : |Work.Spaces.mixed b a f z θ|
      ≤ Real.sqrt (C0 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hbnd
  have h2 : Real.sqrt (C0 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f)
      = Real.sqrt C0 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := by
    rw [Real.sqrt_mul (div_nonneg hC0pos.le hγ.le),
      Real.sqrt_div hC0pos.le (Work.Spaces.gam α - 1), Work.Spaces.HkNorm]
  have hC0le : Real.sqrt C0 ≤ C0 + 1 := by
    have h1 : (Real.sqrt C0) ^ 2 = C0 := Real.sq_sqrt (le_of_lt hC0pos)
    have h2 : 0 ≤ Real.sqrt C0 := Real.sqrt_nonneg C0
    nlinarith [sq_nonneg (Real.sqrt C0 - 1 / 2), h1, h2]
  have h3 : Real.sqrt C0 / Real.sqrt (Work.Spaces.gam α - 1)
      ≤ (C0 + 1) / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_le_div_of_nonneg_right hC0le (Real.sqrt_nonneg _)
  calc |Work.Spaces.mixed b a f z θ|
      ≤ Real.sqrt (C0 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f) := h1
    _ = Real.sqrt C0 / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f := h2
    _ ≤ (C0 + 1) / Real.sqrt (Work.Spaces.gam α - 1) * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_right h3 (Work.Spaces.HkNorm_nonneg α 4 f)

end Work.FTS.H2.T2Qaux
