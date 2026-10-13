/-
Copyright: work module for the Elgindi finite-time singularity project.

# The substitution `Ψ = sin θ cos θ · w` for the `α = 0` elliptic operator

`Work.Elliptic.Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` and `sin θ cos θ = (1/2) sin 2θ` lies in
its kernel.  The point of the substitution is that all *singular* coefficients disappear: for
`Ψ = sin θ cos θ · w` one has the identity

  `Lzero(sin θ cos θ · w) = -sin θ cos θ · ∂_θθ w + (3 sin²θ - 2 cos²θ) · ∂_θ w`

on the open quadrant `0 < θ < π/2` (where `tan` is regular).  Equivalently, in the notation of
the paper (`DivisionBySin`), the divided residual `Lzero(sin 2θ Φ)/(sin 2θ)` is a *bounded*
coefficient combination of `Φ` and `∂_θΦ` — this is the algebraic layer of the paper's tex-1293
argument, by which the `z`-derivatives of `Φ̃_*/sin 2θ` are traded against the elliptic equation.

The computation: with `S = sin θ`, `C = cos θ`, `w = w(z,θ)`, `w' = ∂_θw`, `w'' = ∂_θθ w`,

  `∂_θ(S C w)   = (C² - S²) w + S C w'`,
  `∂_θθ(S C w)  = -4 S C w + 2(C² - S²) w' + S C w''`,
  `∂_θ(tan θ · S C w) = ∂_θ(S² w) = 2 S C w + S² w'`,

so `Lzero(S C w) = (4SC w - 2(C²-S²)w' - SC w'') + (2SC w + S² w') - 6SC w
        = -SC w'' + (3S² - 2C²) w'`, the `w`-coefficient `4 + 2 - 6 = 0` cancelling exactly.

The hypotheses only assume `w` twice `θ`-differentiable on the open quadrant (`∂_θθw` is
`deriv (deriv …)` there), which is exactly what the two derivative computations use.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.StarPkg.SubstBsl

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.StarPkg.LzeroSubst

set_option autoImplicit false

/-! ## Two elementary `HasDerivAt` rules

`sin θ cos θ` and `cos²θ - sin²θ` are the two angular factors produced by differentiating
`S C · g` once and twice. -/

/-- First derivative of `sin θ cos θ · g θ`: `∂_θ(sin θ cos θ · g) = (cos²θ - sin²θ) g +
sin θ cos θ · g'`. -/
lemma hasDerivAt_sin_cos_mul {g : ℝ → ℝ} {θ f' : ℝ} (h : HasDerivAt g f' θ) :
    HasDerivAt (fun θ' => Real.sin θ' * Real.cos θ' * g θ')
      ((Real.cos θ ^ 2 - Real.sin θ ^ 2) * g θ + (Real.sin θ * Real.cos θ) * f') θ := by
  have ha : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ')
      (Real.cos θ ^ 2 - Real.sin θ ^ 2) θ := by
    have h0 := (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)
    convert h0 using 1
    ring
  exact ha.mul h

/-- Second derivative of `sin θ cos θ · g θ`:
`∂_θθ(sin θ cos θ · g) = -4 sin θ cos θ · g + 2(cos²θ - sin²θ) g' + sin θ cos θ · g''`. -/
lemma hasDerivAt_snd_sin_cos_mul {g : ℝ → ℝ} {θ f' f'' : ℝ}
    (h : HasDerivAt g f' θ) (h' : HasDerivAt (deriv g) f'' θ) :
    HasDerivAt (fun θ' => (Real.cos θ' ^ 2 - Real.sin θ' ^ 2) * g θ'
        + (Real.sin θ' * Real.cos θ') * deriv g θ')
      (-4 * (Real.sin θ * Real.cos θ) * g θ
        + 2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2) * f'
        + (Real.sin θ * Real.cos θ) * f'') θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2 - Real.sin θ' ^ 2)
      (-4 * Real.sin θ * Real.cos θ) θ := by
    have hft : (fun θ' : ℝ => Real.cos θ' ^ 2 - Real.sin θ' ^ 2)
        = fun θ' => Real.cos (2 * θ') := by
      funext θ'; rw [Real.cos_two_mul, Real.sin_sq]; ring
    have h0 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(2 * Real.sin (2 * θ))) θ := by
      have hlin : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      have hh := hlin.cos
      convert hh using 1
      ring
    rw [hft]
    convert h0 using 1
    rw [Real.sin_two_mul]; ring
  have h2 : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ')
      (Real.cos θ ^ 2 - Real.sin θ ^ 2) θ := by
    have h0 : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ')
        (Real.cos θ * Real.cos θ + Real.sin θ * -Real.sin θ) θ :=
      (Real.hasDerivAt_sin θ).mul (Real.hasDerivAt_cos θ)
    convert h0 using 1
    ring
  have hmain := (h1.mul h).add (h2.mul h')
  convert hmain using 1
  rw [h.deriv]; ring

/-! ## The substitution identity -/

theorem lzero_sin_cos_mul (w : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
    (h1 : DifferentiableOn ℝ (fun θ' => w z θ') (Set.Ioo (0 : ℝ) (Real.pi / 2)))
    (h2 : DifferentiableOn ℝ (fun θ' => deriv (fun θ'' => w z θ'') θ')
      (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    Work.Elliptic.Lzero (fun z θ => Real.sin θ * Real.cos θ * w z θ) z θ
      = -(Real.sin θ * Real.cos θ) * Work.Spaces.pthIter 2 w z θ
        + (3 * Real.sin θ ^ 2 - 2 * Real.cos θ ^ 2) * Work.Spaces.pth w z θ := by
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- the second `θ`-derivative of `sin θ cos θ · w`
  have hA : deriv (fun θ' => deriv (fun θ'' => Real.sin θ'' * Real.cos θ'' * w z θ'') θ') θ
      = -4 * (Real.sin θ * Real.cos θ) * w z θ
        + 2 * (Real.cos θ ^ 2 - Real.sin θ ^ 2) * deriv (fun θ'' => w z θ'') θ
        + (Real.sin θ * Real.cos θ) * deriv (fun θ' => deriv (fun θ'' => w z θ'') θ') θ := by
    have heq : (fun θ' => deriv (fun θ'' => Real.sin θ'' * Real.cos θ'' * w z θ'') θ')
        =ᶠ[𝓝 θ] fun θ' => (Real.cos θ' ^ 2 - Real.sin θ' ^ 2) * (fun θ'' => w z θ'') θ'
            + (Real.sin θ' * Real.cos θ') * deriv (fun θ'' => w z θ'') θ' := by
      filter_upwards [hIoo] with θ' hθ'
      have hd : HasDerivAt (fun θ'' : ℝ => w z θ'') (deriv (fun θ'' : ℝ => w z θ'') θ') θ' :=
        (h1.differentiableAt (isOpen_Ioo.mem_nhds hθ')).hasDerivAt
      exact (hasDerivAt_sin_cos_mul hd).deriv
    rw [heq.deriv_eq]
    exact (hasDerivAt_snd_sin_cos_mul (g := fun θ'' => w z θ'')
      (h1.differentiableAt hIoo).hasDerivAt (h2.differentiableAt hIoo).hasDerivAt).deriv
  -- the first `θ`-derivative of `tan θ · (sin θ cos θ · w)`
  have hB : deriv (fun θ' => Real.tan θ' * (Real.sin θ' * Real.cos θ' * w z θ')) θ
      = 2 * (Real.sin θ * Real.cos θ) * w z θ
        + Real.sin θ ^ 2 * deriv (fun θ'' => w z θ'') θ := by
    have hne : ∀ᶠ θ' in 𝓝 θ, Real.cos θ' ≠ 0 := Real.continuous_cos.continuousAt.eventually_ne hcos
    have heq : (fun θ' => Real.tan θ' * (Real.sin θ' * Real.cos θ' * w z θ'))
        =ᶠ[𝓝 θ] fun θ' => Real.sin θ' ^ 2 * w z θ' := by
      filter_upwards [hne] with θ' h'
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    rw [heq.deriv_eq]
    have hd : HasDerivAt (fun θ' : ℝ => Real.sin θ' ^ 2) (2 * Real.sin θ * Real.cos θ) θ := by
      have h0 := (Real.hasDerivAt_sin θ).pow 2
      convert h0 using 1
      ring
    rw [(show deriv (fun θ' : ℝ => Real.sin θ' ^ 2 * w z θ') θ
          = deriv ((fun θ' : ℝ => Real.sin θ' ^ 2) * fun θ' => w z θ') θ from rfl),
        (hd.mul (h1.differentiableAt hIoo).hasDerivAt).deriv]
    ring
  simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
    Work.Spaces.pth]
  rw [hA, hB]
  ring

end Work.FTS.H2.StarPkg.LzeroSubst
