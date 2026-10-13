/-
# `Work.FTS.PhiStar.Gegenbauer.eFam_Lzero` — the Gegenbauer eigenfunctions of `Lzero`

`Work.Elliptic.Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ` (`Lzero_eq_deriv` below) acts on a
function of `θ` alone as `Lzero Ψ = -∂_θθΨ + ∂_θ(tan θ · Ψ) - 6Ψ`, so the `z`-variable is
irrelevant.  The `m`-th Dirichlet eigenfunction of the module `Defs.lean` is

  `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`   (`= cos θ · gC (2m+1) (sin θ)`),

and the claim is that it is an eigenfunction with eigenvalue `lam m = 2m(2m+5)`:

  `Lzero (fun _ θ' => eFam m θ') z θ = lam m * eFam m θ`.

**The computation.**  With `c = cos θ`, `s = sin θ`, `q = gC (2m+1)` (extended to a general
twice differentiable `q` in `Lzero_cos_comp`), `e = c · q(s)`:

* `e' = -s q(s) + c² q'(s)`,
* `e'' = -c q(s) - 3 s c q'(s) + c³ q''(s)`,
* `∂_θ(tan θ · e) = ∂_θ(s · q(s)) = c q(s) + s c q'(s)`   (valid where `cos θ ≠ 0`, so on a
  neighbourhood of `θ`),

whence

  `Lzero e = -e'' + ∂_θ(tan · e) - 6e = c·(-(1-s²) q''(s) + 4 s q'(s) - 4 q(s))`.

The Gegenbauer equation `(1-x²)q''(x) - 4x q'(x) + n(n+3) q(x) = 0` for `n = 2m+1`
(`gC_ode`) turns the bracket into `4 s q' - 4q - (4s q' - n(n+3) q) = (n(n+3) - 4) q`, and
`n(n+3) - 4 = (2m+1)(2m+4) - 4 = 2m(2m+5) = lam m`.

Everything is pointwise and holds at every `θ` with `cos θ ≠ 0`; at `θ = π/2` the function
`tan θ · eFam m θ` has a jump of size `-(2m+1)-th` order, which is why the hypothesis
`Real.cos θ ≠ 0` is needed (it is a null condition for every integral of the estimates).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.PhiStar.Gegenbauer

set_option autoImplicit false

/-! ## The one-variable calculus of `θ ↦ cos θ · q (sin θ)` -/

/-- The `θ`-derivative of `θ ↦ cos θ · q (sin θ)`:
`∂_θ(cos θ · q(sin θ)) = -sin θ · q(sin θ) + cos²θ · q'(sin θ)`. -/
lemma deriv_cos_comp_sin (q : ℝ → ℝ) (hq : ContDiff ℝ 3 q) :
    deriv (fun θ' => Real.cos θ' * q (Real.sin θ'))
      = fun θ' => -Real.sin θ' * q (Real.sin θ') + Real.cos θ' ^ 2 * deriv q (Real.sin θ') := by
  funext θ
  have hdq : DifferentiableAt ℝ q (Real.sin θ) := (hq.differentiable (by norm_num)).differentiableAt
  have hcomp : HasDerivAt (fun θ' : ℝ => q (Real.sin θ')) (deriv q (Real.sin θ) * Real.cos θ) θ :=
    (hdq.hasDerivAt).comp θ (Real.hasDerivAt_sin θ)
  have hm := (Real.hasDerivAt_cos θ).mul hcomp
  have h1 : deriv (fun θ' : ℝ => Real.cos θ' * q (Real.sin θ')) θ
      = -Real.sin θ * q (Real.sin θ) + Real.cos θ * (deriv q (Real.sin θ) * Real.cos θ) := hm.deriv
  rw [h1]
  ring

/-- The second `θ`-derivative of `θ ↦ cos θ · q (sin θ)`:
`∂_θθ(cos θ · q(sin θ)) = -cos θ · q(sin θ) - 3 sin θ cos θ · q'(sin θ) + cos³θ · q''(sin θ)`. -/
lemma deriv2_cos_comp_sin (q : ℝ → ℝ) (hq : ContDiff ℝ 3 q) (θ : ℝ) :
    deriv (deriv (fun θ' => Real.cos θ' * q (Real.sin θ'))) θ
      = -Real.cos θ * q (Real.sin θ) - 3 * Real.sin θ * Real.cos θ * deriv q (Real.sin θ)
        + Real.cos θ ^ 3 * deriv (deriv q) (Real.sin θ) := by
  rw [deriv_cos_comp_sin q hq]
  have hdq : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hddq : Differentiable ℝ (deriv q) :=
    ((ContDiff.deriv' (n := 2) hq).differentiable (by norm_num))
  have h1 : HasDerivAt (fun θ' : ℝ => -Real.sin θ' * q (Real.sin θ'))
      ((-Real.cos θ) * q (Real.sin θ)
        + (-Real.sin θ) * (deriv q (Real.sin θ) * Real.cos θ)) θ := by
    have hcomp : HasDerivAt (fun θ' : ℝ => q (Real.sin θ'))
        (deriv q (Real.sin θ) * Real.cos θ) θ :=
      ((hdq.differentiableAt).hasDerivAt).comp θ (Real.hasDerivAt_sin θ)
    exact (Real.hasDerivAt_sin θ).neg.mul hcomp
  have h2 : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2 * deriv q (Real.sin θ'))
      ((2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ)) * deriv q (Real.sin θ)
        + Real.cos θ ^ 2 * (deriv (deriv q) (Real.sin θ) * Real.cos θ)) θ := by
    have hc2 : HasDerivAt (fun θ' : ℝ => Real.cos θ' ^ 2)
        (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ)) θ := (Real.hasDerivAt_cos θ).pow 2
    have hcomp : HasDerivAt (fun θ' : ℝ => deriv q (Real.sin θ'))
        (deriv (deriv q) (Real.sin θ) * Real.cos θ) θ :=
      ((hddq.differentiableAt).hasDerivAt).comp θ (Real.hasDerivAt_sin θ)
    exact hc2.mul hcomp
  have hsum : HasDerivAt (fun θ' : ℝ => -Real.sin θ' * q (Real.sin θ')
        + Real.cos θ' ^ 2 * deriv q (Real.sin θ'))
      (((-Real.cos θ) * q (Real.sin θ)
          + (-Real.sin θ) * (deriv q (Real.sin θ) * Real.cos θ))
        + ((2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ)) * deriv q (Real.sin θ)
          + Real.cos θ ^ 2 * (deriv (deriv q) (Real.sin θ) * Real.cos θ))) θ := h1.add h2
  rw [hsum.deriv]
  norm_num
  ring

/-- Where `cos θ ≠ 0` (hence on a neighbourhood of `θ`),
`∂_θ(tan θ · cos θ · q(sin θ)) = ∂_θ(sin θ · q(sin θ)) = cos θ · q(sin θ) + sin θ cos θ · q'(sin θ)`. -/
lemma deriv_tan_cos_comp_sin (q : ℝ → ℝ) (hq : ContDiff ℝ 3 q) (θ : ℝ)
    (hθ : Real.cos θ ≠ 0) :
    deriv (fun θ' => Real.tan θ' * (Real.cos θ' * q (Real.sin θ'))) θ
      = Real.cos θ * q (Real.sin θ) + Real.sin θ * Real.cos θ * deriv q (Real.sin θ) := by
  have hne : ∀ᶠ θ' in nhds θ, Real.cos θ' ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hθ
  have heq : (fun θ' => Real.tan θ' * (Real.cos θ' * q (Real.sin θ')))
      =ᶠ[nhds θ] fun θ' => Real.sin θ' * q (Real.sin θ') := by
    filter_upwards [hne] with θ' h'
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  rw [heq.deriv_eq]
  have hdq : Differentiable ℝ q := hq.differentiable (by norm_num)
  have hcomp : HasDerivAt (fun θ' : ℝ => q (Real.sin θ'))
      (deriv q (Real.sin θ) * Real.cos θ) θ :=
    ((hdq.differentiableAt).hasDerivAt).comp θ (Real.hasDerivAt_sin θ)
  have hm := (Real.hasDerivAt_sin θ).mul hcomp
  have h1 : deriv (fun θ' : ℝ => Real.sin θ' * q (Real.sin θ')) θ
      = Real.cos θ * q (Real.sin θ) + Real.sin θ * (deriv q (Real.sin θ) * Real.cos θ) := hm.deriv
  rw [h1]
  ring

/-! ## The action of `Lzero` on `cos θ · q(sin θ)` -/

/-- **The reduction of `Lzero` on the Gegenbauer form.**  For a three-times differentiable `q`
and `cos θ ≠ 0`:

  `Lzero (fun _ θ' => cos θ' · q(sin θ')) z θ
     = cos θ · (-(1 - sin²θ) · q''(sin θ) + 4 sin θ · q'(sin θ) - 4 q(sin θ))`

— the operator acquires the factor `cos θ` and the *regular* Gegenbauer operator in the
variable `u = sin θ` (no `tan` remains). -/
lemma Lzero_cos_comp_sin (q : ℝ → ℝ) (hq : ContDiff ℝ 3 q) (z : ℝ) {θ : ℝ}
    (hθ : Real.cos θ ≠ 0) :
    Work.Elliptic.Lzero (fun _ θ' => Real.cos θ' * q (Real.sin θ')) z θ
      = Real.cos θ * (-(1 - Real.sin θ ^ 2) * deriv (deriv q) (Real.sin θ)
          + 4 * Real.sin θ * deriv q (Real.sin θ) - 4 * q (Real.sin θ)) := by
  -- on a `z`-independent function, `Lzero` is the one-variable operator of `Lzero_eq_deriv`
  have hL : Work.Elliptic.Lzero (fun _ θ' => Real.cos θ' * q (Real.sin θ')) z θ
      = -(deriv (deriv (fun θ' => Real.cos θ' * q (Real.sin θ'))) θ)
        + deriv (fun θ' => Real.tan θ' * (Real.cos θ' * q (Real.sin θ'))) θ
        - 6 * (Real.cos θ * q (Real.sin θ)) := by
    simp only [Work.Elliptic.Lzero, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero,
      Work.Spaces.pth]
  rw [hL, deriv2_cos_comp_sin q hq θ, deriv_tan_cos_comp_sin q hq θ hθ]
  have hsq := Real.sin_sq_add_cos_sq θ
  linear_combination (-Real.cos θ * deriv (deriv q) (Real.sin θ)) * hsq

/-! ## The eigenfunction identity -/

theorem eFam_Lzero (m : ℕ) {θ : ℝ} (hθ : Real.cos θ ≠ 0) (z : ℝ) :
    Work.Elliptic.Lzero (fun _ θ' => Work.FTS.PhiStar.Gegenbauer.eFam m θ') z θ
      = Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  change Work.Elliptic.Lzero
      (fun _ θ' => Real.cos θ' * gC (2 * m + 1) (Real.sin θ')) z θ
    = lam m * (Real.cos θ * gC (2 * m + 1) (Real.sin θ))
  rw [Lzero_cos_comp_sin (gC (2 * m + 1)) (contDiff_gC (2 * m + 1)) z hθ]
  have hode := (gC_ode (2 * m + 1)).2 (Real.sin θ)
  have hn : ((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3) - 4 = lam m := by
    simp only [lam]; push_cast; ring
  have hkey : -(1 - Real.sin θ ^ 2) * deriv (deriv (gC (2 * m + 1))) (Real.sin θ)
      + 4 * Real.sin θ * deriv (gC (2 * m + 1)) (Real.sin θ)
      = ((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)
        * gC (2 * m + 1) (Real.sin θ) := by
    linarith [hode]
  rw [hkey, ← hn]
  ring

end Work.FTS.PhiStar.Gegenbauer
