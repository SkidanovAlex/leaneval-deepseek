import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkAux
import Submission.Work.FTS.EllipticEst.pzIter_uncurry_continuousOn
import Submission.Work.FTS.EllipticEst.pzIter_integral_hasDerivAt
import Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Smoothness of the angular moment `F_*`

The angular moment `F_*(z) = ∫_θ F z θ · sin θ cos²θ dθ` of `Work.Elliptic.Defs` is a
parametric integral: the integration variable `θ` runs over the compact interval
`Iθ = [0,π/2]`, while the parameter `z` runs over `(-1,∞)`.  Since `SmoothNbhd F` says that
`(z,θ) ↦ F z θ` is smooth (indeed analytic) on the open neighbourhood
`U = (-1,∞) × (-1,π/2+1)` of the closed quadrant, and the angular weight is smooth, the
integral is smooth in the parameter: differentiating under the integral sign `k` times exhibits
the `k`-th derivative as the integral of the `k`-th `z`-derivative of the integrand, and the
differentiation step is legitimate because `Iθ` is compact (domination by a constant) and the
slices `z ↦ F z θ` are smooth on all of `(-1,∞)`.

The two inputs of the induction below are the delegated lemmas
`pzIter_uncurry_continuousOn` (joint continuity of the integrand and of all its `z`-derivatives
on `(-1,∞) × Iθ`, which is contained in the open set `U` on which `F` is smooth) and
`pzIter_integral_hasDerivAt` (differentiation under the `θ`-integral:
`∂_z ∫_θ ∂_z^k F · φ = ∫_θ ∂_z^{k+1} F · φ`).

The companion fact for the domain `(0,∞)` is `Work.Coercivity.contDiffOn_infty_integral_Itheta`;
here the domain is the full `(-1,∞)` of `SmoothNbhd`. -/

/-- **The parametric angular integral is smooth to all orders on `(-1,∞)`.**  For `u` smooth on
the open neighbourhood `U` of the closed quadrant and any angular weight `φ` continuous on `Iθ`,
the function `z ↦ ∫_θ u z θ · φ θ dθ` is `C^n` on `(-1,∞)` for every `n`. -/
theorem contDiffOn_infty_integral_Itheta_Ioi_neg_one (u : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hu : Work.Spaces.SmoothNbhd u) (hφ : ContinuousOn φ Work.Spaces.Iθ) :
    ContDiffOn ℝ ∞ (fun z => ∫ θ in Work.Spaces.Iθ, u z θ * φ θ) (Set.Ioi (-1)) := by
  -- joint continuity of `(z,θ) ↦ ∂_z^k u (z,θ) · φ θ` on `(-1,∞) × Iθ`
  have hcont : ∀ k : ℕ, ContinuousOn
      (Function.uncurry fun z θ => Work.Spaces.pzIter k u z θ * φ θ)
      (Set.Ioi (-1) ×ˢ Work.Spaces.Iθ) :=
    fun k => pzIter_uncurry_continuousOn u φ hu hφ k
  -- the derivative of the `k`-th integral is the `(k+1)`-st one
  have hderiv : ∀ (k : ℕ) {s : ℝ}, s ∈ Set.Ioi (-1) →
      HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ)
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter (k + 1) u s θ * φ θ) s :=
    fun k _ hs => pzIter_integral_hasDerivAt u φ hu hφ k hs
  -- `C^n` for each of the iterated integrals, by induction on `n`
  have hmain : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ ((n : ℕ) : ℕ∞ω)
      (fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ) (Set.Ioi (-1)) := by
    intro n
    induction n with
    | zero =>
      intro k
      exact (contDiffOn_zero (𝕜 := ℝ)).2
        (Work.Coercivity.continuousOn_integral_Itheta_of_continuousOn isOpen_Ioi (hcont k))
    | succ n ih =>
      intro k
      rw [Nat.cast_add, Nat.cast_one]
      refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ)
        (f := fun s => ∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter k u s θ * φ θ)
        (n := ((n : ℕ) : ℕ∞ω)) (s := Set.Ioi (-1)) isOpen_Ioi).2 ⟨?_, ?_, ?_⟩
      · intro s hs
        exact (hderiv k hs).differentiableAt.differentiableWithinAt
      · intro h
        exact absurd h (by simp)
      · exact (ih (k + 1)).congr (fun s hs => (hderiv k hs).deriv)
  exact contDiffOn_infty.mpr (fun n => hmain n 0)

/-- **The angular moment `F_*` of a `SmoothNbhd` function is `C^n` on `(-1,∞)`.**
Immediate from `contDiffOn_infty_integral_Itheta_Ioi_neg_one` with the angular weight
`sin θ cos²θ` and the identification `Fstar F z = ∫_θ F z θ · sin θ cos²θ dθ`. -/
theorem Fstar_contDiffOn (F : ℝ → ℝ → ℝ) (hF : Work.Spaces.SmoothNbhd F) (n : ℕ) :
    ContDiffOn ℝ n (fun z => Work.Elliptic.Fstar F z) (Set.Ioi (-1)) := by
  have hφ : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have h := contDiffOn_infty_integral_Itheta_Ioi_neg_one F Work.Elliptic.sinCos2 hF hφ
  simpa only [Work.Elliptic.Fstar] using contDiffOn_infty.mp h n

end Work.FTS.EllipticEst
