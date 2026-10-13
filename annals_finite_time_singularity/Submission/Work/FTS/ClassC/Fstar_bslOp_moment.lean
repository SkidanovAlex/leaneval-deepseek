import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.Lzero_orthogonal
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular moment of `L(Ψ)`

Elgindi, Annals 194 (3) 2021, §'Elliptic Regularity Estimates', Step 1 of `prop:L2`.

The `α = 0` part `L₀` of the elliptic operator (PolarBSL) is formally adjoint to the angular
weight `sin θ cos²θ` on `[0,π/2]` with Dirichlet conditions
(`Work.Elliptic.Lzero_orthogonal`), so the angular moment
`F_*(F)(z) = ∫_0^{π/2} F(z,θ) sin θ cos²θ dθ` of the full operator
`L(Ψ) = bslOp α Ψ` is the sum of the moments of the two radial terms only:

  `F_*(bslOp α Ψ)(z) = -(α²z²)·F_*(∂_zzΨ)(z) - α(5+α)z·F_*(∂_zΨ)(z)`.

The proof is linearity of the Bochner integral (`integral_add`, `integral_neg`,
`integral_const_mul`) applied to the definitional splitting
`bslOp α Ψ = -(α²z²)∂_zzΨ - α(5+α)z∂_zΨ + L₀Ψ` together with `Lzero_orthogonal`; the three
`IntegrableOn` hypotheses are exactly the side conditions the splitting needs.

Note on notation: the statement below is written with the `π` notation of `Mathlib`, which
requires the scoped notation `Real` to be open (`open scoped Real` below); the lakefile sets
`autoImplicit = false`, so without it `π` would simply be an unknown identifier.
-/
open scoped Real
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

theorem Fstar_bslOp_moment {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hslice : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Icc 0 (π / 2)))
    (h0 : Ψ z 0 = 0) (h1 : Ψ z (π / 2) = 0)
    (hIntA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hIntB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hIntL : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.Elliptic.Lzero Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (Work.Elliptic.bslOp α Ψ) z
      = -(α ^ 2 * z ^ 2) * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z
        - (α * (5 + α) * z) * Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z := by
  -- `sin θ cos²θ` is annihilated by the adjoint of `L₀` on the Dirichlet slice
  have hL := Work.Elliptic.Lzero_orthogonal Ψ z hslice h0 h1
  -- the three summands of `bslOp α Ψ z θ * sinCos2 θ`
  set A : ℝ → ℝ :=
    fun θ => (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ with hAdef
  set B : ℝ → ℝ :=
    fun θ => (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ with hBdef
  set L : ℝ → ℝ :=
    fun θ => Work.Elliptic.Lzero Ψ z θ * Work.Elliptic.sinCos2 θ with hLdef
  have hAi : MeasureTheory.IntegrableOn A Work.Spaces.Iθ := by rw [hAdef]; exact hIntA
  have hBi : MeasureTheory.IntegrableOn B Work.Spaces.Iθ := by rw [hBdef]; exact hIntB
  have hLi : MeasureTheory.IntegrableOn L Work.Spaces.Iθ := by rw [hLdef]; exact hIntL
  -- the constants come out of the moment
  have hAeval : (∫ θ in Work.Spaces.Iθ, A θ)
      = (α ^ 2 * z ^ 2) * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, A θ)
        = ∫ θ in Work.Spaces.Iθ,
            (α ^ 2 * z ^ 2) * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with θ
      simp only [hAdef]
      ring
    rw [h1, MeasureTheory.integral_const_mul]
  have hBeval : (∫ θ in Work.Spaces.Iθ, B θ)
      = (α * (5 + α) * z) * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, B θ)
        = ∫ θ in Work.Spaces.Iθ,
            (α * (5 + α) * z) * (Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with θ
      simp only [hBdef]
      ring
    rw [h1, MeasureTheory.integral_const_mul]
  have hLeval : (∫ θ in Work.Spaces.Iθ, L θ) = 0 := hL
  -- linearity of the integral over the definitional splitting of `bslOp`
  have key : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ)
      = -(∫ θ in Work.Spaces.Iθ, A θ) - (∫ θ in Work.Spaces.Iθ, B θ)
        + (∫ θ in Work.Spaces.Iθ, L θ) := by
    have hpt : ∀ θ, Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ = -A θ - B θ + L θ := by
      intro θ
      simp only [hAdef, hBdef, hLdef, Work.Elliptic.bslOp_apply]
      ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_add (f := fun θ => -A θ - B θ) (g := L)
      (hAi.neg.sub hBi) hLi]
    rw [MeasureTheory.integral_sub (f := fun θ => -A θ) (g := B) hAi.neg hBi]
    rw [MeasureTheory.integral_neg (f := A)]
  have hgoal : (∫ θ in Work.Spaces.Iθ, Work.Elliptic.bslOp α Ψ z θ * Work.Elliptic.sinCos2 θ)
      = -(α ^ 2 * z ^ 2) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
        - (α * (5 + α) * z) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) := by
    rw [key, hAeval, hBeval, hLeval]
    ring
  simpa only [Work.Elliptic.Fstar] using hgoal

end Work.FTS.ClassC
