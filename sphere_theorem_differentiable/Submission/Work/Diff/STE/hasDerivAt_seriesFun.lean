import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiation of a Fourier series with respect to a parameter

We prove that if every coefficient family `s ↦ c s k` is differentiable with constant derivative
`c' k` (hypothesis `hc`), and both `k ↦ ‖c' k‖` and `k ↦ ‖c t₀ k‖` are summable, then

`t ↦ seriesFun (c t) x`

has derivative `seriesFun c' x` at `t₀`.

Note that `hc` quantifies over *all* `t`, so each `s ↦ c s k` has derivative the constant `c' k`
everywhere; by the mean value theorem such a function is affine:
`c t k = c t₀ k + (t - t₀) * c' k`.  Since `‖fourierExp k x‖ = 1`, both series
`Σ_k c t₀ k · e_k` and `Σ_k c' k · e_k` are absolutely convergent, so the sum splits by linearity
of `tsum` and the statement follows from the derivative of an affine function.
-/

noncomputable section

namespace Work.Diff.STE

open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hasDerivAt_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ → (ι → ℤ) → ℂ) (c' : (ι → ℤ) → ℂ) (t₀ : ℝ) (x : ι → ℝ)
    (hc : ∀ (k : ι → ℤ) (t : ℝ), HasDerivAt (fun s => c s k) (c' k) t)
    (hdom : Summable (fun k : ι → ℤ => ‖c' k‖))
    (h0 : Summable (fun k : ι → ℤ => ‖c t₀ k‖)) :
    HasDerivAt (fun t => Work.Diff.STE.seriesFun (c t) x)
      (Work.Diff.STE.seriesFun c' x) t₀ := by
  -- The Fourier characters have unit modulus (private computation, no name clash with siblings).
  have hnorm : ∀ (k : ι → ℤ) (y : ι → ℝ), ‖fourierExp k y‖ = 1 := by
    intro k y
    rw [fourierExp]
    have h : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, (k i : ℂ) * (y i : ℂ))
        = (((2 * Real.pi * ∑ i, ((k i : ℤ) : ℝ) * (y i)) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h, Complex.norm_exp_ofReal_mul_I]
  -- Each coefficient is affine in `t`, because its derivative is the constant `c' k`.
  have haff : ∀ (k : ι → ℤ) (t : ℝ),
      c t k = c t₀ k + (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * c' k := by
    intro k t
    have hderiv : ∀ s : ℝ,
        HasDerivAt (fun u : ℝ => c u k - (((u : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * c' k) 0 s := by
      intro s
      have hlin : HasDerivAt (fun u : ℝ => (((u : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ))) (1 : ℂ) s :=
        (HasDerivAt.ofReal_comp (hasDerivAt_id s)).sub_const _
      have h2 : HasDerivAt (fun u : ℝ => (((u : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * c' k)
          ((1 : ℂ) * c' k) s := hlin.mul_const (c' k)
      have h3 : HasDerivAt (fun u : ℝ => c u k - (((u : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * c' k)
          (c' k - (1 : ℂ) * c' k) s := (hc k s).sub h2
      simpa using h3
    have hconst := is_const_of_deriv_eq_zero
      (f := fun u : ℝ => c u k - (((u : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * c' k)
      (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t t₀
    have hsub : c t k - (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * c' k = c t₀ k := by
      simpa using hconst
    exact sub_eq_iff_eq_add.mp hsub
  -- Absolute convergence of the two series, from the unit modulus of the characters.
  have hsum0 : Summable (fun k : ι → ℤ => c t₀ k * fourierExp k x) :=
    Summable.of_norm (h0.congr (fun k => by rw [norm_mul, hnorm, mul_one]))
  have hsum1 : Summable (fun k : ι → ℤ => c' k * fourierExp k x) :=
    Summable.of_norm (hdom.congr (fun k => by rw [norm_mul, hnorm, mul_one]))
  -- Hence the series is an affine function of `t`.
  have hkey : ∀ t : ℝ, seriesFun (c t) x
      = seriesFun (c t₀) x + (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * seriesFun c' x := by
    intro t
    have hs2 : Summable (fun k : ι → ℤ =>
        (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * (c' k * fourierExp k x)) := hsum1.mul_left _
    calc seriesFun (c t) x
        = ∑' k : ι → ℤ,
            (c t₀ k + (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * c' k) * fourierExp k x :=
            tsum_congr (fun k => by rw [haff k t])
      _ = ∑' k : ι → ℤ, (c t₀ k * fourierExp k x
            + (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * (c' k * fourierExp k x)) :=
            tsum_congr (fun k => by ring)
      _ = ∑' k : ι → ℤ, c t₀ k * fourierExp k x
            + ∑' k : ι → ℤ, (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * (c' k * fourierExp k x) :=
            hsum0.tsum_add hs2
      _ = seriesFun (c t₀) x + (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * seriesFun c' x := by
            rw [tsum_mul_left]
            rfl
  have hder : HasDerivAt (fun t : ℝ =>
      seriesFun (c t₀) x + (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * seriesFun c' x)
      (seriesFun c' x) t₀ := by
    have h1 : HasDerivAt (fun t : ℝ =>
        (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ)) * seriesFun c' x) (seriesFun c' x) t₀ := by
      have hlin : HasDerivAt (fun t : ℝ => (((t : ℝ) : ℂ) - ((t₀ : ℝ) : ℂ))) (1 : ℂ) t₀ :=
        (HasDerivAt.ofReal_comp (hasDerivAt_id t₀)).sub_const _
      have h2 := hlin.mul_const (seriesFun c' x)
      simpa using h2
    exact h1.const_add (seriesFun (c t₀) x)
  rw [funext hkey]
  exact hder

end Work.Diff.STE
