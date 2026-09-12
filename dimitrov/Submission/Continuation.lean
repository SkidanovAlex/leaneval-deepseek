import Mathlib
import Submission.HoloSqrt
import Submission.SqrtTaylor

/-!
# Holomorphic continuation of the square root, on a given simply connected domain

This module is the monodromy layer of the analytic engine, in its *plane*
form, parameterized by the simply connected domain `U`.

Fix an integer polynomial `G : ℤ[X]` with `G.coeff 0 = 1` and the formal
square root `a : ℕ → ℤ` (`a 0 = 1`, convolution square `= G.coeff`);
`Submission.PowRev.powRev_sqrt_integral` supplies such `a` for
`G := (pow2 P).reflect d * (pow4 P).reflect d`.

Let `U ⊆ ℂ` be an open simply connected set with `0 ∈ U` and containing a
ball around `0`, such that `G` (as a polynomial function) does not vanish on
`U`.  Then there exists a holomorphic function `f : U → ℂ` with

* `f z ^ 2 = G(z)` for all `z ∈ U`,
* `f 0 = 1`, and
* the Taylor coefficients of `f` at `0` are the *integers* `a k`:

        taylorCoeff f k = (a k : ℂ)      (all k)

*Proof.*  `Submission.HoloSqrt.exists_holomorphic_sq_eq` (continuous branch +
holomorphic upgrade) applied to `g := fun z ↦ G.eval₂ (algebraMap ℤ ℂ) z`
(holomorphic because `G` is a polynomial, nonvanishing on `U` by hypothesis)
gives a holomorphic `g₀` on `U` with `g₀ z ^ 2 = G(z)`.  Since `G 0 = 1`,
`g₀ 0 = ±1`; multiply by the sign so that `f 0 = 1` (still a holomorphic
square root).  Then `Submission.SqrtTaylor.taylorCoeff_sqrt_eq` applied on the
ball `ball 0 ρ ⊆ U` (from the hypothesis `hball`) gives the Taylor identity.

(The actual *construction* of a suitable `U` for the specific
`G = ∏(1 - z² w)(1 - z⁴ w)`, e.g. the complement of finitely many rays, is a
separate topological task; this module only assembles the analytic facts once
`U` is given.)

You may add helper lemmas.  Do NOT change the statement of
`sqrt_continuation`.  No sorries may remain in this file.
-/

noncomputable section

open Polynomial
open scoped Polynomial Real Topology

namespace Submission.Continuation

open Submission.HoloSqrt
open Submission.SqrtTaylor

/-- The Taylor coefficients of `f` at `0` equal the given sequence `a`. -/
theorem sqrt_continuation {G : ℤ[X]} (hG0 : G.coeff 0 = 1)
    {a : ℕ → ℤ} (ha0 : a 0 = 1)
    (ha : ∀ k : ℕ, (∑ i ∈ Finset.range (k + 1), a i * a (k - i)) = G.coeff k)
    {U : Set ℂ} (hUo : IsOpen U) (hUsc : IsSimplyConnected U)
    (hU0 : 0 ∈ U) (hball : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball 0 ρ ⊆ U)
    (hGne : ∀ z ∈ U, G.eval₂ (algebraMap ℤ ℂ) z ≠ 0) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f U ∧
      (∀ z ∈ U, f z ^ 2 = G.eval₂ (algebraMap ℤ ℂ) z) ∧ f 0 = 1 ∧
      (∀ k : ℕ, taylorCoeff f k = (a k : ℂ)) := by
  -- `g : U → ℂ` is the polynomial function attached to `G`, holomorphic and
  -- nonvanishing on `U` by hypothesis.
  let g : ℂ → ℂ := fun z => G.eval₂ (algebraMap ℤ ℂ) z
  have hgdiff : DifferentiableOn ℂ g U := by
    dsimp [g]
    simpa [Polynomial.eval₂_eq_eval_map] using
      (Polynomial.differentiableOn (𝕜 := ℂ) (p := G.map (algebraMap ℤ ℂ)) (s := U))
  have hg0 : ∀ z ∈ U, g z ≠ 0 := by
    intro z hz
    exact hGne z hz
  -- A holomorphic square root `g₁` of `g` on `U` (HoloSqrt, simply connected).
  rcases exists_holomorphic_sq_eq hUo hUsc hgdiff hg0 with ⟨g₁, hg₁diff, hg₁sq⟩
  -- Normalize the phase: since `G 0 = 1` we have `g₁ 0 = ±1`; multiplying by
  -- `g₁ 0` (which squares to `1`) fixes the value at `0` to `1` while
  -- preserving `f z ^ 2 = g z`.
  have hg₁0sq : g₁ 0 ^ 2 = 1 := by
    have htmp := hg₁sq 0 hU0
    rw [show g 0 = 1 by
      dsimp [g]
      rw [Polynomial.eval₂_at_zero]
      norm_num [hG0]] at htmp
    exact htmp
  let f : ℂ → ℂ := fun z => g₁ 0 * g₁ z
  have hfdiff : DifferentiableOn ℂ f U := by
    dsimp [f]
    exact hg₁diff.const_mul (g₁ 0)
  have hfsq : ∀ z ∈ U, f z ^ 2 = g z := by
    intro z hz
    dsimp [f]
    calc
      (g₁ 0 * g₁ z) ^ 2 = (g₁ 0) ^ 2 * (g₁ z) ^ 2 := by ring
      _ = 1 * g z := by rw [hg₁0sq, hg₁sq z hz]
      _ = g z := by simp
  have hf0 : f 0 = 1 := by
    dsimp [f]
    simpa [pow_two] using hg₁0sq
  -- The Taylor identity is read off on a ball around `0` inside `U`.
  rcases hball with ⟨ρ, hρ, hρU⟩
  have hfb : DifferentiableOn ℂ f (Metric.ball 0 ρ) := hfdiff.mono hρU
  have hfsqb : ∀ z ∈ Metric.ball 0 ρ, f z ^ 2 = g z := fun z hz => hfsq z (hρU hz)
  have htaylor : ∀ k : ℕ, taylorCoeff f k = (a k : ℂ) := by
    exact SqrtTaylor.taylorCoeff_sqrt_eq hG0 ha0 ha (f := f) (r := ρ) hρ hfb hf0 hfsqb
  refine ⟨f, hfdiff, ?_, hf0, htaylor⟩
  intro z hz
  exact hfsq z hz

end Submission.Continuation

end
