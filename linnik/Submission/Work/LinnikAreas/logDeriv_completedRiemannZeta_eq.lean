import Mathlib
import Submission.Work.LinnikAreas.ZetaTentPrelude

namespace Work.LinnikAreas

open Filter
open scoped Topology

/-!
# Logarithmic derivative of the completed Riemann zeta function

The completed Riemann zeta function `Λ = completedRiemannZeta` and the Riemann zeta
function `ζ` are related by `ζ(s) = Λ(s) / Gammaℝ s` (Mathlib's
`riemannZeta_def_of_ne_zero`).  Consequently, wherever `Gammaℝ s ≠ 0`,
`Λ = Gammaℝ · ζ` in a neighbourhood of `s`, and taking logarithmic derivatives gives

  `logDeriv Λ s = logDeriv Gammaℝ s + logDeriv ζ s`.

The hypotheses `s ≠ 0`, `s ≠ 1` make `Λ` analytic at `s`; `-1 < s.re` forces `Gammaℝ s ≠ 0`
(the only zeros of `Gammaℝ` on `re ≥ -1` are at `s = 0`, excluded), and `ζ s ≠ 0` permits
the product rule for `logDeriv`.
-/

theorem logDeriv_completedRiemannZeta_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hsre : -(1 : ℝ) < s.re)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta s = logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  -- `Gammaℝ` does not vanish at `s`: its zeros are the numbers `-2 * n`, and only `n = 0`
  -- (i.e. `s = 0`) is compatible with `-1 < s.re`.
  have hGam : Complex.Gammaℝ s ≠ 0 := by
    intro h
    rw [Complex.Gammaℝ_eq_zero_iff] at h
    obtain ⟨n, hn⟩ := h
    have hre : -(1 : ℝ) < (-(2 * (n : ℂ))).re := by rw [← hn]; exact hsre
    have h' : (↑(2 * n) : ℝ) < 1 := by
      have hh := hre
      rw [show (-(2 * (n : ℂ))) = -((2 * n : ℕ) : ℂ) by push_cast; ring] at hh
      simp only [Complex.neg_re, Complex.natCast_re] at hh
      exact neg_lt_neg_iff.mp hh
    have hn0 : n = 0 := by
      have h2 : (2 * n : ℕ) < 1 := by exact_mod_cast h'
      omega
    subst hn0
    simp at hn
    exact hs0 hn
  -- `Gammaℝ` is differentiable at `s`, since its reciprocal is entire and non-zero there.
  have hGdiff : DifferentiableAt ℂ Complex.Gammaℝ s := by
    have h : DifferentiableAt ℂ (fun t => (Complex.Gammaℝ t)⁻¹) s :=
      Complex.differentiable_Gammaℝ_inv.differentiableAt
    have h2 : DifferentiableAt ℂ (fun t => ((Complex.Gammaℝ t)⁻¹)⁻¹) s :=
      h.inv (inv_ne_zero hGam)
    rwa [show (fun t : ℂ => ((Complex.Gammaℝ t)⁻¹)⁻¹) = Complex.Gammaℝ from
      funext (fun t => inv_inv _)] at h2
  -- `Λ = Gammaℝ · ζ` in a neighbourhood of `s`
  have hE : completedRiemannZeta =ᶠ[𝓝 s] fun t => Complex.Gammaℝ t * riemannZeta t := by
    have h0 : ∀ᶠ t in 𝓝 s, t ≠ 0 := isOpen_ne.mem_nhds hs0
    have hg : ∀ᶠ t in 𝓝 s, Complex.Gammaℝ t ≠ 0 :=
      hGdiff.continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hGam)
    filter_upwards [h0, hg] with t ht0 hgt
    rw [riemannZeta_def_of_ne_zero ht0]
    exact (mul_div_cancel₀ _ hgt).symm
  rw [Filter.EventuallyEq.eq_of_nhds (logDeriv_congr_nhds hE)]
  erw [logDeriv_mul s hGam hζ hGdiff (differentiableAt_riemannZeta hs1)]

end Work.LinnikAreas
