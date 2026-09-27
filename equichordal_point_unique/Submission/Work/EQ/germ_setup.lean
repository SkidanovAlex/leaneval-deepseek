import Mathlib
import Submission.Work.EQ.Defs

/-!
# The polynomial shape of a rational stable germ

`germ_setup` extracts the elementary consequences of the relation `h u * D u = N u` (for `u`
near `0`), where `h` is a stable germ — so `h 0 = 0` and `h' 0 = -1` — and `D` is a polynomial
denominator with `D 0 ≠ 0`.

Evaluating the relation at `u = 0` gives `N 0 = 0`; differentiating it there gives
`N' 0 = h' 0 * D 0 + h 0 * D' 0 = -D 0 ≠ 0`.  Hence the numerator vanishes at `0` to first
order exactly, which is the "shape" input used by `germ_no_other_roots` and
`no_rational_germ`.

(No continuity argument is needed: an eventual equality at a point `x` implies equality of the
values at `x`, and `Filter.EventuallyEq.deriv_eq` transfers the derivatives.)
-/

namespace Work.EQ

open Filter Topology

set_option linter.unusedVariables false

theorem germ_setup {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) {N D : Polynomial ℂ} (hD0 : Polynomial.eval 0 D ≠ 0)
    (hDN : ∀ᶠ u in nhds (0 : ℂ), h u * Polynomial.eval u D = Polynomial.eval u N) :
    N ≠ 0 ∧ Polynomial.eval 0 N = 0 ∧ Polynomial.eval 0 (Polynomial.derivative N) ≠ 0 := by
  obtain ⟨hr, hana, hh0, hder, _him, _hFE⟩ := hh
  -- `0` lies in the disc of analyticity of `h`
  have hmem : (0 : ℂ) ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, dist_self]; exact hr
  have hdiff : DifferentiableAt ℂ h 0 := (hana 0 hmem).differentiableAt
  -- the eventual relation, as an `EventuallyEq` of functions
  have hDN' : (fun u : ℂ => h u * D.eval u) =ᶠ[𝓝 (0 : ℂ)] (fun u : ℂ => N.eval u) := hDN
  -- value at `0`
  have hval : h 0 * D.eval 0 = N.eval 0 := hDN'.self_of_nhds
  have hN0 : N.eval 0 = 0 := by
    rw [hh0, zero_mul] at hval; exact hval.symm
  -- derivative at `0`
  have h1 : deriv (fun u : ℂ => h u * D.eval u) 0
      = deriv h 0 * D.eval 0 + h 0 * deriv (fun u : ℂ => D.eval u) 0 :=
    deriv_mul hdiff D.differentiableAt
  have h2 : deriv (fun u : ℂ => N.eval u) 0 = N.derivative.eval 0 := N.deriv
  have hNd : N.derivative.eval 0 = -D.eval 0 := by
    have h := hDN'.deriv_eq
    rw [h1, h2, hder, hh0, D.deriv] at h
    simp only [neg_mul, one_mul, zero_mul, add_zero] at h
    exact h.symm
  refine ⟨?_, hN0, ?_⟩
  · intro hN
    rw [hN] at hNd
    simp at hNd
    exact hD0 hNd
  · rw [hNd]
    exact neg_ne_zero.mpr hD0

end Work.EQ
