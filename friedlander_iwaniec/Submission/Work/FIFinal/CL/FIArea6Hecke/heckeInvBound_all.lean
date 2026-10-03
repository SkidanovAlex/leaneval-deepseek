/-
# `Work.FIArea6Hecke.heckeInvBound_all` — the Hecke inverse bound (*FI* (16.23)) at the bridge

The fixed target (see `NOTES_invBound_all.md` in this directory for the full analysis) is

  `∀ ε ∈ (0, 1/4], HeckeInvBoundAll ε`,

where `HeckeInvBoundAll ε` (`FITop4/Bridge/area5_6_defs.lean`) is, for `heckeLSeries` = Mathlib's
`LSeries` of the Hecke eigenvalues `λ(n) = Σ_{|z|²=n, z primary} χ(z)(z/|z|)^m`:

  `∃ c > 0, ∀ d ≥ 1, χ strict mod 4d, ∀ m ∈ ℤ, ∀ s : ℂ with s.re ≤ 2,
      1 - c/(d^ε log(|m|+|s.im|+3)) < s.re →
        ‖(heckeLSeries χ m s)⁻¹‖ ≤ c · d · log²(|m|+|s.im|+3)`.

Since Mathlib's `LSeries` is the `tsum` and equals `0` exactly when the Dirichlet series fails to
converge absolutely (`LSeries.eq_zero_of_not_LSeriesSummable`), the statement splits *exactly* into

* **`re s ≤ 1`**: `heckeLSeries χ m s = 0`, i.e. the abscissa of absolute convergence is `1` —
  a genuine theorem (not the vacuous case: the terms `λ(n)n^{-σ}` do tend to `0` for `σ ≤ 1`
  because `‖λ(n)‖ ≤ 4τ(n)`), supplied below by `heckeLSeries_zero_of_re_le_one`;
* **`1 < re s ≤ 2`**: the L-series is the absolutely convergent Euler product, so this is exactly
  *FI* (16.23) restricted to the half-plane `re s > 1`, with one constant `c = c(ε)` uniform in
  `d, χ, m, s` — supplied below by `heckeLSeries_inv_bound_re_gt_one`.

The region condition `1 - c/(d^ε log(…)) < re s` is used only as a *hypothesis*; for `re s > 1` it
is automatic, and for `re s ≤ 1` the conclusion holds because the value is `0` for any `c`.
-/
import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea6Hecke.heckeLSeries_zero_of_re_le_one
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.heckeLSeries_inv_bound_re_gt_one

namespace Work.FIArea6Hecke

open scoped BigOperators

/-- **The `1 < σ ≤ 2` half of the target**: the Hecke inverse bound *FI* (16.23)/(16.24) in the
half-plane of absolute convergence.  Classical inputs (*FI* §16, pp. 1006–1009):
Hecke's functional equation (available: `FIArea5/S16Hecke/thetaHol_poisson`, `heckeFE_of_theta`,
`heckeFE_primitive`), the Phragmén–Lindelöf bounds (16.18)/(16.19), the zero-free region (16.20)
(from the de la Vallée Poussin `3-4-1` inequality for `ζ_K, L(·,ψ), L(·,ψ²)` together with the
continuation), Lemma 16.1 (Siegel's uniform bound for the real zeros, Goldfeld's method), and the
Borel–Carathéodory argument (`Commons/Analysis/Complex/logDeriv_zeroFree_ball_bound_analytic`,
`…/normSubLeOfReLeOnBall`) turning `‖L'/L‖ ≪ log²` into `‖1/L‖ ≪ d log²`; imprimitive `χ` are
handled by `L(s,χ) = L(s,χ_prim)·∏_{𝔭 | 4d/𝔣}(1 - χ_prim(𝔭)N𝔭^{-s})` with
`∏ (1 + N𝔭^{-σ})^{-1} ≥ 2^{-ω(4d)} ≥ (4d)^{-1}`. -/
theorem heckeLSeries_inv_bound_re_gt_one : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (chi : GaussianInt → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi → ∀ (m : ℤ) (s : ℂ),
        1 < s.re → s.re ≤ 2 →
        ‖(Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹‖
          ≤ c * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ) :=
  Work.FIArea6Hecke.R.heckeLSeries_inv_bound_re_gt_one

/-- **The reduction**: the two halves above give the target.  For a point of the region with
`re s ≤ 1` the `L`-series vanishes (any `c` works); for `1 < re s ≤ 2` the region condition is
automatic and the second half applies with its own constant. -/
theorem heckeInvBound_all_of
    (h1 : ∀ {d : ℕ}, 1 ≤ d → ∀ (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        ∀ (m : ℤ) {s : ℂ}, s.re ≤ 1 → Work.FIArea5.S16Hecke.heckeLSeries chi m s = 0)
    (h2 : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → ∃ c : ℝ, 0 < c ∧
        ∀ (d : ℕ) (chi : GaussianInt → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi → ∀ (m : ℤ) (s : ℂ),
        1 < s.re → s.re ≤ 2 →
        ‖(Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹‖
          ≤ c * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)) :
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 → Work.FITop4.Bridge.HeckeInvBoundAll ε := by
  intro ε hε hε4
  obtain ⟨c, hcpos, hc⟩ := h2 ε hε hε4
  refine ⟨c, hcpos, ?_⟩
  intro d chi hd hchi m s hregion hs2
  by_cases hcase : s.re ≤ 1
  · rw [h1 hd chi hchi m hcase, inv_zero, norm_zero]
    positivity
  · exact hc d chi hd hchi m s (not_le.mp hcase) hs2

end Work.FIArea6Hecke
