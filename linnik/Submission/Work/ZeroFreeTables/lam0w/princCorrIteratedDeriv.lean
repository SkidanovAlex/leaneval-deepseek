import Mathlib
import Submission.Work.ZeroFreeTables.lam0w.PrincipalDefs
import Submission.Work.ZeroFreeTables.XY.PrincipalSigma.LogDerivPrincipalDecomp

open DirichletCharacter Complex
open scoped BigOperators
noncomputable section

namespace Work.ZeroFreeTables.lam0w

open Filter
open scoped Topology

/-- The pointwise form of `princCorr q = zetaCorr - eulFac q` on the half plane `1 < Re z`,
obtained from the logarithmic derivative of the Euler-product identity
`L(·, 1) = ζ · ∏_{p ∣ q} (1 - p^{-z})`. -/
lemma princCorr_apply_eq_zetaCorr_sub_eulFac (q : ℕ) [NeZero q] {z : ℂ} (hz : 1 < z.re) :
    princCorr q z = zetaCorr z - eulFac q z := by
  have h := Work.ZeroFreeTables.XY.PrincipalSigma.logDeriv_LFunctionTrivChar_eq q hz
  rw [princCorr, zetaCorr, eulFac, h]
  ring

/-- `zetaCorr` is analytic on the half plane `1 < Re z`. -/
lemma analyticAt_zetaCorr_lam0w {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ zetaCorr s := by
  have h1 : AnalyticAt ℂ (logDeriv riemannZeta) s :=
    Work.ZeroFreeTables.XY.PrincipalSigma.analyticAt_logDeriv_riemannZeta hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have h2 : AnalyticAt ℂ (fun z : ℂ => (z - 1)⁻¹) s := by
    apply AnalyticAt.inv
    · exact (analyticAt_id (𝕜 := ℂ) (z := s)).sub (analyticAt_const (v := (1 : ℂ)) (x := s))
    · exact sub_ne_zero.mpr hs1
  have h3 : AnalyticAt ℂ ((-(logDeriv riemannZeta)) - fun z : ℂ => (z - 1)⁻¹) s :=
    h1.neg.sub h2
  have hz : zetaCorr = fun z : ℂ => -logDeriv riemannZeta z - (z - 1)⁻¹ := by
    funext z; rfl
  rw [hz]; exact h3

/-- `eulFac q` is analytic on the half plane `1 < Re z`. -/
lemma analyticAt_eulFac_lam0w (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (eulFac q) s := by
  have he : eulFac q = fun z : ℂ => ∑ p ∈ q.primeFactors,
      (Real.log (p : ℝ) : ℂ) / ((p : ℂ) ^ z - 1) := by
    funext z; rfl
  rw [he]; exact Work.ZeroFreeTables.XY.PrincipalSigma.analyticAt_eulerSum q hs

/-- `princCorr q = zetaCorr - eulFac q` on `Re s > 1`, transported to iterated derivatives.

The function-level identity is `L(·,χ₀) = ζ · ∏_{p | q}(1 - p^{-z})` on `Re z > 1`, which follows
from Mathlib's `DirichletCharacter.LSeries_changeLevel` with `M = 1`, `N = q`,
`χ = (1 : DirichletCharacter ℂ 1)`, `hMN = one_dvd q`, together with
`DirichletCharacter.changeLevel_one`, `LSeries_one_eq_riemannZeta` and
`DirichletCharacter.LFunction_eq_LSeries`.  Take `logDeriv` of both sides
(`logDeriv_mul`, `logDeriv_prod`), using that `ζ z ≠ 0` and `1 - p^{-z} ≠ 0` for `Re z > 1`
(`|p^{-z}| = p^{-Re z} < 1`), and that `logDeriv (z ↦ 1 - p^{-z}) z = log p/(p^z - 1)`.
Then conclude with `Filter.EventuallyEq.iteratedDeriv_eq` (`Re > 1` is an open neighbourhood of
`s`) and `iteratedDeriv_sub`, both applied for `j ≤ 2`. -/
theorem princCorrIteratedDeriv (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re)
    (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (Work.ZeroFreeTables.lam0w.princCorr q) s
      = iteratedDeriv j Work.ZeroFreeTables.lam0w.zetaCorr s
        - iteratedDeriv j (Work.ZeroFreeTables.lam0w.eulFac q) s := by
  have hfun : princCorr q =ᶠ[𝓝 s] zetaCorr - eulFac q := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact princCorr_apply_eq_zetaCorr_sub_eulFac q hz
  rw [Filter.EventuallyEq.iteratedDeriv_eq j hfun]
  exact iteratedDeriv_sub (analyticAt_zetaCorr_lam0w hs).contDiffAt
    (analyticAt_eulFac_lam0w q hs).contDiffAt

end Work.ZeroFreeTables.lam0w
