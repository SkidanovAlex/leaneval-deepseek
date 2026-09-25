import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.B.Phi_analyticOn
import Submission.Work.RHContract.B.PhiSecondDerivDefs
import Submission.Work.RHContract.B.h2_eq_h2Closed
import Submission.Work.RHContract.B.deriv_mellin_const_sub
import Submission.Work.RHContract.B.deriv_deriv_mellin_const_sub
import Submission.Work.RHContract.B.h2_eq_mellin
import Submission.Work.RHContract.B.mellin_logSq_phiIntegrandCut

/-!
# `Φ'' = h₂ − h₂′`  (ROUTE_LEAD §3.3, part of lemma B3)

`Φ(s) = ∫_2^∞ (ψ t − t) k(t) t^{−s} dt` with `k t = (log t + 1)/(t² log² t)` is the Mellin
transform of the cut-off integrand `phiIntegrandCut`, and the second derivative in `s` brings
down a factor `log² t`:

`Φ''(s) = ∫_2^∞ (ψ t − t) k(t) log² t · t^{−s} dt`.

Since `k(t) log² t = (1 + log t)/t²`, this equals

`∫_2^∞ (ψ t − t)(1 + log t) t^{−s−2} dt = h₂(s) + ∫_2^∞ (ψ t − t) log t · t^{−s−2} dt`,

and the second summand is `−h₂′(s)`, because differentiating the integrand of
`h₂(s) = ∫_2^∞ (ψ t − t) t^{−s−2} dt` in `s` produces the extra factor `−log t`.  Hence

`Φ''(s) = h₂(s) − h₂′(s)` on `Re s > 0`, and on that half-plane `h₂ = h₂Closed`
(`Submission.Work.RHContract.B.h2_eq_h2Closed`), so `h₂′` may be computed from the closed form.

The ingredients are

* the generic Mellin differentiation lemmas
  `Work.RHContract.B.deriv_mellin_const_sub` and
  `Work.RHContract.B.deriv_deriv_mellin_const_sub`, applied to `f = phiIntegrandCut` and to
  `f = psiSubIdCut`;
* `Work.RHContract.B.h2_eq_mellin`, identifying `h₂` with `mellin psiSubIdCut (−s−1)`;
* `Work.RHContract.B.mellin_logSq_phiIntegrandCut`, the kernel identity
  `log² · k = (1 + log)/t²` transported to Mellin transforms;
* additivity of the Mellin transform, which needs both summands to be Mellin convergent.
-/

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace Work.RHContract.B

noncomputable section

/-! ## Mellin convergence of the two cut-off integrands -/

/-- `mellin psiSubIdCut (−s − 1)` converges for `Re s > 0`: the integrand is `O(t^{−Re s − 1})`. -/
lemma mellinConvergent_psiSubIdCut (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent psiSubIdCut (-s - 1) := by
  have htop : (-s - 1).re < (-1 : ℝ) := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hbot : ((-s - 1).re - 1) < (-s - 1).re := by linarith
  exact mellinConvergent_of_isBigO_rpow (a := -1) (b := (-s - 1).re - 1)
    locallyIntegrableOn_psiSubIdCut (by simpa using psiSubIdCut_isBigO_atTop) htop
    (psiSubIdCut_isBigO_nhdsGT _) hbot

/-- `mellin (log • psiSubIdCut) (−s − 1)` converges for `Re s > 0`. -/
lemma mellinConvergent_log_psiSubIdCut (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (fun t : ℝ => Real.log t • psiSubIdCut t) (-s - 1) := by
  have hlt : (-s - 1).re < (-1 : ℝ) := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  refine mellinConvergent_of_isBigO_rpow (a := ((-s - 1).re + (-1)) / 2)
    (b := (-s - 1).re - 1) locallyIntegrableOn_log_psiSubIdCut ?_ ?_
    (log_psiSubIdCut_isBigO_nhdsGT _) (by linarith)
  · exact log_psiSubIdCut_isBigO_atTop (by linarith)
  · linarith

/-! ## Additivity of the Mellin transform -/

/-- `psiSubIdLogCut = psiSubIdCut + log • psiSubIdCut` pointwise, hence for `Re s > 0` the
Mellin transforms add up. -/
lemma mellin_psiSubIdLogCut_add (s : ℂ) (hs : 0 < s.re) :
    mellin psiSubIdLogCut (-s - 1)
      = mellin psiSubIdCut (-s - 1)
        + mellin (fun t : ℝ => Real.log t • psiSubIdCut t) (-s - 1) := by
  have h1 := mellinConvergent_psiSubIdCut s hs
  have h2 := mellinConvergent_log_psiSubIdCut s hs
  have heq : psiSubIdLogCut = fun t : ℝ => psiSubIdCut t + Real.log t • psiSubIdCut t := by
    funext t
    by_cases ht : 2 < t
    · rw [psiSubIdLogCut_apply_of_gt ht, psiSubIdCut_apply_of_gt ht]
      push_cast
      rw [Complex.real_smul]
      ring
    · rw [psiSubIdLogCut_apply_of_le (not_lt.mp ht), psiSubIdCut_apply_of_le (not_lt.mp ht)]
      simp
  rw [heq]
  exact (hasMellin_add h1 h2).2

/-! ## `h₂` and its derivative -/

/-- On the open half-plane `Re s > 0` the integral `h₂` agrees with the closed form
`h₂Closed` (`Submission.Work.RHContract.B.h2_eq_h2Closed`), hence so do their derivatives. -/
lemma h2_eventuallyEq_h2Closed (s : ℂ) (hs : 0 < s.re) :
    Filter.EventuallyEq (nhds s) Landau.h2Closed Landau.h2 := by
  have hopen : {z : ℂ | 0 < z.re} ∈ nhds s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
  filter_upwards [hopen] with z hz
  exact (h2_eq_h2Closed z hz).symm

/-- `h₂′(s) = −∫_2^∞ (ψ t − t) log t · t^{−s−2} dt` for `Re s > 0`. -/
lemma deriv_h2_eq (s : ℂ) (hs : 0 < s.re) :
    deriv Landau.h2 s = - mellin (fun t : ℝ => Real.log t • psiSubIdCut t) (-s - 1) := by
  have hm : Landau.h2 = fun z : ℂ => mellin psiSubIdCut ((-1 : ℂ) - z) := by
    funext z
    rw [h2_eq_mellin]
    congr 1
    ring
  rw [hm]
  have htop : ((-1 : ℂ) - s).re < (-1 : ℝ) := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hbot : (((-1 : ℂ) - s).re - 1) < ((-1 : ℂ) - s).re := by linarith
  have h := deriv_mellin_const_sub (f := psiSubIdCut) (a := -1) (b := ((-1 : ℂ) - s).re - 1)
    (c := -1) locallyIntegrableOn_psiSubIdCut (by simpa using psiSubIdCut_isBigO_atTop) htop
    (psiSubIdCut_isBigO_nhdsGT _) hbot
  rw [show (-1 : ℂ) - s = -s - 1 by ring] at h
  exact h

/-! ## The second derivative of `Φ` -/

/-- `Φ''(s) = ∫_2^∞ (ψ t − t) k(t) log² t · t^{−s} dt`, i.e. the Mellin transform at `1 − s` of
`log² • phiIntegrandCut`. -/
lemma Phi_secondDeriv_mellin (s : ℂ) (hs : 0 < s.re) :
    deriv (deriv Landau.Phi) s
      = mellin (fun t : ℝ => (Real.log t) ^ 2 • phiIntegrandCut t) (1 - s) := by
  rw [Phi_eq_mellin]
  have htop : (1 - s).re < (1 : ℝ) := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hbot : ((1 - s).re - 1) < (1 - s).re := by linarith
  exact deriv_deriv_mellin_const_sub (f := phiIntegrandCut) (a := 1) (b := (1 - s).re - 1)
    (c := 1) locallyIntegrableOn_phiIntegrandCut phiIntegrandCut_isBigO_atTop htop
    (phiIntegrandCut_isBigO_nhdsGT _) hbot

/-! ## The Landau second-derivative identity -/

/-- **The identity `Φ'' = h₂ − h₂′` of ROUTE_LEAD §3.3 (part of lemma B3).**  For `Re s > 0`,

`deriv (deriv Φ) s = h₂(s) − h₂′(s) = h2Minus s`. -/
theorem Phi_secondDeriv (s : ℂ) (hs : 0 < s.re) :
    deriv (deriv Work.RHContract.Landau.Phi) s = Work.RHContract.Landau.h2Minus s := by
  have hΦ := Phi_secondDeriv_mellin s hs
  have hD := mellin_logSq_phiIntegrandCut s
  have hA := mellin_psiSubIdLogCut_add s hs
  have hC := h2_eq_mellin s
  have hE := deriv_h2_eq s hs
  have hE' : mellin (fun t : ℝ => Real.log t • psiSubIdCut t) (-s - 1)
      = -deriv Landau.h2 s := by
    rw [hE]; ring
  have hF : deriv Landau.h2Closed s = deriv Landau.h2 s :=
    (h2_eventuallyEq_h2Closed s hs).deriv_eq
  rw [hΦ, hD, hA, ← hC, hE', Landau.h2Minus, h2_eq_h2Closed s hs, ← hF]
  ring

end

end Work.RHContract.B
