import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.CDT.FineHolonomy
import Submission.Work.Tau.tau_flat_values
import Submission.Work.Tau.harmonic_values
import Submission.Work.Tau.correction_values

/-! Guidance from the project lead (the requester):

# Area Tau — exact denominator rates (`Submission.CDTPlan.TauValues`)

tauFlat bC = 1136/289 (paper: (1·0 + (3+5)·2 + (7+9+…+33)·4)/17²); tauFlat bA = 191/49.
tauSharpAt eC (7/4) = (2/289)(9·7/4 + I_{7/4}^{17}(7/4)) = 78419/242760;
tauSharpAt eA 2 = (2/196)(6·2 + I_2^{14}(2)) = 27/80. (Numerically verified: 0.32303097709672,
0.3375.) Hence the totals 1032659/242760 and 16603/3920.
I = `Submission.CDTPlan.integratedLcm u v w` (definitionally identical to `Submission.CDT.IntegratedLcm.integratedLcm`) (three interval integrals of piecewise
constant / piecewise rational functions of t with floors). For u = w = ξ ≥ 1 the first integral
is over [1,1] (zero). Split [ξ, m] at the breakpoints of ⌊(t−1)/ξ⌋ and ⌊(t+ξ−1)/ξ⌋ (for ξ=7/4:
t ∈ {1+7k/4} and {7k/4 − 3/4}); on each piece the integrand is constant or t/k − ξ (clipped at 0).
The prior run evaluated a case (`integratedLcm_two_three`, `FineHolonomy.lean`) — reuse its lemmas
(`integral_harmonicFun`, `harmonicFun_eq_*`, `correctionFun_eq_*`) and `Finset.sum` evaluation by
`norm_num`/`decide`. Final equalities in ℝ with rational right-hand sides.

## What is done here

The three pieces are delegated as the sibling lemmas `Work.Tau.tau_flat_values`,
`Work.Tau.harmonic_values`, `Work.Tau.correction_values`; this file assembles them:

* `integratedLcm_xi_17` : `I_{7/4}^{17}(7/4) = 37187/1260 + 7129/5040 = 51959/1680`;
* `integratedLcm_two_14` : `I_2^{14}(2) = 397/20 + 49/40 = 843/40`;
* `tauSharpAt_eC`, `tauSharpAt_eA` : the two `τ♯` values `78419/242760`, `27/80`
  (with `Σ eC = 9`, `Σ eA = 6`, `max eC = max eA = 1`);
* `tau_values` : the contract `TauValues`.

The bridges `Submission.CDTPlan.integratedLcm = Submission.CDT.IntegratedLcm.integratedLcm` etc.
are `rfl` (the two definitions are copies), recorded in `Submission/Work/Tau/defs.lean`.
-/

namespace Work.Tau

open Submission.CDTPlan
open MeasureTheory intervalIntegral
open scoped BigOperators

/-- `I_{7/4}^{17}(7/4)`: the first integral of the definition is over `[min (7/4) 1, 1] = [1,1]`,
hence zero; the harmonic and correction halves are `37187/1260` and `7129/5040`. -/
theorem integratedLcm_xi_17 : Submission.CDTPlan.integratedLcm (7 / 4) 17 (7 / 4) = 51959 / 1680 := by
  change Submission.CDT.IntegratedLcm.integratedLcm (7 / 4) 17 (7 / 4) = _
  unfold Submission.CDT.IntegratedLcm.integratedLcm
  rw [show min ((7 : ℝ) / 4) 1 = 1 from by norm_num,
    show max ((7 : ℝ) / 4) 1 = ((7 : ℝ) / 4) from by norm_num]
  rw [intervalIntegral.integral_same, zero_add, harmonic_values.1, correction_values.1]
  norm_num

/-- `I_2^{14}(2) = 397/20 + 49/40 = 843/40`. -/
theorem integratedLcm_two_14 : Submission.CDTPlan.integratedLcm 2 14 2 = 843 / 40 := by
  change Submission.CDT.IntegratedLcm.integratedLcm 2 14 2 = _
  unfold Submission.CDT.IntegratedLcm.integratedLcm
  rw [show min (2 : ℝ) 1 = 1 from by norm_num,
    show max (2 : ℝ) 1 = (2 : ℝ) from by norm_num]
  rw [intervalIntegral.integral_same, zero_add, harmonic_values.2, correction_values.2]
  norm_num

/-- `Σ_i eC i = 9`. -/
theorem sum_eC : (∑ i : Fin 17, eC i) = 9 := by decide

/-- `Σ_i eA i = 6`. -/
theorem sum_eA : (∑ i : Fin 14, eA i) = 6 := by decide

/-- `max_i eC i = 1`. -/
theorem sup_eC : (Finset.univ.sup eC : ℕ) = 1 := by decide

/-- `max_i eA i = 1`. -/
theorem sup_eA : (Finset.univ.sup eA : ℕ) = 1 := by decide

/-- The Theorem-C additive rate term `τ♯(eC) = (2/17²)((7/4)·9 + 1·I_{7/4}^{17}(7/4))`. -/
theorem tauSharpAt_eC : tauSharpAt eC (7 / 4) = 78419 / 242760 := by
  have hsum : (∑ i : Fin 17, (eC i : ℝ)) = 9 := by
    have h : ((∑ i : Fin 17, eC i : ℕ) : ℝ) = 9 := by
      rw [sum_eC]; norm_num
    rw [← h]; push_cast; rfl
  unfold tauSharpAt
  rw [hsum, sup_eC]
  norm_num only [Nat.cast_ofNat]
  rw [integratedLcm_xi_17]
  norm_num

/-- The Theorem-A additive rate term `τ♯(eA) = (2/14²)(2·6 + 1·I_2^{14}(2))`. -/
theorem tauSharpAt_eA : tauSharpAt eA 2 = 27 / 80 := by
  have hsum : (∑ i : Fin 14, (eA i : ℝ)) = 6 := by
    have h : ((∑ i : Fin 14, eA i : ℕ) : ℝ) = 6 := by
      rw [sum_eA]; norm_num
    rw [← h]; push_cast; rfl
  unfold tauSharpAt
  rw [hsum, sup_eA]
  norm_num only [Nat.cast_ofNat]
  rw [integratedLcm_two_14]
  norm_num

/-- **Area Tau**: the exact denominator rates used by the paper — `τ♭(bC) + τ♯(eC) = 1032659/242760`
(Theorem C) and `τ♭(bA) + τ♯(eA) = 16603/3920` (Theorem A). -/
theorem tau_values : TauValues := by
  unfold Submission.CDTPlan.TauValues
  exact ⟨by rw [tau_flat_values.1, tauSharpAt_eC]; norm_num,
    by rw [tau_flat_values.2, tauSharpAt_eA]; norm_num⟩

end Work.Tau
