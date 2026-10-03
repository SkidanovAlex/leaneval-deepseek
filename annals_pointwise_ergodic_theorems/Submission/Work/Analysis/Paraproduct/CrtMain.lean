/-
# The Chinese-remainder factorisation of the arithmetic averaging operator: norm identity

This module assembles the Chinese-remainder factorisation of Section 10 of Krause--Mirek--Tao,
*Pointwise ergodic theorems for non-conventional bilinear polynomial averages*, Annals 195
(2022): for coprime `m, n`, the arithmetic bilinear averaging estimate for `ℤ/mnℤ` follows from
the same estimate for `ℤ/mℤ` and `ℤ/nℤ`, with the constants multiplied — the paper's use of
`ttensor-bil` in the proof of Theorem `bile`:

> From Examples `avg-mult`, `tensor-mult` we see that the bilinear operator `A_{∏_{p∈S} ℤ_p}` is
> the tensor product of the individual operators `A_{ℤ_p}`, so by (ttensor-bil) we may factor the
> operator norm as `∏_{p∈S} ‖A_{ℤ_p}‖`.

The proof is the composition of three ingredients:

* `crtTransport_polyBilinearAverage` : the arithmetic averaging operator over `ℤ/mnℤ` is, under
  the Chinese-remainder isomorphism `ℤ/mnℤ ≃+* ℤ/mℤ × ℤ/nℤ`, the tensor product of the
  averaging operators over `ℤ/mℤ` and `ℤ/nℤ`;
* `bilinearAverageLq_prod` : the tensor-product norm identity `ttensor-bil` for the arithmetic
  averaging operators (built on `bilinKernelOp_tensorKernel_le`);
* `LpNormZMod_crtTransport` : the normalised `L^p` norm of `ℤ/mnℤ` agrees with the normalised
  `L^p` norm of `ℤ/mℤ × ℤ/nℤ` under the Chinese-remainder relabelling.
-/
import Submission.Work.Analysis.Paraproduct.bilinearAverageLq_prod
import Submission.Work.Analysis.Paraproduct.crtTransport_polyBilinearAverage
import Submission.Work.Analysis.Paraproduct.LpNormZMod_crtTransport

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Paraproduct

noncomputable section

open Work.Analysis.Concentration
open Polynomial

/-- **Chinese-remainder factorisation of the arithmetic bilinear estimate.**  For coprime
`m, n : ℕ` and `1 ≤ q`, if the arithmetic bilinear averaging estimate of Theorem `bile` holds on
`ℤ/mℤ` with constant `C₁` and on `ℤ/nℤ` with constant `C₂`, then it holds on `ℤ/mnℤ` with
constant `C₁ * C₂`.  (In the paper this is applied iteratively over the primes dividing the
denominator `Q`; the base cases are the `ℤ_p` estimates (avg-1)/(avg-2).) -/
theorem BilinearAverageLq_crt (P : ℤ[X]) {m n : ℕ} [NeZero m] [NeZero n] (h : m.Coprime n)
    {q C₁ C₂ : ℝ} (hq : 1 ≤ q)
    (h₁ : BilinearAverageLq P m q C₁) (h₂ : BilinearAverageLq P n q C₂) :
    BilinearAverageLq P (m * n) q (C₁ * C₂) := by
  intro F G
  have hprod := bilinearAverageLq_prod P (m := m) (n := n) hq h₁ h₂
    (fun z => F ((ZMod.chineseRemainder h).symm z))
    (fun z => G ((ZMod.chineseRemainder h).symm z))
  rw [← LpNormZMod_crtTransport h q (polyBilinearAverageZMod X P (m * n) F G),
      crtTransport_polyBilinearAverage X P h F G]
  refine hprod.trans (le_of_eq ?_)
  rw [LpNormZMod_crtTransport h 2 F, LpNormZMod_crtTransport h 2 G]

end

end Work.Analysis.Paraproduct
