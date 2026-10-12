import Mathlib.Tactic.Module
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB7.aDag_eq
import Submission.Work.BoseB7.a_eq
import Submission.Work.BoseB7.bCommutatorDag_swap_apply
import Submission.Work.BoseB7.bCommutator_swap_apply
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.Q3_split` — FS `lem:EstimatesOnQ3-js`: the splitting of `3Q`

FS §10 (`lem:EstimatesOnQ3-js`) rewrites the cubic word `Q3(z)` of
`eq:kroelleQ3z` in terms of the squeezed modes `b_k = a_k + α_k a_{-k}†`
(`eq:Defb_k`) and splits it into four pieces `Q3^(1) … Q3^(4)`.  This module
proves that splitting as an identity of operators on the `B4` Fock interface:

`Q3 = Q3⁽¹⁾ + Q3⁽²⁾ + Q3⁽³⁾ + Q3⁽⁴⁾`

(`Work.BoseB7.FockData.Q3`, `Q3one`, `Q3two`, `Q3three`, `Q3four` of
`Work.BoseB7.Q3Defs`), under the kernel hypotheses `EstHyp` of §10.

## The computation

The substitution is FS's `eq:asInTermsOfbs` (`Work.BoseB7.a_eq`,
`Work.BoseB7.aDag_eq`)

`a_k = (1-α_k²)⁻¹ (b_k - α_k b_{-k}†)`,  `a_k† = (1-α_k²)⁻¹ (b_k† - α_k b_{-k})`,

applied **only** to the two `k`-modes `k` and `s - k` of the two cubic
monomials; the localised mode `ã_s` is kept (`ã_s† = a_s†`, `ã_s = a_s`), which is
exactly how the four pieces are written (the denominators `1-α_k²` are
non-zero by `EstHyp.Bsmall` + `EstHyp.Apos`, cf.
`Work.BoseB7.half_le_one_sub_alphaCoef_sq`: `1-α_k² ≥ 1/2`).

Expanding `(b_{s-k} - α_{s-k}b_{k-s}†)(b_k - α_kb_{-k}†)` produces the `bb` and
`b†b†` pieces directly, but the two "cross" terms come out with the order of the
`b`'s reversed, so the computation needs the squeezed commutator

`[b_{s-k}, b_{-k}†] = [b_{-k}, b_{s-k}†] = (1-α_kα_{s-k})(χ̂²(s) - χ̂(k)χ̂(s-k)) • 1`

(`Work.BoseB7.bCommutator_swap_apply`, `Work.BoseB7.bCommutatorDag_swap_apply`:
FS's kernel computation, a real multiple of the identity).  Hence the leftover
`-α_k[b_{s-k},b_{-k}†]∘ã_s†` from the first monomial and its adjoint
`-α_k[b_{-k},b_{s-k}†]∘ã_s` from the second recombine into

`-α_k[b_{s-k},b_{-k}†]∘(ã_s† + ã_s)`,

which is exactly the `Q3^(4)` summand (FS's "commutator piece").  The equality of
the two commutators is where the kernel hypothesis `EstHyp.hasKernel` (FS
`eq:Commutator_general`) and the parity of `χ̂`, `χ̂²`
(`EstHyp.hatChiEven`, `EstHyp.hatChiSqEven`) are used.

## Contents

* `FockData.qterm_split_apply` — the `(s,k)` summand, pointwise.
* `FockData.qterm_split` — the same, as operators on `F.H`.
* `Q3_split` — the sum over the mode lattice, i.e. `lem:EstimatesOnQ3-js`.
-/

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Work.BoseB7

namespace FockData

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The splitting of one `(s,k)` summand -/

/-- **The `(s,k)` summand of FS `lem:EstimatesOnQ3-js`**: the two cubic monomials
`ã_s†a_{s-k}a_k + a_k†a_{s-k}†ã_s`, rewritten in the `b`'s.  This is the
algebraic heart of the four estimates: every piece of `Q3^(1) … Q3^(4)` appears
with its FS coefficient, and the fourth piece is exactly the commutator term
`-α_k[b_{s-k},b_{-k}†]∘(ã_s† + ã_s)`. -/
theorem qterm_split_apply (F : FockData Mode) (E : Q3Env Mode) (h : EstHyp F E)
    (s k : Mode) (x : F.H) :
    (F.qterm s k + F.qtermDag s k) x
      = (E.q3Denom s k) •
        ( (F.T1a E s k + (E.alpha k * E.alpha (s - k)) • F.T1b E s k
          + F.T1aDag E s k + (E.alpha k * E.alpha (s - k)) • F.T1bDag E s k
          - (E.alpha k) • (F.T2 E s k + F.T2Dag E s k)
          - (E.alpha (s - k)) • (F.T3 E s k + F.T3Dag E s k)
          - (E.alpha k) • (F.bCommutator E s k ∘ₗ (F.aDag s + F.a s)) ) x) := by
  -- unfold the two cubic monomials and the four pieces
  simp only [qterm, qtermDag, T1a, T1b, T1aDag, T1bDag, T2, T2Dag, T3, T3Dag, bCommutator,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  -- substitute `a_k`, `a_k†`, `a_{s-k}`, `a_{s-k}†` (the modes `ã_s`, `ã_s†` are kept)
  rw [a_eq F E h k, a_eq F E h (s - k), aDag_eq F E h k, aDag_eq F E h (s - k)]
  -- expand all the linearity: turns into scalar multiples of the eight `b`-monomials
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add, map_sub,
    map_smul, smul_add, smul_sub, smul_smul, neg_sub]
  -- the two cross terms: move `b_{-k}†` past `b_{s-k}` (resp. `b_{-k}` past `b_{s-k}†`)
  simp only [bCommutator_swap_apply F E h s k, bCommutatorDag_swap_apply F E h s k]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add, map_sub,
    map_smul, smul_add, smul_sub, smul_smul]
  -- `(1-α_k²)⁻¹(1-α_{s-k}²)⁻¹ = q3Denom`
  rw [show E.q3Denom s k = (1 - E.alpha k ^ 2)⁻¹ * (1 - E.alpha (s - k) ^ 2)⁻¹ from by
    simp only [Q3Env.q3Denom, one_div, mul_inv_rev]
    ring]
  module

/-- `qterm_split_apply` as an identity of operators on one `(s,k)`. -/
theorem qterm_split (F : FockData Mode) (E : Q3Env Mode) (h : EstHyp F E) (s k : Mode) :
    F.qterm s k + F.qtermDag s k =
      (E.q3Denom s k) •
        ( F.T1a E s k + (E.alpha k * E.alpha (s - k)) • F.T1b E s k
          + F.T1aDag E s k + (E.alpha k * E.alpha (s - k)) • F.T1bDag E s k
          - (E.alpha k) • (F.T2 E s k + F.T2Dag E s k)
          - (E.alpha (s - k)) • (F.T3 E s k + F.T3Dag E s k)
          - (E.alpha k) • (F.bCommutator E s k ∘ₗ (F.aDag s + F.a s)) ) := by
  ext x
  rw [LinearMap.smul_apply]
  exact qterm_split_apply F E h s k x

end FockData

/-! ## 2. Summing over the lattice: FS `lem:EstimatesOnQ3-js` -/

/-- **FS `lem:EstimatesOnQ3-js`**: the cubic word `Q3` of `eq:kroelleQ3z` is the
sum of its four pieces `Q3^(1) … Q3^(4)`, obtained by the Bogoliubov substitution
`a_k = (1-α_k²)⁻¹(b_k - α_k b_{-k}†)` in the two `k`-modes.

Each `(s,k)` summand of `Q3` carries the weight `f_L(s)Ŵ₁(k)`; multiplying
`qterm_split` by it and regrouping the scalars gives exactly the summands of
`Q3one` … `Q3four`, so the double sums over `s` and `k ∈ P_H` can be added
summand by summand (`Finset.sum_add_distrib`). -/
theorem Q3_split {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (h : Work.BoseB7.EstHyp F E) :
    F.Q3 E = F.Q3one E + F.Q3two E + F.Q3three E + F.Q3four E := by
  have h1 : ∀ s k : Mode, (E.fL s * E.W1 k) • (F.qterm s k + F.qtermDag s k)
      = (E.fL s * E.W1 k * E.q3Denom s k) •
          (F.T1a E s k + (E.alpha k * E.alpha (s - k)) • F.T1b E s k
           + F.T1aDag E s k + (E.alpha k * E.alpha (s - k)) • F.T1bDag E s k)
        + (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)) • (F.T2 E s k + F.T2Dag E s k)
        + (-(E.fL s * E.W1 k * E.alpha (s - k) * E.q3Denom s k)) •
            (F.T3 E s k + F.T3Dag E s k)
        + (-(E.fL s * E.W1 k * E.alpha k * E.q3Denom s k)) •
            (F.bCommutator E s k ∘ₗ (F.aDag s + F.a s)) := by
    intro s k
    rw [FockData.qterm_split F E h s k]
    module
  rw [FockData.Q3, FockData.Q3one, FockData.Q3two, FockData.Q3three, FockData.Q3four]
  simp only [h1, Finset.sum_add_distrib, smul_add]

end Work.BoseB7
