import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ANALYTIC.BoundedSeqC
import Submission.Work.ANALYTIC.exists_pairMor
import Submission.Work.ANALYTIC.boundedSeq_sheaf
import Submission.Work.ANALYTIC.exists_tower_F

/-!
# The truncation data of `δ` is the pullback of `δ` along `pairMor`

The element `δ ∈ ∏^bnd ℤ(ℕ∪∞)` (`Work.ANALYTIC.deltaElem`) is the null sequence
`n ↦ δ_n = [k = n]` of basis vectors.  The truncation data `truncDataElem S x`
(`Submission/Work/ANALYTIC/unprimedSetup.lean`) is the element of `∏^bnd ℤ((ℕ∪∞) × S)` whose
`m`-th component is `(k,s) ↦ x_m(s)·[k ≤ m]`; its value at the point `S = ℕ∪∞` is described by

* `truncDataElemDeltaElem_coeff`: the coefficient `1 - ∏_{i ≤ m}(1 - δ_i k)` is the
  characteristic function of `{k ≤ m}` (with `k = ∞` ↦ `0`), i.e. it is `truncCoeff m k`;
* `truncDataElemDeltaElem_pairFunP` / `truncDataElemDeltaElem_pairMor`: for the truncation map
  `pairMor (k,j) = j` if `k ≤ j` (finite) and `∞` otherwise
  (`Submission/Work/ANALYTIC/exists_pairMor.lean`), the `m`-th basis function satisfies
  `δ_m (pairMor (k,j)) = δ_m (j)·[k ≤ m]`.

Together they give the current statement: `truncDataElem (ℕ∪∞) δ` is the pullback of `δ` along
`pairMor`, because both sides have `m`-th component `(k,j) ↦ [j = m]·[k ≤ m]`.

This is the "primed" coefficient identity (REFS/03 §2) used to compare the primed family
`F' : P ⊗ P ⟶ P` with the unprimed truncation tower: the `k`-th slice of the truncation tower at
`x = δ` is the pullback of `δ` along the map `(k,j) ↦ j` of `[k ≤ j]`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Work.ANALYTIC

/-! ## The truncation coefficient `1 - ∏_{i ≤ m}(1 - δ_i k)` for `k ∈ ℕ∪∞` -/

/-- **The truncation coefficient in one-point form.**  For `k : ℕ∪∞` the product
`1 - ∏_{i ≤ m}(1 - δ_i k)` is the characteristic function of `{k ≤ m}`: it is `truncCoeff m k`,
which is `1` for `k = (n : ℕ∪∞)` with `n ≤ m` and `0` for `k = ∞` or `k = (n : ℕ∪∞)` with
`m < n`.  This is `Work.ANALYTIC.one_sub_prod_deltaFun` (the finite case) plus the computation at
`∞`, where every factor `δ_i(∞)` vanishes. -/
lemma truncDataElemDeltaElem_coeff (m : ℕ) (k : OnePoint ℕ) :
    1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i k) = truncCoeff m k := by
  cases k with
  | infty =>
    rw [truncCoeff_infty]
    have hprod : (∏ i ∈ Finset.range (m + 1), (1 - deltaFun i (∞ : OnePoint ℕ))) = 1 :=
      Finset.prod_eq_one fun i _ => by rw [deltaFun_infty, sub_zero]
    rw [hprod]; ring
  | coe n => rw [one_sub_prod_deltaFun m n, truncCoeff_coe]

/-! ## `δ_m` composed with the truncation map -/

/-- **`pairFunP` computes `δ_m`.**  For `k, j : ℕ∪∞` the `m`-th basis function at
`pairFunP (k,j)` (which is `j` if `k ≤ j` are finite and `∞` otherwise) is `δ_m(j)·[k ≤ m]`.

Both sides are `0` or `1`, and the only substantive case is that of two finite values `k = a`,
`j = b`: then `pairFunP (a,b) = b` if `a ≤ b` and `∞` otherwise, and the identity becomes
`[b = m]·[a ≤ b] = [b = m]·[a ≤ m]`, which holds because `b = m` forces `a ≤ b ↔ a ≤ m`. -/
lemma truncDataElemDeltaElem_pairFunP (m : ℕ) (k j : OnePoint ℕ) :
    deltaFun m (pairFunP (k, j)) = deltaFun m j * truncCoeff m k := by
  cases k with
  | infty => rw [pairFunP_infty_fst, deltaFun_infty, truncCoeff_infty, mul_zero]
  | coe a =>
    cases j with
    | infty => rw [pairFunP_infty_snd, deltaFun_infty, zero_mul]
    | coe b =>
      rw [pairFunP_finite, truncCoeff_coe, deltaFun_eq, deltaFun_eq]
      by_cases hab : a ≤ b
      · rw [ite_eq_left hab]
        by_cases hbm : ((b : ℕ∪{∞}) : OnePoint ℕ) = ↑m
        · rw [ite_eq_left hbm,
            ite_eq_left (by have := OnePoint.coe_eq_coe.mp hbm; omega : a ≤ m), mul_one]
        · rw [ite_eq_right hbm, zero_mul]
      · rw [ite_eq_right hab, ite_eq_right (OnePoint.infty_ne_coe m)]
        by_cases hbm : ((b : ℕ∪{∞}) : OnePoint ℕ) = ↑m
        · rw [ite_eq_left hbm,
            ite_eq_right (by have := OnePoint.coe_eq_coe.mp hbm; omega : ¬ a ≤ m), mul_zero]
        · rw [ite_eq_right hbm, zero_mul]

/-- **`δ_m` at the truncation map `pairMor`.**  Pointwise form of the statement for the elements
of `∏^bnd ℤ`: the `m`-th component of the pullback of `δ` along `pairMor` is
`δ_m(j)·[k ≤ m]`. -/
lemma truncDataElemDeltaElem_pairMor (m : ℕ) (p : ↥(Work.ATOM.NS2)) :
    deltaFun m (pairMor p) = deltaFun m p.2 * truncCoeff m p.1 := by
  rw [pairMor_apply]
  exact truncDataElemDeltaElem_pairFunP m p.1 p.2

/-! ## The statement -/

/-- **Pointwise form of the main identity.**  For every `m : ℕ` and every point
`p : ↥(Work.ATOM.NS2) = ↥((ℕ∪∞) ⊗ (ℕ∪∞))` the `m`-th components of `truncDataElem (ℕ∪∞) δ` and
of the pullback of `δ` along `pairMor` agree: the first is `δ_m(p.2)·[p.1 ≤ m]` and the second is
`δ_m(pairMor p)`, and these are equal by `truncDataElemDeltaElem_pairMor`. -/
lemma truncDataElemDeltaElem_apply (m : ℕ) (p : ↥(Work.ATOM.NS2)) :
    (truncDataElem LightProfinite.NatUnionInfty deltaElem).1 m p =
      (boundedSeq.obj.map (pairMor).op deltaElem).1 m p := by
  have hδ : deltaElem.1 m = deltaFun m := rfl
  rw [truncDataElem_val, boundedSeq_map_apply, hδ, truncDataElemDeltaElem_coeff]
  exact (truncDataElemDeltaElem_pairMor m p).symm

/-- **The truncation data of `δ` is the pullback of `δ` along `pairMor`** (REFS/03 §2, the
"primed" coefficient identity): the `m`-th component of `truncDataElem (ℕ∪∞) δ` at `(k,j)` is
`[j = m]·[k ≤ m]`, which is also the `m`-th component of `δ` pulled back along the truncation map
`(k,j) ↦ j` (`[k ≤ j]`). -/
theorem truncDataElemDeltaElem :
    Work.ANALYTIC.truncDataElem LightProfinite.NatUnionInfty Work.ANALYTIC.deltaElem =
      Work.ANALYTIC.boundedSeq.obj.map (Work.ANALYTIC.pairMor).op Work.ANALYTIC.deltaElem := by
  refine Subtype.ext (funext fun m => ContinuousMap.ext fun p => ?_)
  exact truncDataElemDeltaElem_apply m p

end Work.ANALYTIC
