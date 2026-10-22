import Mathlib
import Submission.Work.ANALYTIC.unprimedSetup
import Submission.Work.ANALYTIC.exists_pairMor
import Submission.Work.ANALYTIC.BoundedSeqC

/-!
# The truncation data of `δ` is the pullback of `δ` along `pairMor`

Let `δ = deltaElem ∈ ∏^bnd ℤ(ℕ∪{∞})` be the null sequence `n ↦ δ_n` of `BoundedSeqC.lean`, and let
`pairMor : (ℕ∪{∞})² ⟶ ℕ∪{∞}` be the map `(k,j) ↦ j` for `k ≤ j` (both finite) and `∞` otherwise
(`exists_pairMor.lean`).  This file proves

`truncDataElem (ℕ∪{∞}) δ = (boundedSeq.obj.map pairMor.op) δ`,

i.e. the "truncation data" of `δ` at `S = ℕ∪{∞}` (the element of `∏^bnd ℤ` over `(ℕ∪∞)²` with
`m`-th component `(k,j) ↦ δ_m(j)·[k ≤ m]`, cf. `unprimedSetup.truncDataElem`) is exactly the
pullback of `δ` along `pairMor`: its `m`-th component is `(k,j) ↦ δ_m(pairMor (k,j))`, which is `1`
at the points `(k,m)` with `k ≤ m` and `0` elsewhere.

Pointwise, the identity is the elementary statement

`δ_m(j)·(1 - ∏_{i ≤ m}(1 - δ_i(k))) = δ_m(pairFunP (k,j))`

for `k, j ∈ ℕ∪{∞}` and `m : ℕ`: the factor `1 - ∏_{i ≤ m}(1 - δ_i(k))` is the characteristic
function of `{k ≤ m}`, and `δ_m ∘ pairFunP` is the characteristic function of the pairs `(k,m)`
with `k ≤ m`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.ANALYTIC

/-- The product `∏_{i ≤ m} (1 - δ_i(∞))` equals `1`: every factor is `1 - 0`. -/
private lemma truncDataElem_prod_at_infty (m : ℕ) :
    (∏ i ∈ Finset.range (m + 1), (1 - deltaFun i (∞ : ℕ∪{∞}))) = 1 :=
  Finset.prod_eq_one fun i _ => by rw [deltaFun_infty, sub_zero]

/-- `1 - ∏_{i ≤ m}(1 - δ_i(n))` is the characteristic function of `{n ≤ m}`. -/
private lemma truncDataElem_one_sub_prod_deltaFun (m n : ℕ) :
    1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i ((n : ℕ) : ℕ∪{∞})) =
      (if n ≤ m then 1 else 0) := by
  by_cases hn : n ≤ m
  · rw [ite_eq_left hn, Finset.prod_eq_single (a := n)]
    · rw [deltaFun_at]; ring
    · intro b hb hbn
      rw [deltaFun_eq,
        ite_eq_right (fun h : ((n : ℕ) : ℕ∪{∞}) = ((b : ℕ) : ℕ∪{∞}) =>
          hbn (OnePoint.coe_eq_coe.mp h).symm), sub_zero]
    · intro hn'
      exact absurd (Finset.mem_range.mpr (by omega)) hn'
  · rw [ite_eq_right hn]
    have h : (∏ i ∈ Finset.range (m + 1), (1 - deltaFun i ((n : ℕ) : ℕ∪{∞}))) = 1 :=
      Finset.prod_eq_one fun i hi => by
        rw [deltaFun_eq,
          ite_eq_right (fun h : ((n : ℕ) : ℕ∪{∞}) = ((i : ℕ) : ℕ∪{∞}) => ?_), sub_zero]
        have hin : n = i := OnePoint.coe_eq_coe.mp h
        have hi' : i < m + 1 := Finset.mem_range.mp hi
        omega
    rw [h]; ring

/-- **The pointwise identity.**  For `k, j ∈ ℕ∪{∞}` and `m : ℕ`,
`δ_m(j)·(1 - ∏_{i ≤ m}(1 - δ_i(k))) = δ_m(pairFunP (k,j))`. -/
private lemma truncDataElem_pairFunP_eval (m : ℕ) (k j : OnePoint ℕ) :
    deltaFun m j * (1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i k)) =
      deltaFun m (pairFunP (k, j)) := by
  cases k with
  | infty =>
    have h : pairFunP (((∞ : OnePoint ℕ)), j) = (∞ : OnePoint ℕ) := pairFunP_infty_fst j
    rw [h, truncDataElem_prod_at_infty, sub_self, mul_zero, deltaFun_infty]
  | coe k =>
    cases j with
    | infty =>
      have h : pairFunP (((k : ℕ) : OnePoint ℕ), (∞ : OnePoint ℕ)) = (∞ : OnePoint ℕ) :=
        pairFunP_infty_snd ((k : ℕ) : OnePoint ℕ)
      rw [h, deltaFun_infty, zero_mul]
    | coe j =>
      have h : pairFunP (((k : ℕ) : OnePoint ℕ), ((j : ℕ) : OnePoint ℕ)) =
          (if k ≤ j then ((j : ℕ) : OnePoint ℕ) else (∞ : OnePoint ℕ)) := pairFunP_finite k j
      rw [h, truncDataElem_one_sub_prod_deltaFun]
      by_cases hj : j = m
      · rw [hj, deltaFun_at]
        by_cases hk : k ≤ m
        · rw [ite_eq_left hk, ite_eq_left hk, deltaFun_at, mul_one]
        · rw [ite_eq_right hk, ite_eq_right hk, mul_zero, deltaFun_infty]
      · rw [deltaFun_eq, ite_eq_right (fun hh => hj (OnePoint.coe_eq_coe.mp hh)), zero_mul]
        by_cases hkj : k ≤ j
        · rw [ite_eq_left hkj, deltaFun_eq,
            ite_eq_right (fun hh => hj (OnePoint.coe_eq_coe.mp hh))]
        · rw [ite_eq_right hkj, deltaFun_infty]

theorem truncDataElem_ns2_deltaElem : Work.ANALYTIC.truncDataElem LightProfinite.NatUnionInfty Work.ANALYTIC.deltaElem = (Work.ANALYTIC.boundedSeq.obj.map (Work.ANALYTIC.pairMor).op) Work.ANALYTIC.deltaElem := by
  apply Subtype.ext
  funext m
  apply ContinuousMap.ext
  intro p
  -- The two sides are the `m`-th coordinates, evaluated at a point `p = (k,j)`.
  show deltaElem.1 m p.2 * (1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i p.1)) =
    deltaElem.1 m (pairMor p)
  show deltaFun m p.2 * (1 - ∏ i ∈ Finset.range (m + 1), (1 - deltaFun i p.1)) =
    deltaFun m (pairFunP (p.1, p.2))
  exact truncDataElem_pairFunP_eval m (p.1 : OnePoint ℕ) (p.2 : OnePoint ℕ)

end Work.ANALYTIC
