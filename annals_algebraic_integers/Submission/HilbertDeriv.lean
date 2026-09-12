import Submission.MinkBox
import Submission.Quantile
import Submission.ThreePages
import Submission.EnergyHalf
import Submission.NormfInterp
import Mathlib.Tactic

/-!
# Product of derivative magnitudes at the quantile nodes is `(Vprod d)^2`

Child task: prove `Submission.HilbertDeriv.deriv_prod_sq` below.  Needed by
`Submission/HilbertMink.lean`.

Statement: for `d ≥ 2`,

    ∏ k : Fin d, |(approxPoly d).derivative.eval (alpha d (k.val + 1))| = (Vprod d)^2

where `approxPoly d = ThreePages.approxPoly d = ∏_{i∈Icc 1 d} (X − C(alpha d i))`
and `Vprod d = ∏_{i ∈ Icc 1 d} ∏_{j ∈ Icc (i+1) d} |alpha d i − alpha d j|`.

## Math background

At the node `α_m = alpha d m` (natural `m ∈ Finset.Icc 1 d`) the derivative is
`∏_{j ∈ (Icc 1 d).erase m} (alpha d m − alpha d j)` (derivative of a product of
monic linear factors).  The magnitude is then the product of the absolute
values.  Multiplying over all `m` counts every unordered pair `{i,j}`, `i<j`,
twice: once from `m=i, j>i` and once from `m=j, i<j` (using `|a−b| = |b−a|`),
giving `Vprod d²`.

## Available lemmas (from NormfInterp, degree `n+1` ↔ degree `d`)

* `NormfInterp.Pk (n k) : Polynomial ℝ := approxPoly (n+1) / (X − C(alpha (n+1) k))`
* `NormfInterp.PkProd (n k) := ∏ j ∈ (Finset.Icc 1 (n+1)).erase k, (X − C(alpha (n+1) j))`
* `NormfInterp.Pk_eq_PkProd {n k} (hk : k ∈ Finset.Icc 1 (n+1)) : Pk n k = PkProd n k`
* `NormfInterp.Pk_eval_self {n k} (hk : k ∈ Finset.Icc 1 (n+1)) :
     (Pk n k).eval (alpha (n+1) k) = (approxPoly (n+1)).derivative.eval (alpha (n+1) k)`
  (Pk_eval_self is stated with derivative on the right: evaluate Pk at the node.)
* `NormfInterp.derivative_eval_ne_zero {n k} (hk : k ∈ Finset.Icc 1 (n+1)) : ≠ 0`
* `ThreePages.approxPoly_eval`, `approxPoly_monic`, `approxPoly_natDegree`.

To use these at degree `d` with nodes `m ∈ Finset.Icc 1 d`, instantiate
`n := d - 1` and rewrite `(d - 1) + 1 = d` (have `h : d - 1 + 1 = d := by omega`
and `simpa [h] using ...`).

`Pk_eval_self` gives `|(Pk (d-1) m).eval (alpha d m)| = |(approxPoly d).derivative.eval (alpha d m)|`,
and `Pk_eq_PkProd` + `Polynomial.eval_prod` + `|∏| = ∏|·|` (`abs_prod` /
`Finset.abs_prod`) turn the left side into
`∏ j ∈ (Icc 1 d).erase m, |alpha d m − alpha d j|`.

Then relate the `Fin d`-product on the left to the natural product over
`m ∈ Finset.Icc 1 d` by the relabelling `k ↦ k.val + 1`
(`Fintype.prod_equiv` with `Fin d ≃ {x // x ∈ Finset.Icc 1 d}`, or
`Finset.prod_bij`), and handle the double-counting with Finset partition
lemmas (`Finset.prod_erase_mul`, `Finset.prod_union`, `Finset.filter_union`,
`Finset.mem_erase`, `abs_sub_comm`, `EnergyHalf.Vprod`).

Allowed axioms: propext/Quot.sound/Classical.choice.
-/

noncomputable section
open Polynomial
open scoped Real BigOperators

namespace Submission.HilbertDeriv

open Submission.MinkBox
open Submission.Quantile
open Submission.ThreePages
open Submission.EnergyHalf
open Submission.NormfInterp
open Submission.EnergyPairs


/-- `k ↦ k.val + 1` bijects `Fin d` with `Icc 1 d`, so the two products agree. -/
private lemma prod_fin_node (d : ℕ) :
    (∏ k : Fin d, |(approxPoly d).derivative.eval (alpha d (k.val + 1))|)
      = ∏ m ∈ Finset.Icc 1 d, |(approxPoly d).derivative.eval (alpha d m)| := by
  classical
  refine Finset.prod_bij (s := (Finset.univ : Finset (Fin d))) (t := Finset.Icc 1 d)
    (f := fun k : Fin d => |(approxPoly d).derivative.eval (alpha d (k.val + 1))|)
    (g := fun m : ℕ => |(approxPoly d).derivative.eval (alpha d m)|)
    (i := fun k _ => (k.val + 1 : ℕ)) ?hi ?i_inj ?i_surj ?h
  · intro k hk
    rw [Finset.mem_Icc]
    exact ⟨by omega, Nat.succ_le_of_lt k.isLt⟩
  · intro a₁ ha₁ a₂ ha₂ h
    apply Fin.ext
    omega
  · intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hbd : b ≤ d := (Finset.mem_Icc.mp hb).2
    refine ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    change (b - 1) + 1 = b
    omega
  · intro k hk
    rfl

/-- The derivative of `approxPoly d` does not vanish at a node, so its absolute
value there is positive. -/
private lemma deriv_abs_pos (d : ℕ) (hd : 2 ≤ d) {m : ℕ} (hm : m ∈ Finset.Icc 1 d) :
    0 < |(approxPoly d).derivative.eval (alpha d m)| := by
  have hdm : d - 1 + 1 = d := by omega
  have hm' : m ∈ Finset.Icc 1 (d - 1 + 1) := by
    simpa [hdm] using hm
  have hne : (approxPoly d).derivative.eval (alpha d m) ≠ 0 := by
    simpa [hdm] using derivative_eval_ne_zero (n := d - 1) (k := m) hm'
  exact abs_pos.mpr hne

/-- `log |P_{d,μ}'(α_m)|` is the sum of `log |α_m − α_j|` over the other nodes
(derivative of the product of linear factors, logs of a product). -/
private lemma log_abs_deriv_eq (d : ℕ) (hd : 2 ≤ d) {m : ℕ} (hm : m ∈ Finset.Icc 1 d) :
    Real.log |(approxPoly d).derivative.eval (alpha d m)| =
      ∑ j ∈ (Finset.Icc 1 d).erase m, Real.log |alpha d m - alpha d j| := by
  have hdm : d - 1 + 1 = d := by omega
  have hm' : m ∈ Finset.Icc 1 (d - 1 + 1) := by
    simpa [hdm] using hm
  have hself : (Pk (d - 1) m).eval (alpha d m) =
      (approxPoly d).derivative.eval (alpha d m) := by
    simpa [hdm] using (Pk_eval_self (n := d - 1) (k := m) hm')
  have hpk : Pk (d - 1) m = PkProd (d - 1) m := Pk_eq_PkProd (n := d - 1) (k := m) hm'
  have hprod : (PkProd (d - 1) m).eval (alpha d m) =
      ∏ j ∈ (Finset.Icc 1 d).erase m, (alpha d m - alpha d j) := by
    simp [PkProd, hdm, Polynomial.eval_prod]
  have hfac : ∀ j ∈ (Finset.Icc 1 d).erase m, |alpha d m - alpha d j| ≠ 0 := by
    intro j hj
    have hj' : j ∈ Finset.Icc 1 d := (Finset.mem_erase.mp hj).2
    have hjm : j ≠ m := (Finset.mem_erase.mp hj).1
    have hd1 : 1 ≤ d := by omega
    have hne : alpha d m ≠ alpha d j :=
      alpha_ne_alpha (n := d) hd1 hm hj' hjm.symm
    exact abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  calc
    Real.log |(approxPoly d).derivative.eval (alpha d m)|
        = Real.log |(Pk (d - 1) m).eval (alpha d m)| := by rw [hself]
    _ = Real.log |(PkProd (d - 1) m).eval (alpha d m)| := by rw [hpk]
    _ = Real.log (∏ j ∈ (Finset.Icc 1 d).erase m, |alpha d m - alpha d j|) := by
          rw [hprod]
          rw [Finset.abs_prod]
    _ = ∑ j ∈ (Finset.Icc 1 d).erase m, Real.log |alpha d m - alpha d j| := by
          exact Real.log_prod hfac

/-- `log ∏_{m∈Icc 1 d} |P_{d,μ}'(α_m)| = log (Vprod d)²` (double counting of
ordered pairs via `EnergyPairs.erase_sum_eq_two_lt_sum`). -/
private lemma log_prod_Icc_eq (d : ℕ) (hd : 2 ≤ d) :
    Real.log (∏ m ∈ Finset.Icc 1 d, |(approxPoly d).derivative.eval (alpha d m)|)
      = Real.log ((Vprod d) ^ 2) := by
  calc
    Real.log (∏ m ∈ Finset.Icc 1 d, |(approxPoly d).derivative.eval (alpha d m)|)
        = ∑ m ∈ Finset.Icc 1 d, ∑ j ∈ (Finset.Icc 1 d).erase m,
            Real.log |alpha d m - alpha d j| := by
          calc
            Real.log (∏ m ∈ Finset.Icc 1 d, |(approxPoly d).derivative.eval (alpha d m)|)
                = ∑ m ∈ Finset.Icc 1 d,
                    Real.log |(approxPoly d).derivative.eval (alpha d m)| := by
                    apply Real.log_prod
                    intro m hm
                    exact ne_of_gt (deriv_abs_pos d hd hm)
            _ = ∑ m ∈ Finset.Icc 1 d, ∑ j ∈ (Finset.Icc 1 d).erase m,
                    Real.log |alpha d m - alpha d j| := by
                    apply Finset.sum_congr rfl
                    intro m hm
                    exact log_abs_deriv_eq d hd hm
    _ = 2 * logV d := by
          rw [erase_sum_eq_two_lt_sum d]
          simp [logV]
    _ = 2 * Real.log (Vprod d) := by
          rw [← log_Vprod d (by omega : 1 ≤ d)]
    _ = Real.log ((Vprod d) ^ 2) := by
          rw [Real.log_pow]
          norm_num

/-- Product of |derivative| at all relabelled Fin nodes equals `(Vprod d)^2`. -/
lemma deriv_prod_sq (d : ℕ) (hd : 2 ≤ d) :
    (∏ k : Fin d, |(approxPoly d).derivative.eval (alpha d (k.val + 1))|) =
      (Vprod d) ^ 2 := by
  let L : ℝ := ∏ k : Fin d, |(approxPoly d).derivative.eval (alpha d (k.val + 1))|
  have hposL : 0 < L := by
    dsimp [L]
    rw [prod_fin_node]
    exact Finset.prod_pos (s := Finset.Icc 1 d)
      (f := fun m : ℕ => |(approxPoly d).derivative.eval (alpha d m)|) (by
        intro m hm
        exact deriv_abs_pos d hd hm)
  have hlog : Real.log L = Real.log ((Vprod d) ^ 2) := by
    dsimp [L]
    rw [prod_fin_node]
    exact log_prod_Icc_eq d hd
  have hVpos : 0 < (Vprod d) ^ 2 := by
    exact pow_pos (Vprod_pos d (by omega : 1 ≤ d)) 2
  have hmain : L = (Vprod d) ^ 2 := by
    rw [← Real.exp_log hposL]
    rw [hlog]
    exact Real.exp_log hVpos
  simpa [L] using hmain

end Submission.HilbertDeriv
