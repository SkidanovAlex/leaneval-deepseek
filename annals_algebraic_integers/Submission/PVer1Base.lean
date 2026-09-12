import Submission.ThreePages
import Submission.QuantileExt
import Submission.WnormShift
import Submission.Bclps
import Submission.ScaleBoundLower
import Submission.ScaleBoundUpper

/-!
# `lem:P_ver1` for the Serre interval (pruned approximating polynomials)

For the single interval Σ = [aSerre,bSerre], take the degree-`(N+2)`
approximating polynomial `P_{N+2,μ} = approxPoly (N+2)` (roots
`α_{N+2,i}`, i = 1..N+2, with `cdf α = i/(N+2)`) and PRUNE the two extreme
roots `i = 1` and `i = N+2`:

    P̃_N := ∏_{i=2}^{N+1} (X − C(α_{N+2,i}))

a monic real polynomial of degree N whose roots all lie strictly inside
`(aSerre,bSerre)` at polynomial distance from the boundary and from each
other.  This module proves Smith's `lem:P_ver1` (adjust.tex) specialised to
our data, in the form needed by the proof of `prop:early_ints_better`:

* (a) every kept root is `≥ (C·N)^{-2}` from `aSerre`, from `bSerre`, and
  from every other kept root (spacing + boundary margin);
* (b) for `0 ≤ s` with `s ≤ Bclps.Dconst`: for all `x ∈ [aSerre,bSerre]`,
  `w_μ(x)^{N+s}·|P̃_N(x)| ≥ N^{-C}·ρ_{P̃}(x)`, where
  `ρ_{P̃}(x) := min_{i=2}^{N+1} |x − α_{N+2,i}|`;
* (c) for such `s`: `‖P̃_N‖_{N+s} ≤ N^C` (weighted norm).

## Proof route (given the machine-verified ThreePages / QuantileExt)

Let `P = approxPoly (N+2)`, `a1 = alpha (N+2) 1`, `aT = alpha (N+2) (N+2)`;
then pointwise `|P(x)| = |x−a1|·|x−aT|·|P̃_N(x)|` (factor the product).

* Root facts: kept roots are increasing (`Quantile.alpha_strict_mono`), and
  consecutive kept roots are spaced by `≥ (C(N+2))^{-2}`
  (`Quantile.exists_spacing` at degree N+2); the first/last ROOT of P
  themselves have boundary margins via `QuantileExt.exists_left_margin_all`
  (i=1) / `exists_right_margin_all` at degree N+2.  The distance
  `gap := aT − a1` is bounded BELOW by a positive constant: from
  `cdf aT − cdf a1 = (N+1)/(N+2) ≥ 1/2` and the Hölder interval bound
  `μ(Icc a1 aT) ≤ C·√(aT − a1)` (`Quantile.exists_interval_holder`).

* (b) lower bound: `w^{N+2}|P| ≥ (N+2)^{-C}·ρ_full(x)`
  (`ThreePages.potential_approx_lower` at degree N+2).  Divide by
  `|x−a1||x−aT|`: with `ρKept := rhoKept N x` and `ρfull :=
  ThreePages.rho (N+2) x` one checks `ρfull/(|x−a1|·|x−aT|) ≥ ρKept/diam²`
  (three cases: the min for ρfull is attained at a kept root, at a1, or at
  aT — use `ThreePages.exists_index_eq_rho`; diam = bSerre−aSerre bounds
  every |·| factor and also ρKept).  Then shift the exponent from N+2 to
  N+s: since `s ≤ Dconst` and `|log w| ≤ K` on the interval
  (`SerrePotentialIcc`), `w^{s−2} ≥ e^{−K·(s−2)} ≥ e^{−K·Dconst}` pointwise,
  a constant absorbed by C.

* (c) upper bound: `w^{N+2}|P| ≤ (N+2)^C·ρfull`
  (`ThreePages.potential_approx_upper`); so
  `w^{N+s}|P̃| ≤ e^{K·Dconst}·(N+2)^C·ρfull/(|x−a1||x−aT|)` and
  `ρfull/(|x−a1||x−aT|) ≤ 1/max(|x−a1|,|x−aT|) ≤ 2/gap` (constant, since
  ρfull ≤ min(|x−a1|,|x−aT|)), giving a pointwise bound → `wnorm (N+s)
  (prunePoly N) ≤ N^C` via `WnormToolkit.wnorm_sSup_le`.

Prove ALL declarations below (replace `sorry`s); add helpers as needed.
Do NOT change the defs or the main theorem statements.
-/

noncomputable section

open MeasureTheory
open Filter
open scoped Real BigOperators Topology
open Polynomial

namespace Submission.PVer1

open Submission.PotentialDefs
open Submission.SerreExample
open Submission.PotentialContinuity
open Submission.Quantile
open Submission.QuantileExt
open Submission.ThreePages
open Submission.Bclps
open Submission.Contracts
open Submission.WeightedNorm
open Submission.WnormShift
open Submission.WnormToolkit

/-- Exponent-shift constant `K·(Dconst+1)` (from `|log w| ≤ Kbound` on Σ). -/
noncomputable def Kshift : ℝ := ((Bclps.Dconst : ℝ) + 1) * Kbound

/-- Diameter of the Serre interval. -/
noncomputable def Dserre : ℝ := bSerre - aSerre

lemma Dserre_pos : 0 < Dserre := by
  unfold Dserre
  exact sub_pos.mpr a_lt_b

lemma Dserre_ge_one : 1 ≤ Dserre := by
  unfold Dserre
  norm_num [aSerre, bSerre]

lemma Kshift_nonneg : 0 ≤ Kshift := by
  unfold Kshift
  have h1 : 0 ≤ (Bclps.Dconst : ℝ) + 1 := by positivity
  exact mul_nonneg h1 Kbound_nonneg

/-- A large enough exponent for any base `≥ 2` to dominate a fixed constant:
`∃ A ≥ 0, ∀ n ≥ 2, M ≤ n^A`. -/
lemma exists_large_rpow {M : ℝ} (hM1 : 1 ≤ M) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 2 ≤ n → M ≤ (n : ℝ) ^ A := by
  let A : ℝ := Real.log M / Real.log 2
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    exact div_nonneg (Real.log_nonneg hM1) (le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 2)))
  · intro n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlnM : 0 ≤ Real.log M := Real.log_nonneg hM1
    have hln2n : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2
    have h1 : Real.log M ≤ A * Real.log (n : ℝ) := by
      dsimp [A]
      have hdiv : 1 ≤ Real.log (n : ℝ) / Real.log (2 : ℝ) := by
        exact (le_div_iff₀ hlog2).mpr (by simpa using hln2n)
      have hmul : Real.log M * 1 ≤ Real.log M * (Real.log (n : ℝ) / Real.log (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv hlnM
      calc
        Real.log M ≤ Real.log M * (Real.log (n : ℝ) / Real.log (2 : ℝ)) := by
          simpa using hmul
        _ = (Real.log M / Real.log 2) * Real.log (n : ℝ) := by
          field_simp [ne_of_gt hlog2]
    have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hM1
    calc
      M = Real.exp (Real.log M) := (Real.exp_log hMpos).symm
      _ ≤ Real.exp (A * Real.log (n : ℝ)) := Real.exp_le_exp.mpr h1
      _ = (n : ℝ) ^ A := by
        rw [Real.rpow_def_of_pos hn0]
        congr 1
        ring

lemma weight_shift_lower {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) (N : ℕ) {s : ℕ}
    (hs : s ≤ Bclps.Dconst) :
    Real.exp (-Kshift) * (weight muSerre x) ^ (N + 2) ≤
      (weight muSerre x) ^ (N + s) := by
  have hK : 0 ≤ Kbound := Kbound_nonneg
  have hwpos : 0 < weight muSerre x := weight_pos muSerre x
  have hwlow : Real.exp (-Kbound) ≤ weight muSerre x := exp_negK_le_weight hx
  have hwup : weight muSerre x ≤ Real.exp Kbound := weight_le_expK hx
  have hD1 : 1 ≤ Bclps.Dconst := Bclps.Dconst_pos
  by_cases h2 : 2 ≤ s
  · have hs2le : (s - 2 : ℕ) ≤ Bclps.Dconst + 1 := by omega
    have hs2r : ((s - 2 : ℕ) : ℝ) ≤ ((Bclps.Dconst : ℕ) + 1 : ℝ) := by exact_mod_cast hs2le
    have hfac : Real.exp (-Kshift) ≤ (weight muSerre x) ^ (s - 2) := by
      unfold Kshift
      have h1 : (Real.exp (-Kbound)) ^ (s - 2) ≤ (weight muSerre x) ^ (s - 2) :=
        pow_le_pow_left₀ (Real.exp_pos (-Kbound)).le hwlow (s - 2)
      calc
        Real.exp (-(((Bclps.Dconst : ℝ) + 1) * Kbound)) ≤
            Real.exp (-(((s - 2 : ℕ) : ℝ) * Kbound)) := by
              apply Real.exp_le_exp.mpr
              have harg : ((s - 2 : ℕ) : ℝ) * Kbound ≤ ((Bclps.Dconst : ℝ) + 1) * Kbound :=
                mul_le_mul_of_nonneg_right hs2r hK
              linarith
        _ = (Real.exp (-Kbound)) ^ (s - 2) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        _ ≤ (weight muSerre x) ^ (s - 2) := h1
    calc
      Real.exp (-Kshift) * (weight muSerre x) ^ (N + 2)
          ≤ (weight muSerre x) ^ (s - 2) * (weight muSerre x) ^ (N + 2) := by
              exact mul_le_mul_of_nonneg_right hfac (pow_nonneg hwpos.le (N + 2))
      _ = (weight muSerre x) ^ (N + 2) * (weight muSerre x) ^ (s - 2) := by ring
      _ = (weight muSerre x) ^ (N + s) := by
          rw [← pow_add]
          congr 1
          omega
  · have hle2s : (2 - s : ℕ) ≤ Bclps.Dconst + 1 := by omega
    have hw2s : (weight muSerre x) ^ (2 - s) ≤ Real.exp ((((2 - s : ℕ) : ℝ)) * Kbound) := by
      have h1 : (weight muSerre x) ^ (2 - s) ≤ (Real.exp Kbound) ^ (2 - s) :=
        pow_le_pow_left₀ hwpos.le hwup (2 - s)
      have hid : (Real.exp Kbound) ^ (2 - s) = Real.exp ((((2 - s : ℕ) : ℝ)) * Kbound) := by
        rw [← Real.exp_nat_mul]
      rw [← hid]
      exact h1
    have hw2s' : (weight muSerre x) ^ (2 - s) ≤ Real.exp Kshift := by
      unfold Kshift
      calc
        (weight muSerre x) ^ (2 - s) ≤ Real.exp ((((2 - s : ℕ) : ℝ)) * Kbound) := hw2s
        _ ≤ Real.exp (((Bclps.Dconst : ℝ) + 1) * Kbound) := by
          apply Real.exp_le_exp.mpr
          have h2sr : ((2 - s : ℕ) : ℝ) ≤ ((Bclps.Dconst : ℕ) + 1 : ℝ) := by exact_mod_cast hle2s
          exact mul_le_mul_of_nonneg_right h2sr hK
    have hwNs : 0 ≤ (weight muSerre x) ^ (N + s) := pow_nonneg hwpos.le (N + s)
    have hprod : Real.exp (-Kshift) * (weight muSerre x) ^ (2 - s) ≤ 1 := by
      calc
        Real.exp (-Kshift) * (weight muSerre x) ^ (2 - s)
            ≤ Real.exp (-Kshift) * Real.exp Kshift := by
                exact mul_le_mul_of_nonneg_left hw2s' (Real.exp_pos (-Kshift)).le
        _ = 1 := by
          rw [← Real.exp_add]
          have : -Kshift + Kshift = 0 := by ring
          rw [this]
          exact Real.exp_zero
    calc
      Real.exp (-Kshift) * (weight muSerre x) ^ (N + 2)
          = Real.exp (-Kshift) * ((weight muSerre x) ^ (N + s) * (weight muSerre x) ^ (2 - s)) := by
              have hN2 : N + 2 = (N + s) + (2 - s) := by omega
              rw [hN2]
              rw [← pow_add]
      _ = (Real.exp (-Kshift) * (weight muSerre x) ^ (2 - s)) * (weight muSerre x) ^ (N + s) := by ring
      _ ≤ 1 * (weight muSerre x) ^ (N + s) := by
              exact mul_le_mul_of_nonneg_right hprod hwNs
      _ = (weight muSerre x) ^ (N + s) := by ring

lemma weight_shift_upper {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) (N : ℕ) {s : ℕ}
    (hs : s ≤ Bclps.Dconst) :
    (weight muSerre x) ^ (N + s) ≤ Real.exp Kshift * (weight muSerre x) ^ (N + 2) := by
  have hK : 0 ≤ Kbound := Kbound_nonneg
  have hwpos : 0 < weight muSerre x := weight_pos muSerre x
  have hwup : weight muSerre x ≤ Real.exp Kbound := weight_le_expK hx
  have hD1 : 1 ≤ Bclps.Dconst := Bclps.Dconst_pos
  by_cases h2 : 2 ≤ s
  · have hs2le : (s - 2 : ℕ) ≤ Bclps.Dconst + 1 := by omega
    have hs2r : ((s - 2 : ℕ) : ℝ) ≤ ((Bclps.Dconst : ℕ) + 1 : ℝ) := by exact_mod_cast hs2le
    have hw2s : (weight muSerre x) ^ (s - 2) ≤ Real.exp ((((s - 2 : ℕ) : ℝ)) * Kbound) := by
      have h1 : (weight muSerre x) ^ (s - 2) ≤ (Real.exp Kbound) ^ (s - 2) :=
        pow_le_pow_left₀ hwpos.le hwup (s - 2)
      have hid : (Real.exp Kbound) ^ (s - 2) = Real.exp ((((s - 2 : ℕ) : ℝ)) * Kbound) := by
        rw [← Real.exp_nat_mul]
      rw [← hid]
      exact h1
    have hw2s' : (weight muSerre x) ^ (s - 2) ≤ Real.exp Kshift := by
      unfold Kshift
      calc
        (weight muSerre x) ^ (s - 2) ≤ Real.exp ((((s - 2 : ℕ) : ℝ)) * Kbound) := hw2s
        _ ≤ Real.exp (((Bclps.Dconst : ℝ) + 1) * Kbound) := by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_right hs2r hK
    calc
      (weight muSerre x) ^ (N + s)
          = (weight muSerre x) ^ (N + 2) * (weight muSerre x) ^ (s - 2) := by
              have hNs : N + s = (N + 2) + (s - 2) := by omega
              rw [hNs, pow_add]
      _ ≤ (weight muSerre x) ^ (N + 2) * Real.exp Kshift := by
              exact mul_le_mul_of_nonneg_left hw2s' (pow_nonneg hwpos.le (N + 2))
      _ = Real.exp Kshift * (weight muSerre x) ^ (N + 2) := by ring
  · have hle2s : (2 - s : ℕ) ≤ Bclps.Dconst + 1 := by omega
    have hw2s : Real.exp (-(((2 - s : ℕ) : ℝ) * Kbound)) ≤ (weight muSerre x) ^ (2 - s) := by
      have h1 : (Real.exp (-Kbound)) ^ (2 - s) ≤ (weight muSerre x) ^ (2 - s) :=
        pow_le_pow_left₀ (Real.exp_pos (-Kbound)).le (by
          have hwlow : Real.exp (-Kbound) ≤ weight muSerre x := exp_negK_le_weight hx
          exact hwlow) (2 - s)
      have hid : (Real.exp (-Kbound)) ^ (2 - s) = Real.exp (-(((2 - s : ℕ) : ℝ) * Kbound)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [← hid]
      exact h1
    have hwlow2 : Real.exp (-Kshift) ≤ (weight muSerre x) ^ (2 - s) := by
      unfold Kshift
      calc
        Real.exp (-(((Bclps.Dconst : ℝ) + 1) * Kbound)) ≤ Real.exp (-(((2 - s : ℕ) : ℝ) * Kbound)) := by
          apply Real.exp_le_exp.mpr
          have h2sr : ((2 - s : ℕ) : ℝ) ≤ ((Bclps.Dconst : ℕ) + 1 : ℝ) := by exact_mod_cast hle2s
          have harg : ((2 - s : ℕ) : ℝ) * Kbound ≤ ((Bclps.Dconst : ℝ) + 1) * Kbound :=
            mul_le_mul_of_nonneg_right h2sr hK
          linarith
        _ ≤ (weight muSerre x) ^ (2 - s) := hw2s
    calc
      (weight muSerre x) ^ (N + s)
          = (weight muSerre x) ^ (N + 2) * ((weight muSerre x) ^ (2 - s))⁻¹ := by
              have hN2 : N + 2 = (N + s) + (2 - s) := by omega
              rw [hN2]
              conv_rhs => rw [pow_add]
              field_simp [ne_of_gt (pow_pos hwpos (2 - s))]
      _ ≤ (weight muSerre x) ^ (N + 2) * Real.exp Kshift := by
              have hposw2 : 0 < (weight muSerre x) ^ (2 - s) := pow_pos hwpos (2 - s)
              have hposE : 0 < Real.exp (-Kshift) := Real.exp_pos (-Kshift)
              have hinv : ((weight muSerre x) ^ (2 - s))⁻¹ ≤ Real.exp Kshift := by
                calc
                  ((weight muSerre x) ^ (2 - s))⁻¹ ≤ (Real.exp (-Kshift))⁻¹ := by
                      exact (inv_le_inv₀ hposw2 hposE).mpr hwlow2
                  _ = Real.exp Kshift := by
                      rw [Real.exp_neg]
                      field_simp
              exact mul_le_mul_of_nonneg_left hinv (pow_nonneg hwpos.le (N + 2))
      _ = Real.exp Kshift * (weight muSerre x) ^ (N + 2) := by ring

/-- The weight `x ↦ w_μ(x)` (for `μ = muS`) is continuous on `ℝ`. -/
lemma continuous_weight_muS : Continuous (fun x : ℝ => weight muS x) := by
  have hfun : (fun x : ℝ => weight muS x) = fun x : ℝ =>
      Real.exp (logPotential muS (x : ℂ)) := by
    funext x
    rfl
  rw [hfun]
  exact Real.continuous_exp.comp logPotential_continuous_real

/-- `x ↦ w(x)^k·|P(x)|` is continuous on `ℝ` (weight `muS`). -/
lemma continuous_weight_pow_eval (k : ℕ) (P : Polynomial ℝ) :
    Continuous (fun x : ℝ => (weight muS x) ^ k * |P.eval x|) := by
  have h1 : Continuous (fun x : ℝ => (weight muS x) ^ k) :=
    continuous_weight_muS.pow k
  have h2 : Continuous (fun x : ℝ => |P.eval x|) := by
    have hc : Continuous (fun x : ℝ => P.eval x) := by
      have hc0 : Continuous (fun x : ℝ => Polynomial.aeval x P) := Polynomial.continuous_aeval P
      have hfun : (fun x : ℝ => P.eval x) = fun x : ℝ => Polynomial.aeval x P := by
        funext x
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
        congr 1
        ext i
        simp
      rwa [hfun]
    exact hc.abs
  exact h1.mul h2

/-- If a continuous function is `≤ c` for all points near `x` (except possibly
`x` itself), then `f x ≤ c`. -/
lemma le_const_of_forall_near {f : ℝ → ℝ} {x c : ℝ} (hf : ContinuousAt f x)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y ≠ x → |y - x| < δ → f y ≤ c) : f x ≤ c := by
  by_contra hnot
  have hgt : c < f x := lt_of_not_ge hnot
  let ε : ℝ := (f x - c) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  rcases hδ with ⟨δ0, hδ0pos, hδ0⟩
  have hmet := Metric.continuousAt_iff.mp hf ε hε
  rcases hmet with ⟨δ1, hδ1pos, hδ1⟩
  let δ : ℝ := min δ0 δ1
  have hδpos : 0 < δ := lt_min hδ0pos hδ1pos
  let y : ℝ := x + δ / 2
  have hyne : y ≠ x := by
    dsimp [y]
    linarith
  have h4 : |y - x| = δ / 2 := by
    dsimp [y]
    have hsimp : x + δ / 2 - x = δ / 2 := by ring
    rw [hsimp]
    exact abs_of_pos (by linarith : (0:ℝ) < δ / 2)
  have hdist0 : |y - x| < δ0 := by
    have h3 : δ / 2 < δ0 := lt_of_lt_of_le (by linarith) (min_le_left δ0 δ1)
    rwa [h4]
  have hyc : f y ≤ c := hδ0 y hyne hdist0
  have hdist1 : |y - x| < δ1 := by
    have h3 : δ / 2 < δ1 := lt_of_lt_of_le (by linarith) (min_le_right δ0 δ1)
    rwa [h4]
  have hdist1' : dist y x < δ1 := by
    simpa [Real.dist_eq] using hdist1
  have hclose : |f y - f x| < ε := hδ1 hdist1'
  have hfy : f y > c := by
    dsimp [ε] at hclose
    have h1 : -( (f x - c) / 2 ) < f y - f x := (abs_lt.mp hclose).1
    linarith
  exact (not_lt_of_ge hyc) hfy

/-- If a continuous function is `≥ c` for all points near `x` (except possibly
`x` itself), then `c ≤ f x`. -/
lemma const_le_of_forall_near {f : ℝ → ℝ} {x c : ℝ} (hf : ContinuousAt f x)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y ≠ x → |y - x| < δ → c ≤ f y) : c ≤ f x := by
  by_contra hnot
  have hlt : f x < c := lt_of_not_ge hnot
  let ε : ℝ := (c - f x) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  rcases hδ with ⟨δ0, hδ0pos, hδ0⟩
  have hmet := Metric.continuousAt_iff.mp hf ε hε
  rcases hmet with ⟨δ1, hδ1pos, hδ1⟩
  let δ : ℝ := min δ0 δ1
  have hδpos : 0 < δ := lt_min hδ0pos hδ1pos
  let y : ℝ := x + δ / 2
  have hyne : y ≠ x := by
    dsimp [y]
    linarith
  have h4 : |y - x| = δ / 2 := by
    dsimp [y]
    have hsimp : x + δ / 2 - x = δ / 2 := by ring
    rw [hsimp]
    exact abs_of_pos (by linarith : (0:ℝ) < δ / 2)
  have hdist0 : |y - x| < δ0 := by
    have h3 : δ / 2 < δ0 := lt_of_lt_of_le (by linarith) (min_le_left δ0 δ1)
    rwa [h4]
  have hyc : c ≤ f y := hδ0 y hyne hdist0
  have hdist1 : |y - x| < δ1 := by
    have h3 : δ / 2 < δ1 := lt_of_lt_of_le (by linarith) (min_le_right δ0 δ1)
    rwa [h4]
  have hdist1' : dist y x < δ1 := by
    simpa [Real.dist_eq] using hdist1
  have hclose : |f y - f x| < ε := hδ1 hdist1'
  have hfy : f y < c := by
    dsimp [ε] at hclose
    have h1 : f y - f x < (c - f x) / 2 := (abs_lt.mp hclose).2
    linarith
  exact (not_lt_of_ge hyc) hfy

lemma le_const_of_forall_gt_near {f : ℝ → ℝ} {x c : ℝ} (hf : ContinuousAt f x)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x < y → y - x < δ → f y ≤ c) : f x ≤ c := by
  by_contra hnot
  have hgt : c < f x := lt_of_not_ge hnot
  let ε : ℝ := (f x - c) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  rcases hδ with ⟨δ0, hδ0pos, hδ0⟩
  have hmet := Metric.continuousAt_iff.mp hf ε hε
  rcases hmet with ⟨δ1, hδ1pos, hδ1⟩
  let δ : ℝ := min δ0 δ1
  have hδpos : 0 < δ := lt_min hδ0pos hδ1pos
  let y : ℝ := x + δ / 2
  have hgtx : x < y := by
    dsimp [y]
    linarith
  have hdiff : y - x = δ / 2 := by
    dsimp [y]
    ring
  have hdy0 : y - x < δ0 := by
    rw [hdiff]
    exact lt_of_lt_of_le (by linarith : δ / 2 < δ) (min_le_left δ0 δ1)
  have hyc : f y ≤ c := hδ0 y hgtx hdy0
  have hdy1 : |y - x| < δ1 := by
    have hd : |y - x| = δ / 2 := by
      have hlt : 0 < y - x := by linarith
      rw [abs_of_pos hlt]
      exact hdiff
    rw [hd]
    exact lt_of_lt_of_le (by linarith : δ / 2 < δ) (min_le_right δ0 δ1)
  have hclose : |f y - f x| < ε := hδ1 hdy1
  have hfy : f y > c := by
    dsimp [ε] at hclose
    have h1 : -((f x - c) / 2) < f y - f x := (abs_lt.mp hclose).1
    linarith
  exact (not_lt_of_ge hyc) hfy

lemma const_le_of_forall_gt_near {f : ℝ → ℝ} {x c : ℝ} (hf : ContinuousAt f x)
    (hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x < y → y - x < δ → c ≤ f y) : c ≤ f x := by
  by_contra hnot
  have hlt : f x < c := lt_of_not_ge hnot
  let ε : ℝ := (c - f x) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  rcases hδ with ⟨δ0, hδ0pos, hδ0⟩
  have hmet := Metric.continuousAt_iff.mp hf ε hε
  rcases hmet with ⟨δ1, hδ1pos, hδ1⟩
  let δ : ℝ := min δ0 δ1
  have hδpos : 0 < δ := lt_min hδ0pos hδ1pos
  let y : ℝ := x + δ / 2
  have hgtx : x < y := by
    dsimp [y]
    linarith
  have hdiff : y - x = δ / 2 := by
    dsimp [y]
    ring
  have hdy0 : y - x < δ0 := by
    rw [hdiff]
    exact lt_of_lt_of_le (by linarith : δ / 2 < δ) (min_le_left δ0 δ1)
  have hyc : c ≤ f y := hδ0 y hgtx hdy0
  have hdy1 : |y - x| < δ1 := by
    have hd : |y - x| = δ / 2 := by
      have hlt : 0 < y - x := by linarith
      rw [abs_of_pos hlt]
      exact hdiff
    rw [hd]
    exact lt_of_lt_of_le (by linarith : δ / 2 < δ) (min_le_right δ0 δ1)
  have hclose : |f y - f x| < ε := hδ1 hdy1
  have hfy : f y < c := by
    dsimp [ε] at hclose
    have h1 : f y - f x < (c - f x) / 2 := (abs_lt.mp hclose).2
    linarith
  exact (not_lt_of_ge hyc) hfy

/-- Kept root indices after pruning: `2..N+1`. -/
noncomputable def kept (N : ℕ) : Finset ℕ := Finset.Icc 2 (N + 1)

/-- The pruned polynomial `P̃_N = ∏_{i=2}^{N+1}(X − α_{N+2,i})`. -/
noncomputable def prunePoly (N : ℕ) : Polynomial ℝ :=
  ∏ i ∈ kept N, (Polynomial.X - Polynomial.C (alpha (N + 2) i))

/-- `ρ_{P̃}(x) = min_{i ∈ kept N} |x − α_{N+2,i}|`. -/
noncomputable def rhoKept (N : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if h : (kept N).Nonempty then
    (kept N).inf' h (fun i : ℕ => |x - alpha (N + 2) i|) else 0

/-- The full (unpruned) rho at degree `N+2`. -/
noncomputable def rhoFull (N : ℕ) (x : ℝ) : ℝ := ThreePages.rho (N + 2) x

/-- The root set of `P_{N+2,μ}` (levels `1..N+2`). -/
noncomputable def allIdx (N : ℕ) : Finset ℕ := Finset.Icc 1 (N + 2)

/-- `kept N ⊆ allIdx N` for `1 ≤ N`. -/
lemma kept_subset_allIdx {N : ℕ} (hN : 1 ≤ N) : kept N ⊆ allIdx N := by
  intro i hi
  unfold kept at hi
  unfold allIdx
  rw [Finset.mem_Icc] at hi ⊢
  omega


/-- `(kept N).Nonempty` for `1 ≤ N`. -/
lemma kept_nonempty {N : ℕ} (hN : 1 ≤ N) : (kept N).Nonempty := by
  refine ⟨2, ?_⟩
  unfold kept
  rw [Finset.mem_Icc]
  omega


/-- Pointwise evaluation of the pruned polynomial. -/
lemma prunePoly_eval (N : ℕ) (x : ℝ) :
    (prunePoly N).eval x = ∏ i ∈ kept N, (x - alpha (N + 2) i) := by
  unfold prunePoly
  rw [Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]


/-- `P̃_N` is monic of degree `N` (for `1 ≤ N`). -/
lemma prunePoly_monic {N : ℕ} (hN : 1 ≤ N) : (prunePoly N).Monic := by
  unfold prunePoly
  exact Polynomial.monic_prod_of_monic (kept N)
    (fun i => Polynomial.X - Polynomial.C (alpha (N + 2) i))
    (by intro i hi; exact Polynomial.monic_X_sub_C (alpha (N + 2) i))


lemma prunePoly_natDegree {N : ℕ} (hN : 1 ≤ N) : (prunePoly N).natDegree = N := by
  unfold prunePoly
  rw [Polynomial.natDegree_prod_of_monic (kept N)
    (fun i => Polynomial.X - Polynomial.C (alpha (N + 2) i))
    (by intro i hi; exact Polynomial.monic_X_sub_C (alpha (N + 2) i))]
  have hsum : (∑ i ∈ kept N, ((Polynomial.X - Polynomial.C (alpha (N + 2) i)).natDegree : ℕ)) = N := by
    calc
      (∑ i ∈ kept N, ((Polynomial.X - Polynomial.C (alpha (N + 2) i)).natDegree : ℕ))
          = ∑ i ∈ kept N, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Polynomial.natDegree_X_sub_C (alpha (N + 2) i)
      _ = (kept N).card := by simp
      _ = N := by
        unfold kept
        rw [Nat.card_Icc]
        omega
  exact hsum

/-- Factorization of the product over all roots into extreme roots and kept roots. -/
lemma prod_allIdx_split (N : ℕ) (f : ℕ → ℝ) :
    (∏ i ∈ allIdx N, f i) = f 1 * f (N + 2) * (∏ i ∈ kept N, f i) := by
  unfold allIdx
  rw [Finset.prod_Icc_succ_top (a := 1) (b := N + 1) (by omega) f]
  have hset : Finset.Icc 1 (N + 1) = insert 1 (Finset.Icc 2 (N + 1)) := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      rw [Finset.mem_Icc] at hi
      by_cases hi1 : i = 1
      · simp [hi1]
      · have : 2 ≤ i := by omega
        simp [Finset.mem_Icc, this, hi.2]
    · intro hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · rw [Finset.mem_Icc]; omega
      · rw [Finset.mem_Icc] at hi
        rw [Finset.mem_Icc]
        omega
  rw [hset]
  rw [Finset.prod_insert (s := Finset.Icc 2 (N + 1)) (a := 1) (f := f)]
  · have hnn : N + 1 + 1 = N + 2 := by omega
    rw [hnn]
    simp [kept, mul_assoc, mul_comm, mul_left_comm]
  · simp [Finset.mem_Icc]


/-- Factorization of the full approximating polynomial (pointwise absolute
value): `|P_{N+2}(x)| = |x−α_1|·|x−α_{N+2}|·|P̃_N(x)|`. -/
lemma abs_factor_full_pruned (N : ℕ) (x : ℝ) :
    |(approxPoly (N + 2)).eval x| =
      |x - alpha (N + 2) 1| * |x - alpha (N + 2) (N + 2)| * |(prunePoly N).eval x| := by
  calc
    |(approxPoly (N + 2)).eval x|
        = |∏ i ∈ allIdx N, (x - alpha (N + 2) i)| := by
            rw [approxPoly_eval (N + 2) x]
            simp [allIdx]
    _ = ∏ i ∈ allIdx N, |x - alpha (N + 2) i| := by
            rw [Finset.abs_prod]
    _ = |x - alpha (N + 2) 1| * |x - alpha (N + 2) (N + 2)| *
          (∏ i ∈ kept N, |x - alpha (N + 2) i|) := by
            rw [prod_allIdx_split N (fun i => |x - alpha (N + 2) i|)]
    _ = |x - alpha (N + 2) 1| * |x - alpha (N + 2) (N + 2)| * |(prunePoly N).eval x| := by
            rw [prunePoly_eval N x]
            rw [Finset.abs_prod]


/-- The `ρKept` vs `ρfull` relationship (case lemma A): if the full minimum
is attained at a kept index then `rhoFull N x = rhoKept N x`. -/
lemma rhoFull_eq_rhoKept_of_kept {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : 0 < rhoFull N x)
    {i : ℕ} (hi : i ∈ kept N) (hatt : rhoFull N x = |x - alpha (N + 2) i|) :
    rhoFull N x = rhoKept N x := by
  apply le_antisymm
  · -- ρFull ≤ ρKept
    unfold rhoKept
    rw [dif_pos (kept_nonempty hN)]
    apply Finset.le_inf' (kept_nonempty hN) (fun i : ℕ => |x - alpha (N + 2) i|)
    intro j hj
    unfold rhoFull
    exact rho_le_root (n := N + 2) (by omega : 1 ≤ N + 2) x (kept_subset_allIdx hN hj)
  · -- ρKept ≤ ρFull
    rw [hatt]
    unfold rhoKept
    rw [dif_pos (kept_nonempty hN)]
    exact Finset.inf'_le (fun i : ℕ => |x - alpha (N + 2) i|) hi

/-- `rhoKept ≤ diam` on the interval. -/
lemma rhoKept_le_diam {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    rhoKept N x ≤ bSerre - aSerre := by
  unfold rhoKept
  rw [dif_pos (kept_nonempty hN)]
  have h2 : 2 ∈ kept N := by
    unfold kept
    rw [Finset.mem_Icc]
    omega
  calc
    (kept N).inf' (kept_nonempty hN) (fun i : ℕ => |x - alpha (N + 2) i|)
        ≤ |x - alpha (N + 2) 2| := Finset.inf'_le (fun i : ℕ => |x - alpha (N + 2) i|) h2
    _ ≤ bSerre - aSerre := by
      have halpha : alpha (N + 2) 2 ∈ Set.Icc aSerre bSerre :=
        alpha_mem_Icc (n := N + 2) (i := 2) (by omega) (by norm_num) (by omega)
      have hxA : aSerre ≤ x := hx.1
      have hxB : x ≤ bSerre := hx.2
      have h1 : x - alpha (N + 2) 2 ≤ bSerre - aSerre := by linarith [hxB, halpha.1]
      have h2' : alpha (N + 2) 2 - x ≤ bSerre - aSerre := by linarith [halpha.2, hxA]
      exact abs_sub_le_iff.mpr ⟨h1, h2'⟩

/-- The gap between the two extreme roots of `P_{N+2}` is bounded below by a
positive constant: `∃ c, 0 < c ∧ ∀ N ≥ 1, c ≤ alpha (N+2) (N+2) − alpha (N+2) 1`. -/
lemma exists_extreme_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      c ≤ alpha (N + 2) (N + 2) - alpha (N + 2) 1 := by
  rcases exists_interval_holder with ⟨C0, hC0, hC0bd⟩
  refine ⟨((1 : ℝ) / 2) ^ 2 / C0 ^ 2, ?pos, ?bnd⟩
  · positivity
  · intro N hN
    have hn : 1 ≤ N + 2 := by omega
    have hnR : 0 < (N + 2 : ℝ) := by exact_mod_cast (by omega : 0 < N + 2)
    have hlt : alpha (N + 2) 1 < alpha (N + 2) (N + 2) :=
      alpha_strict_mono hn (by norm_num) (by omega) (by omega)
    have hd : 0 ≤ alpha (N + 2) (N + 2) - alpha (N + 2) 1 := sub_nonneg.mpr (le_of_lt hlt)
    have hmass : (1 : ℝ) / 2 ≤ (muS (Set.Icc (alpha (N + 2) 1) (alpha (N + 2) (N + 2)))).toReal := by
      have hcdf : cdf (alpha (N + 2) (N + 2)) - cdf (alpha (N + 2) 1) =
          ((N + 1 : ℕ) : ℝ) / (N + 2 : ℝ) := by
        have hT : cdf (alpha (N + 2) (N + 2)) = 1 := by
          rw [alpha_cdf_eq hn (by omega) (by omega)]
          field_simp [ne_of_gt hnR]
        have h1 : cdf (alpha (N + 2) 1) = (1 : ℝ) / (N + 2 : ℝ) := by
          rw [alpha_cdf_eq hn (by norm_num) (by omega)]
          norm_num
        rw [hT, h1]
        field_simp [ne_of_gt hnR]
        norm_num
        ring
      have hfrac : (1 : ℝ) / 2 ≤ ((N + 1 : ℕ) : ℝ) / (N + 2 : ℝ) := by
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) hnR]
        norm_num
        have hNn : (0 : ℝ) ≤ N := by exact_mod_cast (Nat.zero_le N)
        nlinarith
      calc
        (1 : ℝ) / 2 ≤ ((N + 1 : ℕ) : ℝ) / (N + 2 : ℝ) := hfrac
        _ = cdf (alpha (N + 2) (N + 2)) - cdf (alpha (N + 2) 1) := hcdf.symm
        _ ≤ (muS (Set.Icc (alpha (N + 2) 1) (alpha (N + 2) (N + 2)))).toReal :=
          cdf_diff_le_Icc (le_of_lt hlt)
    have hbdbd : (muS (Set.Icc (alpha (N + 2) 1) (alpha (N + 2) (N + 2)))).toReal ≤
        C0 * Real.sqrt (alpha (N + 2) (N + 2) - alpha (N + 2) 1) := by
      have ha1 : alpha (N + 2) 1 ∈ Set.Icc aSerre bSerre := alpha_mem_Icc hn (by norm_num) (by omega)
      have haT : alpha (N + 2) (N + 2) ∈ Set.Icc aSerre bSerre := alpha_mem_Icc hn (by omega) (by omega)
      exact hC0bd ha1.1 (le_of_lt hlt) haT.2
    have hlin : (1 : ℝ) / 2 ≤ C0 * Real.sqrt (alpha (N + 2) (N + 2) - alpha (N + 2) 1) :=
      le_trans hmass hbdbd
    exact lower_bound_from_holder hC0 (by norm_num : (0:ℝ) ≤ 1 / 2) hd hlin

/-- `rhoKept ≥ 0`. -/
lemma rhoKept_nonneg (N : ℕ) (x : ℝ) : 0 ≤ rhoKept N x := by
  by_cases hN : 1 ≤ N
  · unfold rhoKept
    rw [dif_pos (kept_nonempty hN)]
    exact Finset.le_inf' (kept_nonempty hN) (fun i : ℕ => |x - alpha (N + 2) i|) (by
      intro i hi
      exact abs_nonneg _)
  · unfold rhoKept
    have hne : ¬ (kept N).Nonempty := by
      intro h
      rcases h with ⟨j, hj⟩
      unfold kept at hj
      rw [Finset.mem_Icc] at hj
      omega
    rw [dif_neg hne]

/-- distance between two points of Σ is at most the diameter -/
lemma dist_le_diam {u v : ℝ} (hu : u ∈ Set.Icc aSerre bSerre) (hv : v ∈ Set.Icc aSerre bSerre) :
    |u - v| ≤ bSerre - aSerre := by
  have h1 : u - v ≤ bSerre - aSerre := by linarith [hu.2, hv.1]
  have h2 : v - u ≤ bSerre - aSerre := by linarith [hv.2, hu.1]
  exact abs_sub_le_iff.mpr ⟨h1, h2⟩

/-- elementary ratio bound: `r/(ab) ≤ 2/c` when `r ≤ min(a,b)`, `a,b > 0`,
`0 < c ≤ a+b`. -/
lemma ratio_upper_aux {r a b c : ℝ} (hr0 : 0 ≤ r) (hra : r ≤ a) (hrb : r ≤ b)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsum : c ≤ a + b) : r / (a * b) ≤ 2 / c := by
  by_cases hab : a ≤ b
  · have hpos : 0 < a * b := mul_pos ha hb
    have h1 : r / (a * b) ≤ a / (a * b) := div_le_div_of_nonneg_right hra hpos.le
    have hcancel : a / (a * b) = 1 / b := by
      field_simp [ne_of_gt ha]
    have hadd : 0 < a + b := add_pos ha hb
    have h2 : 1 / b ≤ 2 / (a + b) := (div_le_div_iff₀ hb hadd).mpr (by nlinarith [hab])
    have h3 : 2 / (a + b) ≤ 2 / c := (div_le_div_iff₀ hadd hc).mpr (by nlinarith [hsum])
    calc
      r / (a * b) ≤ a / (a * b) := h1
      _ = 1 / b := hcancel
      _ ≤ 2 / (a + b) := h2
      _ ≤ 2 / c := h3
  · have hba : b ≤ a := le_of_not_ge hab
    have hpos : 0 < a * b := mul_pos ha hb
    have h1 : r / (a * b) ≤ b / (a * b) := div_le_div_of_nonneg_right hrb hpos.le
    have hcancel : b / (a * b) = 1 / a := by
      field_simp [ne_of_gt hb]
    have hadd : 0 < a + b := add_pos ha hb
    have h2 : 1 / a ≤ 2 / (a + b) := (div_le_div_iff₀ ha hadd).mpr (by nlinarith [hba])
    have h3 : 2 / (a + b) ≤ 2 / c := (div_le_div_iff₀ hadd hc).mpr (by nlinarith [hsum])
    calc
      r / (a * b) ≤ b / (a * b) := h1
      _ = 1 / a := hcancel
      _ ≤ 2 / (a + b) := h2
      _ ≤ 2 / c := h3

/-- `ρfull/(|x−α_1||x−α_{N+2}|) ≤ 1/max(...) ≤ 2/gap` is bounded: case-free
upper bound used for (c): `∃ C, 0 < C ∧ ∀ N ≥ 1, ∀ x ∈ Icc, 0 < rhoFull N x →
  rhoFull N x / (|x − alpha (N+2) 1| * |x − alpha (N+2) (N+2)|) ≤ C`. -/
lemma exists_full_ratio_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      0 < rhoFull N x →
      rhoFull N x / (|x - alpha (N + 2) 1| * |x - alpha (N + 2) (N + 2)|) ≤ C := by
  rcases exists_extreme_gap with ⟨cg, hcg, hgap⟩
  refine ⟨2 / cg, div_pos (by norm_num) hcg, ?_⟩
  intro N hN x hx hρ
  let A : ℝ := |x - alpha (N + 2) 1|
  let B : ℝ := |x - alpha (N + 2) (N + 2)|
  have hρn : 0 ≤ rhoFull N x := by
    unfold rhoFull
    exact rho_nonneg (n := N + 2) x
  have hn : 1 ≤ N + 2 := by omega
  have hleA : rhoFull N x ≤ A := by
    unfold rhoFull A
    exact rho_le_root (n := N + 2) hn x (by rw [Finset.mem_Icc]; omega)
  have hleB : rhoFull N x ≤ B := by
    unfold rhoFull B
    exact rho_le_root (n := N + 2) hn x (by rw [Finset.mem_Icc]; omega)
  have hApos : 0 < A := lt_of_lt_of_le hρ hleA
  have hBpos : 0 < B := lt_of_lt_of_le hρ hleB
  have hsum : cg ≤ A + B := by
    have hT : alpha (N + 2) 1 ≤ alpha (N + 2) (N + 2) :=
      le_of_lt (alpha_strict_mono hn (by norm_num) (by omega) (by omega))
    have hgapN : cg ≤ alpha (N + 2) (N + 2) - alpha (N + 2) 1 := hgap N hN
    have hmain : alpha (N + 2) (N + 2) - alpha (N + 2) 1 ≤ A + B := by
      have hsub : alpha (N + 2) 1 - alpha (N + 2) (N + 2) =
          (alpha (N + 2) 1 - x) + (x - alpha (N + 2) (N + 2)) := by ring
      have htri : |alpha (N + 2) 1 - alpha (N + 2) (N + 2)| ≤ A + B := by
        rw [hsub]
        have h1 : |alpha (N + 2) 1 - x| ≤ A := by
          simpa [A, abs_sub_comm]
        have h2 : |x - alpha (N + 2) (N + 2)| ≤ B := by
          simpa [B]
        linarith [abs_add_le (alpha (N + 2) 1 - x) (x - alpha (N + 2) (N + 2)), h1, h2]
      have habs : |alpha (N + 2) 1 - alpha (N + 2) (N + 2)| = alpha (N + 2) (N + 2) - alpha (N + 2) 1 := by
        rw [abs_of_nonpos (sub_nonpos.mpr hT)]
        ring
      rw [← habs]
      exact htri
    exact le_trans hgapN hmain
  change rhoFull N x / (A * B) ≤ 2 / cg
  exact ratio_upper_aux hρn hleA hleB hApos hBpos hcg hsum

/-- `ρfull/(|x−α_1||x−α_{N+2}|) ≥ ρKept/diam²`: lower bound used for (b).
`∃ C, 0 < C ∧ ∀ N ≥ 1, ∀ x ∈ Icc, 0 < rhoFull N x →
  (1/C) * rhoKept N x ≤ rhoFull N x / (|x − alpha (N+2) 1| * |x − alpha (N+2) (N+2)|)`. -/
lemma exists_full_ratio_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      0 < rhoFull N x →
      (1 / C) * rhoKept N x ≤
        rhoFull N x / (|x - alpha (N + 2) 1| * |x - alpha (N + 2) (N + 2)|) := by
  refine ⟨(bSerre - aSerre) ^ 2, ?_, ?_⟩
  · have hD : 0 < bSerre - aSerre := sub_pos.mpr a_lt_b
    positivity
  · intro N hN x hx hρ
    have hD0 : 0 < bSerre - aSerre := sub_pos.mpr a_lt_b
    have hD0le : 0 ≤ bSerre - aSerre := le_of_lt hD0
    let A : ℝ := |x - alpha (N + 2) 1|
    let B : ℝ := |x - alpha (N + 2) (N + 2)|
    change (1 / (bSerre - aSerre) ^ 2) * rhoKept N x ≤ rhoFull N x / (A * B)
    have hn : 1 ≤ N + 2 := by omega
    have hB0 : 0 ≤ B := by dsimp [B]; exact abs_nonneg _
    have hA0 : 0 ≤ A := by dsimp [A]; exact abs_nonneg _
    have hAD : A ≤ bSerre - aSerre := by
      dsimp [A]
      exact dist_le_diam hx (alpha_mem_Icc (n := N + 2) (i := 1) hn (by norm_num) (by omega))
    have hBD : B ≤ bSerre - aSerre := by
      dsimp [B]
      exact dist_le_diam hx (alpha_mem_Icc (n := N + 2) (i := N + 2) hn (by omega) (by omega))
    have hApos : 0 < A := by
      have hle : rhoFull N x ≤ A := by
        unfold rhoFull A
        exact rho_le_root (n := N + 2) hn x (by rw [Finset.mem_Icc]; omega)
      exact lt_of_lt_of_le hρ hle
    have hBpos : 0 < B := by
      have hle : rhoFull N x ≤ B := by
        unfold rhoFull B
        exact rho_le_root (n := N + 2) hn x (by rw [Finset.mem_Icc]; omega)
      exact lt_of_lt_of_le hρ hle
    have hρu : 0 < rho (N + 2) x := by
      unfold rhoFull at hρ
      exact hρ
    rcases exists_index_eq_rho (n := N + 2) hn x hρu with ⟨i, hi, hatt⟩
    have hρfull : rhoFull N x = |x - alpha (N + 2) i| := by
      unfold rhoFull
      exact hatt
    have hKeptD : rhoKept N x ≤ bSerre - aSerre := rhoKept_le_diam hN hx
    have hmain : rhoKept N x * (A * B) ≤ (bSerre - aSerre) ^ 2 * rhoFull N x := by
      rw [Finset.mem_Icc] at hi
      by_cases hEq1 : i = 1
      · subst i
        rw [hρfull]
        dsimp [A]
        have hprod : rhoKept N x * B ≤ (bSerre - aSerre) * (bSerre - aSerre) :=
          mul_le_mul hKeptD hBD hB0 hD0le
        calc
          rhoKept N x * (|x - alpha (N + 2) 1| * B)
              = |x - alpha (N + 2) 1| * (rhoKept N x * B) := by ring
          _ ≤ |x - alpha (N + 2) 1| * ((bSerre - aSerre) * (bSerre - aSerre)) := by
              exact mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
          _ = (bSerre - aSerre) ^ 2 * |x - alpha (N + 2) 1| := by ring
      · by_cases hEqT : i = N + 2
        · subst i
          rw [hρfull]
          dsimp [B]
          have hprod : rhoKept N x * A ≤ (bSerre - aSerre) * (bSerre - aSerre) :=
            mul_le_mul hKeptD hAD hA0 hD0le
          calc
            rhoKept N x * (A * |x - alpha (N + 2) (N + 2)|)
                = (rhoKept N x * A) * |x - alpha (N + 2) (N + 2)| := by ring
            _ ≤ ((bSerre - aSerre) * (bSerre - aSerre)) * |x - alpha (N + 2) (N + 2)| := by
                exact mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
            _ = (bSerre - aSerre) ^ 2 * |x - alpha (N + 2) (N + 2)| := by ring
        · have ik : i ∈ kept N := by
            unfold kept
            rw [Finset.mem_Icc]
            omega
          have heq : rhoFull N x = rhoKept N x := rhoFull_eq_rhoKept_of_kept hN hρ ik hρfull
          rw [heq]
          have hAB : A * B ≤ (bSerre - aSerre) * (bSerre - aSerre) :=
            mul_le_mul hAD hBD hB0 hD0le
          calc
            rhoKept N x * (A * B) ≤ rhoKept N x * ((bSerre - aSerre) * (bSerre - aSerre)) := by
                exact mul_le_mul_of_nonneg_left hAB (rhoKept_nonneg N x)
            _ = (bSerre - aSerre) ^ 2 * rhoKept N x := by ring
    have hcross : (1 / (bSerre - aSerre) ^ 2) * rhoKept N x * (A * B) ≤ rhoFull N x := by
      calc
        (1 / (bSerre - aSerre) ^ 2) * rhoKept N x * (A * B)
            = (rhoKept N x * (A * B)) / (bSerre - aSerre) ^ 2 := by
              field_simp [pow_two, ne_of_gt hD0]
        _ ≤ rhoFull N x := by
              exact (div_le_iff₀ (sq_pos_of_pos hD0)).mpr (by simpa [mul_comm] using hmain)
    rw [le_div_iff₀ (mul_pos hApos hBpos)]
    exact hcross

/-- cast of `N + 2` -/
lemma nat_cast_two_le (N : ℕ) : ((N + 2 : ℕ) : ℝ) = (N : ℝ) + 2 := by norm_num

/-- if `0 < x`, `0 < y` and `y ≤ x` then `x⁻¹² ≤ y⁻¹²`. -/
lemma inv_sq_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : y ≤ x) : x⁻¹ ^ 2 ≤ y⁻¹ ^ 2 := by
  have h1 : x⁻¹ ≤ y⁻¹ := (inv_le_inv₀ hx hy).mpr h
  exact pow_le_pow_left₀ (inv_nonneg.mpr hx.le) h1 2

/-- Explicit form of the ratio lower bound (C = diam² = Dserre²):
`ρfull/(A·B) ≥ ρKept/Dserre²` whenever `0 < ρfull`. -/
lemma rhoKept_ratio_lower {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hρ : 0 < rhoFull N x) :
    (1 / (bSerre - aSerre) ^ 2) * rhoKept N x ≤
      rhoFull N x / (|x - alpha (N + 2) 1| * |x - alpha (N + 2) (N + 2)|) := by
    have hD0 : 0 < bSerre - aSerre := sub_pos.mpr a_lt_b
    have hD0le : 0 ≤ bSerre - aSerre := le_of_lt hD0
    let A : ℝ := |x - alpha (N + 2) 1|
    let B : ℝ := |x - alpha (N + 2) (N + 2)|
    change (1 / (bSerre - aSerre) ^ 2) * rhoKept N x ≤ rhoFull N x / (A * B)
    have hn : 1 ≤ N + 2 := by omega
    have hB0 : 0 ≤ B := by dsimp [B]; exact abs_nonneg _
    have hA0 : 0 ≤ A := by dsimp [A]; exact abs_nonneg _
    have hAD : A ≤ bSerre - aSerre := by
      dsimp [A]
      exact dist_le_diam hx (alpha_mem_Icc (n := N + 2) (i := 1) hn (by norm_num) (by omega))
    have hBD : B ≤ bSerre - aSerre := by
      dsimp [B]
      exact dist_le_diam hx (alpha_mem_Icc (n := N + 2) (i := N + 2) hn (by omega) (by omega))
    have hApos : 0 < A := by
      have hle : rhoFull N x ≤ A := by
        unfold rhoFull A
        exact rho_le_root (n := N + 2) hn x (by rw [Finset.mem_Icc]; omega)
      exact lt_of_lt_of_le hρ hle
    have hBpos : 0 < B := by
      have hle : rhoFull N x ≤ B := by
        unfold rhoFull B
        exact rho_le_root (n := N + 2) hn x (by rw [Finset.mem_Icc]; omega)
      exact lt_of_lt_of_le hρ hle
    have hρu : 0 < rho (N + 2) x := by
      unfold rhoFull at hρ
      exact hρ
    rcases exists_index_eq_rho (n := N + 2) hn x hρu with ⟨i, hi, hatt⟩
    have hρfull : rhoFull N x = |x - alpha (N + 2) i| := by
      unfold rhoFull
      exact hatt
    have hKeptD : rhoKept N x ≤ bSerre - aSerre := rhoKept_le_diam hN hx
    have hmain : rhoKept N x * (A * B) ≤ (bSerre - aSerre) ^ 2 * rhoFull N x := by
      rw [Finset.mem_Icc] at hi
      by_cases hEq1 : i = 1
      · subst i
        rw [hρfull]
        dsimp [A]
        have hprod : rhoKept N x * B ≤ (bSerre - aSerre) * (bSerre - aSerre) :=
          mul_le_mul hKeptD hBD hB0 hD0le
        calc
          rhoKept N x * (|x - alpha (N + 2) 1| * B)
              = |x - alpha (N + 2) 1| * (rhoKept N x * B) := by ring
          _ ≤ |x - alpha (N + 2) 1| * ((bSerre - aSerre) * (bSerre - aSerre)) := by
              exact mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
          _ = (bSerre - aSerre) ^ 2 * |x - alpha (N + 2) 1| := by ring
      · by_cases hEqT : i = N + 2
        · subst i
          rw [hρfull]
          dsimp [B]
          have hprod : rhoKept N x * A ≤ (bSerre - aSerre) * (bSerre - aSerre) :=
            mul_le_mul hKeptD hAD hA0 hD0le
          calc
            rhoKept N x * (A * |x - alpha (N + 2) (N + 2)|)
                = (rhoKept N x * A) * |x - alpha (N + 2) (N + 2)| := by ring
            _ ≤ ((bSerre - aSerre) * (bSerre - aSerre)) * |x - alpha (N + 2) (N + 2)| := by
                exact mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
            _ = (bSerre - aSerre) ^ 2 * |x - alpha (N + 2) (N + 2)| := by ring
        · have ik : i ∈ kept N := by
            unfold kept
            rw [Finset.mem_Icc]
            omega
          have heq : rhoFull N x = rhoKept N x := rhoFull_eq_rhoKept_of_kept hN hρ ik hρfull
          rw [heq]
          have hAB : A * B ≤ (bSerre - aSerre) * (bSerre - aSerre) :=
            mul_le_mul hAD hBD hB0 hD0le
          calc
            rhoKept N x * (A * B) ≤ rhoKept N x * ((bSerre - aSerre) * (bSerre - aSerre)) := by
                exact mul_le_mul_of_nonneg_left hAB (rhoKept_nonneg N x)
            _ = (bSerre - aSerre) ^ 2 * rhoKept N x := by ring
    have hcross : (1 / (bSerre - aSerre) ^ 2) * rhoKept N x * (A * B) ≤ rhoFull N x := by
      calc
        (1 / (bSerre - aSerre) ^ 2) * rhoKept N x * (A * B)
            = (rhoKept N x * (A * B)) / (bSerre - aSerre) ^ 2 := by
              field_simp [pow_two, ne_of_gt hD0]
        _ ≤ rhoFull N x := by
              exact (div_le_iff₀ (sq_pos_of_pos hD0)).mpr (by simpa [mul_comm] using hmain)
    rw [le_div_iff₀ (mul_pos hApos hBpos)]
    exact hcross

/-- cast of `N + 2` -/
theorem exists_root_isolation :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ i : ℕ, i ∈ kept N →
      (C * (N : ℝ))⁻¹ ^ 2 ≤ alpha (N + 2) i - aSerre ∧
      (C * (N : ℝ))⁻¹ ^ 2 ≤ bSerre - alpha (N + 2) i ∧
      ∀ j : ℕ, j ∈ kept N → j ≠ i →
        (C * (N : ℝ))⁻¹ ^ 2 ≤ |alpha (N + 2) i - alpha (N + 2) j| := by
  rcases exists_spacing with ⟨Cs, hCs, hSp⟩
  rcases exists_left_margin_all with ⟨Cl, hCl, hLm⟩
  rcases exists_right_margin_all with ⟨Cr, hCr, hRm⟩
  let C : ℝ := 2 * (Cs + Cl + Cr + 1)
  have hC1 : 1 ≤ C := by
    dsimp [C]
    nlinarith [hCs, hCl, hCr]
  refine ⟨C, hC1, ?_⟩
  intro N hN i hi
  have hn : 1 ≤ N + 2 := by omega
  have hd2 : 2 ≤ N + 2 := by omega
  unfold kept at hi
  rw [Finset.mem_Icc] at hi
  have hi1 : 1 ≤ i := by omega
  have hin1 : i ≤ N + 1 := by omega
  have hin : i ≤ N + 2 := by omega
  have hN2r : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hn20 : 0 < ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N + 2)
  have hCpos : 0 < C * (N : ℝ) := by
    dsimp [C]
    have hCp : 0 < 2 * (Cs + Cl + Cr + 1) := by nlinarith
    exact mul_pos hCp (lt_of_lt_of_le (by norm_num) hN2r)
  -- comparisons C·N vs the three constants·(N+2)
  have hCsN : Cs * ((N + 2 : ℕ) : ℝ) ≤ C * (N : ℝ) := by
    dsimp [C]
    have hCs0 : 0 ≤ Cs := le_of_lt (lt_of_lt_of_le (by norm_num) hCs)
    calc
      Cs * ((N + 2 : ℕ) : ℝ) ≤ Cs * (2 * (N : ℝ)) := by
        have h' : ((N + 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
          rw [nat_cast_two_le]
          nlinarith
        exact mul_le_mul_of_nonneg_left h' hCs0
      _ = (2 * Cs) * (N : ℝ) := by ring
      _ ≤ (2 * (Cs + Cl + Cr + 1)) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) hN0
  have hClN : Cl * ((N + 2 : ℕ) : ℝ) ≤ C * (N : ℝ) := by
    dsimp [C]
    have hCl0 : 0 ≤ Cl := le_of_lt (lt_of_lt_of_le (by norm_num) hCl)
    calc
      Cl * ((N + 2 : ℕ) : ℝ) ≤ Cl * (2 * (N : ℝ)) := by
        have h' : ((N + 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
          rw [nat_cast_two_le]
          nlinarith
        exact mul_le_mul_of_nonneg_left h' hCl0
      _ = (2 * Cl) * (N : ℝ) := by ring
      _ ≤ (2 * (Cs + Cl + Cr + 1)) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) hN0
  have hCrN : Cr * ((N + 2 : ℕ) : ℝ) ≤ C * (N : ℝ) := by
    dsimp [C]
    have hCr0 : 0 ≤ Cr := le_of_lt (lt_of_lt_of_le (by norm_num) hCr)
    calc
      Cr * ((N + 2 : ℕ) : ℝ) ≤ Cr * (2 * (N : ℝ)) := by
        have h' : ((N + 2 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
          rw [nat_cast_two_le]
          nlinarith
        exact mul_le_mul_of_nonneg_left h' hCr0
      _ = (2 * Cr) * (N : ℝ) := by ring
      _ ≤ (2 * (Cs + Cl + Cr + 1)) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith) hN0
  have hLmarg : (C * (N : ℝ))⁻¹ ^ 2 ≤ alpha (N + 2) i - aSerre := by
    have hb : (Cl * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤ alpha (N + 2) i - aSerre :=
      hLm (N + 2) hd2 i hi1 hin
    have htmp : (C * (N : ℝ))⁻¹ ^ 2 ≤ (Cl * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 := by
      exact inv_sq_le hCpos (mul_pos (lt_of_lt_of_le (by norm_num) hCl) hn20) hClN
    exact le_trans htmp hb
  have hRmarg : (C * (N : ℝ))⁻¹ ^ 2 ≤ bSerre - alpha (N + 2) i := by
    have hin' : i < N + 2 := by omega
    have hb : (Cr * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤ bSerre - alpha (N + 2) i :=
      hRm (N + 2) hd2 i hi1 (by omega)
    have htmp : (C * (N : ℝ))⁻¹ ^ 2 ≤ (Cr * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 := by
      exact inv_sq_le hCpos (mul_pos (lt_of_lt_of_le (by norm_num) hCr) hn20) hCrN
    exact le_trans htmp hb
  constructor
  · exact hLmarg
  · constructor
    · exact hRmarg
    · intro j hj hji
      unfold kept at hj
      rw [Finset.mem_Icc] at hj
      by_cases hij : i < j
      · -- separation with i < j
        have hsum : alpha (N + 2) j - alpha (N + 2) i =
            (∑ k ∈ Finset.Icc i (j - 1), (alpha (N + 2) (k + 1) - alpha (N + 2) k)) := by
          have hle : i ≤ j - 1 := by omega
          have hs := Finset.sum_Icc_sub (m := i) (n := j - 1) hle (fun k => alpha (N + 2) k)
          rw [hs]
          rw [show (j - 1 + 1) = j by omega]
        have hge : (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤
            alpha (N + 2) j - alpha (N + 2) i := by
          rw [hsum]
          have hterms : ∀ k ∈ Finset.Icc i (j - 1),
              (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤ alpha (N + 2) (k + 1) - alpha (N + 2) k := by
            intro k hk
            have hk1 : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
            have hkn : k < N + 2 := by rw [Finset.mem_Icc] at hk; omega
            exact hSp (N + 2) hd2 k hk1 hkn
          have hcp : 0 < (Finset.Icc i (j - 1)).card := by
            rw [Finset.card_pos]
            exact ⟨i, by rw [Finset.mem_Icc]; omega⟩
          have hcard1 : (1 : ℝ) ≤ ((Finset.Icc i (j - 1)).card : ℝ) := by
            have hc1 : 1 ≤ (Finset.Icc i (j - 1)).card := by omega
            exact_mod_cast hc1
          have hnonneg : 0 ≤ (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 := by positivity
          have hcc : (∑ k ∈ Finset.Icc i (j - 1), (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2) ≤
              (∑ k ∈ Finset.Icc i (j - 1), (alpha (N + 2) (k + 1) - alpha (N + 2) k)) := by
            exact Finset.sum_le_sum (by intro k hk; exact hterms k hk)
          calc
            (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤ (1 : ℝ) * ((Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2) := by
                nlinarith
            _ ≤ ((Finset.Icc i (j - 1)).card : ℝ) * ((Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2) := by
                exact mul_le_mul_of_nonneg_right hcard1 hnonneg
            _ = (∑ k ∈ Finset.Icc i (j - 1), (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2) := by
                rw [Finset.sum_const]
                ring
            _ ≤ (∑ k ∈ Finset.Icc i (j - 1), (alpha (N + 2) (k + 1) - alpha (N + 2) k)) := hcc
        -- |α_j − α_i| = α_j − α_i
        have habs : |alpha (N + 2) i - alpha (N + 2) j| = alpha (N + 2) j - alpha (N + 2) i := by
          have hlt := alpha_strict_mono hn (by omega) hij (by omega)
          rw [abs_sub_comm]
          exact abs_of_pos (sub_pos.mpr hlt)
        have hcomp : (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤ |alpha (N + 2) i - alpha (N + 2) j| := by
          rw [habs]
          exact hge
        have htmp : (C * (N : ℝ))⁻¹ ^ 2 ≤ (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 := by
          exact inv_sq_le hCpos (mul_pos (lt_of_lt_of_le (by norm_num) hCs) hn20) hCsN
        exact le_trans htmp hcomp
      · have hjg : j < i := by
          have hne : i ≠ j := by exact Ne.symm hji
          omega
        have hsum : alpha (N + 2) i - alpha (N + 2) j =
            (∑ k ∈ Finset.Icc j (i - 1), (alpha (N + 2) (k + 1) - alpha (N + 2) k)) := by
          have hle : j ≤ i - 1 := by omega
          have hs := Finset.sum_Icc_sub (m := j) (n := i - 1) hle (fun k => alpha (N + 2) k)
          rw [hs]
          rw [show (i - 1 + 1) = i by omega]
        have hge : (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤
            alpha (N + 2) i - alpha (N + 2) j := by
          rw [hsum]
          have hterms : ∀ k ∈ Finset.Icc j (i - 1),
              (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤ alpha (N + 2) (k + 1) - alpha (N + 2) k := by
            intro k hk
            have hk1 : 1 ≤ k := by rw [Finset.mem_Icc] at hk; omega
            have hkn : k < N + 2 := by rw [Finset.mem_Icc] at hk; omega
            exact hSp (N + 2) hd2 k hk1 hkn
          have hcp : 0 < (Finset.Icc j (i - 1)).card := by
            rw [Finset.card_pos]
            exact ⟨j, by rw [Finset.mem_Icc]; omega⟩
          have hcard1 : (1 : ℝ) ≤ ((Finset.Icc j (i - 1)).card : ℝ) := by
            have hc1 : 1 ≤ (Finset.Icc j (i - 1)).card := by omega
            exact_mod_cast hc1
          have hnonneg : 0 ≤ (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 := by positivity
          have hcc : (∑ k ∈ Finset.Icc j (i - 1), (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2) ≤
              (∑ k ∈ Finset.Icc j (i - 1), (alpha (N + 2) (k + 1) - alpha (N + 2) k)) := by
            exact Finset.sum_le_sum (by intro k hk; exact hterms k hk)
          calc
            (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤ (1 : ℝ) * ((Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2) := by
                nlinarith
            _ ≤ ((Finset.Icc j (i - 1)).card : ℝ) * ((Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2) := by
                exact mul_le_mul_of_nonneg_right hcard1 hnonneg
            _ = (∑ k ∈ Finset.Icc j (i - 1), (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2) := by
                rw [Finset.sum_const]
                ring
            _ ≤ (∑ k ∈ Finset.Icc j (i - 1), (alpha (N + 2) (k + 1) - alpha (N + 2) k)) := hcc
        have habs : |alpha (N + 2) i - alpha (N + 2) j| = alpha (N + 2) i - alpha (N + 2) j := by
          have hlt := alpha_strict_mono hn (by omega) hjg (by omega)
          exact abs_of_pos (sub_pos.mpr hlt)
        have hcomp : (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤ |alpha (N + 2) i - alpha (N + 2) j| := by
          rw [habs]
          exact hge
        have htmp : (C * (N : ℝ))⁻¹ ^ 2 ≤ (Cs * ((N + 2 : ℕ) : ℝ))⁻¹ ^ 2 := by
          exact inv_sq_le hCpos (mul_pos (lt_of_lt_of_le (by norm_num) hCs) hn20) hCsN
        exact le_trans htmp hcomp

/-- **lem:P_ver1(a)** — roots of `P̃_N` are spaced and away from the
boundary at a polynomial rate. -/
theorem roots_spaced_boundary :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ i : ℕ, i ∈ kept N →
      (C * (N : ℝ))⁻¹ ^ 2 ≤ alpha (N + 2) i - aSerre ∧
      (C * (N : ℝ))⁻¹ ^ 2 ≤ bSerre - alpha (N + 2) i := by
  rcases exists_root_isolation with ⟨C, hC, hIso⟩
  refine ⟨C, hC, ?_⟩
  intro N hN i hi
  exact ⟨(hIso N hN i hi).1, (hIso N hN i hi).2.1⟩

lemma rhoFull_eq_gt_left {N : ℕ} (hN : 2 ≤ N) {x : ℝ}
    (hxg : alpha (N + 2) 1 < x)
    (hxd : x - alpha (N + 2) 1 < (alpha (N + 2) 2 - alpha (N + 2) 1) / 2) :
    rhoFull N x = x - alpha (N + 2) 1 := by
  have hn : 1 ≤ N + 2 := by omega
  apply le_antisymm
  · unfold rhoFull
    have hle : rho (N + 2) x ≤ |x - alpha (N + 2) 1| :=
      rho_le_root (n := N + 2) hn x (by rw [Finset.mem_Icc]; omega)
    have habs : |x - alpha (N + 2) 1| = x - alpha (N + 2) 1 := abs_of_pos (sub_pos.mpr hxg)
    rw [habs] at hle
    exact hle
  · unfold rhoFull
    rw [rho_eq_inf (n := N + 2) hn x]
    exact Finset.le_inf' (Icc_one_n_nonempty hn) (fun i => |x - alpha (N + 2) i|) (by
      intro j hj
      rw [Finset.mem_Icc] at hj
      by_cases hj1 : j = 1
      · subst j
        have habs : |x - alpha (N + 2) 1| = x - alpha (N + 2) 1 := abs_of_pos (sub_pos.mpr hxg)
        rw [habs]
      · have hj2 : 2 ≤ j := by omega
        have h21 : alpha (N + 2) 1 < alpha (N + 2) 2 := alpha_strict_mono hn (by norm_num) (by norm_num) (by omega)
        have h2j : alpha (N + 2) 2 ≤ alpha (N + 2) j := by
          by_cases hEq : j = 2
          · rw [hEq]
          · have hlt : 2 < j := by omega
            exact le_of_lt (alpha_strict_mono hn (by norm_num) hlt hj.2)
        have hxlt2 : x < alpha (N + 2) 2 := by
          nlinarith [hxd, h21]
        have hxj : x ≤ alpha (N + 2) j := le_trans (le_of_lt hxlt2) h2j
        have habs : |x - alpha (N + 2) j| = alpha (N + 2) j - x := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr hxj)
        rw [habs]
        nlinarith [hxd, h2j])

lemma rhoFull_eq_lt_right {N : ℕ} (hN : 2 ≤ N) {x : ℝ}
    (hxl : x < alpha (N + 2) (N + 2))
    (hxd : alpha (N + 2) (N + 2) - x <
      (alpha (N + 2) (N + 2) - alpha (N + 2) (N + 1)) / 2) :
    rhoFull N x = alpha (N + 2) (N + 2) - x := by
  have hn : 1 ≤ N + 2 := by omega
  apply le_antisymm
  · unfold rhoFull
    have hle : rho (N + 2) x ≤ |x - alpha (N + 2) (N + 2)| :=
      rho_le_root (n := N + 2) hn x (by rw [Finset.mem_Icc]; omega)
    have habs : |x - alpha (N + 2) (N + 2)| = alpha (N + 2) (N + 2) - x := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr (le_of_lt hxl))
    rw [habs] at hle
    exact hle
  · unfold rhoFull
    rw [rho_eq_inf (n := N + 2) hn x]
    exact Finset.le_inf' (Icc_one_n_nonempty hn) (fun i => |x - alpha (N + 2) i|) (by
      intro j hj
      rw [Finset.mem_Icc] at hj
      by_cases hjT : j = N + 2
      · subst j
        have habs : |x - alpha (N + 2) (N + 2)| = alpha (N + 2) (N + 2) - x := by
          rw [abs_sub_comm]
          exact abs_of_nonneg (sub_nonneg.mpr (le_of_lt hxl))
        rw [habs]
      · have hjle : j ≤ N + 1 := by omega
        have hT1 : alpha (N + 2) (N + 1) < alpha (N + 2) (N + 2) :=
          alpha_strict_mono hn (by omega) (by omega) (by omega)
        have hjT2 : alpha (N + 2) j ≤ alpha (N + 2) (N + 1) := by
          by_cases hEq : j = N + 1
          · rw [hEq]
          · have hlt : j < N + 1 := by omega
            exact le_of_lt (alpha_strict_mono hn hj.1 hlt (by omega))
        have hxgt : alpha (N + 2) (N + 1) < x := by
          nlinarith [hxd, hT1]
        have hxj : alpha (N + 2) j ≤ x := le_trans hjT2 (le_of_lt hxgt)
        have habs : |x - alpha (N + 2) j| = x - alpha (N + 2) j :=
          abs_of_nonneg (sub_nonneg.mpr hxj)
        rw [habs]
        nlinarith [hxd, hjT2])

end Submission.PVer1
