import Submission.Contracts
import Submission.CompQ
import Submission.CompQRoots
import Submission.CompQRoots2
import Submission.CompQEnum
import Submission.ChebMargin
import Submission.PruneRoots
import Submission.MvtInterval
import Submission.SortedUnion
import Submission.PVer1
import Submission.WnormProduct
import Submission.Quantile
import Submission.QuantileExt
import Submission.Asymptotics
import Submission.QuantileMeanBound
import Submission.QuantileSums
import Submission.MuBridge
import Submission.Commons.Combinatorics.Fin.sorted_union_sum_eq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics


/-!
# Assembly of Proposition `early_ints_better` (contract 3) — per-n core

GOAL (this module): prove `early_ints_eventual`, the EVENTUAL form of
`Submission.Contracts.EarlyIntsContract`:

    ∀ B > 0, ∃ C > 3, ∀ᶠ n : ℕ in atTop, 2 ≤ n − mFloor B n →
        EarlyPolynomialData B C n

(`EarlyPolynomialData B C n` is the body of `Contracts.EarlyIntsContract`:
see `Submission/Contracts.lean`.)  The straightforward
eventual→universal absorption step (`∃ C, ∀ n > C, …`), is done OUTSIDE this
module (in the same file below or by the parent).

## The construction (Smith, adjust.tex, proof of `prop:early_ints_better`,
single interval `Σ = [aSerre,bSerre]`, `k₀ = 1`, `κ = kappa = kappaC`)

Fix `B > 0`.  Let `D = Bclps.Dconst` (a fixed integer ≥ 2), `C2val` as in
`Submission/CompQNums`.  For a sufficiently large `n` put
`m = mFloor B n`,  `r = (m + D) / D`  (integer division; then
`m + 1 ≤ D·r ≤ m + D`, so `d' := D·r − m` satisfies `1 ≤ d' ≤ D`), and
`N := n − D·r`  (`N ≥ 2` for large `n`;  `n − m = N + d'`).

1. **P̃ = prunePoly N** (`PVer1.prunePoly`): real monic degree `N`, roots
   `gammaRoot N k = alpha (N+2) (k.val+2)`, strictly increasing in the OPEN
   interval, pairwise distances and margins `≥ ((C_pr·(N+2))⁻¹)²`
   (`PruneRoots.prune_roots`).  PVer1 (`weighted_lower_bound` with `s = d' ≤ D`,
   `weighted_norm_bound`) gives  `w^{N+d'}|P̃(x)| ≥ N^{-C_low}·rhoKept N x` and
   `wnorm (N+d') P̃ ≤ N^{C_up}` for `x ∈ Icc aSerre bSerre`.

2. **Q** = the degree-`Dr` complementary polynomial from `CompQ.comp_q`
   applied to `(r, N, P̃)` (hypotheses `r ≥ 2`, `N ≥ 1`).  Its output clauses
   feed:
   * `CompQRoots2.comp_Q_roots2`:  `supNorm Q ≤ (r+3)^{Cq}·κ^{Dr}`,
     `supNorm Q.derivative ≤ (r+3)^{Cq}·κ^{Dr}`, and local growth
     `|Q(w)| ≥ (r+3)^{-Cq}·κ^{Dr}·|w−β|` whenever `Q.eval β = 0` and
     `|w−β| ≤ (r+3)^{-Cq}`;
   * `CompQEnum.comp_q_roots_sorted`: `Q` squarefree, every complex root in the
     OPEN interval, and an increasing root family `β : Fin (Dr) → ℝ` with
     `Q = ∏(X − C(β k))`; each `β k` lies in the interior Chebyshev window
     `[extPoint (r+3) (r+1), extPoint (r+3) 1]` (so margins
     `≥ c_Q/(r+3)²` by `ChebMargin.extPoint_margin`);
   * the pigeonhole clause: for every root `α` of `P̃`,
     `|Q(α)| ≥ N⁻¹·C2val⁻¹·κ^{Dr}`;
   * the even-coefficient band: for every `k` with
     `N+1 ≤ k ≤ N+Dr−1`, `(P̃·Q).coeff k = (z:ℝ)` for an EVEN integer `z`.

3. **Root separation and δ** (paper's claim "any two distinct roots of P_n
   are ≥ 3δ apart").  Distinct roots of `P̃·Q` split into three kinds, each
   separated by the given quantity:
   * P̃-P̃: ≥ `((C_pr·(N+2))⁻¹)²` (spacing of `gammaRoot`);
   * Q-Q:    ≥ `(r+3)^{-Cq}`  (local growth: if `|β−β'| ≤ (r+3)^{-Cq}` then
     `0 = |Q(β')| ≥ (r+3)^{-Cq}κ^{Dr}|β−β'| > 0`, contradiction);
   * P̃-Q (cross): ≥ `N⁻¹·C2val⁻¹·(r+3)^{-Cq}`  (pigeonhole + `MvtInterval`
     Lipschitz `|Q(γ)−Q(β)| ≤ supNorm Q.derivative·|γ−β|`).
   Margins from the Serre ends: P̃ roots ≥ `((C_pr·(N+2))⁻¹)²`, Q roots
   ≥ `c_Q/(r+3)²`.  Set
   `δ = (1/3)·min{((C_pr·(N+2))⁻¹)², (r+3)^{-Cq}, N⁻¹C2val⁻¹(r+3)^{-Cq}, c_Q/(r+3)²}`.
   Then every two distinct roots are `≥ 3δ` apart and every root has margin
   `≥ 3δ` from `aSerre`, `bSerre`.

4. **Sorted enumeration α of all roots of P̃·Q**: apply
   `SortedUnion.sorted_union` to `gammaRoot N` and `β` (both strictly
   increasing; disjoint ranges because `|Q(γ k)| ≥ N⁻¹C2val⁻¹κ^{Dr} > 0`):
   get `α : Fin n → ℝ` strictly increasing with
   `P̃·Q = ∏_{i:Fin n} (X − C(α i))` (since `P̃ = ∏γ`, `Q = ∏β`).

5. **Brackets** `x i = α i − δ`, `y i = α i + δ`.  All required properties:
   * `x i < α i < y i`;  `y i < x j` for `i<j` (roots `≥ 3δ` apart);
   * `[x i, y i] ⊆ [aSerre, bSerre]` (margins `≥ 3δ`);
   * `P_n(x i) ≠ 0`, `P_n(y i) ≠ 0` (no other root within `3δ`);
   * weighted endpoint values: for `t = α i ± δ`, prove
     `w^{n−m}|P̃(t)·Q(t)| ≥ n^{-C_tot}·κ^m` by the two-case split:
     + **P̃-root case** (`P̃.eval (α i) = 0`, so `α i` is some `gammaRoot`):
       ρKept-argument gives `w^{N+d'}|P̃(t)| ≥ N^{-C_low}·δ`, and
       `|Q(t)| ≥ (2/3)·N⁻¹·C2val⁻¹·κ^{Dr}` from the pigeonhole bound at `α i`
       plus the Lipschitz/MVT bound `|Q(t)−Q(α i)| ≤ supNorm Q.derivative·δ`
       (the δ-choice makes the loss ≤ `(1/3)·N⁻¹C2val⁻¹κ^{Dr}`);
       since `(r+3)^{Cq}·δ ≤ (2/3)N⁻¹C2val⁻¹(r+3)^{2Cq}` eventually — simpler:
       use the bound `|Q(t)| ≥ (r+3)^{-Cq}·κ^{Dr}·δ` DIRECTLY, valid in BOTH
       cases (Q-root case: local growth; P̃-root case: from the pigeonhole +
       Lipschitz bound because `δ` is chosen small enough that
       `(r+3)^{-Cq}δ ≤ (2/3)N⁻¹C2val⁻¹`);
     + **Q-root case** (`P̃.eval (α i) ≠ 0` forces `Q.eval (α i) = 0`):
       `ρKept(t) ≥ δ` (all kept roots are `≥ 3δ` away from the Q-root, so
       `≥ 2δ` away from `t`), hence
       `w^{N+d'}|P̃(t)| ≥ N^{-C_low}·δ`; and local growth gives
       `|Q(t)| ≥ (r+3)^{-Cq}κ^{Dr}δ`.
     Combining: `w^{n−m}|P_n(t)| ≥ N^{-C_low}·(r+3)^{-Cq}·κ^{Dr}·δ²` in both
     cases, and for `n` large this is `≥ n^{-C}·κ^m` (because
     `κ^{Dr} = κ^{d'}·κ^m ≥ κ^m` and `δ ≥ n^{-(large fixed exponent)}`
     eventually).

6. **Coefficients**: `P_n = P̃·Q` has even integer coefficients in degrees
   `[N+1, N+Dr−1]` (comp_q), and `[n−m, n−1] ⊆ [N+1, N+Dr−1]` because
   `Dr ≥ m+1`, so `n−m ≥ N+1`.

7. **Norm bound**: `wnorm (n−m) P_n ≤ (wnorm (n−m) P̃)·supNorm Q`
   (`WnormProduct.wnorm_mul_le_sup`) `≤ N^{C_up}·(r+3)^{Cq}·κ^{Dr}`
   `≤ n^{C}·κ^m` for `n` large (κ^{Dr} = κ^{d'}κ^m ≤ κ^D·κ^m, and
   `N ≤ n`, `r+3 ≤ n` eventually).

Choose the output constant `C` large enough that all the polynomial
`n^{…}`-inequalities above hold for all sufficiently large `n`, and `3 < C`.

## Names / conventions (check each in the module before use)
* `Bclps.Dconst`, `CompQNums.C2val`, `kappaC` (= `Contracts.kappa`: both are
  `(bSerre − aSerre)/4`, prove equality by `simp [kappa, kappaC]`),
  `AdjustedCheb.bracketPoint`, `AdjustedCheb.prunedPoly`,
  `CompQRoots.d r = (Bclps.Dconst − 1)·r`,
  `ChebSerre.extPoint`.
* `PVer1.prunePoly N`, `PVer1.kept N`, `PVer1.rhoKept N x`;
  `PruneRoots.gammaRoot N k`, `PruneRoots.prune_roots`;
  `Quantile.alpha n i`, `QuantileExt.exists_left_margin_all`,
  `exists_right_margin_all`, `Quantile.exists_spacing`.
* PVer1 theorems (namespace `Submission.PVer1`):
  `weighted_lower_bound : ∃ C, 0 < C ∧ ∀ N ≥ 2, ∀ s ≤ Bclps.Dconst,
    ∀ x ∈ Icc aSerre bSerre, N^{-C}·rhoKept N x ≤ w(x)^{N+s}|prunePoly N x|`;
  `weighted_norm_bound : ∃ C, 0 < C ∧ ∀ N ≥ 2, ∀ s ≤ Bclps.Dconst,
    wnorm (N+s) (prunePoly N) ≤ N^C`.
* `CompQ.comp_q (r) (N) hr2 hN1 hPmon hPdeg : ∃ C > 0, ∃ T Q0 Q1 Q eps Nc,
   …` (read the full statement in `Submission/CompQ.lean`).
* `CompQRoots.comp_Q_roots` and `CompQRoots2.comp_Q_roots2` have the SAME
  first hypotheses as `comp_q` output (T monic/deg, T close to pruned,
  bracket sign/magnitude, Q0/Q1/Q equalities, eps, N bounds) — feed comp_q's
  clauses directly.
* `CompQEnum.comp_q_roots_sorted` (same hypotheses + Q.Monic + Q.natDegree)
  gives squarefree + β/gL/gR/window.
-/

noncomputable section

set_option maxHeartbeats 20000000

open MeasureTheory
open ComplexOrder
open Filter
open scoped Real BigOperators Topology
open Polynomial

namespace Submission.EarlyAssembly

open Submission.Contracts
open Submission.Serre
open Submission.SerreExample
open Submission.WeightedNorm
open Submission.WnormToolkit
open Submission.WnormProduct
open Submission.Bclps
open Submission.CompQNums
open Submission.CompQ
open Submission.CompQRoots
open Submission.CompQRoots2
open Submission.CompQEnum
open Submission.ChebMargin
open Submission.PruneRoots
open Submission.MvtInterval
open Submission.SortedUnion
open Submission.PVer1
open Submission.Quantile
open Submission.QuantileExt
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.QuantileMeanBound
open Submission.QuantileSums

/-- eventually: `M ≤ n^a` for fixed `M` and `a > 0` -/
lemma eventually_rpow_ge (a M : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, M ≤ (n : ℝ) ^ a := by
  have hx : ∀ᶠ x : ℝ in atTop, M ≤ x ^ a := by
    have h := (tendsto_rpow_atTop ha).eventually_ge_atTop M
    filter_upwards [h] with x hx
    exact hx
  exact tendsto_natCast_atTop_atTop.eventually hx

/-- `mFloor B n` eventually grows beyond every fixed bound. -/
lemma eventually_mFloor_ge (B : ℝ) (hB : 0 < B) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, (M : ℝ) ≤ (mFloor B n : ℝ) := by
  have hlog := Asymptotics.eventually_log_ge ((M + 1) / B)
  have h4 : ∀ᶠ n : ℕ in atTop, (2 : ℕ) ≤ n := eventually_ge_atTop 2
  filter_upwards [hlog, h4] with n hlog' h2n
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 2) h2n)
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    calc (1 : ℝ) = Real.sqrt (1 : ℝ) := by norm_num
    _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hn1R
  have hB0 : 0 ≤ B := le_of_lt hB
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1R
  have hlb := mFloor_ge_sub_one hB.le h2n
  have hbig : (M : ℝ) + 1 ≤ B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    calc
      (M : ℝ) + 1 = B * ((M + 1) / B) := by field_simp [hB.ne']
      _ ≤ B * Real.log (n : ℝ) := by
          exact mul_le_mul_of_nonneg_left hlog' hB0
      _ ≤ B * (Real.sqrt (n : ℝ) * Real.log (n : ℝ)) := by
          have hstep : Real.log (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
            simpa using (mul_le_mul_of_nonneg_right hsq1 hlog0)
          exact mul_le_mul_of_nonneg_left hstep hB0
      _ = B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by ring
  calc
    (M : ℝ) ≤ (M : ℝ) + 1 - 1 := by linarith
    _ ≤ B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) - 1 := by linarith
    _ ≤ (mFloor B n : ℝ) := hlb

/-- `mFloor B n ≤ n − K` eventually for every fixed `K`. -/
lemma eventually_mFloor_le_sub (B : ℝ) (hB : 0 < B) (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, mFloor B n ≤ n - K := by
  have hlog := Asymptotics.eventually_log_le_sqrt_mul (c := 1 / (2 * B)) (by positivity)
  have h4 : ∀ᶠ n : ℕ in atTop, (max (2 * K) 2 : ℕ) ≤ n := eventually_ge_atTop (max (2 * K) 2)
  filter_upwards [hlog, h4] with n hlb hn4
  have h2n : 2 ≤ n := by omega
  have hKn : K ≤ n := by omega
  have hx0 : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
    calc Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (Real.sqrt (n : ℝ)) ^ 2 := by ring
    _ = (n : ℝ) := Real.sq_sqrt hx0
  have hBB : B * (1 / (2 * B)) = 1 / 2 := by
    field_simp [hB.ne']
  have hu : B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) / 2 := by
    calc
      B * Real.sqrt (n : ℝ) * Real.log (n : ℝ)
          ≤ B * Real.sqrt (n : ℝ) * ((1 / (2 * B)) * Real.sqrt (n : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hlb (mul_nonneg hB.le (Real.sqrt_nonneg (n : ℝ)))
      _ = (1 / 2) * (n : ℝ) := by
        calc B * Real.sqrt (n : ℝ) * ((1 / (2 * B)) * Real.sqrt (n : ℝ))
            = (B * (1 / (2 * B))) * (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) := by ring
        _ = (1 / 2) * (n : ℝ) := by rw [hBB, hsq]
      _ = (n : ℝ) / 2 := by ring
  have hu2 : (n : ℝ) / 2 ≤ (n : ℝ) - K := by
    have hKnR : (K : ℝ) ≤ (n : ℝ) / 2 := by
      have : (2 * K : ℕ) ≤ n := by omega
      have : (2 * (K : ℝ)) ≤ (n : ℝ) := by exact_mod_cast this
      linarith
    linarith
  have hcast : ((n - K : ℕ) : ℝ) = (n : ℝ) - K := by
    rw [Nat.cast_sub hKn]
  have hub : B * Real.sqrt (n : ℝ) * Real.log (n : ℝ) ≤ ((n - K : ℕ) : ℝ) := by
    rw [hcast]
    exact le_trans hu hu2
  simpa [mFloor] using (Nat.floor_le_of_le hub)

private noncomputable def pruneC : ℝ := Classical.choose (prune_roots)

/-- The constant produced by `PVer1.weighted_lower_bound`. -/
private noncomputable def lowC : ℝ := Classical.choose (weighted_lower_bound)

/-- The constant produced by `PVer1.weighted_norm_bound`. -/
private noncomputable def upC : ℝ := Classical.choose (weighted_norm_bound)

/-- The constant produced by `CompQRoots2.comp_Q_roots2`. -/
private noncomputable def roots2C : ℝ := Classical.choose (comp_Q_roots2)

/-- The natural threshold produced by `CompQEnum.comp_q_roots_sorted`. -/
private noncomputable def enumC0 : ℕ := Classical.choose (comp_q_roots_sorted)

/-- The margin constant produced by `ChebMargin.extPoint_margin`. -/
private noncomputable def cQext : ℝ := Classical.choose (extPoint_margin)

/-- Lower-bound constant of the root-separation parameter `ρ` (so that
`ρ ≥ rho0 · n^{-(roots2C+3)}` eventually): `min` of the four leading
constants `1/(4·pruneC²)`, `1`, `C2val⁻¹`, `bSerre−aSerre`. -/
private noncomputable def rho0 : ℝ :=
  min (min (1 / (4 * pruneC ^ 2)) 1) (min (C2val⁻¹) cQext)

/-- `D·((m+D)/D) ≤ m+D` and `m+1 ≤ D·((m+D)/D)` for `D ≥ 1`. -/
private lemma nat_div_bounds (m D : ℕ) (hD : 0 < D) :
    D * ((m + D) / D) ≤ m + D ∧ m + 1 ≤ D * ((m + D) / D) := by
  constructor
  · have h := Nat.div_mul_le_self (m + D) D
    rwa [Nat.mul_comm] at h
  · have hmod : (m + D) % D < D := Nat.mod_lt (m + D) hD
    have hsum : (m + D) = (m + D) % D + D * ((m + D) / D) :=
      (Nat.mod_add_div (m + D) D).symm
    have hstep : m + D < D * ((m + D) / D) + D := by
      calc
        m + D = (m + D) % D + D * ((m + D) / D) := hsum
        _ < D * ((m + D) / D) + D := by omega
    omega

/-- positivity of the four separation constants (bundled). -/
private lemma rho0_pos : 0 < rho0 := by
  dsimp [rho0]
  have hprune : 0 < pruneC := lt_of_lt_of_le (by norm_num) (Classical.choose_spec (prune_roots)).1
  have hc2 : 0 < C2val := C2val_pos
  have hd : 0 < cQext := (Classical.choose_spec (extPoint_margin)).1
  have h1 : 0 < 1 / (4 * pruneC ^ 2) := by
    exact div_pos (by norm_num) (mul_pos (by norm_num) (pow_pos hprune 2))
  have h12 : 0 < min (1 / (4 * pruneC ^ 2)) 1 := lt_min h1 (by norm_num)
  have h34 : 0 < min (C2val⁻¹) cQext := lt_min (inv_pos.mpr hc2) hd
  exact lt_min h12 h34

/-- `rho0 ≤` each of the four constants. -/
private lemma rho0_le_candidates :
    rho0 ≤ 1 / (4 * pruneC ^ 2) ∧ rho0 ≤ 1 ∧ rho0 ≤ C2val⁻¹ ∧
      rho0 ≤ cQext := by
  have hA : rho0 ≤ 1 / (4 * pruneC ^ 2) := by
    dsimp [rho0]
    exact le_trans
      (min_le_left (min (1 / (4 * pruneC ^ 2)) 1) (min (C2val⁻¹) cQext))
      (min_le_left (1 / (4 * pruneC ^ 2)) (1 : ℝ))
  have hB : rho0 ≤ 1 := by
    dsimp [rho0]
    exact le_trans
      (min_le_left (min (1 / (4 * pruneC ^ 2)) 1) (min (C2val⁻¹) cQext))
      (min_le_right (1 / (4 * pruneC ^ 2)) (1 : ℝ))
  have hC : rho0 ≤ C2val⁻¹ := by
    dsimp [rho0]
    exact le_trans
      (min_le_right (min (1 / (4 * pruneC ^ 2)) 1) (min (C2val⁻¹) cQext))
      (min_le_left (C2val⁻¹) cQext)
  have hD : rho0 ≤ cQext := by
    dsimp [rho0]
    exact le_trans
      (min_le_right (min (1 / (4 * pruneC ^ 2)) 1) (min (C2val⁻¹) cQext))
      (min_le_right (C2val⁻¹) cQext)
  exact ⟨hA, hB, hC, hD⟩


/-- Reindex a product of linear factors along an equality of index types. -/
private lemma prod_fin_congr {N n : ℕ} (h : N = n)
    (f : Fin N → ℝ) (g : Fin n → ℝ)
    (hfg : ∀ i : Fin N, f i = g ⟨i.val, by simpa [h] using i.isLt⟩) :
    (∏ i : Fin N, (Polynomial.X - Polynomial.C (f i))) =
      ∏ j : Fin n, (Polynomial.X - Polynomial.C (g j)) := by
  subst h
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  rw [hfg i]

/-- `mFloor B n` is eventually at least any fixed bound (as a natural). -/
private lemma eventually_mFloor_ge_nat (B : ℝ) (hB : 0 < B) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, (M : ℕ) ≤ mFloor B n := by
  have h := eventually_mFloor_ge B hB (M : ℝ)
  filter_upwards [h] with n hn
  exact_mod_cast hn


/-- monotone in exponent (upper): `x^a ≤ y^a` for `0≤x≤y`, `0≤a`. -/
private lemma rpow_le_rpow_of_le_left {a x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (ha : 0 ≤ a) :
    x ^ a ≤ y ^ a := by
  exact Real.rpow_le_rpow hx hxy ha

/-- decreasing negative powers: for `1 ≤ x ≤ y`, `y^{-a} ≤ x^{-a}` when `0 ≤ a`. -/
private lemma rpow_neg_ge_of_le {a x y : ℝ} (h1x : 1 ≤ x) (hxy : x ≤ y) (ha : 0 ≤ a) :
    y ^ (-a) ≤ x ^ (-a) := by
  exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one h1x) hxy (by linarith)

/-- `x^a = (x^b)^(a/b)` style identity we use: `(n:ℝ)^(a+b) = n^a * n^b`. -/
private lemma rpow_add_mul {x a b : ℝ} (hx : 0 < x) :
    x ^ (a + b) = x ^ a * x ^ b := by
  rw [Real.rpow_add hx]

/-- eventually: big `C` absorbs `(rho0/3)` and fixed exponents: the exact
hypothesis `hIE` holds for all large `n`. -/
private lemma eventually_hIE (Ct : ℝ) (hCbig : lowC + 3 * roots2C + 6 < Ct) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-Ct) ≤ (rho0 / 3) ^ 2 * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) := by
  have ha : 0 < Ct - (lowC + 3 * roots2C + 6) := by linarith
  have h1 := eventually_rpow_ge (Ct - (lowC + 3 * roots2C + 6)) ((3 / rho0) ^ 2) ha
  have h4 : ∀ᶠ n : ℕ in atTop, (2 : ℕ) ≤ n := eventually_ge_atTop 2
  filter_upwards [h1, h4] with n hn h2n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by norm_num) h2n)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hpow : (3 / rho0) ^ 2 ≤ (n : ℝ) ^ (Ct - (lowC + 3 * roots2C + 6)) := hn
  have hrho0 : rho0 ≠ 0 := ne_of_gt rho0_pos
  have hrho3 : (rho0 / 3) ≠ 0 := by
    intro h
    have : rho0 = 0 := by
      have hz := congrArg (fun x : ℝ => x * (3 : ℝ)) h
      nlinarith [hrho0]
    exact hrho0 this
  have hsq : (rho0 / 3) ^ 2 * (3 / rho0) ^ 2 = 1 := by
    field_simp [hrho3]
  calc
    (n : ℝ) ^ (-Ct)
        = (n : ℝ) ^ (-Ct) * ((rho0 / 3) ^ 2 * (3 / rho0) ^ 2) := by rw [hsq, mul_one]
    _ = (rho0 / 3) ^ 2 * ((n : ℝ) ^ (-Ct) * (3 / rho0) ^ 2) := by ring
    _ ≤ (rho0 / 3) ^ 2 * ((n : ℝ) ^ (-Ct) * (n : ℝ) ^ (Ct - (lowC + 3 * roots2C + 6))) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ (rho0 / 3) ^ 2)
        exact mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (-Ct))
    _ = (rho0 / 3) ^ 2 * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) := by
        congr 1
        rw [← Real.rpow_add hnpos]
        congr 1
        ring

/-- eventually: the norm-bound inequality `hIU` holds for all large `n`. -/
private lemma eventually_hIU (Ct : ℝ) (hCbig : upC + roots2C < Ct) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (upC + roots2C) * kappaC ^ Bclps.Dconst ≤ (n : ℝ) ^ Ct := by
  have hκ1 : 1 < kappaC := kappaC_gt_one
  have ha : 0 < Ct - (upC + roots2C) := by linarith
  have h1 := eventually_rpow_ge (Ct - (upC + roots2C)) (kappaC ^ Bclps.Dconst) ha
  have h4 : ∀ᶠ n : ℕ in atTop, (2 : ℕ) ≤ n := eventually_ge_atTop 2
  filter_upwards [h1, h4] with n hn h2n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by norm_num) h2n)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hpow : kappaC ^ Bclps.Dconst ≤ (n : ℝ) ^ (Ct - (upC + roots2C)) := hn
  calc
    (n : ℝ) ^ (upC + roots2C) * kappaC ^ Bclps.Dconst
        ≤ (n : ℝ) ^ (upC + roots2C) * (n : ℝ) ^ (Ct - (upC + roots2C)) := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (n : ℝ) ^ Ct := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring


/-- `(x^a)² = x^{2a}` for `x > 0`. -/
private lemma sq_rpow {x : ℝ} (hx : 0 < x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  have h1 : (x ^ a) ^ (2 : ℝ) = x ^ (a * 2) := (Real.rpow_mul (le_of_lt hx) a (2 : ℝ)).symm
  rw [← Real.rpow_natCast (x ^ a) 2]
  calc
    (x ^ a) ^ (2 : ℝ) = x ^ (a * 2) := h1
    _ = x ^ (2 * a) := by congr 1; ring

/-- `x^{-2} = (x⁻¹)²` for `x > 0`. -/
private lemma rpow_neg_two {x : ℝ} (hx : 0 < x) : x ^ (-(2 : ℝ)) = (x⁻¹) ^ 2 := by
  have h1 : x ^ (2 : ℝ) = x ^ 2 := Real.rpow_natCast x 2
  rw [Real.rpow_neg (le_of_lt hx) 2]
  rw [h1]
  exact (inv_pow x 2).symm


/-- κ from `Contracts` equals the Chebyshev `kappaC`. -/
lemma kappa_eq_kappaC : Contracts.kappa = ChebSerre.kappaC := by
  simp [Contracts.kappa, ChebSerre.kappaC]




/-- product of four inequalities (all factors nonnegative) -/
private lemma mul_le_mul4 {a b c d a' b' c' d' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d')
    (ha0 : 0 ≤ a') (hb0 : 0 ≤ b') (hc0 : 0 ≤ c')
    (hd0 : 0 ≤ d) (h0b : 0 ≤ b) (h0c : 0 ≤ c) :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have h1 : a * b * c * d ≤ a' * b * c * d := by
    calc
      a * b * c * d = a * (b * c * d) := by ring
      _ ≤ a' * (b * c * d) := mul_le_mul_of_nonneg_right ha (mul_nonneg (mul_nonneg h0b h0c) hd0)
      _ = a' * b * c * d := by ring
  have h2 : a' * b * c * d ≤ a' * b' * c * d := by
    calc
      a' * b * c * d = (a' * b) * (c * d) := by ring
      _ ≤ (a' * b') * (c * d) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb ha0) (mul_nonneg h0c hd0)
      _ = a' * b' * c * d := by ring
  have h3 : a' * b' * c * d ≤ a' * b' * c' * d := by
    calc
      a' * b' * c * d = (a' * b') * (c * d) := by ring
      _ ≤ (a' * b') * (c' * d) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hd0) (mul_nonneg ha0 hb0)
      _ = a' * b' * c' * d := by ring
  have h4 : a' * b' * c' * d ≤ a' * b' * c' * d' := by
    calc
      a' * b' * c' * d = (a' * b' * c') * d := by ring
      _ ≤ (a' * b' * c') * d' := mul_le_mul_of_nonneg_left hd (mul_nonneg (mul_nonneg ha0 hb0) hc0)
      _ = a' * b' * c' * d' := by ring
  exact le_trans (le_trans (le_trans h1 h2) h3) h4

/-- `r = (mFloor B n + Dconst) / Dconst`, the index of the complementary
polynomial (an integer division in `ℕ`). -/
private noncomputable def stepR (B : ℝ) (n : ℕ) : ℕ :=
  (mFloor B n + Bclps.Dconst) / Bclps.Dconst

/-- Coefficient for the per-`n` root-mean bound (mean clause of
`EarlyPolynomialData`): absorbs the quantile-rate constant, the endpoints and
the complementary roots (`4·bSerre + qRateC + bSerre·(Dconst+1)`). -/
noncomputable def Cm_big : ℝ :=
  (4 * bSerre + qRateC) + bSerre * ((Bclps.Dconst : ℝ) + 1)

/-- `Cm_big ≥ 0`. -/
lemma Cm_big_nonneg : 0 ≤ Cm_big := by
  dsimp [Cm_big]
  have hq : 0 ≤ qRateC := le_of_lt qRateC_pos
  have h1 : 0 ≤ 4 * bSerre + qRateC := by nlinarith [bSerre_pos, hq]
  have h2 : 0 ≤ bSerre * ((Bclps.Dconst : ℝ) + 1) := by
    exact mul_nonneg (le_of_lt bSerre_pos) (by positivity)
  linarith

/-- The raw union bound numerator is absorbed by `Cm_big · (m+1)`. -/
lemma Cm_big_absorbs (Dr m : ℕ) (hDr : (Dr : ℝ) ≤ (m : ℝ) + (Bclps.Dconst : ℝ)) :
    (4 * bSerre + qRateC) + bSerre * (Dr : ℝ) ≤ Cm_big * ((m : ℝ) + 1) := by
  have hq : 0 ≤ qRateC := le_of_lt qRateC_pos
  have hN0 : 0 ≤ 4 * bSerre + qRateC := by nlinarith [bSerre_pos, hq]
  have hb0 : 0 ≤ bSerre := le_of_lt bSerre_pos
  have hD0 : 0 ≤ (Bclps.Dconst : ℝ) := by positivity
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have h1 : bSerre * (Dr : ℝ) ≤ bSerre * ((m : ℝ) + (Bclps.Dconst : ℝ)) :=
    mul_le_mul_of_nonneg_left hDr hb0
  have h2 : (m : ℝ) + (Bclps.Dconst : ℝ) ≤ ((Bclps.Dconst : ℝ) + 1) * ((m : ℝ) + 1) := by
    have hDm : 0 ≤ (Bclps.Dconst : ℝ) * (m : ℝ) := mul_nonneg hD0 hm0
    nlinarith
  have h3 : bSerre * ((m : ℝ) + (Bclps.Dconst : ℝ)) ≤
      bSerre * (((Bclps.Dconst : ℝ) + 1) * ((m : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left h2 hb0
  have h4 : bSerre * (Dr : ℝ) ≤ bSerre * (((Bclps.Dconst : ℝ) + 1) * ((m : ℝ) + 1)) :=
    le_trans h1 h3
  have h5 : 4 * bSerre + qRateC ≤ (4 * bSerre + qRateC) * ((m : ℝ) + 1) := by
    have hm1 : 1 ≤ (m : ℝ) + 1 := by linarith
    simpa using (mul_le_mul_of_nonneg_left hm1 hN0)
  have hcm : Cm_big * ((m : ℝ) + 1) =
      (4 * bSerre + qRateC) * ((m : ℝ) + 1) +
        bSerre * (((Bclps.Dconst : ℝ) + 1) * ((m : ℝ) + 1)) := by
    dsimp [Cm_big]
    ring
  calc
    (4 * bSerre + qRateC) + bSerre * (Dr : ℝ)
        ≤ (4 * bSerre + qRateC) + bSerre * ((m : ℝ) + (Bclps.Dconst : ℝ)) := add_le_add le_rfl h1
    _ ≤ (4 * bSerre + qRateC) * ((m : ℝ) + 1) + bSerre * ((m : ℝ) + (Bclps.Dconst : ℝ)) :=
        add_le_add h5 le_rfl
    _ ≤ (4 * bSerre + qRateC) * ((m : ℝ) + 1) +
        bSerre * (((Bclps.Dconst : ℝ) + 1) * ((m : ℝ) + 1)) := add_le_add le_rfl h3
    _ = Cm_big * ((m : ℝ) + 1) := hcm.symm

/-- The per-`n` construction (brackets, separation, coefficients, norm).
All "eventual" numeric hypotheses are explicit.  -/
private lemma per_n_data (B Ct Cm : ℝ) (hCmbig : Cm_big ≤ Cm) {n : ℕ}
    (h1n : 1 ≤ n)
    (hN2 : 2 ≤ n - Bclps.Dconst * stepR B n)
    (hr2 : 2 ≤ stepR B n)
    (hRe : enumC0 ≤ stepR B n)
    (hRC : (roots2C : ℝ) ≤ (stepR B n : ℝ))
    (hr3n : stepR B n + 3 ≤ n)
    (hnm2 : 2 ≤ n - mFloor B n)
    (hIE : (n : ℝ) ^ (-Ct) ≤ (rho0 / 3) ^ 2 * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)))
    (hIU : (n : ℝ) ^ (upC + roots2C) * kappaC ^ Bclps.Dconst ≤ (n : ℝ) ^ Ct) :
    EarlyPolynomialData B Ct Cm n := by
  classical
  set m : ℕ := mFloor B n with hm
  set r : ℕ := stepR B n with hr
  set Dr : ℕ := Bclps.Dconst * r with hDr
  set N : ℕ := n - Dr with hN
  set dp : ℕ := Dr - m with hdp
  have hN2' : 2 ≤ N := by
    simpa [hN, hDr, hr] using hN2
  have hr2' : 2 ≤ r := by simpa [hr] using hr2
  have hRe' : enumC0 ≤ r := by simpa [hr] using hRe
  have hRC' : (roots2C : ℝ) ≤ (r : ℝ) := by simpa [hr] using hRC
  have hr3n' : r + 3 ≤ n := by simpa [hr] using hr3n
  have hnm2' : 2 ≤ n - m := by simpa [hm] using hnm2
  have hN1 : 1 ≤ N := by omega
  have hD0 : 0 < Bclps.Dconst := by
    have h := Bclps.Dconst_pos
    omega
  have hdiv1' : Bclps.Dconst * stepR B n ≤ mFloor B n + Bclps.Dconst := by
    have h := (nat_div_bounds (mFloor B n) Bclps.Dconst hD0).1
    simpa [stepR] using h
  have hdiv2' : mFloor B n + 1 ≤ Bclps.Dconst * stepR B n := by
    have h := (nat_div_bounds (mFloor B n) Bclps.Dconst hD0).2
    simpa [stepR] using h
  have hdivA : Bclps.Dconst * r ≤ m + Bclps.Dconst := by
    simpa [hr, hm] using hdiv1'
  have hdivB : m + 1 ≤ Dr := by
    simpa [hDr, hr, hm] using hdiv2'
  have hmDr : m ≤ Dr := by omega
  have hdp1 : 1 ≤ dp := by omega
  have hdpD : dp ≤ Bclps.Dconst := by omega
  have hN2e : 2 ≤ n - Dr := by
    simpa [hN] using hN2'
  have hDrle : Dr ≤ n := by omega
  have hsum : N + Dr = n := by
    simpa [hN] using (Nat.sub_add_cancel hDrle)
  have hAr0 : n - m = (n - Dr) + (Dr - m) := by omega
  have hAr : n - m = N + dp := by
    simpa [hN, hdp] using hAr0
  have hn2 : 2 ≤ n := by omega
  have hn1' : 1 ≤ n := h1n
  -- constants provided by the modules
  rcases Classical.choose_spec (prune_roots) with ⟨hCP1, hPR⟩
  rcases Classical.choose_spec (weighted_lower_bound) with ⟨hLpos, hwlb⟩
  rcases Classical.choose_spec (weighted_norm_bound) with ⟨hUpos, hwub⟩
  rcases Classical.choose_spec (comp_Q_roots2) with ⟨hC2pos, hC21, hcq2⟩
  rcases Classical.choose_spec (comp_q_roots_sorted) with ⟨hC0en2, hC0ens⟩
  rcases Classical.choose_spec (extPoint_margin) with ⟨hcQpos, hcQ⟩
  have hpruneN := hPR N hN2'
  rcases hpruneN with ⟨hfacP, hmemP, hmonoP, hspaceP, hmargP⟩
  have hPmon : (prunePoly N).Monic := prunePoly_monic hN1
  have hPdeg : (prunePoly N).natDegree = N := prunePoly_natDegree hN1
  -- complementary polynomial Q
  rcases (comp_q r N hr2' hN1 hPmon hPdeg) with ⟨Ccomp, hCcomp0, hcrest⟩
  rcases hcrest with ⟨T, Q0, Q1, Q, eps, NN, hq⟩
  rcases hq with ⟨hTmon, hTdeg, hTclose, hTsm, hTforce, hQ0eq, hQ1eq, hQeq,
      heps, hNN0, hNNle, hQmon, hQdeg, hevenPQ, hpigeon, hsupC⟩
  rcases (hcq2 r hRC' hr2' T Q0 Q1 Q eps NN hTmon hTdeg hTclose hTsm hQ0eq
      hQ1eq hQeq heps hNN0 hNNle) with ⟨hsupQ, hsupQd, hgrowQ⟩
  rcases (hC0ens r hRe' T Q0 Q1 Q eps NN hTmon hTdeg hTsm hQ0eq hQ1eq hQeq
      heps hNN0 hNNle hQmon hQdeg) with ⟨hsqfQ, hrootCQ, hbs⟩
  rcases hbs with ⟨β, gL, gR, hb⟩
  rcases hb with ⟨hβ1, hβ2, hβ3, hβ4, hβ5, hβ6, hβ7, hβ8⟩
  -- the separation parameter
  let s1 : ℝ := (((pruneC : ℝ) * ((N + 2 : ℕ) : ℝ))⁻¹) ^ 2
  let s2 : ℝ := ((r : ℝ) + 3) ^ (-roots2C)
  let s3 : ℝ := (N : ℝ)⁻¹ * (C2val⁻¹) * ((r : ℝ) + 3) ^ (-roots2C)
  let s4 : ℝ := cQext / ((r : ℝ) + 3) ^ 2
  let rho : ℝ := min (min s1 s2) (min s3 s4)
  let delta : ℝ := rho / 3
  have hs1pos : 0 < s1 := by
    dsimp [s1]
    have hprune : 0 < pruneC := lt_of_lt_of_le (by norm_num) hCP1
    have hN2R : 0 < ((N + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N + 2)
    positivity
  have hs2pos : 0 < s2 := by
    dsimp [s2]
    have hr3 : 0 < (r : ℝ) + 3 := by linarith
    exact Real.rpow_pos_of_pos hr3 (-roots2C)
  have hs3pos : 0 < s3 := by
    dsimp [s3]
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    exact mul_pos (mul_pos (inv_pos.mpr hNpos) (inv_pos.mpr C2val_pos)) hs2pos
  have hs4pos : 0 < s4 := by
    dsimp [s4]
    exact div_pos hcQpos (pow_pos (by linarith : (0 : ℝ) < (r : ℝ) + 3) 2)
  have hρpos : 0 < rho := by
    dsimp [rho]
    exact lt_min (lt_min hs1pos hs2pos) (lt_min hs3pos hs4pos)
  have hδpos : 0 < delta := by
    dsimp [delta]
    positivity
  have hρ_le_s1 : rho ≤ s1 := by
    dsimp [rho]
    exact le_trans (min_le_left (min s1 s2) (min s3 s4)) (min_le_left s1 s2)
  have hρ_le_s2 : rho ≤ s2 := by
    dsimp [rho]
    exact le_trans (min_le_left (min s1 s2) (min s3 s4)) (min_le_right s1 s2)
  have hρ_le_s3 : rho ≤ s3 := by
    dsimp [rho]
    exact le_trans (min_le_right (min s1 s2) (min s3 s4)) (min_le_left s3 s4)
  have hρ_le_s4 : rho ≤ s4 := by
    dsimp [rho]
    exact le_trans (min_le_right (min s1 s2) (min s3 s4)) (min_le_right s3 s4)
  -- δ is bounded below by `(rho0/3)·n^{-(roots2C+3)}` (eventual bound used
  -- to close the endpoint inequalities)
  have hNL : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : N ≤ n)
  have hr3le : (r : ℝ) + 3 ≤ (n : ℝ) := by exact_mod_cast hr3n'
  have hNposR : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hr3ge1 : (1 : ℝ) ≤ (r : ℝ) + 3 := by linarith
  have hnge1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1'
  have hprune0 : 0 < pruneC := lt_of_lt_of_le (by norm_num) hCP1
  have hnpos2 : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnge1R
  have hz2 : -(roots2C + 3) ≤ -(2 : ℝ) := by
    have h21 : (1 : ℝ) ≤ roots2C := hC21
    have h2 : (2 : ℝ) ≤ roots2C + 3 := by nlinarith
    nlinarith
  have hzCq : -(roots2C + 3) ≤ -roots2C := by nlinarith
  have hzCq1 : -(roots2C + 3) ≤ -(1 + roots2C) := by nlinarith
  have hpow2leF : (n : ℝ) ^ (-(roots2C + 3)) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hnge1R hz2
  have hpowCqleF : (n : ℝ) ^ (-(roots2C + 3)) ≤ (n : ℝ) ^ (-roots2C) :=
    Real.rpow_le_rpow_of_exponent_le hnge1R hzCq
  have hpowCq1leF : (n : ℝ) ^ (-(roots2C + 3)) ≤ (n : ℝ) ^ (-(1 + roots2C)) :=
    Real.rpow_le_rpow_of_exponent_le hnge1R hzCq1
  have hcomp1 : (1 / (4 * pruneC ^ 2)) * (n : ℝ) ^ (-(roots2C + 3)) ≤ s1 := by
    have hN2le : (N : ℝ) + 2 ≤ 2 * (n : ℝ) := by
      have hnat : N + 2 ≤ 2 * n := by omega
      exact_mod_cast hnat
    have hAm : pruneC * ((N : ℝ) + 2) ≤ pruneC * (2 * (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hN2le hprune0.le
    have hApos : 0 < pruneC * ((N : ℝ) + 2) := by positivity
    have hBpos : 0 < pruneC * (2 * (n : ℝ)) := by positivity
    have hBleA : (pruneC * (2 * (n : ℝ)))⁻¹ ≤ (pruneC * ((N : ℝ) + 2))⁻¹ :=
      (inv_le_inv₀ hBpos hApos).mpr hAm
    have hSq : ((pruneC * (2 * (n : ℝ)))⁻¹) ^ 2 ≤ ((pruneC * ((N : ℝ) + 2))⁻¹) ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hBpos.le) hBleA 2
    have hB2 : ((pruneC * (2 * (n : ℝ)))⁻¹) ^ 2 =
        (1 / (4 * pruneC ^ 2)) * (n : ℝ) ^ (-(2 : ℝ)) := by
      rw [rpow_neg_two hnpos2]
      field_simp
      ring
    calc
      (1 / (4 * pruneC ^ 2)) * (n : ℝ) ^ (-(roots2C + 3))
          ≤ (1 / (4 * pruneC ^ 2)) * (n : ℝ) ^ (-(2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hpow2leF (by positivity)
      _ = ((pruneC * (2 * (n : ℝ)))⁻¹) ^ 2 := hB2.symm
      _ ≤ ((pruneC * ((N : ℝ) + 2))⁻¹) ^ 2 := hSq
      _ = s1 := by
          dsimp [s1]
          congr 2
          have hcast : ((N + 2 : ℕ) : ℝ) = (N : ℝ) + 2 := by norm_num
          rw [hcast]
  have hcomp2 : 1 * (n : ℝ) ^ (-(roots2C + 3)) ≤ s2 := by
    have h1 : (n : ℝ) ^ (-(roots2C + 3)) ≤ ((r : ℝ) + 3) ^ (-roots2C) := by
      calc
        (n : ℝ) ^ (-(roots2C + 3)) ≤ (n : ℝ) ^ (-roots2C) := hpowCqleF
        _ ≤ ((r : ℝ) + 3) ^ (-roots2C) :=
          rpow_neg_ge_of_le hr3ge1 hr3le (le_of_lt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hC21))
    simpa [s2] using h1
  have hpowm1 : (n : ℝ) ^ (-roots2C) ≤ s2 := by
    calc
      (n : ℝ) ^ (-roots2C) ≤ ((r : ℝ) + 3) ^ (-roots2C) :=
        rpow_neg_ge_of_le hr3ge1 hr3le (le_of_lt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hC21))
      _ = s2 := by rfl
  have hcomp3 : (C2val⁻¹) * (n : ℝ) ^ (-(roots2C + 3)) ≤ s3 := by
    have hstep1 : (n : ℝ) ^ (-(roots2C + 3)) ≤ (n : ℝ)⁻¹ * (n : ℝ) ^ (-roots2C) := by
      calc
        (n : ℝ) ^ (-(roots2C + 3)) ≤ (n : ℝ) ^ (-(1 + roots2C)) := hpowCq1leF
        _ = (n : ℝ) ^ (-(1 : ℝ)) * (n : ℝ) ^ (-roots2C) := by
            rw [← Real.rpow_add hnpos2]
            congr 1
            ring
        _ = (n : ℝ)⁻¹ * (n : ℝ) ^ (-roots2C) := by
            rw [Real.rpow_neg_one]
    have hstep2 : (n : ℝ)⁻¹ * (n : ℝ) ^ (-roots2C) ≤ (N : ℝ)⁻¹ * s2 := by
      have hNn : (n : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ := by
        exact (inv_le_inv₀ (by positivity : 0 < (n : ℝ)) (by positivity : 0 < (N : ℝ))).2 hNL
      have h1 : (n : ℝ)⁻¹ * (n : ℝ) ^ (-roots2C) ≤ (n : ℝ)⁻¹ * s2 := by
        exact mul_le_mul_of_nonneg_left hpowm1 (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)
      calc
        (n : ℝ)⁻¹ * (n : ℝ) ^ (-roots2C) ≤ (n : ℝ)⁻¹ * s2 := h1
        _ ≤ (N : ℝ)⁻¹ * s2 := by
            exact mul_le_mul_of_nonneg_right hNn (by positivity : (0 : ℝ) ≤ s2)
    have hmain : (n : ℝ) ^ (-(roots2C + 3)) ≤ (N : ℝ)⁻¹ * s2 := le_trans hstep1 hstep2
    calc
      (C2val⁻¹) * (n : ℝ) ^ (-(roots2C + 3)) ≤ (C2val⁻¹) * ((N : ℝ)⁻¹ * s2) := by
          exact mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr (le_of_lt C2val_pos))
      _ = s3 := by
          dsimp [s3]
          ring
  have hcomp4 : cQext * (n : ℝ) ^ (-(roots2C + 3)) ≤ s4 := by
    have hmain4 : (n : ℝ) ^ (-(2 : ℝ)) ≤ (((r : ℝ) + 3) ^ 2)⁻¹ := by
      rw [rpow_neg_two hnpos2]
      rw [inv_pow]
      have hsq : ((r : ℝ) + 3) ^ 2 ≤ (n : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (r : ℝ) + 3) hr3le 2
      exact (inv_le_inv₀ (by positivity : 0 < (n : ℝ) ^ 2) (by positivity : 0 < ((r : ℝ) + 3) ^ 2)).mpr hsq
    calc
      cQext * (n : ℝ) ^ (-(roots2C + 3))
          ≤ cQext * (n : ℝ) ^ (-(2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hpow2leF (le_of_lt hcQpos)
      _ ≤ cQext * ((((r : ℝ) + 3) ^ 2)⁻¹) := by
              exact mul_le_mul_of_nonneg_left hmain4 (le_of_lt hcQpos)
      _ = s4 := by
          dsimp [s4]
          ring
  have hδLB : (rho0 / 3) * (n : ℝ) ^ (-(roots2C + 3)) ≤ delta := by
    let t : ℝ := (n : ℝ) ^ (-(roots2C + 3))
    have ht0 : 0 ≤ t := by
      dsimp [t]
      positivity
    have hc1 : rho0 ≤ 1 / (4 * pruneC ^ 2) := (rho0_le_candidates).1
    have hc2 : rho0 ≤ 1 := (rho0_le_candidates).2.1
    have hc3 : rho0 ≤ C2val⁻¹ := (rho0_le_candidates).2.2.1
    have hc4 : rho0 ≤ cQext := (rho0_le_candidates).2.2.2
    have h1 : rho0 * t ≤ s1 := by
      calc
        rho0 * t ≤ (1 / (4 * pruneC ^ 2)) * t := mul_le_mul_of_nonneg_right hc1 ht0
        _ ≤ s1 := by simpa [t] using hcomp1
    have h2 : rho0 * t ≤ s2 := by
      calc
        rho0 * t ≤ 1 * t := mul_le_mul_of_nonneg_right hc2 ht0
        _ ≤ s2 := by simpa [t] using hcomp2
    have h3 : rho0 * t ≤ s3 := by
      calc
        rho0 * t ≤ (C2val⁻¹) * t := mul_le_mul_of_nonneg_right hc3 ht0
        _ ≤ s3 := by simpa [t] using hcomp3
    have h4 : rho0 * t ≤ s4 := by
      calc
        rho0 * t ≤ cQext * t := mul_le_mul_of_nonneg_right hc4 ht0
        _ ≤ s4 := by simpa [t] using hcomp4
    have hρt : rho0 * t ≤ rho := by
      dsimp [rho]
      exact le_min (le_min h1 h2) (le_min h3 h4)
    calc
      (rho0 / 3) * t = (rho0 * t) / 3 := by ring
      _ ≤ rho / 3 := div_le_div_of_nonneg_right hρt (by norm_num)
      _ = delta := rfl
  have hκge1m : (1 : ℝ) ≤ kappaC ^ m := by
    exact one_le_pow₀ (le_of_lt kappaC_gt_one)
  have hκDr_m : kappaC ^ m ≤ kappaC ^ Dr := by
    exact pow_le_pow_right₀ (le_of_lt kappaC_gt_one) (by omega : m ≤ Dr)
  have hκdpD : kappaC ^ dp ≤ kappaC ^ Bclps.Dconst := by
    exact pow_le_pow_right₀ (le_of_lt kappaC_gt_one) (by omega : dp ≤ Bclps.Dconst)
  have hκpos : 0 < kappaC := lt_trans zero_lt_one kappaC_gt_one
  have hκmpos : 0 < kappaC ^ m := pow_pos hκpos m
  have hκDrpos : 0 < kappaC ^ Dr := pow_pos hκpos Dr
  -- Q-Q and cross and gamma separations
  have hβmonoDr : ∀ l l' : Fin Dr, l.val < l'.val → β l < β l' := hβ6
  -- roots of P̃ evaluate to zero
  have hPevalγ : ∀ i : Fin N, (prunePoly N).eval (gammaRoot N i) = 0 := by
    intro i
    rw [hfacP]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hsepQQ : ∀ l l' : Fin Dr, l.val < l'.val → rho ≤ β l' - β l := by
    intro l l' hll'
    by_contra h
    have hlt : β l' - β l < s2 := lt_of_lt_of_le (lt_of_not_ge h) hρ_le_s2
    have hpos : 0 < β l' - β l := sub_pos.mpr (hβ6 l l' hll')
    have habs : |β l' - β l| = β l' - β l := abs_of_pos hpos
    have hle : |β l' - β l| ≤ s2 := by
      simpa [habs] using (le_of_lt hlt)
    have hg := hgrowQ (β l) (hβ2 l) (β l') hle
    have h0 : |Q.eval (β l')| = 0 := by
      rw [hβ2 l']
      exact abs_zero
    have habs2 : 0 < |β l' - β l| := by
      rwa [habs]
    have hpos2 : 0 < s2 * kappaC ^ Dr * |β l' - β l| := by
      exact mul_pos (mul_pos hs2pos hκDrpos) habs2
    rw [h0] at hg
    exact (not_le_of_gt hpos2) hg
  have hsepGQ : ∀ i : Fin N, ∀ l : Fin Dr, rho ≤ |gammaRoot N i - β l| := by
    intro i l
    have hQγ : |Q.eval (gammaRoot N i)| ≥ (N : ℝ)⁻¹ * (C2val⁻¹) * kappaC ^ Dr := by
      have hh := hpigeon (gammaRoot N i) (hPevalγ i)
      simpa [← hDr] using hh
    have hγIcc : gammaRoot N i ∈ Set.Icc aSerre bSerre :=
      ⟨le_of_lt (hmemP i).1, le_of_lt (hmemP i).2⟩
    have hβIcc : β l ∈ Set.Icc aSerre bSerre :=
      ⟨le_of_lt (hβ7 l).1, le_of_lt (hβ7 l).2⟩
    have hLip := abs_eval_sub_le_supNorm_deriv Q (gammaRoot N i) hγIcc (β l) hβIcc
    have hQγβ : |Q.eval (gammaRoot N i) - Q.eval (β l)| = |Q.eval (gammaRoot N i)| := by
      rw [hβ2 l, sub_zero]
    have hBpos : 0 < ((r : ℝ) + 3) ^ roots2C := by
      exact Real.rpow_pos_of_pos (by linarith : 0 < (r : ℝ) + 3) roots2C
    have hA : (N : ℝ)⁻¹ * (C2val⁻¹) ≤ ((r : ℝ) + 3) ^ roots2C * |gammaRoot N i - β l| := by
      have h1 : (N : ℝ)⁻¹ * (C2val⁻¹) * kappaC ^ Dr ≤
          ((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr * |gammaRoot N i - β l| := by
        calc
          (N : ℝ)⁻¹ * (C2val⁻¹) * kappaC ^ Dr ≤ |Q.eval (gammaRoot N i)| := hQγ
          _ = |Q.eval (gammaRoot N i) - Q.eval (β l)| := hQγβ.symm
          _ ≤ DivLinear.supNorm Q.derivative * |gammaRoot N i - β l| := hLip
          _ ≤ ((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr * |gammaRoot N i - β l| := by
              have h2 : DivLinear.supNorm Q.derivative * |gammaRoot N i - β l| ≤
                  (((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr) * |gammaRoot N i - β l| := by
                  exact mul_le_mul_of_nonneg_right hsupQd (abs_nonneg _)
              simpa [mul_assoc] using h2
      have hκne : kappaC ^ Dr ≠ 0 := pow_ne_zero Dr hκpos.ne'
      calc
        (N : ℝ)⁻¹ * (C2val⁻¹) = ((N : ℝ)⁻¹ * (C2val⁻¹) * kappaC ^ Dr) * (kappaC ^ Dr)⁻¹ := by
            field_simp [hκne]
        _ ≤ ((((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr) * |gammaRoot N i - β l|) * (kappaC ^ Dr)⁻¹ := by
            simpa [mul_assoc] using (mul_le_mul_of_nonneg_right h1
              (inv_nonneg.mpr (le_of_lt hκDrpos)))
        _ = ((r : ℝ) + 3) ^ roots2C * |gammaRoot N i - β l| := by
            field_simp [hκne]
    have hA2 : (N : ℝ)⁻¹ * (C2val⁻¹) * (((r : ℝ) + 3) ^ roots2C)⁻¹ ≤ |gammaRoot N i - β l| := by
      have h := mul_le_mul_of_nonneg_right hA (inv_nonneg.mpr hBpos.le)
      calc
        (N : ℝ)⁻¹ * (C2val⁻¹) * (((r : ℝ) + 3) ^ roots2C)⁻¹
            ≤ (((r : ℝ) + 3) ^ roots2C * |gammaRoot N i - β l|) * (((r : ℝ) + 3) ^ roots2C)⁻¹ := by
                simpa [mul_assoc] using h
        _ = |gammaRoot N i - β l| := by
            field_simp [hBpos.ne']
    have hBinveq : ((r : ℝ) + 3) ^ (-roots2C) = (((r : ℝ) + 3) ^ roots2C)⁻¹ := by
      exact Real.rpow_neg (by positivity : 0 ≤ (r : ℝ) + 3) roots2C
    have hs3eq : s3 = (N : ℝ)⁻¹ * (C2val⁻¹) * (((r : ℝ) + 3) ^ roots2C)⁻¹ := by
      dsimp [s3]
      rw [hBinveq]
    calc
      rho ≤ s3 := hρ_le_s3
      _ = (N : ℝ)⁻¹ * (C2val⁻¹) * (((r : ℝ) + 3) ^ roots2C)⁻¹ := hs3eq
      _ ≤ |gammaRoot N i - β l| := hA2
  have hsepGG : ∀ i j : Fin N, i.val < j.val → rho ≤ gammaRoot N j - gammaRoot N i := by
    intro i j hij
    have hsp := hspaceP i j hij
    exact le_trans hρ_le_s1 hsp
  -- gamma margins and beta margins
  have hgammargL : ∀ i : Fin N, rho ≤ gammaRoot N i - aSerre := by
    intro i
    exact le_trans hρ_le_s1 (hmargP i).1
  have hgammargR : ∀ i : Fin N, rho ≤ bSerre - gammaRoot N i := by
    intro i
    exact le_trans hρ_le_s1 (hmargP i).2
  have hbetamargL : ∀ l : Fin Dr, rho ≤ β l - aSerre := by
    intro l
    have hwin := (hβ4 l).1
    have hc := (hcQ (r + 3) (by omega) (r + 1) (by omega) (by omega)).1
    have hseq : s4 = cQext / (((r + 3 : ℕ) : ℝ) ^ 2) := by
      dsimp [s4]
      congr 1
      norm_num
    have h1 : rho ≤ cQext / (((r + 3 : ℕ) : ℝ) ^ 2) := by
      simpa [hseq] using hρ_le_s4
    have h3 : extPoint (r + 3) (r + 1) - aSerre ≤ β l - aSerre := by
      exact sub_le_sub_right hwin aSerre
    exact le_trans (le_trans h1 hc) h3
  have hbetamargR : ∀ l : Fin Dr, rho ≤ bSerre - β l := by
    intro l
    have hwin := (hβ4 l).2
    have hc := (hcQ (r + 3) (by omega) 1 (by omega) (by omega)).2
    have hseq : s4 = cQext / (((r + 3 : ℕ) : ℝ) ^ 2) := by
      dsimp [s4]
      congr 1
      norm_num
    have h1 : rho ≤ cQext / (((r + 3 : ℕ) : ℝ) ^ 2) := by
      simpa [hseq] using hρ_le_s4
    have h3 : bSerre - extPoint (r + 3) 1 ≤ bSerre - β l := by
      exact sub_le_sub_left hwin (bSerre)
    exact le_trans (le_trans h1 hc) h3
  -- disjointness for the sorted union
  have hdisj : ∀ i : Fin N, ∀ l : Fin Dr, gammaRoot N i ≠ β l := by
    intro i l h
    have hQγ : Q.eval (gammaRoot N i) = 0 := by
      rw [h]
      exact hβ2 l
    have hbig := hpigeon (gammaRoot N i) (hPevalγ i)
    have hzero : |Q.eval (gammaRoot N i)| = 0 := by
      rw [hQγ]
      exact abs_zero
    have hposv : 0 < (N : ℝ)⁻¹ * (C2val⁻¹) * kappaC ^ Dr := by
      exact mul_pos (mul_pos (inv_pos.mpr hNposR) (inv_pos.mpr C2val_pos)) hκDrpos
    rw [hzero] at hbig
    exact (not_le_of_gt hposv) hbig
  rcases (sorted_union (gammaRoot N) β hmonoP hβ6 hdisj) with ⟨α0, hα0mono, hα0cover, hα0fac⟩
  -- transport to Fin n
  let emb : Fin n → Fin (N + Dr) := fun i => ⟨i.val, by omega⟩
  let α : Fin n → ℝ := fun i => α0 (emb i)
  have hcov : ∀ i : Fin n, (∃ k : Fin N, α i = gammaRoot N k) ∨ (∃ l : Fin Dr, α i = β l) := by
    intro i
    have hi := hα0cover (emb i)
    rcases hi with h | h
    · left
      rcases h with ⟨k, hk⟩
      exact ⟨k, by simpa [α] using hk⟩
    · right
      rcases h with ⟨l, hl⟩
      exact ⟨l, by simpa [α] using hl⟩
  have hαab : ∀ i : Fin n, aSerre < α i ∧ α i < bSerre := by
    intro i
    rcases hcov i with h | h
    · rcases h with ⟨k, hk⟩
      rw [hk]
      exact hmemP k
    · rcases h with ⟨l, hl⟩
      rw [hl]
      exact hβ7 l
  have hαmono2 : ∀ i j : Fin n, i.val < j.val → α i < α j := by
    intro i j hij
    have hij' : (emb i).val < (emb j).val := hij
    have hm := hα0mono (emb i) (emb j) hij'
    simpa [α] using hm
  have hαmargL : ∀ i : Fin n, rho ≤ α i - aSerre := by
    intro i
    rcases hcov i with h | h
    · rcases h with ⟨k, hk⟩
      simpa [hk] using hgammargL k
    · rcases h with ⟨l, hl⟩
      simpa [hl] using hbetamargL l
  have hαmargR : ∀ i : Fin n, rho ≤ bSerre - α i := by
    intro i
    rcases hcov i with h | h
    · rcases h with ⟨k, hk⟩
      simpa [hk] using hgammargR k
    · rcases h with ⟨l, hl⟩
      simpa [hl] using hbetamargR l
  have hggAbs : ∀ k k' : Fin N, k ≠ k' → rho ≤ |gammaRoot N k - gammaRoot N k'| := by
    intro k k' hne
    have hval : k.val ≠ k'.val := by
      intro hv
      exact hne (Fin.ext hv)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hsp := hsepGG k k' hlt
      have hpos : 0 < gammaRoot N k' - gammaRoot N k := sub_pos.mpr (hmonoP k k' hlt)
      rw [abs_sub_comm, abs_of_pos hpos]
      exact hsp
    · have hsp := hsepGG k' k hgt
      have hpos : 0 < gammaRoot N k - gammaRoot N k' := sub_pos.mpr (hmonoP k' k hgt)
      rw [abs_of_pos hpos]
      exact hsp
  have hqqAbs : ∀ l l' : Fin Dr, l ≠ l' → rho ≤ |β l - β l'| := by
    intro l l' hne
    have hval : l.val ≠ l'.val := by
      intro hv
      exact hne (Fin.ext hv)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hsp := hsepQQ l l' hlt
      have hpos : 0 < β l' - β l := sub_pos.mpr (hβmonoDr l l' hlt)
      rw [abs_sub_comm, abs_of_pos hpos]
      exact hsp
    · have hsp := hsepQQ l' l hgt
      have hpos : 0 < β l - β l' := sub_pos.mpr (hβmonoDr l' l hgt)
      rw [abs_of_pos hpos]
      exact hsp
  have hαsep : ∀ i j : Fin n, i.val < j.val → rho ≤ α j - α i := by
    intro i j hij
    have hlt : α i < α j := hαmono2 i j hij
    have hpos : 0 < α j - α i := sub_pos.mpr hlt
    rcases hcov i with hi | hi
    · rcases hcov j with hj | hj
      · rcases hi with ⟨ki, hki⟩
        rcases hj with ⟨kj, hkj⟩
        have hne : ki ≠ kj := by
          intro hk
          have : α i = α j := by
            rw [hki, hkj, hk]
          exact (ne_of_lt hlt) this
        have habs := hggAbs ki kj hne
        have hposG : 0 < gammaRoot N kj - gammaRoot N ki := by
          simpa [hki, hkj] using hpos
        have h1 : |gammaRoot N ki - gammaRoot N kj| = gammaRoot N kj - gammaRoot N ki := by
          rw [abs_sub_comm]
          exact abs_of_pos hposG
        rw [hki, hkj, ← h1]
        exact habs
      · rcases hi with ⟨ki, hki⟩
        rcases hj with ⟨lj, hlj⟩
        have habs := hsepGQ ki lj
        have hposG : 0 < β lj - gammaRoot N ki := by
          simpa [hki, hlj] using hpos
        have h1 : |gammaRoot N ki - β lj| = β lj - gammaRoot N ki := by
          rw [abs_sub_comm]
          exact abs_of_pos hposG
        rw [hki, hlj, ← h1]
        exact habs
    · rcases hcov j with hj | hj
      · rcases hi with ⟨li, hli⟩
        rcases hj with ⟨kj, hkj⟩
        have habs := hsepGQ kj li
        have hposG : 0 < gammaRoot N kj - β li := by
          simpa [hli, hkj] using hpos
        have h1 : |gammaRoot N kj - β li| = gammaRoot N kj - β li := by
          exact abs_of_pos hposG
        rw [hkj, hli, ← h1]
        exact habs
      · rcases hi with ⟨li, hli⟩
        rcases hj with ⟨lj, hlj⟩
        have hne : li ≠ lj := by
          intro hl
          have : α i = α j := by
            rw [hli, hlj, hl]
          exact (ne_of_lt hlt) this
        have habs := hqqAbs li lj hne
        have hposB : 0 < β lj - β li := by
          simpa [hli, hlj] using hpos
        have h1 : |β li - β lj| = β lj - β li := by
          rw [abs_sub_comm]
          exact abs_of_pos hposB
        rw [hli, hlj, ← h1]
        exact habs
  have hαAbs : ∀ i j : Fin n, i ≠ j → rho ≤ |α i - α j| := by
    intro i j hne
    have hval : i.val ≠ j.val := by
      intro hv
      exact hne (Fin.ext hv)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hh := hαsep i j hlt
      have hpos : 0 < α j - α i := sub_pos.mpr (hαmono2 i j hlt)
      rw [abs_sub_comm, abs_of_pos hpos]
      exact hh
    · have hh := hαsep j i hgt
      have hpos : 0 < α i - α j := sub_pos.mpr (hαmono2 j i hgt)
      rw [abs_of_pos hpos]
      exact hh
  -- the polynomial and its bracket data
  let P : Polynomial ℝ := prunePoly N * Q
  have hprod0 : P = ∏ j : Fin (N + Dr), (X - C (α0 j)) := by
    dsimp [P]
    rw [hfacP, hβ8]
    exact hα0fac
  have hPfac2 : P = ∏ i : Fin n, (X - C (α i)) := by
    rw [hprod0]
    apply prod_fin_congr (N := N + Dr) hsum (fun j : Fin (N + Dr) => α0 j) (fun i : Fin n => α i)
    intro j
    simp [α, emb]
  have hPmon2 : P.Monic := by
    rw [hPfac2]
    exact Polynomial.monic_prod_of_monic Finset.univ (fun i : Fin n => Polynomial.X - Polynomial.C (α i))
      (by intro i hi; exact Polynomial.monic_X_sub_C (α i))
  have hPdeg2 : P.natDegree = n := by
    rw [hPfac2]
    rw [Polynomial.natDegree_prod_of_monic]
    · simp
    · intro i hi
      exact Polynomial.monic_X_sub_C (α i)
  let x : Fin n → ℝ := fun i => α i - delta
  let y : Fin n → ℝ := fun i => α i + delta
  have hxyIcc : ∀ i : Fin n, aSerre ≤ x i ∧ y i ≤ bSerre := by
    intro i
    have hL := hαmargL i
    have hR := hαmargR i
    constructor
    · dsimp [x]
      have hδρ : delta ≤ rho := by
        dsimp [delta]
        nlinarith [hρpos]
      have hδm : delta ≤ α i - aSerre := le_trans hδρ hL
      linarith
    · dsimp [y]
      have hδρ : delta ≤ rho := by
        dsimp [delta]
        nlinarith [hρpos]
      have hδm : delta ≤ bSerre - α i := le_trans hδρ hR
      linarith
  have hxy : ∀ i : Fin n, x i < y i := by
    intro i
    dsimp [x, y]
    linarith [hδpos]
  have hxαy : ∀ i : Fin n, x i < α i ∧ α i < y i := by
    intro i
    dsimp [x, y]
    constructor <;> linarith [hδpos]
  have hsep2 : ∀ i j : Fin n, i.val < j.val → y i < x j := by
    intro i j hij
    have hs := hαsep i j hij
    dsimp [x, y]
    have hδρ : 2 * delta < rho := by
      dsimp [delta]
      nlinarith [hρpos]
    nlinarith [hs, hδρ]
  have hPne0 : ∀ i : Fin n, P.eval (x i) ≠ 0 ∧ P.eval (y i) ≠ 0 := by
    intro i
    constructor
    · intro hz
      have hP : P.eval (x i) = ∏ j : Fin n, ((x i) - α j) := by
        rw [hPfac2, Polynomial.eval_prod]
        apply Finset.prod_congr rfl
        intro j hj
        simp
      rw [hP] at hz
      rcases (Finset.prod_eq_zero_iff.mp hz) with ⟨j, hj, hzfact⟩
      have hx : x i = α j := sub_eq_zero.mp hzfact
      have hne : i ≠ j := by
        intro heq
        have hx' : x i = α i := by simpa [heq] using hx
        have : delta = 0 := by
          dsimp [x] at hx'
          linarith
        exact (ne_of_gt hδpos) this
      have hsp := hαAbs i j hne
      have hd : |α i - α j| = delta := by
        have hx2 : α i - delta = α j := by
          simpa [x] using hx
        have hd2 : delta = α i - α j := by linarith
        have hαpos : 0 < α i - α j := by linarith
        rw [hd2]
        exact abs_of_pos hαpos
      have hlt : |α i - α j| < rho := by
        rw [hd]
        dsimp [delta]
        nlinarith [hρpos]
      exact (not_lt_of_ge hsp) hlt
    · intro hz
      have hP : P.eval (y i) = ∏ j : Fin n, ((y i) - α j) := by
        rw [hPfac2, Polynomial.eval_prod]
        apply Finset.prod_congr rfl
        intro j hj
        simp
      rw [hP] at hz
      rcases (Finset.prod_eq_zero_iff.mp hz) with ⟨j, hj, hzfact⟩
      have hy : y i = α j := sub_eq_zero.mp hzfact
      have hne : i ≠ j := by
        intro heq
        have hy' : y i = α i := by simpa [heq] using hy
        have : delta = 0 := by
          dsimp [y] at hy'
          linarith
        exact (ne_of_gt hδpos) this
      have hsp := hαAbs i j hne
      have hd : |α i - α j| = delta := by
        have hy2 : α i + delta = α j := by
          simpa [y] using hy
        have hd2 : delta = α j - α i := by linarith
        have hαpos : 0 < α j - α i := by linarith
        rw [hd2]
        rw [abs_sub_comm]
        exact abs_of_pos hαpos
      have hlt : |α i - α j| < rho := by
        rw [hd]
        dsimp [delta]
        nlinarith [hρpos]
      exact (not_lt_of_ge hsp) hlt
  -- weighted endpoint lower bounds
  have hwv : ∀ i : Fin n,
      (weight muSerre (x i)) ^ (n - m) * |P.eval (x i)| ≥ (n : ℝ) ^ (-Ct) * kappaC ^ m ∧
      (weight muSerre (y i)) ^ (n - m) * |P.eval (y i)| ≥ (n : ℝ) ^ (-Ct) * kappaC ^ m := by
    -- shared monoticity facts for the δ²-bound
    have hn1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
    have hNlow : (n : ℝ) ^ (-lowC) ≤ (N : ℝ) ^ (-lowC) := by
      exact rpow_neg_ge_of_le hn1N hNL (le_of_lt hLpos)
    have hr3Cq : (n : ℝ) ^ (-roots2C) ≤ ((r : ℝ) + 3) ^ (-roots2C) := by
      exact rpow_neg_ge_of_le hr3ge1 hr3le (le_of_lt hC2pos)
    let F : ℝ := roots2C + 3
    have hδLB2 : (rho0 / 3) ^ 2 * (n : ℝ) ^ (-(2 * F)) ≤ delta ^ 2 := by
      have hδ : (rho0 / 3) * (n : ℝ) ^ (-F) ≤ delta := by
        simpa [F] using hδLB
      have hnFpos : 0 < (n : ℝ) ^ (-F) := Real.rpow_pos_of_pos hnpos2 (-F)
      have hδnonneg : 0 ≤ (rho0 / 3) * (n : ℝ) ^ (-F) := by
        exact mul_nonneg (le_of_lt (div_pos rho0_pos (by norm_num))) (le_of_lt hnFpos)
      have hsq := pow_le_pow_left₀ hδnonneg hδ 2
      -- (a·b)² = a²·b² and (n^{-F})² = n^{-2F}
      have hrew : ((rho0 / 3) ^ 2) * ((n : ℝ) ^ (-F)) ^ 2 = (rho0 / 3) ^ 2 * (n : ℝ) ^ (-(2 * F)) := by
        rw [sq_rpow (by positivity : 0 < (n : ℝ)) (-F)]
        congr 1
        ring
      have hsq2 : ((rho0 / 3) * (n : ℝ) ^ (-F)) ^ 2 ≤ delta ^ 2 := hsq
      simpa [mul_pow, hrew] using hsq2
    have hE : lowC + roots2C + 2 * F = lowC + 3 * roots2C + 6 := by
      dsimp [F]
      ring
    -- the chain from the per-point bound to the target (end of the proof)
    have htarget : (rho0 / 3) ^ 2 * kappaC ^ m * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) ≥
        (n : ℝ) ^ (-Ct) * kappaC ^ m := by
      have hh := mul_le_mul_of_nonneg_right hIE (by positivity : 0 ≤ kappaC ^ m)
      calc
        (n : ℝ) ^ (-Ct) * kappaC ^ m
            ≤ (rho0 / 3) ^ 2 * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) * kappaC ^ m := hh
        _ = (rho0 / 3) ^ 2 * kappaC ^ m * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) := by ring_nf
    -- the per-point lower bound (stated with internal quantities)
    have hpt : ∀ i : Fin n, ∀ t : ℝ, t ∈ Set.Icc aSerre bSerre →
        |t - α i| = delta →
        (weight muSerre t) ^ (n - m) * |P.eval t| ≥
          (rho0 / 3) ^ 2 * kappaC ^ m * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) := by
      intro i t htIcc hdist
      -- the tail: (A·(r+3)^{-r}·κ^{Dr}·δ²) ≥ (rho0/3)²·κ^m·n^{-E}
      have hchain : (N : ℝ) ^ (-lowC) * ((r : ℝ) + 3) ^ (-roots2C) * kappaC ^ Dr * delta ^ 2 ≤
          (weight muSerre t) ^ (n - m) * |P.eval t| →
          (weight muSerre t) ^ (n - m) * |P.eval t| ≥
            (rho0 / 3) ^ 2 * kappaC ^ m * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) := by
        intro hLB
        have hA : (n : ℝ) ^ (-lowC) ≤ (N : ℝ) ^ (-lowC) := hNlow
        have hB : (n : ℝ) ^ (-roots2C) ≤ ((r : ℝ) + 3) ^ (-roots2C) := hr3Cq
        have hD : (rho0 / 3) ^ 2 * (n : ℝ) ^ (-(2 * F)) ≤ delta ^ 2 := hδLB2
        have hc0 : 0 ≤ kappaC ^ m := by positivity
        have hd0 : 0 ≤ (rho0 / 3) ^ 2 * (n : ℝ) ^ (-(2 * F)) := by positivity
        have ha0 : 0 ≤ (N : ℝ) ^ (-lowC) := by positivity
        have hb0n : 0 ≤ (n : ℝ) ^ (-roots2C) := by positivity
        have hb0 : 0 ≤ ((r : ℝ) + 3) ^ (-roots2C) := by positivity
        have hc0' : 0 ≤ kappaC ^ Dr := by positivity
        have hx := mul_le_mul4 (a := (n : ℝ) ^ (-lowC)) (b := (n : ℝ) ^ (-roots2C))
          (c := kappaC ^ m) (d := (rho0 / 3) ^ 2 * (n : ℝ) ^ (-(2 * F)))
          (a' := (N : ℝ) ^ (-lowC)) (b' := ((r : ℝ) + 3) ^ (-roots2C))
          (c' := kappaC ^ Dr) (d' := delta ^ 2) hA hB hκDr_m hD ha0 hb0 hc0' hd0 hb0n hc0
        have hprod : (n : ℝ) ^ (-lowC) * (n : ℝ) ^ (-roots2C) * kappaC ^ m *
            ((rho0 / 3) ^ 2 * (n : ℝ) ^ (-(2 * F))) ≤
            (N : ℝ) ^ (-lowC) * ((r : ℝ) + 3) ^ (-roots2C) * kappaC ^ Dr * delta ^ 2 := by
          simpa [mul_assoc] using hx
        have hnmerge : (n : ℝ) ^ (-lowC) * (n : ℝ) ^ (-roots2C) * (n : ℝ) ^ (-(2 * F)) =
            (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) := by
          have h1 : (n : ℝ) ^ (-lowC) * (n : ℝ) ^ (-roots2C) = (n : ℝ) ^ (-lowC - roots2C) := by
            rw [← Real.rpow_add (by positivity : 0 < (n : ℝ))]
            ring
          calc
            (n : ℝ) ^ (-lowC) * (n : ℝ) ^ (-roots2C) * (n : ℝ) ^ (-(2 * F))
                = (n : ℝ) ^ (-lowC - roots2C) * (n : ℝ) ^ (-(2 * F)) := by rw [h1]
            _ = (n : ℝ) ^ (-lowC - roots2C - 2 * F) := by
                rw [← Real.rpow_add (by positivity : 0 < (n : ℝ))]
                ring
            _ = (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) := by
                congr 1
                dsimp [F]
                ring
        have hR2 : (rho0 / 3) ^ 2 * kappaC ^ m * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) =
            (rho0 / 3) ^ 2 * (n : ℝ) ^ (-lowC) * (n : ℝ) ^ (-roots2C) * kappaC ^ m *
              ((n : ℝ) ^ (-(2 * F))) := by
          calc
            (rho0 / 3) ^ 2 * kappaC ^ m * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6))
                = (rho0 / 3) ^ 2 * kappaC ^ m * ((n : ℝ) ^ (-lowC) * (n : ℝ) ^ (-roots2C) * (n : ℝ) ^ (-(2 * F))) := by
                    rw [hnmerge]
            _ = (rho0 / 3) ^ 2 * (n : ℝ) ^ (-lowC) * (n : ℝ) ^ (-roots2C) * kappaC ^ m * (n : ℝ) ^ (-(2 * F)) := by ring
        have hR1 : (rho0 / 3) ^ 2 * kappaC ^ m * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) ≤
            (n : ℝ) ^ (-lowC) * (n : ℝ) ^ (-roots2C) * kappaC ^ m * ((rho0 / 3) ^ 2 * (n : ℝ) ^ (-(2 * F))) := by
          rw [hR2]
          exact le_of_eq (by ring)
        have hmid : (rho0 / 3) ^ 2 * kappaC ^ m * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) ≤
            (N : ℝ) ^ (-lowC) * ((r : ℝ) + 3) ^ (-roots2C) * kappaC ^ Dr * delta ^ 2 := by
          exact le_trans hR1 hprod
        exact le_trans hmid hLB
      -- common completion: from ρKept- and |Q|-lower bounds
      have hfinish : delta ≤ rhoKept N t →
          |Q.eval t| ≥ ((r : ℝ) + 3) ^ (-roots2C) * kappaC ^ Dr * delta →
          (weight muSerre t) ^ (n - m) * |P.eval t| ≥
            (rho0 / 3) ^ 2 * kappaC ^ m * (n : ℝ) ^ (-(lowC + 3 * roots2C + 6)) := by
        intro hrho hQlower
        have hwP0 : (N : ℝ) ^ (-lowC) * delta ≤
            (weight muSerre t) ^ (n - m) * |(prunePoly N).eval t| := by
          have h1 : (N : ℝ) ^ (-lowC) * rhoKept N t ≤
              (weight muSerre t) ^ (n - m) * |(prunePoly N).eval t| := by
            have hw := hwlb N hN2' dp hdpD t htIcc
            have h2 : (N : ℝ) ^ (-lowC) * rhoKept N t ≤
                (weight muSerre t) ^ (N + dp) * |(prunePoly N).eval t| := by
              simpa [lowC, muSerre] using hw
            simpa [hAr] using h2
          have hNn0 : 0 ≤ (N : ℝ) ^ (-lowC) := by positivity
          have hm := mul_le_mul_of_nonneg_right hrho hNn0
          calc
            (N : ℝ) ^ (-lowC) * delta ≤ (N : ℝ) ^ (-lowC) * rhoKept N t := by
                simpa [mul_comm] using hm
            _ ≤ (weight muSerre t) ^ (n - m) * |(prunePoly N).eval t| := h1
        have hPabs : |P.eval t| = |(prunePoly N).eval t| * |Q.eval t| := by
          dsimp [P]
          rw [Polynomial.eval_mul]
          exact abs_mul _ _
        have htot1 : (N : ℝ) ^ (-lowC) * delta * |Q.eval t| ≤
            (weight muSerre t) ^ (n - m) * |P.eval t| := by
          have hh := mul_le_mul_of_nonneg_right hwP0 (abs_nonneg (Q.eval t))
          calc
            (N : ℝ) ^ (-lowC) * delta * |Q.eval t|
                ≤ ((weight muSerre t) ^ (n - m) * |(prunePoly N).eval t|) * |Q.eval t| := by
                    simpa [mul_assoc] using hh
            _ = (weight muSerre t) ^ (n - m) * (|(prunePoly N).eval t| * |Q.eval t|) := by ring
            _ = (weight muSerre t) ^ (n - m) * |P.eval t| := by rw [hPabs]
        have hlow : (N : ℝ) ^ (-lowC) * delta * (((r : ℝ) + 3) ^ (-roots2C) * kappaC ^ Dr * delta) ≤
            (N : ℝ) ^ (-lowC) * delta * |Q.eval t| := by
          have h0 : 0 ≤ (N : ℝ) ^ (-lowC) * delta := by positivity
          exact mul_le_mul_of_nonneg_left hQlower h0
        have hLB : (N : ℝ) ^ (-lowC) * ((r : ℝ) + 3) ^ (-roots2C) * kappaC ^ Dr * delta ^ 2 ≤
            (weight muSerre t) ^ (n - m) * |P.eval t| := by
          calc
            (N : ℝ) ^ (-lowC) * ((r : ℝ) + 3) ^ (-roots2C) * kappaC ^ Dr * delta ^ 2
                = (N : ℝ) ^ (-lowC) * delta * (((r : ℝ) + 3) ^ (-roots2C) * kappaC ^ Dr * delta) := by ring
            _ ≤ (N : ℝ) ^ (-lowC) * delta * |Q.eval t| := hlow
            _ ≤ (weight muSerre t) ^ (n - m) * |P.eval t| := htot1
        exact hchain hLB
      rcases hcov i with hi | hi
      · -- P̃-root case (α i is a γ-root)
        rcases hi with ⟨k, hk⟩
        have hγeq : α i = gammaRoot N k := hk
        have hdistG : |t - gammaRoot N k| = delta := by
          simpa [hγeq] using hdist
        -- |Q(t)| ≥ (r+3)^{-roots2C}κ^{Dr}·δ
        have hQγ : |Q.eval (gammaRoot N k)| ≥ (N : ℝ)⁻¹ * (C2val⁻¹) * kappaC ^ Dr := by
          have hh := hpigeon (gammaRoot N k) (hPevalγ k)
          simpa [← hDr] using hh
        have hγIcc : gammaRoot N k ∈ Set.Icc aSerre bSerre :=
          ⟨le_of_lt (hmemP k).1, le_of_lt (hmemP k).2⟩
        have hLip := abs_eval_sub_le_supNorm_deriv Q t htIcc (gammaRoot N k) hγIcc
        have hLips : |Q.eval t - Q.eval (gammaRoot N k)| ≤
            ((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr * delta := by
          calc
            |Q.eval t - Q.eval (gammaRoot N k)| ≤ DivLinear.supNorm Q.derivative * |t - gammaRoot N k| := hLip
            _ ≤ (((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr) * delta := by
                rw [hdistG]
                exact mul_le_mul_of_nonneg_right hsupQd (le_of_lt hδpos)
        have htriQ : |Q.eval t| ≥ |Q.eval (gammaRoot N k)| - |Q.eval t - Q.eval (gammaRoot N k)| := by
          have ht : |Q.eval (gammaRoot N k)| ≤ |Q.eval t| + |Q.eval t - Q.eval (gammaRoot N k)| := by
            have hh0 : |(Q.eval (gammaRoot N k) - Q.eval t) + Q.eval t| ≤
                |Q.eval (gammaRoot N k) - Q.eval t| + |Q.eval t| := abs_add_le _ _
            have hh1 : (Q.eval (gammaRoot N k) - Q.eval t) + Q.eval t = Q.eval (gammaRoot N k) := by ring
            have hh1' : |(Q.eval (gammaRoot N k) - Q.eval t) + Q.eval t| = |Q.eval (gammaRoot N k)| := by
              rw [hh1]
            have hh2 : |Q.eval (gammaRoot N k) - Q.eval t| = |Q.eval t - Q.eval (gammaRoot N k)| := abs_sub_comm _ _
            nlinarith [hh0, hh1', hh2]
          nlinarith [ht]
        have hQ0 : |Q.eval t| ≥
            (N : ℝ)⁻¹ * (C2val⁻¹) * kappaC ^ Dr - ((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr * delta := by
          nlinarith [htriQ, hQγ, hLips]
        let A : ℝ := (N : ℝ)⁻¹ * (C2val⁻¹)
        let B : ℝ := ((r : ℝ) + 3) ^ roots2C
        have hApos : 0 < A := by
          dsimp [A]
          exact mul_pos (inv_pos.mpr hNposR) (inv_pos.mpr C2val_pos)
        have hBge1 : 1 ≤ B := by
          have hb1 : 1 ≤ (r : ℝ) + 3 := hr3ge1
          have hb2 : (1 : ℝ) ^ roots2C ≤ B := by
            dsimp [B]
            exact Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hb1 (le_of_lt hC2pos)
          simpa using hb2
        have hδs3 : delta ≤ A * B⁻¹ / 3 := by
          have h1 : rho ≤ (N : ℝ)⁻¹ * (C2val⁻¹) * ((r : ℝ) + 3) ^ (-roots2C) := hρ_le_s3
          have hBinv : ((r : ℝ) + 3) ^ (-roots2C) = B⁻¹ := by
            dsimp [B]
            exact Real.rpow_neg (by positivity : 0 ≤ (r : ℝ) + 3) roots2C
          have h1' : rho ≤ A * B⁻¹ := by
            simpa [A, hBinv] using h1
          dsimp [delta]
          nlinarith
        have hBδ : B * delta ≤ (1 / 3) * A := by
          have h3 : 0 ≤ B := le_trans zero_le_one hBge1
          have hd := mul_le_mul_of_nonneg_left hδs3 h3
          have hBne : B ≠ 0 := by positivity
          have hc : B * (A * B⁻¹ / 3) = (1 / 3) * A := by
            field_simp [hBne]
          simpa [hc] using hd
        have hBinvδ : B⁻¹ * delta ≤ (1 / 3) * A := by
          have h3 : 0 ≤ B⁻¹ := by positivity
          have hd := mul_le_mul_of_nonneg_left hδs3 h3
          have hbpos : 0 < B⁻¹ := by positivity
          have hb1' : B⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hBge1
          have hBinv2 : B⁻¹ * B⁻¹ ≤ 1 := by
            calc
              B⁻¹ * B⁻¹ ≤ 1 * B⁻¹ := mul_le_mul_of_nonneg_right hb1' (le_of_lt hbpos)
              _ ≤ 1 := by simpa using hb1'
          have hc : B⁻¹ * (A * B⁻¹ / 3) ≤ (1 / 3) * A := by
            calc
              B⁻¹ * (A * B⁻¹ / 3) = (1 / 3) * A * (B⁻¹ * B⁻¹) := by ring
              _ ≤ (1 / 3) * A * 1 := by
                  exact mul_le_mul_of_nonneg_left hBinv2 (by positivity : 0 ≤ (1 / 3) * A)
              _ = (1 / 3) * A := by ring
          exact le_trans hd hc
        have hMain : A - B * delta ≥ B⁻¹ * delta := by
          nlinarith [hBδ, hBinvδ, hApos]
        have hQ1 : |Q.eval t| ≥ B⁻¹ * kappaC ^ Dr * delta := by
          have hz : |Q.eval t| ≥ (A - B * delta) * kappaC ^ Dr := by
            have hw : |Q.eval t| ≥ A * kappaC ^ Dr - B * kappaC ^ Dr * delta := hQ0
            nlinarith
          have hstep : (A - B * delta) * kappaC ^ Dr ≥ B⁻¹ * delta * kappaC ^ Dr := by
            exact mul_le_mul_of_nonneg_right hMain (le_of_lt hκDrpos)
          have h1 : |Q.eval t| ≥ B⁻¹ * delta * kappaC ^ Dr := le_trans hstep hz
          have hcomm : B⁻¹ * delta * kappaC ^ Dr = B⁻¹ * kappaC ^ Dr * delta := by ring
          simpa [hcomm] using h1
        have hQlower : |Q.eval t| ≥ ((r : ℝ) + 3) ^ (-roots2C) * kappaC ^ Dr * delta := by
          have hBinv : ((r : ℝ) + 3) ^ (-roots2C) = B⁻¹ := by
            dsimp [B]
            exact Real.rpow_neg (by positivity : 0 ≤ (r : ℝ) + 3) roots2C
          simpa [hBinv, mul_assoc] using hQ1
        -- ρKept(t) ≥ δ
        have hrho : delta ≤ rhoKept N t := by
          unfold rhoKept
          rw [dif_pos (kept_nonempty (by omega : 1 ≤ N))]
          apply Finset.le_inf' (kept_nonempty (by omega : 1 ≤ N)) (fun u : ℕ => |t - alpha (N + 2) u|)
          intro u hu
          let k0 : Fin N := ⟨u - 2, by
              have hu' : u ∈ Finset.Icc 2 (N + 1) := by simpa [kept] using hu
              rw [Finset.mem_Icc] at hu'
              rcases hu' with ⟨h12, huN⟩
              omega⟩
          have hgamma_eq : gammaRoot N k0 = alpha (N + 2) u := by
            unfold gammaRoot
            congr 1
            have hk0 : k0.val = u - 2 := rfl
            rw [hk0]
            have hu' : u ∈ Finset.Icc 2 (N + 1) := by simpa [kept] using hu
            rw [Finset.mem_Icc] at hu'
            omega
          by_cases hkk : k0 = k
          · rw [← hgamma_eq, hkk, hdistG]
          · have hgg := hggAbs k0 k hkk
            have htr0 : |gammaRoot N k0 - gammaRoot N k| ≤ |gammaRoot N k0 - t| + |t - gammaRoot N k| := by
              simpa [Real.dist_eq] using (dist_triangle (x := gammaRoot N k0) (y := t) (z := gammaRoot N k))
            have h2 : |gammaRoot N k0 - t| = |t - gammaRoot N k0| := abs_sub_comm (gammaRoot N k0) t
            have htri : |t - gammaRoot N k0| ≥ |gammaRoot N k0 - gammaRoot N k| - |t - gammaRoot N k| := by
              nlinarith [htr0, h2]
            have hbig : |t - gammaRoot N k0| ≥ delta := by
              have hgg' : rho ≤ |gammaRoot N k0 - gammaRoot N k| := hgg
              calc
                |t - gammaRoot N k0| ≥ |gammaRoot N k0 - gammaRoot N k| - |t - gammaRoot N k| := htri
                _ ≥ rho - delta := by
                    rw [hdistG]
                    nlinarith [hgg']
                _ ≥ delta := by
                    dsimp [delta]
                    nlinarith [hρpos]
            rw [← hgamma_eq]
            exact hbig
        exact hfinish hrho hQlower
      · -- Q-root case
        rcases hi with ⟨l, hl⟩
        have hdistB : |t - β l| = delta := by
          simpa [hl] using hdist
        have hQl : |Q.eval t| ≥ ((r : ℝ) + 3) ^ (-roots2C) * kappaC ^ Dr * delta := by
          have hle : |t - β l| ≤ ((r : ℝ) + 3) ^ (-roots2C) := by
            have h1 : delta ≤ ((r : ℝ) + 3) ^ (-roots2C) := by
              have hρs2 : rho ≤ ((r : ℝ) + 3) ^ (-roots2C) := hρ_le_s2
              dsimp [delta]
              nlinarith
            rw [hdistB]
            exact h1
          have hg := hgrowQ (β l) (hβ2 l) t hle
          rw [hdistB] at hg
          exact hg
        have hrho : delta ≤ rhoKept N t := by
          unfold rhoKept
          rw [dif_pos (kept_nonempty (by omega : 1 ≤ N))]
          apply Finset.le_inf' (kept_nonempty (by omega : 1 ≤ N)) (fun u : ℕ => |t - alpha (N + 2) u|)
          intro u hu
          let k0 : Fin N := ⟨u - 2, by
              have hu' : u ∈ Finset.Icc 2 (N + 1) := by simpa [kept] using hu
              rw [Finset.mem_Icc] at hu'
              rcases hu' with ⟨h12, huN⟩
              omega⟩
          have hgamma_eq : gammaRoot N k0 = alpha (N + 2) u := by
            unfold gammaRoot
            congr 1
            have hk0 : k0.val = u - 2 := rfl
            rw [hk0]
            have hu' : u ∈ Finset.Icc 2 (N + 1) := by simpa [kept] using hu
            rw [Finset.mem_Icc] at hu'
            omega
          have hsep := hsepGQ k0 l
          have htr0 : |gammaRoot N k0 - β l| ≤ |gammaRoot N k0 - t| + |t - β l| := by
            simpa [Real.dist_eq] using (dist_triangle (x := gammaRoot N k0) (y := t) (z := β l))
          have h2 : |gammaRoot N k0 - t| = |t - gammaRoot N k0| := abs_sub_comm (gammaRoot N k0) t
          have htri : |t - gammaRoot N k0| ≥ |gammaRoot N k0 - β l| - |t - β l| := by
            nlinarith [htr0, h2]
          have htriδ : |t - gammaRoot N k0| ≥ |gammaRoot N k0 - β l| - delta := by
            simpa [hdistB] using htri
          have hbig : |t - gammaRoot N k0| ≥ delta := by
            calc
              |t - gammaRoot N k0| ≥ |gammaRoot N k0 - β l| - delta := htriδ
              _ ≥ rho - delta := by nlinarith [hsep]
              _ ≥ delta := by
                  dsimp [delta]
                  nlinarith [hρpos]
          rw [← hgamma_eq]
          exact hbig
        exact hfinish hrho hQl
    intro i
    have hxIcc : x i ∈ Set.Icc aSerre bSerre := by
      constructor
      · exact (hxyIcc i).1
      · have hyy := hxy i
        have hyb := (hxyIcc i).2
        dsimp [x, y] at hyy
        linarith
    have hdx : |x i - α i| = delta := by
      dsimp [x]
      have : (α i - delta) - α i = -delta := by ring
      rw [this]
      rw [abs_neg]
      exact abs_of_pos hδpos
    have hLx := hpt i (x i) hxIcc hdx
    have hyIcc : y i ∈ Set.Icc aSerre bSerre := by
      constructor
      · have hxx := hxy i
        have hxa := (hxyIcc i).1
        dsimp [x, y] at hxx
        linarith
      · exact (hxyIcc i).2
    have hdy : |y i - α i| = delta := by
      dsimp [y]
      have : (α i + delta) - α i = delta := by ring
      rw [this]
      exact abs_of_pos hδpos
    have hLy := hpt i (y i) hyIcc hdy
    exact ⟨le_trans htarget hLx, le_trans htarget hLy⟩
  -- even coefficient band
  have heven_final : ∀ k : ℕ, n - m ≤ k → k ≤ n - 1 →
      ∃ z : ℤ, P.coeff k = (z : ℝ) ∧ Even z := by
    intro k hklo hkhi
    have hk1 : N + 1 ≤ k := by
      have hnm : n - m = N + dp := hAr
      rw [hnm] at hklo
      omega
    have hk2 : k ≤ N + Dr - 1 := by omega
    rcases (hevenPQ k hk1 hk2) with ⟨z, hz, hE⟩
    refine ⟨z, ?_, hE⟩
    simpa [P] using hz
  -- weighted norm bound
  have hPpart : wnorm (n - m) (prunePoly N) ≤ (n : ℝ) ^ upC := by
    have hw := hwub N hN2' dp hdpD
    have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : N ≤ n)
    have hup0 : 0 ≤ upC := le_of_lt hUpos
    calc
      wnorm (n - m) (prunePoly N) = wnorm (N + dp) (prunePoly N) := by rw [hAr]
      _ ≤ (N : ℝ) ^ upC := hw
      _ ≤ (n : ℝ) ^ upC := by
          exact Real.rpow_le_rpow (by positivity : 0 ≤ (N : ℝ)) hNn hup0
  have hmulP : wnorm (n - m) P ≤ wnorm (n - m) (prunePoly N) * DivLinear.supNorm Q := by
    simpa [P] using (wnorm_mul_le_sup (n - m) (prunePoly N) Q)
  have hstep1 : wnorm (n - m) P ≤ (n : ℝ) ^ upC * (((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr) := by
    exact le_trans hmulP (mul_le_mul hPpart hsupQ (DivLinear.supNorm_nonneg Q)
      (by positivity : 0 ≤ (n : ℝ) ^ upC))
  have hstep2 : wnorm (n - m) P ≤ (n : ℝ) ^ (upC + roots2C) * kappaC ^ Dr := by
    have hbase : ((r : ℝ) + 3) ^ roots2C ≤ (n : ℝ) ^ roots2C := by
      exact Real.rpow_le_rpow (by positivity : 0 ≤ (r : ℝ) + 3) hr3le (le_of_lt hC2pos)
    have hh : (n : ℝ) ^ upC * (((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr) ≤
        (n : ℝ) ^ upC * ((n : ℝ) ^ roots2C * kappaC ^ Dr) := by
      have hbase2 : ((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr ≤ (n : ℝ) ^ roots2C * kappaC ^ Dr :=
        mul_le_mul_of_nonneg_right hbase (by positivity : 0 ≤ kappaC ^ Dr)
      exact mul_le_mul_of_nonneg_left hbase2 (by positivity : 0 ≤ (n : ℝ) ^ upC)
    calc
      wnorm (n - m) P ≤ (n : ℝ) ^ upC * (((r : ℝ) + 3) ^ roots2C * kappaC ^ Dr) := hstep1
      _ ≤ (n : ℝ) ^ upC * ((n : ℝ) ^ roots2C * kappaC ^ Dr) := hh
      _ = (n : ℝ) ^ (upC + roots2C) * kappaC ^ Dr := by
          rw [← mul_assoc]
          congr 1
          rw [← Real.rpow_add (by positivity : 0 < (n : ℝ))]
  have hmdp : m + dp = Dr := by omega
  have hκDr : kappaC ^ Dr = kappaC ^ m * kappaC ^ dp := by
    rw [← hmdp, pow_add]
  have hstep3 : (n : ℝ) ^ (upC + roots2C) * kappaC ^ Dr ≤
      (n : ℝ) ^ (upC + roots2C) * (kappaC ^ Bclps.Dconst * kappaC ^ m) := by
    rw [hκDr]
    have h2 : 0 ≤ (n : ℝ) ^ (upC + roots2C) := by positivity
    have hh : kappaC ^ dp * kappaC ^ m ≤ kappaC ^ Bclps.Dconst * kappaC ^ m :=
      mul_le_mul_of_nonneg_right hκdpD (by positivity : 0 ≤ kappaC ^ m)
    have h3 : kappaC ^ m * kappaC ^ dp ≤ kappaC ^ Bclps.Dconst * kappaC ^ m := by
      simpa [mul_comm] using hh
    exact mul_le_mul_of_nonneg_left h3 h2
  have hnorm_final : wnorm (n - m) P ≤ (n : ℝ) ^ Ct * kappaC ^ m := by
    calc
      wnorm (n - m) P ≤ (n : ℝ) ^ (upC + roots2C) * kappaC ^ Dr := hstep2
      _ ≤ (n : ℝ) ^ (upC + roots2C) * (kappaC ^ Bclps.Dconst * kappaC ^ m) := hstep3
      _ ≤ (n : ℝ) ^ Ct * kappaC ^ m := by
          have hh : (n : ℝ) ^ (upC + roots2C) * kappaC ^ Bclps.Dconst ≤ (n : ℝ) ^ Ct := hIU
          have h2 : 0 ≤ kappaC ^ m := by positivity
          calc
            (n : ℝ) ^ (upC + roots2C) * (kappaC ^ Bclps.Dconst * kappaC ^ m)
                = ((n : ℝ) ^ (upC + roots2C) * kappaC ^ Bclps.Dconst) * kappaC ^ m := by ring
            _ ≤ (n : ℝ) ^ Ct * kappaC ^ m := by
                exact mul_le_mul_of_nonneg_right hh h2
  -- root-mean closeness of the early-ints roots (the mean clause)
  have hb01 : ∀ l : Fin Dr, 0 ≤ β l ∧ β l ≤ bSerre := by
    intro l
    exact ⟨le_trans (le_of_lt aSerre_pos) (le_of_lt (hβ7 l).1), le_of_lt (hβ7 l).2⟩
  have hreidx : (∑ i : Fin n, α i) = ∑ t : Fin (N + Dr), α0 t := by
    exact QuantileSums.sum_reindex_fin (n := n) (N := N + Dr) (hsum := hsum) (g := α0) (α := α)
      (by intro i; simp [α, emb])
  have hsu : (∑ t : Fin (N + Dr), α0 t) =
      (∑ k : Fin N, gammaRoot N k) + (∑ l : Fin Dr, β l) := by
    exact Commons.Combinatorics.Fin.sorted_union_sum_eq (N := N) (M := Dr) (γ := gammaRoot N)
      (β := β) (α := α0) hmonoP hβ6 hdisj hα0mono hα0cover
  have hunion2 : (∑ i : Fin n, α i) =
      (∑ k : Fin N, alpha (N + 2) (k.val + 2)) + (∑ l : Fin Dr, β l) := by
    rw [hreidx, hsu]
    simpa [gammaRoot]
  have humc := union_mean_close (N := N) (Dr := Dr) (n := n) (α := α) (β := β) hN1 hsum hunion2 hb01
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one h1n)
  have hDrn : (Dr : ℝ) ≤ (m : ℝ) + (Bclps.Dconst : ℝ) := by
    exact_mod_cast hdivA
  have hnum_le : (4 * bSerre + qRateC) + bSerre * (Dr : ℝ) ≤ Cm_big * ((m : ℝ) + 1) :=
    Cm_big_absorbs Dr m hDrn
  have hαmean : |((∑ i : Fin n, α i) / (n : ℝ)) - (∫ x : ℝ, x ∂muSerre)|
      ≤ Cm * ((m : ℝ) + 1) / (n : ℝ) := by
    calc
      |((∑ i : Fin n, α i) / (n : ℝ)) - (∫ x : ℝ, x ∂muSerre)|
          ≤ (4 * bSerre + qRateC + bSerre * (Dr : ℝ)) / (n : ℝ) := by
              rw [MuBridge.integral_id_eq.symm]
              exact humc
      _ ≤ Cm_big * ((m : ℝ) + 1) / (n : ℝ) := by
              exact div_le_div_of_nonneg_right hnum_le (le_of_lt hnpos)
      _ ≤ Cm * ((m : ℝ) + 1) / (n : ℝ) := by
              have hle : Cm_big * ((m : ℝ) + 1) ≤ Cm * ((m : ℝ) + 1) :=
                mul_le_mul_of_nonneg_right hCmbig (by positivity : 0 ≤ (m : ℝ) + 1)
              exact div_le_div_of_nonneg_right hle (le_of_lt hnpos)
  -- assemble
  refine ⟨P, hPmon2, hPdeg2, ⟨α, x, y, hPfac2, hαab, hαmono2, hxyIcc, hxy, hxαy,
      hsep2, ?hwvdata, hαmean⟩, heven_final, hnorm_final⟩
  · intro i
    exact ⟨(hwv i).1, (hwv i).2, (hPne0 i).1, (hPne0 i).2⟩



/-- The EVENTUAL per-n core of Proposition early_ints_better. -/
theorem early_ints_eventual (B : ℝ) (hB : 0 < B) :
    ∃ C Cm : ℝ, 3 < C ∧ 0 ≤ Cm ∧ ∀ᶠ n : ℕ in atTop,
      2 ≤ n - mFloor B n → EarlyPolynomialData B C Cm n := by
  classical
  let Ct : ℝ := lowC + upC + 6 * roots2C + 50
  have hL0 : 0 < lowC := (Classical.choose_spec (weighted_lower_bound)).1
  have hU0 : 0 < upC := (Classical.choose_spec (weighted_norm_bound)).1
  have hC21 : 1 ≤ roots2C := (Classical.choose_spec (comp_Q_roots2)).2.1
  have hC3 : 3 < Ct := by
    dsimp [Ct]
    nlinarith
  have hD0 : 0 < Bclps.Dconst := by
    have h := Bclps.Dconst_pos
    omega
  -- the eventual numeric hypotheses
  have evN2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n - Bclps.Dconst * stepR B n := by
    have hlog := eventually_mFloor_le_sub B hB (Bclps.Dconst + 2)
    filter_upwards [hlog, eventually_ge_atTop (Bclps.Dconst + 2)] with n hmsmall hnge
    have hdivn : Bclps.Dconst * stepR B n ≤ mFloor B n + Bclps.Dconst := by
      have h := (nat_div_bounds (mFloor B n) Bclps.Dconst hD0).1
      simpa [stepR] using h
    have hm : mFloor B n + (Bclps.Dconst + 2) ≤ n := by omega
    have h1 : Bclps.Dconst * stepR B n + 2 ≤ n := by omega
    omega
  have evr2 : ∀ᶠ n : ℕ in atTop, 2 ≤ stepR B n := by
    have hm := eventually_mFloor_ge_nat B hB Bclps.Dconst
    filter_upwards [hm] with n hmn
    have hd : 2 * Bclps.Dconst ≤ mFloor B n + Bclps.Dconst := by omega
    have hr : 2 ≤ (mFloor B n + Bclps.Dconst) / Bclps.Dconst := by
      exact (Nat.le_div_iff_mul_le hD0).2 hd
    simpa [stepR] using hr
  have evRe : ∀ᶠ n : ℕ in atTop, enumC0 ≤ stepR B n := by
    have hm := eventually_mFloor_ge_nat B hB (enumC0 * Bclps.Dconst)
    filter_upwards [hm] with n hmn
    have hd : enumC0 * Bclps.Dconst ≤ mFloor B n + Bclps.Dconst := by omega
    have hr : enumC0 ≤ (mFloor B n + Bclps.Dconst) / Bclps.Dconst := by
      exact (Nat.le_div_iff_mul_le hD0).2 hd
    simpa [stepR] using hr
  have evRC : ∀ᶠ n : ℕ in atTop, (roots2C : ℝ) ≤ (stepR B n : ℝ) := by
    let R1 : ℕ := Nat.ceil roots2C
    have hle := eventually_mFloor_ge_nat B hB (R1 * Bclps.Dconst)
    filter_upwards [hle] with n hmn
    have hd : R1 * Bclps.Dconst ≤ mFloor B n + Bclps.Dconst := by omega
    have hr : R1 ≤ (mFloor B n + Bclps.Dconst) / Bclps.Dconst := by
      exact (Nat.le_div_iff_mul_le hD0).2 hd
    have hrR : R1 ≤ stepR B n := by
      simpa [stepR] using hr
    have hceil : roots2C ≤ (R1 : ℝ) := Nat.le_ceil roots2C
    exact le_trans hceil (by exact_mod_cast hrR)
  have evr3n : ∀ᶠ n : ℕ in atTop, stepR B n + 3 ≤ n := by
    have hlog := eventually_mFloor_le_sub B hB (Bclps.Dconst + 3)
    filter_upwards [hlog, eventually_ge_atTop (Bclps.Dconst + 3)] with n hmsmall hnge
    have hdivn : Bclps.Dconst * stepR B n ≤ mFloor B n + Bclps.Dconst := by
      have h := (nat_div_bounds (mFloor B n) Bclps.Dconst hD0).1
      simpa [stepR] using h
    have hs : stepR B n ≤ (mFloor B n + Bclps.Dconst) / Bclps.Dconst := by rfl
    have hs2 : stepR B n ≤ mFloor B n + Bclps.Dconst := by
      have : (mFloor B n + Bclps.Dconst) / Bclps.Dconst ≤ mFloor B n + Bclps.Dconst := by
        exact Nat.div_le_self _ _
      omega
    omega
  have hIEbig : lowC + 3 * roots2C + 6 < Ct := by
    dsimp [Ct]
    nlinarith
  have hIUbig : upC + roots2C < Ct := by
    dsimp [Ct]
    nlinarith
  have evIE := eventually_hIE Ct hIEbig
  have evIU := eventually_hIU Ct hIUbig
  refine ⟨Ct, Cm_big, hC3, Cm_big_nonneg, ?_⟩
  filter_upwards [evN2, evr2, evRe, evRC, evr3n, evIE, evIU, eventually_ge_atTop (2 : ℕ)] with
      n hN2 hr2 hRe hRC hr3n hIE hIU hn2
  intro hnm2
  exact per_n_data B Ct Cm_big le_rfl (by omega : 1 ≤ n) hN2 hr2 hRe hRC hr3n hnm2 hIE hIU

end Submission.EarlyAssembly
