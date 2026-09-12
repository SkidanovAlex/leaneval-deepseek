import Mathlib
import Submission.Reduction
import Submission.Commons.Analysis.Real.refine_param_n0
import Submission.PropRefineExport
import Submission.PropRefine3
import Submission.Ell2Update
import Submission.Ell2Greedy
import Submission.IntFun
import Submission.L2Norm
import Submission.Sec3Tower

open Submission.PropRefinePhase2
open Submission.PropRefineExport
open Submission.Sec3Tower
open Submission.ProdCount
open Submission.L2Norm
open Submission.Reduction

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop refinement: paper-form counting exports

This module presents the phase-2 counting exports of `Submission.Reduction`
(`phase2_export_even` / `phase2_export_odd`) with **paper-style hypotheses**:
the kernel `f` is only required to satisfy the hypotheses of `prop: refinement`
(Tikhomirov 2020, Section 3): nonnegative, `‖f‖₁ ≤ 1`, `log₂`-Lipschitz in the
`ratioLip (μ⁴)`-encoding, window mass `≤ Rt/√n`, sup `≤ L/(N√n)`; the
phase-1 `Cdrop`/`norm₂sq` side conditions are derived internally from the
parameter inequality

`L/(N√n) < Cdrop·(⌊m/2⌋+1)`  (the paper's eq. aux 209823059325-2),

where `m := ⌊εn/2⌋`, `Cdrop := (1/2)·p(1−p)·μ⁶·Rt²/(Nn)`, `μ := mu0 M ε`.

The conclusion bounds the number of tuples (prefix, tail) of length `2m` (even)
or `2m+1` (odd) whose level-`⌊εn⌋` average reaches
`(√2p+2(1−p))·H` in supremum, `H := L/(2N√n)` (which equals the paper's
threshold `(p/√2+1−p)·L/(N√n)`, see `thetaH_eq`).
-/

namespace Submission.RefineExport

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- `‖f‖₂² ≤ S` when `0 ≤ f ≤ S` and `‖f‖₁ ≤ 1`. -/
lemma norm₂sq_le_of_sup_mass {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
    (hf2 : Summable (fun t : ℤ => (f t) ^ 2)) (hf : Summable f) {S : ℝ} (hS0 : 0 ≤ S)
    (hfsup : ∀ t : ℤ, f t ≤ S) (hmass : IntFun.norm₁ f ≤ 1) :
    norm₂sq f ≤ S := by
  have hpt : ∀ t : ℤ, (f t) ^ 2 ≤ S * f t := by
    intro t
    have hf0 : 0 ≤ f t := hfpos t
    have hfl := hfsup t
    calc
      (f t) ^ 2 = f t * f t := by ring
      _ ≤ S * f t := by
        exact mul_le_mul_of_nonneg_right hfl hf0
  have hsum : Summable (fun t : ℤ => S * f t) := Summable.mul_left S hf
  have hle : norm₂sq f ≤ (∑' t : ℤ, S * f t) := by
    dsimp [norm₂sq]
    exact Summable.tsum_le_tsum hpt hf2 hsum
  calc
    norm₂sq f ≤ (∑' t : ℤ, S * f t) := hle
    _ = S * IntFun.norm₁ f := by
      dsimp [IntFun.norm₁]
      rw [tsum_mul_left]
    _ ≤ S * 1 := by
      exact mul_le_mul_of_nonneg_left hmass hS0
    _ = S := by ring

/-- The paper threshold identity `(√2p+2(1−p))·H = (p/√2+1−p)·L/(N√n)`
for `H := L/(2N√n)`. -/
lemma thetaH_eq (p : ℝ) (L : ℝ) (N n : ℕ) (hN1 : 1 ≤ N) (hn1 : 1 ≤ n) :
    (Real.sqrt 2 * p + 2 * (1 - p)) * (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) =
      (p / Real.sqrt 2 + 1 - p) * L / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN1))
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hn1))
  have hs2 : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hsqn : Real.sqrt (n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn1)))
  have hNn : (N : ℝ) * Real.sqrt (n : ℝ) ≠ 0 := mul_ne_zero hN0 hsqn
  field_simp [hNn, hs2]
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    norm_num
  have hx : Real.sqrt 2 * (Real.sqrt 2 * p) = 2 * p := by
    rw [← mul_assoc]
    rw [← pow_two (Real.sqrt 2)]
    rw [hs2sq]
  calc
    Real.sqrt 2 * (Real.sqrt 2 * p + 2 * (1 - p)) * L
        = (Real.sqrt 2 * (Real.sqrt 2 * p) + Real.sqrt 2 * (2 * (1 - p))) * L := by ring
    _ = (2 * p + Real.sqrt 2 * (2 * (1 - p))) * L := by rw [hx]
    _ = 2 * L * (p + Real.sqrt 2 - Real.sqrt 2 * p) := by ring


/-- (paper-form Prop-refinement export, even parity) For every `M ≥ 1`, `ε ∈ (0,1/2]`,
`Rt ≥ 1`, `L0 ≥ 16Rt` and `p ∈ (0,1/2]` there is `n₀` such that for every `n ≥ n₀`,
`1 ≤ N ≤ 2^n`, `16Rt ≤ L`, `m = ⌊εn/2⌋`, and every nonnegative `f` with
`ratioLip (μ⁴)` (`μ := mu0 M ε`), window mass `≤ Rt/√n`, `‖f‖₁ ≤ 1`,
sup `≤ L/(N√n)`, and the parameter inequality
`L/(N√n) < Cdrop·(⌊m/2⌋+1)` (`Cdrop := (1/2)p(1−p)μ⁶Rt²/(Nn)`),
the number of `(2m)`-tuples whose level-`2m` average exceeds the threshold in supremum is
`≤ exp(−Mn)·∏|coords|`.  Interval families `c,d` (prefix) and `loS,hiS` (tail) of
cardinality `≥ N`. -/
theorem refine_export_even {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {Rt L0 : ℝ} (hRt1 : 1 ≤ Rt) (hL016 : 16 * Rt ≤ L0) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ (N : ℕ) (hN1 : 1 ≤ N), (N : ℝ) ≤ (2 : ℝ) ^ n →
    ∀ (L : ℝ) (hL16 : 16 * Rt ≤ L),
    ∀ (m : ℕ), m = Nat.floor (ε * (n : ℝ) / 2) →
    ∀ {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2),
    ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
      (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
      (hfsum : Summable f),
    ∀ (hlip : Ell2Update.ratioLip ((PropRefine3.mu0 M ε) ^ 4) f)
      (hmass : ∀ lo : ℤ, (∑ t ∈ Submission.Ell2Greedy.I0 lo N, f t) ≤ Rt / Real.sqrt (n : ℝ))
      (hnorm1 : IntFun.norm₁ f ≤ 1)
      (hfsupL : ∀ t : ℤ, f t ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ)))
      (hpar : L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
          (((1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * (PropRefine3.mu0 M ε) ^ 6 * Rt ^ 2 /
            ((N : ℝ) * (n : ℝ))) * (((m / 2 + 1 : ℕ) : ℝ)))),
    ∀ {c d loS hiS : Fin m → ℤ}
      (hJlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (c k) (d k)).card : ℝ))
      (hSlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (loS k) (hiS k)).card : ℝ)),
      (((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
          (fun pz : (Fin m → ℤ) × (Fin m → ℤ) =>
            (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) *
                (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) <
              Submission.Sec3Tower.esup
                (lvl f p (2 * m) (pre (catTwo pz) (2 * m) (le_refl (2 * m)))))).card : ℕ) : ℝ) ≤
        Real.exp (-M * (n : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) := by
  classical
  rcases phase2_export_even (M := M) (ε := ε) hM hε0 hε1 with ⟨n₀', hE⟩
  let n₀ : ℕ := max n₀' 1
  refine ⟨n₀, ?_⟩
  intro n hn N hN1 hNpow L hL16 m hm p hp0 hp1 f hfpos hf2 hfsum hlip hmass hnorm1 hfsupL
    hpar c d loS hiS hJlen hSlen
  let μ : ℝ := PropRefine3.mu0 M ε
  let H : ℝ := L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))
  let Cdrop : ℝ := (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
    ((N : ℝ) * (n : ℝ))
  have hn0' : n₀' ≤ n := by
    exact le_trans (le_max_left n₀' 1) hn
  have hn1 : 1 ≤ n := by
    exact le_trans (le_max_right n₀' 1) hn
  have hn1R : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn1)
  have hN1R : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN1)
  have hR0 : 0 < Rt := by linarith
  have hL0 : 0 < L := by
    have h16 : (16 : ℝ) ≤ L := by
      calc
        (16 : ℝ) ≤ 16 * Rt := by nlinarith
        _ ≤ L := hL16
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hμ0 : 0 < μ := by
    dsimp [μ]
    exact mu0_pos M ε
  have hμ1 : μ ≤ 1 / 64 := by
    dsimp [μ]
    exact mu0_le_64 hM hε0 hε1
  have hH0 : 0 < H := by
    dsimp [H]
    have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn1R
    positivity
  have hCdrop0 : 0 ≤ Cdrop := by
    dsimp [Cdrop]
    have h1p : 0 < 1 - (p : ℝ) := by linarith
    have hμ6 : 0 ≤ μ ^ 6 := pow_nonneg hμ0.le 6
    have hnum : 0 ≤ (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 := by
      positivity
    have hden : 0 < (N : ℝ) * (n : ℝ) := mul_pos hN1R hn1R
    exact div_nonneg hnum hden.le
  have hXpos : 0 < (N : ℝ) * Real.sqrt (n : ℝ) := by
    positivity
  have hS0 : 0 ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
    positivity
  have hn2sq : norm₂sq f ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ)) :=
    norm₂sq_le_of_sup_mass hfpos hf2 hfsum hS0 hfsupL hnorm1
  have hsmall : norm₂sq f < Cdrop * (((m / 2 + 1 : ℕ) : ℝ)) := by
    exact lt_of_le_of_lt hn2sq (by simpa [Cdrop, μ] using hpar)
  have hXne : (N : ℝ) * Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hXpos
  have hE2 : 2 * (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) = L / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
    field_simp [hXne]
  have hfsup : ∀ t : ℤ, f t ≤ 2 * H := by
    intro t
    calc
      f t ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ)) := hfsupL t
      _ = 2 * H := by
        dsimp [H]
        exact hE2.symm
  have hμeq : μ = PropRefine3.mu0 M ε := rfl
  have hH : H = L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ))) := rfl
  have hCdrop : Cdrop = (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
    ((N : ℝ) * (n : ℝ)) := rfl
  have hb := hE n hn0' (m := m) hm (p := p) hp0 hp1 (f := f) hfpos hf2 hfsum (Rt := Rt)
    (L := L) hR0 hL16 hL1 (N := N) hN1 hn1 (μ := μ) hμeq hμ0 hμ1 (H := H) hH hCdrop
    hlip hmass hCdrop0 hsmall hnorm1 hfsup hH0 (c := c) (d := d) hJlen (loS := loS)
    (hiS := hiS) hSlen hNpow
  simpa [H, Cdrop, μ] using hb


/-- (paper-form Prop-refinement export, odd parity) For every `M ≥ 1`, `ε ∈ (0,1/2]`,
`Rt ≥ 1`, `L0 ≥ 16Rt` and `p ∈ (0,1/2]` there is `n₀` such that for every `n ≥ n₀`,
`1 ≤ N ≤ 2^n`, `16Rt ≤ L`, `m = ⌊εn/2⌋`, and every nonnegative `f` with
`ratioLip (μ⁴)` (`μ := mu0 M ε`), window mass `≤ Rt/√n`, `‖f‖₁ ≤ 1`,
sup `≤ L/(N√n)`, and the parameter inequality
`L/(N√n) < Cdrop·(⌊m/2⌋+1)` (`Cdrop := (1/2)p(1−p)μ⁶Rt²/(Nn)`),
the number of `(2m+1)`-tuples whose level-`(2m+1)` average exceeds the threshold in supremum is
`≤ exp(−Mn)·∏|coords|`.  Interval families `c,d` (prefix) and `loS,hiS` (tail) of
cardinality `≥ N`. -/
theorem refine_export_odd {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {Rt L0 : ℝ} (hRt1 : 1 ≤ Rt) (hL016 : 16 * Rt ≤ L0) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ (N : ℕ) (hN1 : 1 ≤ N), (N : ℝ) ≤ (2 : ℝ) ^ n →
    ∀ (L : ℝ) (hL16 : 16 * Rt ≤ L),
    ∀ (m : ℕ), m = Nat.floor (ε * (n : ℝ) / 2) →
    ∀ {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2),
    ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
      (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
      (hfsum : Summable f),
    ∀ (hlip : Ell2Update.ratioLip ((PropRefine3.mu0 M ε) ^ 4) f)
      (hmass : ∀ lo : ℤ, (∑ t ∈ Submission.Ell2Greedy.I0 lo N, f t) ≤ Rt / Real.sqrt (n : ℝ))
      (hnorm1 : IntFun.norm₁ f ≤ 1)
      (hfsupL : ∀ t : ℤ, f t ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ)))
      (hpar : L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
          (((1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * (PropRefine3.mu0 M ε) ^ 6 * Rt ^ 2 /
            ((N : ℝ) * (n : ℝ))) * (((m / 2 + 1 : ℕ) : ℝ)))),
    ∀ {c d loS hiS : Fin m → ℤ}
      (hJlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (c k) (d k)).card : ℝ))
      (hSlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (loS k) (hiS k)).card : ℝ)),
    ∀ (cl dl : ℤ),
      ((((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).product
            (Finset.Icc cl dl)).filter
          (fun pza : ((Fin m → ℤ) × (Fin m → ℤ)) × ℤ =>
            (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) *
                (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) <
              Submission.Sec3Tower.esup (lvl f p (2 * m + 1)
                (pre (oddVec (catTwo pza.1) pza.2) (2 * m + 1) (le_refl (2 * m + 1)))))).card : ℕ) : ℝ) ≤
        Real.exp (-M * (n : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) *
          (((Finset.Icc cl dl).card : ℕ) : ℝ) := by
  classical
  rcases phase2_export_odd (M := M) (ε := ε) hM hε0 hε1 with ⟨n₀', hO⟩
  let n₀ : ℕ := max n₀' 1
  refine ⟨n₀, ?_⟩
  intro n hn N hN1 hNpow L hL16 m hm p hp0 hp1 f hfpos hf2 hfsum hlip hmass hnorm1 hfsupL
    hpar c d loS hiS hJlen hSlen cl dl
  let μ : ℝ := PropRefine3.mu0 M ε
  let H : ℝ := L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))
  let Cdrop : ℝ := (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
    ((N : ℝ) * (n : ℝ))
  have hn0' : n₀' ≤ n := by
    exact le_trans (le_max_left n₀' 1) hn
  have hn1 : 1 ≤ n := by
    exact le_trans (le_max_right n₀' 1) hn
  have hn1R : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn1)
  have hN1R : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN1)
  have hR0 : 0 < Rt := by linarith
  have hL0 : 0 < L := by
    have h16 : (16 : ℝ) ≤ L := by
      calc
        (16 : ℝ) ≤ 16 * Rt := by nlinarith
        _ ≤ L := hL16
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hμ0 : 0 < μ := by
    dsimp [μ]
    exact mu0_pos M ε
  have hμ1 : μ ≤ 1 / 64 := by
    dsimp [μ]
    exact mu0_le_64 hM hε0 hε1
  have hH0 : 0 < H := by
    dsimp [H]
    have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn1R
    positivity
  have hCdrop0 : 0 ≤ Cdrop := by
    dsimp [Cdrop]
    have h1p : 0 < 1 - (p : ℝ) := by linarith
    have hμ6 : 0 ≤ μ ^ 6 := pow_nonneg hμ0.le 6
    have hnum : 0 ≤ (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 := by
      positivity
    have hden : 0 < (N : ℝ) * (n : ℝ) := mul_pos hN1R hn1R
    exact div_nonneg hnum hden.le
  have hXpos : 0 < (N : ℝ) * Real.sqrt (n : ℝ) := by
    positivity
  have hS0 : 0 ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
    positivity
  have hn2sq : norm₂sq f ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ)) :=
    norm₂sq_le_of_sup_mass hfpos hf2 hfsum hS0 hfsupL hnorm1
  have hsmall : norm₂sq f < Cdrop * (((m / 2 + 1 : ℕ) : ℝ)) := by
    exact lt_of_le_of_lt hn2sq (by simpa [Cdrop, μ] using hpar)
  have hXne : (N : ℝ) * Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hXpos
  have hE2 : 2 * (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) = L / ((N : ℝ) * Real.sqrt (n : ℝ)) := by
    field_simp [hXne]
  have hfsup : ∀ t : ℤ, f t ≤ 2 * H := by
    intro t
    calc
      f t ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ)) := hfsupL t
      _ = 2 * H := by
        dsimp [H]
        exact hE2.symm
  have hμeq : μ = PropRefine3.mu0 M ε := rfl
  have hH : H = L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ))) := rfl
  have hCdrop : Cdrop = (1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * μ ^ 6 * Rt ^ 2 /
    ((N : ℝ) * (n : ℝ)) := rfl
  have hb := hO n hn0' (m := m) hm (p := p) hp0 hp1 (f := f) hfpos hf2 hfsum (Rt := Rt)
    (L := L) hR0 hL16 hL1 (N := N) hN1 hn1 (μ := μ) hμeq hμ0 hμ1 (H := H) hH hCdrop
    hlip hmass hCdrop0 hsmall hnorm1 hfsup hH0 (c := c) (d := d) hJlen (loS := loS)
    (hiS := hiS) hSlen hNpow cl dl
  simpa [H, Cdrop, μ] using hb



/-- (paper-form Prop refinement, even parity, automatic `n₀`).  Same
conclusion as `refine_export_even`, with the parameter inequality discharged
from `L ≤ L0` for all sufficiently large `n`
(via `Commons.Analysis.Real.refine_param_n0`). -/
theorem prop_refinement_even {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {Rt L0 : ℝ} (hRt1 : 1 ≤ Rt) (hL016 : 16 * Rt ≤ L0)
    {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ (N : ℕ) (hN1 : 1 ≤ N), (N : ℝ) ≤ (2 : ℝ) ^ n →
    ∀ (L : ℝ) (hL16 : 16 * Rt ≤ L) (hLL0 : L ≤ L0),
    ∀ (m : ℕ), m = Nat.floor (ε * (n : ℝ) / 2) →
    ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
      (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
      (hfsum : Summable f),
    ∀ (hlip : Ell2Update.ratioLip ((PropRefine3.mu0 M ε) ^ 4) f)
      (hmass : ∀ lo : ℤ, (∑ t ∈ Submission.Ell2Greedy.I0 lo N, f t) ≤ Rt / Real.sqrt (n : ℝ))
      (hnorm1 : IntFun.norm₁ f ≤ 1)
      (hfsupL : ∀ t : ℤ, f t ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ))),
    ∀ {c d loS hiS : Fin m → ℤ}
      (hJlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (c k) (d k)).card : ℝ))
      (hSlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (loS k) (hiS k)).card : ℝ)),
      (((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).filter
          (fun pz : (Fin m → ℤ) × (Fin m → ℤ) =>
            (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) *
                (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) <
              Submission.Sec3Tower.esup
                (lvl f p (2 * m) (pre (catTwo pz) (2 * m) (le_refl (2 * m)))))).card : ℕ) : ℝ) ≤
        Real.exp (-M * (n : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) := by
  classical
  have hμ0 : 0 < PropRefine3.mu0 M ε := mu0_pos M ε
  have hRt0 : 0 < Rt := by linarith
  have hL000 : 0 ≤ L0 := by
    have h16 : (16 : ℝ) ≤ L0 := by
      calc
        (16 : ℝ) ≤ 16 * Rt := by nlinarith
        _ ≤ L0 := hL016
    linarith
  rcases Commons.Analysis.Real.refine_param_n0 (ε := ε) (p := (p : ℝ))
    (μ := PropRefine3.mu0 M ε) (Rt := Rt) (L0 := L0) hε0 hp0 hp1 hμ0 hRt0 hL000 with ⟨n₀p, hparm⟩
  rcases refine_export_even (M := M) (ε := ε) hM hε0 hε1 (Rt := Rt) (L0 := L0) hRt1 hL016 with ⟨n₂, hE⟩
  refine ⟨max n₀p n₂, ?_⟩
  intro n hn N hN1 hNpow L hL16 hLL0 m hm f hfpos hf2 hfsum hlip hmass hnorm1 hfsupL
    c d loS hiS hJlen hSlen
  have hn₀p : n₀p ≤ n := le_trans (le_max_left n₀p n₂) hn
  have hn₂ : n₂ ≤ n := le_trans (le_max_right n₀p n₂) hn
  have hpar : L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
      (((1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * (PropRefine3.mu0 M ε) ^ 6 * Rt ^ 2 /
        ((N : ℝ) * (n : ℝ))) * (((m / 2 + 1 : ℕ) : ℝ))) :=
    hparm n hn₀p N hN1 m hm L hLL0
  have hb := hE n hn₂ (N := N) hN1 hNpow (L := L) hL16 (m := m) hm (p := p) hp0 hp1 (f := f)
    hfpos hf2 hfsum hlip hmass hnorm1 hfsupL hpar (c := c) (d := d) hJlen (loS := loS)
    (hiS := hiS) hSlen
  simpa using hb


/-- (paper-form Prop refinement, odd parity, automatic `n₀`).  Same
conclusion as `refine_export_odd`, with the parameter inequality discharged
from `L ≤ L0` for all sufficiently large `n`
(via `Commons.Analysis.Real.refine_param_n0`). -/
theorem prop_refinement_odd {M ε : ℝ} (hM : 1 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    {Rt L0 : ℝ} (hRt1 : 1 ≤ Rt) (hL016 : 16 * Rt ≤ L0)
    {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 2) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ (N : ℕ) (hN1 : 1 ≤ N), (N : ℝ) ≤ (2 : ℝ) ^ n →
    ∀ (L : ℝ) (hL16 : 16 * Rt ≤ L) (hLL0 : L ≤ L0),
    ∀ (m : ℕ), m = Nat.floor (ε * (n : ℝ) / 2) →
    ∀ {f : ℤ → ℝ} (hfpos : ∀ t : ℤ, 0 ≤ f t)
      (hf2 : Summable (fun t : ℤ => (f t) ^ 2))
      (hfsum : Summable f),
    ∀ (hlip : Ell2Update.ratioLip ((PropRefine3.mu0 M ε) ^ 4) f)
      (hmass : ∀ lo : ℤ, (∑ t ∈ Submission.Ell2Greedy.I0 lo N, f t) ≤ Rt / Real.sqrt (n : ℝ))
      (hnorm1 : IntFun.norm₁ f ≤ 1)
      (hfsupL : ∀ t : ℤ, f t ≤ L / ((N : ℝ) * Real.sqrt (n : ℝ))),
    ∀ {c d loS hiS : Fin m → ℤ}
      (hJlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (c k) (d k)).card : ℝ))
      (hSlen : ∀ k : Fin m, (N : ℝ) ≤ ((Finset.Icc (loS k) (hiS k)).card : ℝ)),
    ∀ (cl dl : ℤ),
      ((((((prodFinset m (fun j : Fin m => Finset.Icc (c j) (d j))).product
            (prodFinset m (fun j : Fin m => Finset.Icc (loS j) (hiS j)))).product
            (Finset.Icc cl dl)).filter
          (fun pza : ((Fin m → ℤ) × (Fin m → ℤ)) × ℤ =>
            (Real.sqrt 2 * (p : ℝ) + 2 * (1 - (p : ℝ))) *
                (L / (2 * ((N : ℝ) * Real.sqrt (n : ℝ)))) <
              Submission.Sec3Tower.esup (lvl f p (2 * m + 1)
                (pre (oddVec (catTwo pza.1) pza.2) (2 * m + 1) (le_refl (2 * m + 1)))))).card : ℕ) : ℝ) ≤
        Real.exp (-M * (n : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (c j) (d j)).card : ℕ) : ℝ)) *
          (∏ j : Fin m, (((Finset.Icc (loS j) (hiS j)).card : ℕ) : ℝ)) *
          (((Finset.Icc cl dl).card : ℕ) : ℝ) := by
  classical
  have hμ0 : 0 < PropRefine3.mu0 M ε := mu0_pos M ε
  have hRt0 : 0 < Rt := by linarith
  have hL000 : 0 ≤ L0 := by
    have h16 : (16 : ℝ) ≤ L0 := by
      calc
        (16 : ℝ) ≤ 16 * Rt := by nlinarith
        _ ≤ L0 := hL016
    linarith
  rcases Commons.Analysis.Real.refine_param_n0 (ε := ε) (p := (p : ℝ))
    (μ := PropRefine3.mu0 M ε) (Rt := Rt) (L0 := L0) hε0 hp0 hp1 hμ0 hRt0 hL000 with ⟨n₀p, hparm⟩
  rcases refine_export_odd (M := M) (ε := ε) hM hε0 hε1 (Rt := Rt) (L0 := L0) hRt1 hL016 with ⟨n₂, hO⟩
  refine ⟨max n₀p n₂, ?_⟩
  intro n hn N hN1 hNpow L hL16 hLL0 m hm f hfpos hf2 hfsum hlip hmass hnorm1 hfsupL
    c d loS hiS hJlen hSlen cl dl
  have hn₀p : n₀p ≤ n := le_trans (le_max_left n₀p n₂) hn
  have hn₂ : n₂ ≤ n := le_trans (le_max_right n₀p n₂) hn
  have hpar : L / ((N : ℝ) * Real.sqrt (n : ℝ)) <
      (((1 / 2) * (p : ℝ) * (1 - (p : ℝ)) * (PropRefine3.mu0 M ε) ^ 6 * Rt ^ 2 /
        ((N : ℝ) * (n : ℝ))) * (((m / 2 + 1 : ℕ) : ℝ))) :=
    hparm n hn₀p N hN1 m hm L hLL0
  have hb := hO n hn₂ (N := N) hN1 hNpow (L := L) hL16 (m := m) hm (p := p) hp0 hp1 (f := f)
    hfpos hf2 hfsum hlip hmass hnorm1 hfsupL hpar (c := c) (d := d) hJlen (loS := loS)
    (hiS := hiS) hSlen cl dl
  simpa using hb


end Submission.RefineExport