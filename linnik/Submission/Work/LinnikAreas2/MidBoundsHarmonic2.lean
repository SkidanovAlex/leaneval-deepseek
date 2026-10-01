/-
# `LinnikAreas2.MidBoundsHarmonic2` — harmonic mid-range bounds (HB §11, (11.14)), local copy

A copy of `Submission/Work/LinnikAreas/Density4/mid_bounds_harmonic.lean` moved into the
`Work.LinnikAreas2` namespace, with the two elementary logarithmic-telescoping lemmas of the
module `Submission/Work/LinnikAreas/Density4/sum_log_div_le` *copied in* (`log_term_le_aux`,
`sum_log_div_le_aux`).

Why: `sum_log_div_le` is both a module name and (in
`Submission/Work/LinnikAreas/Density4/sum_abs_selLam_le.lean`) a lemma name, so the module
`Work.LinnikAreas.Density4.sum_log_div_le` cannot coexist with the `ZeroDensity/Jutila` branch
which the `θ`-sieve needs.  Copying the two lemmas removes the module from this area's import
cone without touching any other area's files.
-/

import Mathlib
import Submission.Work.LinnikAreas2.PsiDefs2

/-!
# Harmonic mid-range bounds (HB §11, the `log n` and harmonic pieces of (11.14))

Two elementary summation estimates for the range `⌊U⌋ < n ≤ ⌊V⌋`:

* `Σ log(n/U)·wt(n+1)/(n+1) ≤ (log(V/U))²/2 + log(V/U)/V + 1/(2V²)`,
* `Σ wt(n+1)/(n+1) ≤ log(V/U) + 1/V`.

Both use only `wt ≤ 1`, the non-negativity of `log(n/U)` on the range, the harmonic and
logarithmic telescoping bounds `sum_one_div_succ_le_log`, `sum_log_div_le`, and the
elementary inequality `log((V+1)/U) ≤ log(V/U) + 1/V`.
-/

namespace Work.LinnikAreas2

open scoped BigOperators

open Work.LinnikAreas.Density4

/-! ## The copied logarithmic telescoping lemmas

(From `Submission/Work/LinnikAreas/Density4/sum_log_div_le.lean`.) -/


/-- Termwise step of the telescoping comparison: for `1 ≤ U` and `U < n`,
`log(n/U)/(n+1) ≤ (1/2)(log((n+1)/U)² - log(n/U)²)`.
It uses `log(1+1/n) ≥ 2/(2n+1) ≥ 1/(n+1)` and the identity
`(x-y)(x+y) = x²-y²` together with `x ≥ y ≥ 0`. -/
private lemma log_term_le_aux {U : ℝ} (hU : 1 ≤ U) {n : ℕ} (hUn : U < (n:ℝ)) :
    Real.log ((n:ℝ)/U) / ((n:ℝ) + 1)
      ≤ (1/2) * ((Real.log (((n:ℝ)+1)/U))^2 - (Real.log ((n:ℝ)/U))^2) := by
  have hUpos : (0:ℝ) < U := lt_of_lt_of_le one_pos hU
  have hn1 : (1:ℝ) < (n:ℝ) := lt_of_le_of_lt hU hUn
  have hnpos : (0:ℝ) < (n:ℝ) := lt_trans one_pos hn1
  have hlt1 : (1:ℝ) < (n:ℝ)/U := (one_lt_div hUpos).mpr hUn
  have hypos : 0 < Real.log ((n:ℝ)/U) := Real.log_pos hlt1
  have hxge : Real.log ((n:ℝ)/U) ≤ Real.log (((n:ℝ)+1)/U) := by
    apply Real.log_le_log (div_pos hnpos hUpos)
    exact div_le_div_of_nonneg_right (by linarith) hUpos.le
  have hquot : (((n:ℝ)+1)/U) / ((n:ℝ)/U) = 1 + 1/(n:ℝ) := by field_simp
  have hdiff : Real.log (((n:ℝ)+1)/U) - Real.log ((n:ℝ)/U) = Real.log (1 + 1/(n:ℝ)) := by
    rw [← Real.log_div (div_ne_zero (by linarith) (ne_of_gt hUpos))
        (ne_of_gt (div_pos hnpos hUpos))]
    rw [hquot]
  have hlogterm : (1:ℝ)/((n:ℝ)+1) ≤ Real.log (1 + 1/(n:ℝ)) := by
    have hx : 0 ≤ 1/(n:ℝ) := by positivity
    have hA := Real.le_log_one_add_of_nonneg hx
    have hsimp : 2 * (1/(n:ℝ)) / ((1/(n:ℝ)) + 2) = 2/(2*(n:ℝ) + 1) := by field_simp; ring
    rw [hsimp] at hA
    have hcomp : (1:ℝ)/((n:ℝ)+1) ≤ 2/(2*(n:ℝ)+1) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
    linarith
  have hstep : (1:ℝ)/((n:ℝ)+1) ≤ Real.log (((n:ℝ)+1)/U) - Real.log ((n:ℝ)/U) := by
    rw [hdiff]; exact hlogterm
  have hbpos : (0:ℝ) < Real.log (((n:ℝ)+1)/U) - Real.log ((n:ℝ)/U) :=
    lt_of_lt_of_le (by positivity) hstep
  have key : (1/((n:ℝ)+1)) * (2 * Real.log ((n:ℝ)/U))
      ≤ (Real.log (((n:ℝ)+1)/U) - Real.log ((n:ℝ)/U))
        * (Real.log (((n:ℝ)+1)/U) + Real.log ((n:ℝ)/U)) :=
    mul_le_mul hstep (by linarith) (by linarith) hbpos.le
  have key' : 2 * (Real.log ((n:ℝ)/U) / ((n:ℝ)+1))
      ≤ (Real.log (((n:ℝ)+1)/U))^2 - (Real.log ((n:ℝ)/U))^2 := by
    have h2 : (Real.log (((n:ℝ)+1)/U) - Real.log ((n:ℝ)/U))
          * (Real.log (((n:ℝ)+1)/U) + Real.log ((n:ℝ)/U))
        = (Real.log (((n:ℝ)+1)/U))^2 - (Real.log ((n:ℝ)/U))^2 := by ring
    have h3 : (1/((n:ℝ)+1)) * (2 * Real.log ((n:ℝ)/U))
        = 2 * (Real.log ((n:ℝ)/U) / ((n:ℝ)+1)) := by ring
    rwa [h2, h3] at key
  linarith [key']

/-- Elementary bound: `Σ_{⌊U⌋<n≤⌊V⌋} log(n/U)/(n+1) ≤ (1/2)(log((V+1)/U))²`.
(Per-term `log(n/U)/(n+1) ≤ (1/2)(log((n+1)/U)² - log(n/U)²)`, which follows from
`log(1+1/n) ≥ 1/(n+1)`, then telescope.) -/
private lemma sum_log_div_le_aux {U V : ℝ} (hU : 1 ≤ U) (hV : U ≤ V) :
    ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V), Real.log ((n:ℝ)/U) / ((n:ℝ) + 1)
      ≤ (1/2) * (Real.log ((V + 1)/U))^2 := by
  have hUpos : (0:ℝ) < U := lt_of_lt_of_le one_pos hU
  let g : ℕ → ℝ := fun n => (Real.log ((n:ℝ)/U))^2
  set A : ℕ := Nat.floor U + 1 with hA
  set B : ℕ := Nat.floor V with hB
  have hBle : (B:ℝ) ≤ V := by rw [hB]; exact Nat.floor_le (le_trans (le_of_lt hUpos) hV)
  rcases lt_or_ge B A with hBA | hAB
  · rw [Finset.Icc_eq_empty (not_le.mpr hBA)]
    simp only [Finset.sum_empty]
    positivity
  · have hkey : ∀ n ∈ Finset.Icc A B,
        Real.log ((n:ℝ)/U) / ((n:ℝ) + 1) ≤ (1/2) * (g (n+1) - g n) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      have hUn : U < (n:ℝ) := by
        have h1 : U < (Nat.floor U : ℝ) + 1 := Nat.lt_floor_add_one U
        have h2 : (A:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
        have h3 : (A:ℝ) = (Nat.floor U : ℝ) + 1 := by rw [hA]; push_cast; ring
        linarith
      have := log_term_le_aux hU hUn
      simpa only [g, Nat.cast_add, Nat.cast_one] using this
    calc ∑ n ∈ Finset.Icc A B, Real.log ((n:ℝ)/U) / ((n:ℝ) + 1)
        ≤ ∑ n ∈ Finset.Icc A B, (1/2) * (g (n+1) - g n) := Finset.sum_le_sum hkey
      _ = (1/2) * ∑ n ∈ Finset.Icc A B, (g (n+1) - g n) := by rw [Finset.mul_sum]
      _ = (1/2) * (g (B+1) - g A) := by rw [Finset.sum_Icc_sub hAB g]
      _ ≤ (1/2) * g (B+1) := by
            have hgA : 0 ≤ g A := by
              show 0 ≤ (Real.log ((A:ℝ)/U))^2
              exact sq_nonneg _
            linarith
      _ ≤ (1/2) * (Real.log ((V+1)/U))^2 := by
            have hBcast : ((B+1 : ℕ) : ℝ) = (B:ℝ) + 1 := by push_cast; ring
            have hVlt : V < ((B+1 : ℕ) : ℝ) := by
              have h := Nat.lt_floor_add_one V
              rw [hBcast, hB]; exact h
            have hUle : U ≤ ((B+1 : ℕ) : ℝ) := le_trans hV (le_of_lt hVlt)
            have hge1 : (1:ℝ) ≤ ((B+1:ℕ):ℝ)/U := by
              have h := div_le_div_of_nonneg_right hUle hUpos.le
              rwa [div_self (ne_of_gt hUpos)] at h
            have hnonneg : 0 ≤ Real.log (((B+1:ℕ):ℝ)/U) := Real.log_nonneg hge1
            have hmono : ((B+1:ℕ):ℝ)/U ≤ (V+1)/U := by
              apply div_le_div_of_nonneg_right _ hUpos.le
              rw [hBcast]; linarith
            have hlogmono : Real.log (((B+1:ℕ):ℝ)/U) ≤ Real.log ((V+1)/U) :=
              Real.log_le_log (by positivity) hmono
            show (1/2) * (Real.log (((B+1:ℕ):ℝ)/U))^2 ≤ (1/2) * (Real.log ((V+1)/U))^2
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hlogmono 2) (by norm_num)

/-- The elementary logarithm bound `log(1 + 1/V) ≤ 1/V` for `V > 0`. -/
private lemma log_one_add_inv_le {V : ℝ} (hV : 0 < V) : Real.log (1 + 1/V) ≤ 1/V := by
  have hpos : (0:ℝ) < 1 + 1/V := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-- `log((V+1)/U) ≤ log(V/U) + 1/V` for `U, V > 0`. -/
private lemma log_div_add_one_le {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    Real.log ((V + 1)/U) ≤ Real.log (V/U) + 1/V := by
  have hVU : (0:ℝ) < V/U := div_pos hV hU
  have hfac : (V + 1)/U = (V/U) * (1 + 1/V) := by
    field_simp
  rw [hfac, Real.log_mul (ne_of_gt hVU) (by positivity : (1 + 1/V) ≠ 0)]
  linarith [log_one_add_inv_le hV]

/-- `(⌊V⌋+1)/(⌊U⌋+1) ≤ (V+1)/U` for `U, V > 0`. -/
private lemma floor_ratio_le {U V : ℝ} (hU : 0 < U) (hV : 0 < V) :
    ((Nat.floor V : ℝ) + 1) / ((Nat.floor U : ℝ) + 1) ≤ (V + 1)/U := by
  have hgt : U < (Nat.floor U : ℝ) + 1 := Nat.lt_floor_add_one U
  have hle : (Nat.floor V : ℝ) ≤ V := Nat.floor_le hV.le
  have hden : (0:ℝ) < (Nat.floor U : ℝ) + 1 := by linarith
  rw [div_le_div_iff₀ hden hU]
  nlinarith

theorem mid_bounds_harmonic {L U V X : ℝ} (hU : 0 < U) (hX : 0 < X) (hU1 : 1 ≤ U)
    (hUV : U < V) (hAB : Nat.floor U + 1 ≤ Nat.floor V) :
    (∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        Real.log ((n:ℝ)/U) * (wt L U X (n+1)/((n:ℝ)+1))
        ≤ (Real.log (V/U))^2/2 + Real.log (V/U)/V + 1/(2*V^2))
    ∧ (∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        wt L U X (n+1)/((n:ℝ)+1) ≤ Real.log (V/U) + 1/V) := by
  have hV : (0:ℝ) < V := lt_trans hU hUV
  have hA1 : 1 ≤ Nat.floor U + 1 := Nat.succ_le_succ (Nat.zero_le _)
  -- the range `⌊U⌋ < n ≤ n` forces `U < n`, hence `log(n/U) ≥ 1`
  have hlog_nonneg : ∀ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
      0 ≤ Real.log ((n:ℝ)/U) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hUn : U < (n:ℝ) := by
      have h1 : U < (Nat.floor U : ℝ) + 1 := Nat.lt_floor_add_one U
      have h2 : ((Nat.floor U + 1 : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn.1
      push_cast at h2
      linarith
    exact Real.log_nonneg ((one_le_div hU).mpr hUn.le)
  constructor
  · -- The `log n` piece: compare with `Σ log(n/U)/(n+1)` using `wt ≤ 1`.
    have hterm : ∀ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        Real.log ((n:ℝ)/U) * (wt L U X (n+1)/((n:ℝ)+1))
          ≤ Real.log ((n:ℝ)/U) / ((n:ℝ)+1) := by
      intro n hn
      have hdiv : wt L U X (n+1)/((n:ℝ)+1) ≤ 1/((n:ℝ)+1) :=
        div_le_div_of_nonneg_right (wt_le_one hU hX (n+1)) (by positivity)
      have hmain := mul_le_mul_of_nonneg_left hdiv (hlog_nonneg n hn)
      calc Real.log ((n:ℝ)/U) * (wt L U X (n+1)/((n:ℝ)+1))
          ≤ Real.log ((n:ℝ)/U) * (1/((n:ℝ)+1)) := hmain
        _ = Real.log ((n:ℝ)/U) / ((n:ℝ)+1) := by ring
    -- the geometric comparison `(1/2)log((V+1)/U)² ≤ (log(V/U))²/2 + log(V/U)/V + 1/(2V²)`
    have hgeom : (1/2) * (Real.log ((V+1)/U))^2
        ≤ (Real.log (V/U))^2/2 + Real.log (V/U)/V + 1/(2*V^2) := by
      have hb0 : 0 ≤ Real.log ((V+1)/U) :=
        Real.log_nonneg ((one_le_div hU).mpr (by linarith))
      have hb := log_div_add_one_le hU hV
      have hsq : (Real.log ((V+1)/U))^2 ≤ (Real.log (V/U) + 1/V)^2 :=
        pow_le_pow_left₀ hb0 hb 2
      have hident : (1/2) * (Real.log (V/U) + 1/V)^2
          = (Real.log (V/U))^2/2 + Real.log (V/U)/V + 1/(2*V^2) := by
        field_simp
        ring
      nlinarith [hsq, hident]
    calc ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
            Real.log ((n:ℝ)/U) * (wt L U X (n+1)/((n:ℝ)+1))
        ≤ ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
            Real.log ((n:ℝ)/U) / ((n:ℝ)+1) := Finset.sum_le_sum hterm
      _ ≤ (1/2) * (Real.log ((V+1)/U))^2 := sum_log_div_le_aux hU1 hUV.le
      _ ≤ (Real.log (V/U))^2/2 + Real.log (V/U)/V + 1/(2*V^2) := hgeom
  · -- The harmonic piece: compare with `Σ 1/(n+1)`.
    have hterm : ∀ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
        wt L U X (n+1)/((n:ℝ)+1) ≤ (1:ℝ)/((n:ℝ)+1) := by
      intro n _
      exact div_le_div_of_nonneg_right (wt_le_one hU hX (n+1)) (by positivity)
    have hlog := sum_one_div_succ_le_log (A := Nat.floor U + 1) (B := Nat.floor V) hA1
      (by omega)
    have hratio : (((Nat.floor V : ℝ) + 1) / ((Nat.floor U : ℝ) + 1)) ≤ (V + 1)/U :=
      floor_ratio_le hU hV
    calc ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V),
            wt L U X (n+1)/((n:ℝ)+1)
        ≤ ∑ n ∈ Finset.Icc (Nat.floor U + 1) (Nat.floor V), (1:ℝ)/((n:ℝ)+1) :=
          Finset.sum_le_sum hterm
      _ ≤ Real.log (((Nat.floor V : ℝ) + 1) / ((Nat.floor U + 1 : ℕ) : ℝ)) := hlog
      _ ≤ Real.log ((V + 1)/U) := by
          apply Real.log_le_log
          · positivity
          · push_cast
            exact hratio
      _ ≤ Real.log (V/U) + 1/V := log_div_add_one_le hU hV

end Work.LinnikAreas2
