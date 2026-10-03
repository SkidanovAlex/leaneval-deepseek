/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Ulower.gap_local_aux

/-!
# The numerics of the gap-regime localisation window

The elementary numerical estimates comparing the constants `gapNs`, `gapHalf`, `gapR`, `gapA0` of
`Submission/Work/Peluse/Ulower/gap_local_aux.lean` with the scale `N₀` of the mass function and
with the scale `N ^ deg P` of the window.  In the gap regime `2 N ^ deg P < N₀` the window sits
*inside* the support of the mass function.

Recall
* `gapCsum P = ∑_{i ≤ deg P} |coeff_i P|`, `gapC2 P s = 2 (gapCsum P + 1 + s |lc P|) + 4`,
* `gapNs P s N = gapC2 P s * N ^ deg P = 2 * gapHalf P s N`,
* `gapHalf P s N = (gapCsum P + 1 + s |lc P| + 2) * N ^ deg P`,
* `gapR P s N N₀ D = gapRho P s N N₀ D + gapHalf P s N` where
  `gapRho = dSup P N₀ N + gapSig P s D + 2 D |lc P|`, `gapSig P s D = s D |lc P|`,
* `gapA0 P s = 1000 (gapC2 P s + 1) (s + 1) + 1000`.

The main content is `gap_numerics`: in the gap regime `gapR` is dominated by `gapA0 P s * N₀`, the
window scales `gapNs`, `gapHalf` are comparable to `N ^ deg P` up to `gapA0 P s`, and the state
space `2 (gapNs + polySup) + 1` of the *localised* problem is dominated by `gapA0 P s` times the
state space `(2 gapHalf + 1) (2 (N₀ + polySup) + 1)` of the original one -- the estimate that lets
the localisation pay for its extra factor (with slack `2` for the `dSup P N₀ N`-side and slack `8`
for the `L¹`/`L²` bookkeeping of the localisation).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- **The leading coefficient is one of the summed coefficients**: `|lc P| ≤ gapCsum P`. -/
theorem gapCsum_leadingCoeff_le (P : Polynomial ℤ) :
    P.leadingCoeff.natAbs ≤ gapCsum P := by
  have hmem : P.natDegree ∈ Finset.range (P.natDegree + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self _)
  have h := Finset.single_le_sum (f := fun i => (P.coeff i).natAbs)
      (fun i _ => Nat.zero_le _) hmem
  simpa only [gapCsum, Polynomial.leadingCoeff] using h

/-- **The numerical core of the real estimates.**  For `L ≤ c`,
`2 (2c + 2sL + 2L + 6)(6c + 4sL + 13) ≤ A₀ (c + sL + 3)`, where `A₀` is `gapA0` at
`gapCsum = c`, `|lc| = L`.  (Substituting `w = c + sL` and using `L ≤ c`, this is
`2 (4w + 6)(6w + 13) ≤ (2000 w + 7000)(w + 3)`, elementary.) -/
theorem gapA0_core (c L s : ℕ) (hLc : L ≤ c) :
    2 * (2 * c + 2 * s * L + 2 * L + 6) * (6 * c + 4 * s * L + 13)
      ≤ (1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000) * (c + s * L + 3) := by
  set w := c + s * L with hw
  have h1 : 2 * c + 2 * s * L + 2 * L + 6 ≤ 4 * w + 6 := by rw [hw]; nlinarith
  have h2 : 6 * c + 4 * s * L + 13 ≤ 6 * w + 13 := by rw [hw]; nlinarith
  have h3 : 2000 * w + 7000 ≤ 1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) := by
    have heq : 2 * (c + 1 + s * L) + 4 + 1 = 2 * w + 7 := by rw [hw]; ring
    rw [heq]
    have hww : 2000 * w + 7000 = 1000 * (2 * w + 7) := by ring
    rw [hww]
    calc 1000 * (2 * w + 7) = 1000 * (2 * w + 7) * 1 := by ring
      _ ≤ 1000 * (2 * w + 7) * (s + 1) := Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 * (4 * w + 6) * (6 * w + 13) ≤ (2000 * w + 7000) * (w + 3) := by nlinarith
  have h5 : (2000 * w + 7000) * (w + 3)
      ≤ (1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1)) * (w + 3) :=
    Nat.mul_le_mul_right _ h3
  have h6 : w + 3 = c + s * L + 3 := by rw [hw]
  calc 2 * (2 * c + 2 * s * L + 2 * L + 6) * (6 * c + 4 * s * L + 13)
      ≤ 2 * (4 * w + 6) * (6 * w + 13) := by nlinarith [h1, h2]
    _ ≤ (2000 * w + 7000) * (w + 3) := h4
    _ ≤ (1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1)) * (w + 3) := h5
    _ = (1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1)) * (c + s * L + 3) := by rw [h6]
    _ ≤ (1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000) * (c + s * L + 3) :=
        Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- **The range of the localisation centres is dominated by `gapA0 · N₀`** in the gap regime
`2 t < N₀` (`t = N ^ deg P`), with `p ≤ c t` bounding `polySup P N`. -/
theorem gapR_bound (s N₀ t p c L D : ℕ) (hN0 : 2 * t + 1 ≤ N₀) (hDt : D ≤ t)
    (hLc : L ≤ c) (hps : p ≤ c * t) :
    N₀ + p + s * D * L + 2 * (D * L) + (c + 1 + s * L + 2) * t
      ≤ (1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000) * N₀ := by
  have htN : t ≤ N₀ := by omega
  have hD1 : s * (D * L) ≤ s * (t * L) := Nat.mul_le_mul_left s (Nat.mul_le_mul_right L hDt)
  have hD2 : 2 * (D * L) ≤ 2 * (t * L) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right L hDt)
  have hsum : N₀ + p + s * D * L + 2 * (D * L) + (c + 1 + s * L + 2) * t
      ≤ N₀ + (2 * c + 2 * s * L + 2 * L + 3) * t := by nlinarith [hps, hD1, hD2]
  have h3 : (2 * c + 2 * s * L + 2 * L + 3) * t ≤ (2 * c + 2 * s * L + 2 * L + 3) * N₀ :=
    Nat.mul_le_mul_left _ htN
  have h4 : 2 * c + 2 * s * L + 2 * L + 4
      ≤ 1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 := by
    have ha : 1000 * (2 * (c + 1 + s * L) + 4 + 1)
        ≤ 1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) := by
      calc 1000 * (2 * (c + 1 + s * L) + 4 + 1)
          = 1000 * (2 * (c + 1 + s * L) + 4 + 1) * 1 := by ring
        _ ≤ 1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) :=
            Nat.mul_le_mul_left _ (by omega)
    have hb : 2 * c + 2 * s * L + 2 * L + 4 ≤ 1000 * (2 * (c + 1 + s * L) + 4 + 1) := by
      nlinarith [hLc]
    exact le_trans hb (le_trans ha (Nat.le_add_right _ _))
  refine le_trans hsum ?_
  calc N₀ + (2 * c + 2 * s * L + 2 * L + 3) * t
      ≤ N₀ + (2 * c + 2 * s * L + 2 * L + 3) * N₀ := add_le_add (le_refl N₀) h3
    _ = (2 * c + 2 * s * L + 2 * L + 4) * N₀ := by ring
    _ ≤ (1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000) * N₀ :=
        Nat.mul_le_mul_right _ h4

/-- **The localised state space is dominated by `gapA0` times the original one.**  With
`t = N ^ deg P`, `c = gapCsum P`, `L = |lc P|` and `p ≥ polySup P N`,

`8 (2 gapR + 1) (2 (gapNs + p) + 1) ≤ gapA0 · ((2 gapHalf + 1) (2 (N₀ + p) + 1))`.

The slack `8` is what the `L¹`/`L²` bookkeeping of the localisation consumes. -/
theorem gap_real_aux (s N₀ t p c L D : ℕ)
    (hN0 : 2 * t + 1 ≤ N₀) (ht1 : 1 ≤ t) (hDt : D ≤ t) (hLc : L ≤ c) (hps : p ≤ c * t) :
    8 * ((2 * (N₀ + p + s * D * L + 2 * (D * L) + (c + 1 + s * L + 2) * t) + 1 : ℕ) : ℝ)
        * ((2 * ((2 * (c + 1 + s * L) + 4) * t + p) + 1 : ℕ) : ℝ)
      ≤ ((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
        * (((2 * ((c + 1 + s * L + 2) * t) + 1 : ℕ) : ℝ)
           * ((2 * (N₀ + p) + 1 : ℕ) : ℝ)) := by
  have hN0pos : 1 ≤ N₀ := by omega
  have h2t : 2 * t ≤ N₀ := by omega
  have hAsum : 2 * (N₀ + p + s * D * L + 2 * (D * L) + (c + 1 + s * L + 2) * t) + 1
      ≤ (2 * c + 2 * s * L + 2 * L + 6) * N₀ := by
    have hp : 2 * p ≤ 2 * (c * t) := Nat.mul_le_mul_left 2 hps
    have hD1 : s * (D * L) ≤ s * (t * L) := Nat.mul_le_mul_left s (Nat.mul_le_mul_right L hDt)
    have hD2 : 2 * (D * L) ≤ 2 * (t * L) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right L hDt)
    have hstep1 : 2 * (N₀ + p + s * D * L + 2 * (D * L) + (c + 1 + s * L + 2) * t) + 1
        ≤ 2 * N₀ + (4 * c + 4 * s * L + 4 * L + 6) * t + 1 := by nlinarith [hp, hD1, hD2]
    have hstep2 : 2 * N₀ + (4 * c + 4 * s * L + 4 * L + 6) * t + 1
        ≤ (2 * c + 2 * s * L + 2 * L + 6) * N₀ := by
      have hfac : (4 * c + 4 * s * L + 4 * L + 6) * t
          = (2 * c + 2 * s * L + 2 * L + 3) * (2 * t) := by ring
      rw [hfac]
      nlinarith [Nat.mul_le_mul_left (2 * c + 2 * s * L + 2 * L + 3) h2t, hN0pos]
    linarith [hstep1, hstep2]
  have hBsum : 2 * ((2 * (c + 1 + s * L) + 4) * t + p) + 1 ≤ (6 * c + 4 * s * L + 13) * t := by
    have hp2 : 2 * p ≤ 2 * (c * t) := Nat.mul_le_mul_left 2 hps
    calc 2 * ((2 * (c + 1 + s * L) + 4) * t + p) + 1
        = (4 * c + 4 * s * L + 12) * t + 2 * p + 1 := by ring
      _ ≤ (4 * c + 4 * s * L + 12) * t + 2 * (c * t) + 1 := by linarith
      _ = (6 * c + 4 * s * L + 12) * t + 1 := by ring
      _ ≤ (6 * c + 4 * s * L + 13) * t := by
          rw [show (6 * c + 4 * s * L + 13) * t = (6 * c + 4 * s * L + 12) * t + t by ring]
          exact Nat.add_le_add_left ht1 _
  have hcore : 2 * ((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ) * ((6 * c + 4 * s * L + 13 : ℕ) : ℝ)
      ≤ ((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
        * ((c + s * L + 3 : ℕ) : ℝ) := by
    exact_mod_cast gapA0_core c L s hLc
  have hA : ((2 * (N₀ + p + s * D * L + 2 * (D * L) + (c + 1 + s * L + 2) * t) + 1 : ℕ) : ℝ)
      ≤ ((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ) * (N₀ : ℝ) := by
    exact_mod_cast hAsum
  have hB : ((2 * ((2 * (c + 1 + s * L) + 4) * t + p) + 1 : ℕ) : ℝ)
      ≤ ((6 * c + 4 * s * L + 13 : ℕ) : ℝ) * (t : ℝ) := by
    exact_mod_cast hBsum
  have hGH : (2 : ℝ) * ((c + s * L + 3 : ℕ) : ℝ) * (t : ℝ)
      ≤ (((2 * ((c + 1 + s * L + 2) * t) + 1 : ℕ)) : ℝ) := by
    have heq : ((2 * ((c + 1 + s * L + 2) * t) : ℕ) : ℝ)
        = 2 * ((c + s * L + 3 : ℕ) : ℝ) * (t : ℝ) := by
      push_cast
      ring
    have hle : ((2 * ((c + 1 + s * L + 2) * t) : ℕ) : ℝ)
        ≤ (((2 * ((c + 1 + s * L + 2) * t) + 1 : ℕ)) : ℝ) := by
      exact_mod_cast Nat.le_succ _
    linarith [heq, hle]
  have hGN : (2 : ℝ) * (N₀ : ℝ) ≤ (((2 * (N₀ + p) + 1 : ℕ)) : ℝ) := by
    have h : 2 * N₀ ≤ 2 * (N₀ + p) + 1 := by omega
    exact_mod_cast h
  have hA0nn : (0 : ℝ) ≤ ((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hBnn : (0 : ℝ) ≤ ((2 * ((2 * (c + 1 + s * L) + 4) * t + p) + 1 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hGHnn : (0 : ℝ) ≤ (((2 * ((c + 1 + s * L + 2) * t) + 1 : ℕ)) : ℝ) := Nat.cast_nonneg _
  have hAA : 8 * ((2 * (N₀ + p + s * D * L + 2 * (D * L) + (c + 1 + s * L + 2) * t) + 1 : ℕ) : ℝ)
      ≤ 8 * (((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ) * (N₀ : ℝ)) := by linarith [hA]
  have e1 : 8 * ((2 * (N₀ + p + s * D * L + 2 * (D * L) + (c + 1 + s * L + 2) * t) + 1 : ℕ) : ℝ)
        * ((2 * ((2 * (c + 1 + s * L) + 4) * t + p) + 1 : ℕ) : ℝ)
      ≤ 8 * (((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ) * (N₀ : ℝ))
        * (((6 * c + 4 * s * L + 13 : ℕ) : ℝ) * (t : ℝ)) := by
    have h1 : 8 * ((2 * (N₀ + p + s * D * L + 2 * (D * L) + (c + 1 + s * L + 2) * t) + 1 : ℕ) : ℝ)
          * ((2 * ((2 * (c + 1 + s * L) + 4) * t + p) + 1 : ℕ) : ℝ)
        ≤ 8 * (((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ) * (N₀ : ℝ))
          * ((2 * ((2 * (c + 1 + s * L) + 4) * t + p) + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hAA hBnn
    have h2 : 8 * (((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ) * (N₀ : ℝ))
          * ((2 * ((2 * (c + 1 + s * L) + 4) * t + p) + 1 : ℕ) : ℝ)
        ≤ 8 * (((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ) * (N₀ : ℝ))
          * (((6 * c + 4 * s * L + 13 : ℕ) : ℝ) * (t : ℝ)) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    linarith [h1, h2]
  have e2 : 8 * (((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ) * (N₀ : ℝ))
        * (((6 * c + 4 * s * L + 13 : ℕ) : ℝ) * (t : ℝ))
      ≤ 4 * (((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
          * ((c + s * L + 3 : ℕ) : ℝ)) * (N₀ : ℝ) * (t : ℝ) := by
    have h2 : 2 * ((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ)
          * ((6 * c + 4 * s * L + 13 : ℕ) : ℝ)
        ≤ ((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
          * ((c + s * L + 3 : ℕ) : ℝ) := hcore
    calc 8 * (((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ) * (N₀ : ℝ))
          * (((6 * c + 4 * s * L + 13 : ℕ) : ℝ) * (t : ℝ))
        = 4 * (2 * ((2 * c + 2 * s * L + 2 * L + 6 : ℕ) : ℝ)
              * ((6 * c + 4 * s * L + 13 : ℕ) : ℝ)) * ((N₀ : ℝ) * (t : ℝ)) := by ring
      _ ≤ 4 * (((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
              * ((c + s * L + 3 : ℕ) : ℝ)) * ((N₀ : ℝ) * (t : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith [h2]) (by positivity)
      _ = 4 * (((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
              * ((c + s * L + 3 : ℕ) : ℝ)) * (N₀ : ℝ) * (t : ℝ) := by ring
  have e3 : 4 * (((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
          * ((c + s * L + 3 : ℕ) : ℝ)) * (N₀ : ℝ) * (t : ℝ)
      ≤ ((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
        * (((2 * ((c + 1 + s * L + 2) * t) + 1 : ℕ) : ℝ)
           * ((2 * (N₀ + p) + 1 : ℕ) : ℝ)) := by
    have hprod : (2 * ((c + s * L + 3 : ℕ) : ℝ) * (t : ℝ)) * (2 * (N₀ : ℝ))
        ≤ (((2 * ((c + 1 + s * L + 2) * t) + 1 : ℕ)) : ℝ) * (((2 * (N₀ + p) + 1 : ℕ)) : ℝ) :=
      mul_le_mul hGH hGN (by positivity) hGHnn
    have h3 := mul_le_mul_of_nonneg_left hprod hA0nn
    calc 4 * (((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
            * ((c + s * L + 3 : ℕ) : ℝ)) * (N₀ : ℝ) * (t : ℝ)
        = ((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
          * ((2 * ((c + s * L + 3 : ℕ) : ℝ) * (t : ℝ)) * (2 * (N₀ : ℝ))) := by ring
      _ ≤ ((1000 * (2 * (c + 1 + s * L) + 4 + 1) * (s + 1) + 1000 : ℕ) : ℝ)
          * ((((2 * ((c + 1 + s * L + 2) * t) + 1 : ℕ)) : ℝ)
             * (((2 * (N₀ + p) + 1 : ℕ)) : ℝ)) := h3
  exact le_trans e1 (le_trans e2 e3)

theorem gap_numerics (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (s N N₀ D : ℕ)
    (hN : 1 ≤ N) (hN₀ : 1 ≤ N₀) (hD : D ≤ N ^ P.natDegree) (hgap : 2 * N ^ P.natDegree < N₀) :
    Work.Peluse.Ulower.gapR P s N N₀ D ≤ Work.Peluse.Ulower.gapA0 P s * N₀ ∧
    N ≤ Work.Peluse.Ulower.gapNs P s N ∧
    N ^ P.natDegree ≤ Work.Peluse.Ulower.gapA0 P s * Work.Peluse.Ulower.gapNs P s N ∧
    Work.Peluse.Ulower.gapNs P s N ≤ Work.Peluse.Ulower.gapA0 P s * N ^ P.natDegree ∧
    2 * ((2 * Work.Peluse.Ulower.gapR P s N N₀ D + 1 : ℕ) : ℝ)
        * ((2 * Work.Peluse.dSup P (Work.Peluse.Ulower.gapNs P s N) N + 1 : ℕ) : ℝ)
      ≤ (Work.Peluse.Ulower.gapA0 P s : ℝ)
        * (((2 * Work.Peluse.Ulower.gapHalf P s N + 1 : ℕ) : ℝ)
           * ((2 * Work.Peluse.dSup P N₀ N + 1 : ℕ) : ℝ)) ∧
    8 * ((2 * Work.Peluse.Ulower.gapR P s N N₀ D + 1 : ℕ) : ℝ)
        * ((2 * Work.Peluse.dSup P (Work.Peluse.Ulower.gapNs P s N) N + 1 : ℕ) : ℝ)
      ≤ (Work.Peluse.Ulower.gapA0 P s : ℝ)
        * (((2 * Work.Peluse.Ulower.gapHalf P s N + 1 : ℕ) : ℝ)
           * ((2 * Work.Peluse.dSup P N₀ N + 1 : ℕ) : ℝ)) := by
  have ht1 : 1 ≤ N ^ P.natDegree := one_le_pow₀ hN
  have hNt : N ≤ N ^ P.natDegree := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ P.natDegree := Nat.pow_le_pow_right hN hd
  have hN0 : 2 * N ^ P.natDegree + 1 ≤ N₀ := by omega
  have hLc : P.leadingCoeff.natAbs ≤ gapCsum P := gapCsum_leadingCoeff_le P
  have hps : polySup P N ≤ gapCsum P * N ^ P.natDegree := by
    simpa only [gapCsum] using polySup_le P hN
  have hmain : 8 * ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ)
      * ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ)
      ≤ (gapA0 P s : ℝ)
        * (((2 * gapHalf P s N + 1 : ℕ) : ℝ) * ((2 * dSup P N₀ N + 1 : ℕ) : ℝ)) := by
    have h8 := gap_real_aux s N₀ (N ^ P.natDegree) (polySup P N) (gapCsum P)
      (P.leadingCoeff.natAbs) D hN0 ht1 hD hLc hps
    simpa only [gapR, gapRho, gapHalf, gapNs, gapA0, gapC2, dSup, gapSig] using h8
  refine ⟨?_, ?_, ?_, ?_, ?_, hmain⟩
  · simp only [gapR, gapRho, gapHalf, gapA0, gapC2, dSup, gapSig]
    exact gapR_bound s N₀ (N ^ P.natDegree) (polySup P N) (gapCsum P) (P.leadingCoeff.natAbs) D
      hN0 hD hLc hps
  · simp only [gapNs, gapC2]
    calc N ≤ N ^ P.natDegree := hNt
      _ = 1 * N ^ P.natDegree := (one_mul _).symm
      _ ≤ (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4) * N ^ P.natDegree :=
          Nat.mul_le_mul_right _ (by omega)
  · simp only [gapNs, gapA0, gapC2]
    have h1 : N ^ P.natDegree ≤ (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4)
        * N ^ P.natDegree := by
      calc N ^ P.natDegree = 1 * N ^ P.natDegree := (one_mul _).symm
        _ ≤ (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4) * N ^ P.natDegree :=
            Nat.mul_le_mul_right _ (by omega)
    calc N ^ P.natDegree
        ≤ (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4) * N ^ P.natDegree := h1
      _ = 1 * ((2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4) * N ^ P.natDegree) :=
          (one_mul _).symm
      _ ≤ (1000 * (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4 + 1) * (s + 1) + 1000)
            * ((2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4) * N ^ P.natDegree) :=
          Nat.mul_le_mul_right _ (by omega)
  · simp only [gapNs, gapA0, gapC2]
    have hX : 2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4
        ≤ 1000 * (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4 + 1) := by omega
    have hY : 1000 * (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4 + 1)
        ≤ 1000 * (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4 + 1) * (s + 1) + 1000 := by
      calc 1000 * (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4 + 1)
          = 1000 * (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4 + 1) * 1 := by ring
        _ ≤ 1000 * (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4 + 1) * (s + 1) :=
            Nat.mul_le_mul_left _ (by omega)
        _ ≤ 1000 * (2 * (gapCsum P + 1 + s * P.leadingCoeff.natAbs) + 4 + 1) * (s + 1) + 1000 :=
            Nat.le_add_right _ _
    exact Nat.mul_le_mul_right _ (le_trans hX hY)
  · have hXY : (0 : ℝ)
        ≤ ((2 * gapR P s N N₀ D + 1 : ℕ) : ℝ)
          * ((2 * dSup P (gapNs P s N) N + 1 : ℕ) : ℝ) := by positivity
    linarith [hmain, hXY]

end

end Work.Peluse.Ulower
