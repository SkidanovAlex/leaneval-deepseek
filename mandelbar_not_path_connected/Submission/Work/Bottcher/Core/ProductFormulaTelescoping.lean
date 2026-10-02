import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.ParamRays.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The product formula for `bottcher`: exact finite telescoping, and the branch obstruction

`Work.Bottcher.bottcher c` is defined (in `Submission/Work/Bottcher/Defs.lean`) by the product
formula

`bottcher c z = z * exp (∑' n, (1/4)^{n+1} * Complex.log (pMap c ((pMap c)^[n] z) / ((pMap c)^[n] z)^4))`

with the **principal branch** of `Complex.log`.

## What is true (proved here)

The *real parts* of the series terms telescope **exactly**

`Re (∑_{n<N} bottcherTerm c n z) = 4^{-N} log ‖(pMap c)^[N] z‖ - log ‖z‖`

so the modulus of every partial product is exactly `exp (4^{-N} log ‖(pMap c)^[N] z‖)`
(`norm_bottcherPartial`).  Consequently the modulus half of the Böttcher theory
(`‖bottcher c z‖ = exp (G_c z)`) carries no branch ambiguity.

## What is false (the obstruction)

`Complex.log` is *not* additive: on the locus where a factor `pMap c w / w^4` crosses the negative
real axis the corresponding term jumps by `2π i`, and the accumulated jump
`∑ 4^{-(n+1)} κ_n` (`κ_n ∈ ℤ`) need not be an integer.  Hence the product formula agrees with the
genuine Böttcher coordinate only up to a locally constant factor with values in the roots of unity
of `2`-power order, and the Böttcher equation `φ (T_c z) = conj (φ z)^2` — the statement
`Work.Bottcher.Core.bottcher_comm_Tantibar` — fails.

The exact sign data of a counterexample (`c = -15/2`, `z = -13/4`) is certified below:
the `z`-series has all its factors positive, while the very first factor of the `T_c z`-series is
negative, contributing the phase `π/4` to `bottcher c (T_c z)`:

`bottcher (-15/2) (-13/4)       = -1.1368727291923355`  (a negative real),
`bottcher (-15/2) (T (-15/2) (-13/4)) = 0.9139210913890669 + 0.9139210913890669 I`,
`conj (bottcher (-15/2) (-13/4))^2    = 1.2924796023812295`  (a positive real).

Both hypotheses of `bottcher_comm_Tantibar` hold for this pair (the orbit is real, escaping and
never zero: `x_0 = -13/4, x_1 = 49/16, x_2 = 481/256, x_3 = -260159/65536, x_4 > 8.25`, and
`x_{n+1} = x_n^2 - 15/2 > x_n` for `n ≥ 4`), and the two sides differ by `exp (I π/4)`.
-/

namespace Work.Bottcher.Core

open Work.Bottcher
open scoped Topology

/-! ## Exact finite telescoping (the modulus half) -/

/-- The real part of the `N`-th partial sum of the Böttcher series is exactly
`4^{-N} log ‖(pMap c)^[N] z‖ - log ‖z‖`: the real parts telescope, because `Real.log` is
additive on positive reals and no branch choice is involved. -/
theorem re_sum_bottcherTerm (c z : ℂ) (N : ℕ) (h : ∀ n ≤ N, (pMap c)^[n] z ≠ 0) :
    (∑ n ∈ Finset.range N, bottcherTerm c n z).re
      = (1 / 4 : ℝ) ^ N * Real.log ‖(pMap c)^[N] z‖ - Real.log ‖z‖ := by
  have hstep : ∀ n ∈ Finset.range N,
      (bottcherTerm c n z).re
        = ((1 / 4 : ℝ) ^ (n + 1) * Real.log ‖(pMap c)^[n + 1] z‖)
          - ((1 / 4 : ℝ) ^ n * Real.log ‖(pMap c)^[n] z‖) := by
    intro n hn
    have hn' : n < N := Finset.mem_range.mp hn
    have h1 : (pMap c)^[n] z ≠ 0 := h n (le_of_lt hn')
    have h2 : (pMap c)^[n + 1] z ≠ 0 := h (n + 1) (Nat.succ_le_of_lt hn')
    rw [bottcherTerm, ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.log_re, normFactor, Complex.norm_div, Complex.norm_pow,
      ← Function.iterate_succ_apply' (pMap c) n z,
      Real.log_div (ne_of_gt (norm_pos_iff.mpr h2))
        (pow_ne_zero 4 (ne_of_gt (norm_pos_iff.mpr h1))),
      Real.log_pow, pow_succ]
    ring
  rw [Complex.re_sum, Finset.sum_congr rfl hstep]
  simpa using
    (Finset.sum_range_sub (f := fun k : ℕ => (1 / 4 : ℝ) ^ k * Real.log ‖(pMap c)^[k] z‖) N)

/-- The modulus of the `N`-th partial product of the product formula is exactly
`exp (4^{-N} log ‖(pMap c)^[N] z‖)`. -/
theorem norm_bottcherPartial (c z : ℂ) (N : ℕ) (h : ∀ n ≤ N, (pMap c)^[n] z ≠ 0) :
    ‖bottcherPartial c N z‖ = Real.exp ((1 / 4 : ℝ) ^ N * Real.log ‖(pMap c)^[N] z‖) := by
  have hpos : ∀ n ≤ N, (0 : ℝ) < ‖(pMap c)^[n] z‖ := fun n hn => norm_pos_iff.mpr (h n hn)
  rw [bottcherPartial, norm_mul, Complex.norm_exp, re_sum_bottcherTerm c z N h, Real.exp_sub]
  have hz : (0 : ℝ) < ‖z‖ := by simpa using hpos 0 (Nat.zero_le N)
  rw [Real.exp_log hz]
  field_simp


/-! ## Real orbits: transfer from the complex map, and the phase telescoping

For real data (`c`, `z` real) the whole `T_c`-orbit is real; the product formula can then be
evaluated in terms of the two real orbits

`tOrbit c z n = T_c^n z`  and  `qReal c u = (u^2+c)^2+c`  (`= pMap` on real arguments).

The `pMap`-orbit of `z` is the even part `tOrbit c z (2n)`; the `pMap`-orbit of `T_c z` is the odd
part `tOrbit c z (2n+1)`.
-/

/-- The second iterate `pMap`, restricted to real arguments. -/
noncomputable def qReal (c u : ℝ) : ℝ := (u ^ 2 + c) ^ 2 + c

/-- The real `T_c`-orbit `T_c^n z` for real `c`, `z`. -/
noncomputable def tOrbit (c z : ℝ) : ℕ → ℝ := fun n => (fun u : ℝ => u ^ 2 + c)^[n] z

theorem tOrbit_succ (c z : ℝ) (n : ℕ) : tOrbit c z (n + 1) = (tOrbit c z n) ^ 2 + c := by
  simp [tOrbit, Function.iterate_succ_apply']

theorem tOrbit_shift (c z : ℝ) (k m : ℕ) : tOrbit c (tOrbit c z k) m = tOrbit c z (k + m) := by
  simp only [tOrbit]
  calc (fun u : ℝ => u ^ 2 + c)^[m] ((fun u : ℝ => u ^ 2 + c)^[k] z)
      = (fun u : ℝ => u ^ 2 + c)^[m + k] z := (Function.iterate_add_apply _ m k z).symm
    _ = (fun u : ℝ => u ^ 2 + c)^[k + m] z := by rw [Nat.add_comm]

theorem Tantibar_ofReal (c u : ℝ) :
    LeanEval.ComplexAnalysis.Tantibar (c : ℂ) (u : ℂ) = ((u ^ 2 + c : ℝ) : ℂ) := by
  simp [LeanEval.ComplexAnalysis.Tantibar, Complex.conj_ofReal]

theorem Tantibar_iterate_ofReal (c z : ℝ) (n : ℕ) :
    (LeanEval.ComplexAnalysis.Tantibar (c : ℂ))^[n] (z : ℂ) = ((tOrbit c z n : ℝ) : ℂ) := by
  induction n with
  | zero => simp [tOrbit]
  | succ n ih => rw [Function.iterate_succ_apply', ih, Tantibar_ofReal, tOrbit_succ]

theorem pMap_ofReal (c v : ℝ) : pMap (c : ℂ) (v : ℂ) = ((qReal c v : ℝ) : ℂ) := by
  simp [pMap, qReal, Complex.conj_ofReal]

theorem pMap_iterate_ofReal (c v : ℝ) (n : ℕ) :
    (pMap (c : ℂ))^[n] (v : ℂ) = (((qReal c)^[n] v : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pMap_ofReal,
        Function.iterate_succ_apply' (qReal c) n v]

theorem qReal_eq_tOrbit (c u : ℝ) (n : ℕ) : (qReal c)^[n] u = tOrbit c u (2 * n) := by
  have h2 : qReal c = (fun v : ℝ => v ^ 2 + c)^[2] := by
    funext v
    simp [qReal, Function.iterate_succ_apply']
  rw [h2, tOrbit, Function.iterate_mul (fun v : ℝ => v ^ 2 + c) 2 n]

theorem normFactor_ofReal (c u : ℝ) :
    normFactor (c : ℂ) (u : ℂ) = ((qReal c u / u ^ 4 : ℝ) : ℂ) := by
  simp [normFactor, pMap_ofReal]

/-- For a real argument, the imaginary part of `Complex.log (normFactor c u)` is `0` or `π`
according to the sign of the factor — this is the branch effect that the product formula
accumulates. -/
theorem log_im_normFactor_ofReal (c u : ℝ) (hu : u ≠ 0) :
    (Complex.log (normFactor (c : ℂ) (u : ℂ))).im
      = if qReal c u < 0 then Real.pi else 0 := by
  have h4 : (0 : ℝ) < u ^ 4 := by positivity
  rw [Complex.log_im, normFactor_ofReal]
  by_cases h : qReal c u < 0
  · rw [if_pos h, Complex.arg_ofReal_of_neg (div_neg_of_neg_of_pos h h4)]
  · rw [if_neg h, Complex.arg_ofReal_of_nonneg (div_nonneg (le_of_not_gt h) h4.le)]

/-- **Phase telescoping.** For a real orbit, the imaginary part of the `N`-th partial sum of the
Böttcher series is `π` times the (finite, `4`-adic rational) phase count
`∑ 4^{-(n+1)}` over the indices whose Böttcher factor is negative. -/
theorem im_sum_bottcherTerm_ofReal (c u : ℝ) (N : ℕ)
    (h : ∀ n ≤ N, (qReal c)^[n] u ≠ 0) :
    (∑ n ∈ Finset.range N, (bottcherTerm (c : ℂ) n (u : ℂ)).im)
      = Real.pi * (∑ n ∈ Finset.range N,
          if (qReal c)^[n + 1] u < 0 then (1 / 4 : ℝ) ^ (n + 1) else 0) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n < N := Finset.mem_range.mp hn
  have hu : (qReal c)^[n] u ≠ 0 := h n (le_of_lt hn')
  rw [bottcherTerm, ← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    zero_mul, add_zero, pMap_iterate_ofReal c u n,
    log_im_normFactor_ofReal c ((qReal c)^[n] u) hu, Function.iterate_succ_apply' (qReal c) n u]
  split_ifs <;> ring

/-! ## The counterexample `c = -15/2`, `z = -13/4` -/

/-- The real `T_c`-orbit of the counterexample (exact values). -/
theorem counterexample_values :
    tOrbit (-15/2) (-13/4) 0 = -13/4 ∧ tOrbit (-15/2) (-13/4) 1 = 49/16 ∧
    tOrbit (-15/2) (-13/4) 2 = 481/256 ∧ tOrbit (-15/2) (-13/4) 3 = -260159/65536 ∧
    tOrbit (-15/2) (-13/4) 4 = 35470450561/4294967296 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [tOrbit, Function.iterate_succ_apply']

private theorem grow_step {u : ℝ} (h : 8 ≤ u) : 8 ≤ u ^ 2 + (-15 / 2 : ℝ) := by nlinarith
private theorem grow_mono {u : ℝ} (h : 8 ≤ u) : u ≤ u ^ 2 + (-15 / 2 : ℝ) := by nlinarith

/-- From the fourth point on, the orbit of the counterexample is monotone increasing and `≥ 8`. -/
theorem counterexample_ge : ∀ n : ℕ, 4 ≤ n → 8 ≤ tOrbit (-15/2) (-13/4) n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [tOrbit, Function.iterate_succ_apply']
  | succ m hm ih => rw [tOrbit_succ]; exact grow_step ih

/-- All Böttcher factors of the `z`-series of the counterexample are positive. -/
theorem counterexample_phase_z (N : ℕ) :
    (∑ n ∈ Finset.range N,
        if (qReal (-15/2))^[n + 1] (-13/4) < 0 then (1 / 4 : ℝ) ^ (n + 1) else 0) = 0 := by
  refine Finset.sum_eq_zero fun n _ => ?_
  have hpos : 0 < (qReal (-15/2))^[n + 1] (-13/4) := by
    rw [qReal_eq_tOrbit]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num [tOrbit, Function.iterate_succ_apply']
    · exact lt_of_lt_of_le (by norm_num) (counterexample_ge _ (by omega))
  rw [if_neg (not_lt.mpr hpos.le)]

/-- Conversely, exactly the first Böttcher factor of the `T_c z`-series is negative. -/
theorem counterexample_phase_Tz (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range N,
        if (qReal (-15/2))^[n + 1] (49/16) < 0 then (1 / 4 : ℝ) ^ (n + 1) else 0) = 1 / 4 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have hzero : (∑ x ∈ Finset.range M,
      (if (qReal (-15/2))^[x + 1 + 1] (49/16) < 0 then (1 / 4 : ℝ) ^ (x + 1 + 1) else 0)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    have hpos : 0 < (qReal (-15/2))^[x + 1 + 1] (49/16) := by
      rw [qReal_eq_tOrbit, ← counterexample_values.2.1, tOrbit_shift]
      exact lt_of_lt_of_le (by norm_num) (counterexample_ge _ (by omega))
    rw [if_neg (not_lt.mpr hpos.le)]
  rw [hzero, zero_add]
  have hneg : (qReal (-15/2))^[1] (49/16) < 0 := by
    rw [qReal_eq_tOrbit, ← counterexample_values.2.1, tOrbit_shift]
    norm_num [tOrbit, Function.iterate_succ_apply']
  rw [if_pos hneg]
  norm_num

/-- The `pMap`-orbit of the counterexample point `z` is `≥ 8` in norm from step `2` on. -/
theorem counterexample_norm_ge_z : ∀ n : ℕ, 2 ≤ n → 8 ≤ ‖(pMap ((-15/2 : ℝ) : ℂ))^[n] ((-13/4 : ℝ) : ℂ)‖ := by
  intro n hn
  rw [pMap_iterate_ofReal, qReal_eq_tOrbit]
  have hnorm : ‖(((tOrbit (-15/2) (-13/4) (2 * n)) : ℝ) : ℂ)‖
      = |tOrbit (-15/2) (-13/4) (2 * n)| := by simp
  rw [hnorm]
  have : |tOrbit (-15/2) (-13/4) (2 * n)| = tOrbit (-15/2) (-13/4) (2 * n) :=
    abs_of_nonneg (le_of_lt (lt_of_lt_of_le (by norm_num) (counterexample_ge _ (by omega))))
  rw [this]
  exact counterexample_ge _ (by omega)

/-- The `pMap`-orbit of the counterexample point `T_c z` is `≥ 8` in norm from step `2` on. -/
theorem counterexample_norm_ge_Tz : ∀ n : ℕ, 2 ≤ n → 8 ≤ ‖(pMap ((-15/2 : ℝ) : ℂ))^[n] ((49/16 : ℝ) : ℂ)‖ := by
  intro n hn
  rw [pMap_iterate_ofReal, qReal_eq_tOrbit, ← counterexample_values.2.1, tOrbit_shift]
  have hnorm : ‖(((tOrbit (-15/2) (-13/4) (1 + 2 * n)) : ℝ) : ℂ)‖
      = |tOrbit (-15/2) (-13/4) (1 + 2 * n)| := by simp
  rw [hnorm]
  have : |tOrbit (-15/2) (-13/4) (1 + 2 * n)| = tOrbit (-15/2) (-13/4) (1 + 2 * n) :=
    abs_of_nonneg (le_of_lt (lt_of_lt_of_le (by norm_num) (counterexample_ge _ (by omega))))
  rw [this]
  exact counterexample_ge _ (by omega)

/-! ## Certified sign data of the counterexample

With `c = -15/2` the real `T_c`-orbit of `z = -13/4` is
`-13/4, 49/16, 481/256, -260159/65536, 35470450561/4294967296, …`; the fourth value is the first
one bigger than `8` and from there on the orbit increases (`x_{n+1} = x_n^2 - 15/2 > x_n` for
`x_n > 8`), in particular it stays positive and never vanishes.  The three values below are the
ones that drive the branch obstruction: the Böttcher factor `F_n = pMap c w / w^4` of the
`z`-series is `x_{2n+2}/x_{2n}^4 > 0` while the first factor of the `T_c z`-series is
`x_3/x_1^4 < 0`.
-/

/-- The first four points of the `T_c`-orbit of the counterexample. -/
theorem counterexample_orbit :
    (LeanEval.ComplexAnalysis.Tantibar (-15 / 2) (-13 / 4) : ℂ) = 49 / 16 ∧
    (LeanEval.ComplexAnalysis.Tantibar (-15 / 2))^[2] (-13 / 4) = 481 / 256 ∧
    (LeanEval.ComplexAnalysis.Tantibar (-15 / 2))^[3] (-13 / 4) = -260159 / 65536 ∧
    (LeanEval.ComplexAnalysis.Tantibar (-15 / 2))^[4] (-13 / 4) = 35470450561 / 4294967296 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [LeanEval.ComplexAnalysis.Tantibar, Function.iterate_succ_apply',
      Function.iterate_zero, map_div₀, Complex.conj_ofNat]

/-- The first Böttcher factor of the `z`-series is the *positive* real `481/256 / (-13/4)^4`. -/
theorem counterexample_normFactor_z :
    normFactor (-15 / 2) (-13 / 4) = (((481 / 256 : ℝ) / (-13 / 4 : ℝ) ^ 4 : ℝ) : ℂ) := by
  norm_num [normFactor, pMap, map_div₀, Complex.conj_ofNat, Complex.ofReal_pow, Complex.ofReal_add]

/-- The first Böttcher factor of the `T_c z`-series is the *negative* real `-260159/65536 / (49/16)^4`. -/
theorem counterexample_normFactor_Tz :
    normFactor (-15 / 2) (49 / 16) = (((-260159 / 65536 : ℝ) / (49 / 16 : ℝ) ^ 4 : ℝ) : ℂ) := by
  norm_num [normFactor, pMap, map_div₀, Complex.conj_ofNat, Complex.ofReal_pow, Complex.ofReal_add]

/-- Hence the two first logarithms have imaginary parts `0` and `π`. -/
theorem counterexample_phases :
    (Complex.log (normFactor (-15 / 2) (-13 / 4))).im = 0 ∧
    (Complex.log (normFactor (-15 / 2) (49 / 16))).im = Real.pi := by
  constructor
  · rw [Complex.log_im, counterexample_normFactor_z]
    exact Complex.arg_ofReal_of_nonneg (by norm_num)
  · rw [Complex.log_im, counterexample_normFactor_Tz]
    exact Complex.arg_ofReal_of_neg (by norm_num)

/-- The first term of the `T_c z`-series therefore has imaginary part exactly `π/4`, the
irreducible phase that makes `bottcher_comm_Tantibar` fail. -/
theorem counterexample_first_term_phase :
    (bottcherTerm (-15 / 2) 0 (49 / 16)).im = Real.pi / 4 := by
  rw [bottcherTerm, ← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    zero_mul, zero_add]
  simp only [Function.iterate_zero, id_eq]
  rw [counterexample_phases.2]
  ring


open Filter

/-! ## Summability of the series and convergence of the partial products -/

/-- `pMap c w / w^4 - 1 = 2 conj c / w^2 + (conj c^2 + c)/w^4`. -/
theorem normFactor_sub_one_eq (c w : ℂ) (hw : w ≠ 0) :
    normFactor c w - 1
      = 2 * (starRingEnd ℂ c) / w ^ 2 + ((starRingEnd ℂ c) ^ 2 + c) / w ^ 4 := by
  rw [normFactor, pMap]
  field_simp
  ring

/-- `‖pMap c w / w^4 - 1‖ ≤ 1/2` as soon as `‖w‖ ≥ 8` and `‖c‖ ≤ 8`. -/
theorem norm_normFactor_sub_one (c w : ℂ) (hw : 8 ≤ ‖w‖) (hc : ‖c‖ ≤ 8) :
    ‖normFactor c w - 1‖ ≤ 1 / 2 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    norm_num at hw
  rw [normFactor_sub_one_eq c w hw0]
  have h1 : ‖2 * (starRingEnd ℂ c) / w ^ 2‖ ≤ 2 * 8 / 8 ^ 2 := by
    rw [norm_div, norm_mul, Complex.norm_conj, norm_pow, Complex.norm_ofNat]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [norm_nonneg c, hc, hw]
  have h2 : ‖((starRingEnd ℂ c) ^ 2 + c) / w ^ 4‖ ≤ (8 ^ 2 + 8) / 8 ^ 4 := by
    rw [norm_div, norm_pow]
    have h3 : ‖(starRingEnd ℂ c) ^ 2 + c‖ ≤ 8 ^ 2 + 8 := by
      calc ‖(starRingEnd ℂ c) ^ 2 + c‖ ≤ ‖(starRingEnd ℂ c) ^ 2‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
        _ ≤ 8 ^ 2 + 8 := by nlinarith [norm_nonneg c, hc]
    have hw4 : (8 : ℝ) ^ 4 ≤ ‖w‖ ^ 4 := pow_le_pow_left₀ (by norm_num) hw 4
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [h3, hw4]
  linarith [norm_add_le (2 * (starRingEnd ℂ c) / w ^ 2) (((starRingEnd ℂ c) ^ 2 + c) / w ^ 4),
    h1, h2]

/-- `‖Complex.log F‖ ≤ log 2 + π` for `‖F - 1‖ ≤ 1/2`. -/
theorem norm_log_le_log_two_add_pi (F : ℂ) (h : ‖F - 1‖ ≤ 1 / 2) :
    ‖Complex.log F‖ ≤ Real.log 2 + Real.pi := by
  have hnorm := abs_norm_sub_norm_le F 1
  simp only [norm_one] at hnorm
  have hF1 : (1 / 2 : ℝ) ≤ ‖F‖ := by linarith [abs_le.mp hnorm]
  have hF2 : ‖F‖ ≤ 3 / 2 := by linarith [abs_le.mp hnorm]
  have hsplit : Complex.log F = ↑(Real.log ‖F‖) + ↑(F.arg) * Complex.I := by
    refine Complex.ext ?_ ?_ <;> simp [Complex.log_re, Complex.log_im]
  rw [hsplit]
  have h1 : ‖(↑(Real.log ‖F‖) : ℂ) + ↑(F.arg) * Complex.I‖ ≤ |Real.log ‖F‖| + |F.arg| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp
  have hlog : |Real.log ‖F‖| ≤ Real.log 2 := by
    rw [abs_le]
    constructor
    · have hh : Real.log (1 / 2 : ℝ) ≤ Real.log ‖F‖ := Real.log_le_log (by norm_num) hF1
      have h2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [Real.log_div] <;> norm_num
      linarith
    · exact Real.log_le_log (by linarith) (by linarith : ‖F‖ ≤ 2)
  have harg : |F.arg| ≤ Real.pi := abs_le.mpr ⟨le_of_lt F.neg_pi_lt_arg, F.arg_le_pi⟩
  linarith

/-- The Böttcher series converges absolutely as soon as the orbit stays outside the disk of
radius `8` from the second step on. -/
theorem summable_bottcherTerm_of_norm_ge (c w : ℂ) (hc : ‖c‖ ≤ 8)
    (h8 : ∀ n : ℕ, 2 ≤ n → 8 ≤ ‖(pMap c)^[n] w‖) :
    Summable (fun n : ℕ => bottcherTerm c n w) := by
  rw [← summable_nat_add_iff 2]
  refine Summable.of_norm_bounded (g := fun n : ℕ => (Real.log 2 + Real.pi) * (1 / 4 : ℝ) ^ n)
    ?_ ?_
  · have hgeom : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
      summable_geometric_iff_norm_lt_one.mpr (by norm_num)
    exact hgeom.mul_left (Real.log 2 + Real.pi)
  · intro n
    have hb : ‖normFactor c ((pMap c)^[n + 2] w) - 1‖ ≤ 1 / 2 :=
      norm_normFactor_sub_one c _ (h8 (n + 2) (by omega)) hc
    have hl : ‖Complex.log (normFactor c ((pMap c)^[n + 2] w))‖ ≤ Real.log 2 + Real.pi :=
      norm_log_le_log_two_add_pi _ hb
    rw [bottcherTerm, ← Complex.ofReal_pow, norm_mul]
    have h4 : ‖(↑((1 / 4 : ℝ) ^ (n + 2 + 1)) : ℂ)‖ = (1 / 4) ^ (n + 2 + 1) := by
      rw [show ‖(↑((1 / 4 : ℝ) ^ (n + 2 + 1)) : ℂ)‖ = |((1 / 4 : ℝ) ^ (n + 2 + 1))| from by simp]
      exact abs_of_nonneg (by positivity)
    rw [h4]
    calc (1 / 4 : ℝ) ^ (n + 2 + 1) * ‖Complex.log (normFactor c ((pMap c)^[n + 2] w))‖
        ≤ (1 / 4) ^ (n + 2 + 1) * (Real.log 2 + Real.pi) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ ≤ (Real.log 2 + Real.pi) * (1 / 4) ^ n := by
          have hsplit : (1 / 4 : ℝ) ^ (n + 2 + 1) = (1 / 4) ^ n * (1 / 4) ^ 3 := by
            rw [show n + 2 + 1 = n + 3 from by omega, pow_add]
          rw [hsplit]
          have h3 : (1 / 4 : ℝ) ^ 3 ≤ 1 := by norm_num
          have hC : (0 : ℝ) ≤ Real.log 2 + Real.pi := by positivity
          calc (1 / 4) ^ n * (1 / 4) ^ 3 * (Real.log 2 + Real.pi)
              ≤ (1 / 4) ^ n * 1 * (Real.log 2 + Real.pi) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) hC
            _ = (Real.log 2 + Real.pi) * (1 / 4) ^ n := by ring

/-- If the Böttcher series is summable, then the partial products converge to `bottcher`. -/
theorem tendsto_bottcherPartial_of_summable (c w : ℂ)
    (h : Summable (fun n : ℕ => bottcherTerm c n w)) :
    Tendsto (fun N : ℕ => bottcherPartial c N w) atTop (𝓝 (bottcher c w)) := by
  have hlim : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, bottcherTerm c n w) atTop
      (𝓝 (bottcherSeries c w)) := h.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun N : ℕ => Complex.exp (∑ n ∈ Finset.range N, bottcherTerm c n w))
      atTop (𝓝 (Complex.exp (bottcherSeries c w))) :=
    (Complex.continuous_exp.tendsto _).comp hlim
  have h3 : Tendsto (fun N : ℕ => w * Complex.exp (∑ n ∈ Finset.range N, bottcherTerm c n w))
      atTop (𝓝 (w * Complex.exp (bottcherSeries c w))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => w) atTop (𝓝 w)).mul h2
  simpa [bottcherPartial, bottcher] using h3

/-! ## The partial products at a real point -/

/-- The `N`-th partial sum of the Böttcher series at a real point, in closed form. -/
theorem sum_bottcherTerm_ofReal (c u : ℝ) (N : ℕ) (hu : u ≠ 0)
    (h : ∀ n ≤ N, (qReal c)^[n] u ≠ 0) :
    (∑ n ∈ Finset.range N, bottcherTerm (c : ℂ) n (u : ℂ))
      = ↑((1 / 4 : ℝ) ^ N * Real.log ‖(qReal c)^[N] u‖ - Real.log ‖u‖)
        + ↑(Real.pi * (∑ n ∈ Finset.range N,
            if (qReal c)^[n + 1] u < 0 then (1 / 4 : ℝ) ^ (n + 1) else 0)) * Complex.I := by
  have hre : (∑ n ∈ Finset.range N, bottcherTerm (c : ℂ) n (u : ℂ)).re
      = (1 / 4 : ℝ) ^ N * Real.log ‖(qReal c)^[N] u‖ - Real.log ‖u‖ := by
    rw [re_sum_bottcherTerm (c : ℂ) (u : ℂ) N ?_]
    · rw [pMap_iterate_ofReal]
      simp
    · intro n hn
      rw [pMap_iterate_ofReal]
      exact_mod_cast h n hn
  have him : (∑ n ∈ Finset.range N, bottcherTerm (c : ℂ) n (u : ℂ)).im
      = Real.pi * (∑ n ∈ Finset.range N,
          if (qReal c)^[n + 1] u < 0 then (1 / 4 : ℝ) ^ (n + 1) else 0) := by
    rw [Complex.im_sum]
    exact im_sum_bottcherTerm_ofReal c u N h
  refine Complex.ext ?_ ?_
  · rw [hre]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  · rw [him]
    simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero]
    ring

/-- The imaginary part of the `N`-th partial product at a real point.  The accumulated phase
`π B` (`B` the `4`-adic rational phase count) makes the partial product leave the real axis
unless `B ∈ ℤ`. -/
theorem im_bottcherPartial_ofReal (c u : ℝ) (N : ℕ) (hu : u ≠ 0)
    (h : ∀ n ≤ N, (qReal c)^[n] u ≠ 0) :
    (bottcherPartial (c : ℂ) N (u : ℂ)).im
      = u * Real.exp ((1 / 4 : ℝ) ^ N * Real.log ‖(qReal c)^[N] u‖ - Real.log ‖u‖)
        * Real.sin (Real.pi * (∑ n ∈ Finset.range N,
            if (qReal c)^[n + 1] u < 0 then (1 / 4 : ℝ) ^ (n + 1) else 0)) := by
  rw [bottcherPartial, sum_bottcherTerm_ofReal c u N hu h, Complex.exp_add, ← Complex.ofReal_exp,
    Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- `u * exp (X - log ‖u‖) = exp X` for `u > 0`. -/
theorem mul_exp_sub_log {u : ℝ} (hu : 0 < u) (X : ℝ) :
    u * Real.exp (X - Real.log ‖u‖) = Real.exp X := by
  have hnorm : ‖u‖ = u := abs_of_pos hu
  have hexp : Real.exp (Real.log u) = u := Real.exp_log hu
  rw [hnorm, Real.exp_sub, hexp]
  field_simp [ne_of_gt hu]

/-! ## The counterexample never vanishes -/

theorem counterexample_ne_zero (n : ℕ) : tOrbit (-15/2) (-13/4) n ≠ 0 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num [tOrbit, Function.iterate_succ_apply']
  · exact ne_of_gt (lt_of_lt_of_le (by norm_num) (counterexample_ge n h))

theorem counterexample_norm_one_le (n : ℕ) (hn : 1 ≤ n) : 1 ≤ |tOrbit (-15/2) (-13/4) n| := by
  rcases Nat.lt_or_ge n 4 with h | h
  · interval_cases n <;> norm_num [tOrbit, Function.iterate_succ_apply']
  · exact le_trans (by norm_num) (le_trans (counterexample_ge n h) (le_abs_self _))

/-! ## The two imaginary parts -/

/-- For `N ≥ 1` the partial product at `z = -13/4` is a (negative) real number. -/
theorem counterexample_im_partial_z (N : ℕ) (hN : 1 ≤ N) :
    (bottcherPartial ((-15 / 2 : ℝ) : ℂ) N (((-13 / 4 : ℝ) : ℂ))).im = 0 := by
  rw [im_bottcherPartial_ofReal _ _ N (by norm_num) ?_, counterexample_phase_z]
  · simp
  · intro n _
    rw [qReal_eq_tOrbit]
    exact counterexample_ne_zero (2 * n)

/-- For `N ≥ 1` the imaginary part of the partial product at `T_c z` is at least
`sin (π/4) > 0`. -/
theorem counterexample_im_partial_Tz (N : ℕ) (hN : 1 ≤ N) :
    Real.sin (Real.pi / 4)
      ≤ (bottcherPartial ((-15 / 2 : ℝ) : ℂ) N (((49 / 16 : ℝ) : ℂ))).im := by
  rw [im_bottcherPartial_ofReal _ _ N (by norm_num) ?_, counterexample_phase_Tz N hN]
  rw [mul_exp_sub_log (by norm_num : (0 : ℝ) < 49 / 16)]
  have hnorm1 : (1 : ℝ) ≤ ‖(qReal (-15/2))^[N] (49 / 16)‖ := by
    rw [qReal_eq_tOrbit, ← counterexample_values.2.1, tOrbit_shift]
    have h := counterexample_norm_one_le (1 + 2 * N) (by omega)
    rwa [show ‖((tOrbit (-15/2) (-13/4) (1 + 2 * N)) : ℝ)‖
        = |tOrbit (-15/2) (-13/4) (1 + 2 * N)| from by simp]
  have h0 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ N * Real.log ‖(qReal (-15/2))^[N] (49 / 16)‖ :=
    mul_nonneg (by positivity) (Real.log_nonneg hnorm1)
  have hone : (1 : ℝ) ≤ Real.exp ((1 / 4 : ℝ) ^ N
      * Real.log ‖(qReal (-15/2))^[N] (49 / 16)‖) :=
    le_trans (by linarith) (Real.add_one_le_exp _)
  have hsin : 0 ≤ Real.sin (Real.pi / 4) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]))
  have hmain : (1 : ℝ) * Real.sin (Real.pi / 4)
      ≤ Real.exp ((1 / 4 : ℝ) ^ N * Real.log ‖(qReal (-15/2))^[N] (49 / 16)‖)
        * Real.sin (Real.pi * (1 / 4)) := by
    rw [show Real.pi * (1 / 4) = Real.pi / 4 from by ring]
    exact mul_le_mul_of_nonneg_right hone hsin
  linarith [hmain]
  · intro n _
    rw [qReal_eq_tOrbit, ← counterexample_values.2.1, tOrbit_shift]
    exact counterexample_ne_zero (1 + 2 * n)

/-! ## The machine-checked refutation -/

/-- **`Work.Bottcher.Core.bottcher_comm_Tantibar` is false.**  For `c = -15/2` and `z = -13/4`
(both hypotheses of the statement hold: the orbit is real, escaping and never zero) the product
formula fails the Böttcher equation by the factor `exp (I π/4)`.  The two sides have the same
modulus (`1.2924796023812295`), but `bottcher c (T_c z)` is `exp (2 G_c z) * exp (I π/4)` while
`conj (bottcher c z)^2` is the positive real `exp (2 G_c z)`. -/
theorem bottcher_comm_Tantibar_false :
    bottcher ((-15 / 2 : ℝ) : ℂ)
        (LeanEval.ComplexAnalysis.Tantibar ((-15 / 2 : ℝ) : ℂ) ((-13 / 4 : ℝ) : ℂ))
      ≠ (starRingEnd ℂ) (bottcher ((-15 / 2 : ℝ) : ℂ) ((-13 / 4 : ℝ) : ℂ)) ^ 2 := by
  intro hcon
  have hcz : LeanEval.ComplexAnalysis.Tantibar ((-15 / 2 : ℝ) : ℂ) ((-13 / 4 : ℝ) : ℂ)
      = ((49 / 16 : ℝ) : ℂ) := by
    rw [Tantibar_ofReal]
    norm_num
  have hsumm_z : Summable
      (fun n : ℕ => bottcherTerm ((-15 / 2 : ℝ) : ℂ) n (((-13 / 4 : ℝ) : ℂ))) :=
    summable_bottcherTerm_of_norm_ge _ _ (by norm_num) counterexample_norm_ge_z
  have hsumm_T : Summable
      (fun n : ℕ => bottcherTerm ((-15 / 2 : ℝ) : ℂ) n (((49 / 16 : ℝ) : ℂ))) :=
    summable_bottcherTerm_of_norm_ge _ _ (by norm_num) counterexample_norm_ge_Tz
  -- the imaginary part of the `z`-product is `0`
  have him_z : (bottcher ((-15 / 2 : ℝ) : ℂ) (((-13 / 4 : ℝ) : ℂ))).im = 0 := by
    have h1 : Tendsto
        (fun N : ℕ => (bottcherPartial ((-15 / 2 : ℝ) : ℂ) N (((-13 / 4 : ℝ) : ℂ))).im)
        atTop (𝓝 ((bottcher ((-15 / 2 : ℝ) : ℂ) (((-13 / 4 : ℝ) : ℂ))).im)) :=
      (Complex.continuous_im.tendsto _).comp
        (tendsto_bottcherPartial_of_summable _ _ hsumm_z)
    have h2 : (fun N : ℕ => (bottcherPartial ((-15 / 2 : ℝ) : ℂ) N (((-13 / 4 : ℝ) : ℂ))).im)
        =ᶠ[atTop] fun _ : ℕ => (0 : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      exact counterexample_im_partial_z N hN
    exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' h2.symm)
  -- the imaginary part of the `T_c z`-product is positive
  have hTpos : 0 < (bottcher ((-15 / 2 : ℝ) : ℂ) (((49 / 16 : ℝ) : ℂ))).im := by
    have h1 : Tendsto
        (fun N : ℕ => (bottcherPartial ((-15 / 2 : ℝ) : ℂ) N (((49 / 16 : ℝ) : ℂ))).im)
        atTop (𝓝 ((bottcher ((-15 / 2 : ℝ) : ℂ) (((49 / 16 : ℝ) : ℂ))).im)) :=
      (Complex.continuous_im.tendsto _).comp
        (tendsto_bottcherPartial_of_summable _ _ hsumm_T)
    have h2 : ∀ᶠ N : ℕ in atTop,
        Real.sin (Real.pi / 4)
          ≤ (bottcherPartial ((-15 / 2 : ℝ) : ℂ) N (((49 / 16 : ℝ) : ℂ))).im := by
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      exact counterexample_im_partial_Tz N hN
    have h3 : Real.sin (Real.pi / 4)
        ≤ (bottcher ((-15 / 2 : ℝ) : ℂ) (((49 / 16 : ℝ) : ℂ))).im := ge_of_tendsto h1 h2
    have h4 : 0 < Real.sin (Real.pi / 4) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    linarith
  have hrhs : ((starRingEnd ℂ) (bottcher ((-15 / 2 : ℝ) : ℂ) (((-13 / 4 : ℝ) : ℂ)))^2).im
      = 0 := by
    have hconj : (starRingEnd ℂ) (bottcher ((-15 / 2 : ℝ) : ℂ) (((-13 / 4 : ℝ) : ℂ)))
        = bottcher ((-15 / 2 : ℝ) : ℂ) (((-13 / 4 : ℝ) : ℂ)) :=
      Complex.conj_eq_iff_im.mpr him_z
    rw [hconj, pow_two, Complex.mul_im, him_z]
    ring
  rw [hcz] at hcon
  rw [hcon] at hTpos
  rw [hrhs] at hTpos
  exact lt_irrefl 0 hTpos
/-! ## Both hypotheses of the statement hold for the counterexample -/

/-- The orbit of the counterexample escapes to infinity. -/
theorem counterexample_escaping :
    Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar ((-15 / 2 : ℝ) : ℂ))^[n]
      (((-13 / 4 : ℝ) : ℂ))‖) atTop atTop := by
  have h4 : (LeanEval.ComplexAnalysis.Tantibar ((-15 / 2 : ℝ) : ℂ))^[4]
      (((-13 / 4 : ℝ) : ℂ)) = ((35470450561 / 4294967296 : ℝ) : ℂ) := by
    rw [Tantibar_iterate_ofReal, counterexample_values.2.2.2.2]
  have hlt : max 2 ‖((-15 / 2 : ℝ) : ℂ)‖ < ‖((35470450561 / 4294967296 : ℝ) : ℂ)‖ := by
    norm_num
  have h1 : Work.ParamRays.Escaping ((-15 / 2 : ℝ) : ℂ)
      ((35470450561 / 4294967296 : ℝ) : ℂ) :=
    Work.ParamRays.escaping_of_lt_norm _ _ hlt
  have h2 : ∀ m : ℕ, Work.ParamRays.orbit ((-15 / 2 : ℝ) : ℂ)
      ((35470450561 / 4294967296 : ℝ) : ℂ) m
      = (LeanEval.ComplexAnalysis.Tantibar ((-15 / 2 : ℝ) : ℂ))^[4 + m]
        (((-13 / 4 : ℝ) : ℂ)) := by
    intro m
    rw [Work.ParamRays.orbit, ← h4,
      ← Function.iterate_add_apply (LeanEval.ComplexAnalysis.Tantibar ((-15 / 2 : ℝ) : ℂ)) m 4
        (((-13 / 4 : ℝ) : ℂ)), Nat.add_comm]
  rw [Work.ParamRays.Escaping] at h1
  rw [Filter.tendsto_atTop_atTop] at h1 ⊢
  intro b
  obtain ⟨N, hN⟩ := h1 b
  refine ⟨N + 4, fun n hn => ?_⟩
  have hm : N ≤ n - 4 := by omega
  have h := hN (n - 4) hm
  rw [h2 (n - 4), show 4 + (n - 4) = n from by omega] at h
  exact h

/-- The orbit of the counterexample never hits zero. -/
theorem counterexample_orbit_ne_zero (n : ℕ) :
    (LeanEval.ComplexAnalysis.Tantibar ((-15 / 2 : ℝ) : ℂ))^[n] (((-13 / 4 : ℝ) : ℂ)) ≠ 0 := by
  rw [Tantibar_iterate_ofReal]
  exact_mod_cast counterexample_ne_zero n

/-- **The requested statement is false.**  There are `c z` satisfying both hypotheses of
`Work.Bottcher.Core.bottcher_comm_Tantibar` for which its conclusion fails; here
`c = -15/2`, `z = -13/4`. -/
theorem counterexample_refutes_statement :
    ∃ c z : ℂ,
      Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖) atTop atTop ∧
      (∀ n : ℕ, (LeanEval.ComplexAnalysis.Tantibar c)^[n] z ≠ 0) ∧
      bottcher c (LeanEval.ComplexAnalysis.Tantibar c z) ≠ (starRingEnd ℂ) (bottcher c z) ^ 2 :=
  ⟨((-15 / 2 : ℝ) : ℂ), (((-13 / 4 : ℝ) : ℂ)), counterexample_escaping,
    counterexample_orbit_ne_zero, bottcher_comm_Tantibar_false⟩

end Work.Bottcher.Core
