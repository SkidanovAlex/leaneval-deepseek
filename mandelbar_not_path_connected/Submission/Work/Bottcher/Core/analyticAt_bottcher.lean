/-
# Analyticity of the Böttcher coordinate of the tricorn

`bottcher c z = z * exp (∑' n, 4^{-(n+1)} log (normFactor c ((pMap c)^[n] z)))`.

The goal of this file is `analyticAt_bottcher`: the Böttcher coordinate is analytic at
every point with `‖z‖ ≥ escapeRadius c`.  The proof is a Weierstrass-type argument for the
series of logarithms: on a small ball around `z` every term of the series is holomorphic
(the `p_c`-orbit stays far from the origin, where `normFactor c` is close to `1`), and the
derivatives of the terms are dominated by a summable sequence, so the series is
holomorphic there.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function Metric
open scoped Topology ComplexConjugate
open LeanEval.ComplexAnalysis (Tantibar)

namespace Work.Bottcher.Core

noncomputable section

variable {c : ℂ}

/-! ## Holomorphic data of the second iterate `p_c`

`p_c(u) = (u^2 + c̄)^2 + c` is monic of degree `4`, so
`normFactor c v = p_c v / v^4 = 1 + O(v^{-2})`; the correction term and the relevant
derivatives are gathered here. -/

/-- The derivative `p_c'(u) = 4 u (u^2 + c̄)` of the monic quartic `p_c`. -/
def pDeriv (c u : ℂ) : ℂ := 4 * u * (u ^ 2 + conj c)

/-- The `O(v^{-2})` correction: `normFactor c v = 1 + nfG c v` for `v ≠ 0`. -/
def nfG (c v : ℂ) : ℂ := (2 * conj c * v ^ 2 + (conj c) ^ 2 + c) / v ^ 4

/-- The derivative of `nfG c v = -4 c̄/v^3 - 4 (c̄^2 + c)/v^5` (`v ≠ 0`). -/
def dnf (c v : ℂ) : ℂ := (-4 * conj c) / v ^ 3 - 4 * ((conj c) ^ 2 + c) / v ^ 5

/-- The logarithmic derivative of `normFactor c`. -/
def dlognf (c v : ℂ) : ℂ := dnf c v / Work.Bottcher.normFactor c v

/-- The derivative of the `n`-fold iterate of `p_c`, defined recursively. -/
def Pd (c : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  Nat.rec 1 (fun k ih => pDeriv c ((Work.Bottcher.pMap c)^[k] w) * ih) n

@[simp] lemma Pd_zero (c : ℂ) (w : ℂ) : Pd c 0 w = 1 := rfl

@[simp] lemma Pd_succ (c : ℂ) (n : ℕ) (w : ℂ) :
    Pd c (n + 1) w = pDeriv c ((Work.Bottcher.pMap c)^[n] w) * Pd c n w := rfl

/-- The candidate derivative of the `n`-th term of the Böttcher series. -/
def btDeriv (c : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  ((1 / 4 : ℝ) ^ (n + 1) : ℂ) * (dlognf c ((Work.Bottcher.pMap c)^[n] w) * Pd c n w)

/-- The summable majorant for the derivative of the `n`-th term. -/
def uSeq (c : ℂ) (n : ℕ) : ℝ := (8 * ‖c‖ + 8) * (1 / 4) ^ n

/-! ## Elementary real bounds

The orbit of a point with `‖w‖ ≥ 2 + ‖c‖` grows; the relevant numerical estimates are
collected here. -/

/-- `(r^2 - t)^2 - t ≥ r^4/2` for `r ≥ 2 + t`, `t ≥ 0`. -/
lemma pow_four_div_two_le_sub {t r : ℝ} (ht : 0 ≤ t) (hr : 2 + t ≤ r) :
    r ^ 4 / 2 ≤ (r ^ 2 - t) ^ 2 - t := by
  have h : (0 : ℝ) ≤ r - 2 := by linarith
  nlinarith [sq_nonneg (r - 2), pow_nonneg h 3, pow_nonneg h 4]

/-- `r ≤ r^2 - t` for `r ≥ 1 + t`, `t ≥ 0`. -/
lemma le_sq_sub {t r : ℝ} (ht : 0 ≤ t) (hr : 1 + t ≤ r) : r ≤ r ^ 2 - t := by nlinarith

/-- `1 + t ≤ r^2 - t` for `r ≥ 1 + t`, `t ≥ 0`. -/
lemma one_add_le_sq_sub {t r : ℝ} (ht : 0 ≤ t) (hr : 1 + t ≤ r) : 1 + t ≤ r ^ 2 - t := by
  nlinarith

/-- `r ≤ r^4/2` for `r ≥ 2`. -/
lemma le_pow_four_div_two {r : ℝ} (hr : 2 ≤ r) : r ≤ r ^ 4 / 2 := by
  nlinarith [sq_nonneg r, pow_nonneg (by linarith : (0 : ℝ) ≤ r) 3]

/-- `2 + t ≤ r^4/2` for `r ≥ 2 + t`, `t ≥ 0`. -/
lemma two_add_le_pow_four_div_two {t r : ℝ} (ht : 0 ≤ t) (hr : 2 + t ≤ r) :
    2 + t ≤ r ^ 4 / 2 := by
  have h1 : (2 + t) ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (by linarith) hr 4
  have h2 : (0 : ℝ) ≤ 2 + t := by linarith
  nlinarith [h1, h2, sq_nonneg (2 + t), pow_nonneg h2 3]

/-- The numerical bound behind `‖nfG c v‖ ≤ 3/4`. -/
lemma two_t_div_sq_add_div_pow_le {t : ℝ} (ht : 0 ≤ t) :
    2 * t / (1 + t) ^ 2 + (t ^ 2 + t) / (1 + t) ^ 4 ≤ 3 / 4 := by
  have h1 : (0 : ℝ) < (1 + t) ^ 3 := by positivity
  have h2 : 2 * t / (1 + t) ^ 2 + (t ^ 2 + t) / (1 + t) ^ 4 = t * (2 * t + 3) / (1 + t) ^ 3 := by
    field_simp
    ring
  rw [h2, div_le_iff₀ h1]
  nlinarith [pow_nonneg ht 3, sq_nonneg (t - 3 / 2)]

/-- Two auxiliary growth lemmas for a sequence dominating `B n ↦ B n^4 / 2`. -/
private lemma prod_div_le_aux (B : ℕ → ℝ) (hB : ∀ n, 2 ≤ B n)
    (hstep : ∀ n, B n ^ 4 / 2 ≤ B (n + 1)) :
    ∀ n, (∏ k ∈ Finset.range n, B k ^ 3) / B n ^ 2 ≤ (1 / 2) ^ n := by
  have hkey : ∀ x y : ℝ, 2 ≤ x → x ^ 4 / 2 ≤ y → x ^ 5 ≤ y ^ 2 / 2 := by
    intro x y hx hy
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hsq : (x ^ 4 / 2) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
    have hx3 : (8 : ℝ) ≤ x ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 3
      norm_num at h
      exact h
    nlinarith [hsq, hx3, hx0]
  have hBpos : ∀ n, (0 : ℝ) < B n := fun n => by linarith [hB n]
  have hmain : ∀ n, (∏ k ∈ Finset.range n, B k ^ 3) ≤ (1 / 2) ^ n * B n ^ 2 := by
    intro n
    induction n with
    | zero =>
        rw [Finset.prod_range_zero, pow_zero, one_mul]
        nlinarith [hB 0]
    | succ n ih =>
        have h2' := hkey (B n) (B (n + 1)) (hB n) (hstep n)
        have h2 : B n ^ 5 ≤ (1 / 2) * B (n + 1) ^ 2 := by nlinarith [h2']
        calc (∏ k ∈ Finset.range (n + 1), B k ^ 3)
            = (∏ k ∈ Finset.range n, B k ^ 3) * B n ^ 3 := Finset.prod_range_succ _ _
          _ ≤ ((1 / 2) ^ n * B n ^ 2) * B n ^ 3 :=
                mul_le_mul_of_nonneg_right ih (pow_nonneg (by linarith [hB n] : (0 : ℝ) ≤ B n) 3)
          _ = (1 / 2) ^ n * B n ^ 5 := by ring
          _ ≤ (1 / 2) ^ n * ((1 / 2) * B (n + 1) ^ 2) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = (1 / 2) ^ (n + 1) * B (n + 1) ^ 2 := by rw [pow_succ]; ring
  intro n
  rw [div_le_iff₀ (pow_pos (hBpos n) 2)]
  exact hmain n

private lemma two_pow_sq_le_aux (B : ℕ → ℝ) (h0 : 2 ≤ B 0)
    (hstep : ∀ n, B n ^ 4 / 2 ≤ B (n + 1)) : ∀ n, (2 : ℝ) ^ (2 * n) ≤ B n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => norm_num; linarith
  | one =>
      have h0' : (2 : ℝ) ^ 4 ≤ B 0 ^ 4 := pow_le_pow_left₀ (by norm_num) h0 4
      have hh : (2 : ℝ) ^ 4 / 2 ≤ B 0 ^ 4 / 2 := by linarith
      have h1 := hstep 0
      have : (2 : ℝ) ^ 4 / 2 ≤ B (0 + 1) := le_trans hh h1
      norm_num at this ⊢
      linarith
  | more n _ih1 ih2 =>
      have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * (n + 1)) := by positivity
      have h4 : ((2 : ℝ) ^ (2 * (n + 1))) ^ 4 ≤ (B (n + 1)) ^ 4 :=
        pow_le_pow_left₀ hpos ih2 4
      have hstep' : (B (n + 1)) ^ 4 / 2 ≤ B (n + 2) := by
        have h := hstep (n + 1)
        rwa [show (n + 1) + 1 = n + 2 by omega] at h
      have key : (2 : ℝ) ^ (2 * (n + 2)) * 2 ≤ ((2 : ℝ) ^ (2 * (n + 1))) ^ 4 := by
        have h : (2 : ℝ) ^ (2 * (n + 2) + 1) ≤ (2 : ℝ) ^ ((2 * (n + 1)) * 4) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        rw [pow_succ] at h
        have h' : (2 : ℝ) ^ ((2 * (n + 1)) * 4) = ((2 : ℝ) ^ (2 * (n + 1))) ^ 4 := by
          rw [pow_mul]
        rw [h'] at h
        exact h
      have hB : (B (n + 1)) ^ 4 ≤ B (n + 2) * 2 :=
        (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hstep'
      have hfin : (2 : ℝ) ^ (2 * (n + 2)) * 2 ≤ B (n + 2) * 2 :=
        le_trans key (le_trans h4 hB)
      exact le_of_mul_le_mul_right hfin (by norm_num)

/-! ## Norm estimates for `p_c` and its derivative -/

lemma norm_sq_add_conj_ge (c u : ℂ) : ‖u‖ ^ 2 - ‖c‖ ≤ ‖u ^ 2 + conj c‖ := by
  have h := norm_add_le (u ^ 2 + conj c) (-conj c)
  have h2 : (u ^ 2 + conj c) + (-conj c) = u ^ 2 := by ring
  rw [h2, norm_pow, norm_neg, Complex.norm_conj] at h
  linarith [norm_nonneg u]

lemma norm_Tantibar_ge (c u : ℂ) : ‖u‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c u‖ := by
  have h := norm_add_le (Tantibar c u) (-c)
  have h2 : Tantibar c u + (-c) = (starRingEnd ℂ u) ^ 2 := by
    rw [LeanEval.ComplexAnalysis.Tantibar]; ring
  rw [h2, norm_pow, norm_neg, Complex.norm_conj] at h
  linarith [norm_nonneg u]

/-- `‖p_c u‖ ≥ (‖u‖^2 - ‖c‖)^2 - ‖c‖`: the second iterate of a point with `‖u‖ ≥ max 1 ‖c‖`. -/
lemma norm_pMap_ge (c u : ℂ) (hu : max 1 ‖c‖ ≤ ‖u‖) :
    (‖u‖ ^ 2 - ‖c‖) ^ 2 - ‖c‖ ≤ ‖Work.Bottcher.pMap c u‖ := by
  have h1 : ‖u‖ ^ 2 - ‖c‖ ≤ ‖u ^ 2 + conj c‖ := norm_sq_add_conj_ge c u
  have hu1 : (1 : ℝ) ≤ ‖u‖ := (le_max_left _ _).trans hu
  have hut : ‖c‖ ≤ ‖u‖ := (le_max_right _ _).trans hu
  have h1' : (0 : ℝ) ≤ ‖u‖ ^ 2 - ‖c‖ := by nlinarith [norm_nonneg u]
  have h2 : (‖u‖ ^ 2 - ‖c‖) ^ 2 ≤ ‖u ^ 2 + conj c‖ ^ 2 := by
    nlinarith [norm_nonneg (u ^ 2 + conj c)]
  have h4 : ‖(u ^ 2 + conj c) ^ 2 + c‖ ≥ ‖(u ^ 2 + conj c) ^ 2‖ - ‖c‖ := by
    have h := norm_add_le ((u ^ 2 + conj c) ^ 2 + c) (-c)
    have h5 : ((u ^ 2 + conj c) ^ 2 + c) + (-c) = (u ^ 2 + conj c) ^ 2 := by ring
    rw [h5, norm_neg] at h
    linarith
  rw [norm_pow] at h4
  rw [Work.Bottcher.pMap_apply]
  linarith

set_option linter.unusedVariables false in
/-- The norm of `p_c'` on the region `‖u‖ ≥ 1 + ‖c‖`. -/
lemma norm_pDeriv_le (c u : ℂ) (hu : 1 + ‖c‖ ≤ ‖u‖) :
    ‖pDeriv c u‖ ≤ 8 * ‖u‖ ^ 3 := by
  have ht : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hu1 : (1 : ℝ) ≤ ‖u‖ := by linarith
  have h1 : ‖u ^ 2 + conj c‖ ≤ ‖u‖ ^ 2 + ‖c‖ := by
    have h := norm_add_le (u ^ 2) (conj c)
    rwa [norm_pow, Complex.norm_conj] at h
  have h2 : ‖c‖ ≤ ‖u‖ := by linarith
  have h3 : ‖c‖ ≤ ‖u‖ ^ 2 := by nlinarith
  rw [pDeriv, norm_mul, norm_mul]
  have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  rw [h4]
  nlinarith [norm_nonneg u, norm_nonneg (u ^ 2 + conj c)]

/-- The correction term `nfG` is bounded by `3/4` on `‖v‖ ≥ 1 + ‖c‖`. -/
lemma norm_nfG_le (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) : ‖nfG c v‖ ≤ 3 / 4 := by
  have ht : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hv0 : (0 : ℝ) < ‖v‖ := by linarith
  have hnum : ‖2 * conj c * v ^ 2 + (conj c) ^ 2 + c‖ ≤
      2 * ‖c‖ * ‖v‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖ := by
    have h1 : ‖2 * conj c * v ^ 2‖ = 2 * ‖c‖ * ‖v‖ ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_conj, norm_pow]
      norm_num
    have h2 : ‖(conj c) ^ 2‖ = ‖c‖ ^ 2 := by rw [norm_pow, Complex.norm_conj]
    calc ‖2 * conj c * v ^ 2 + (conj c) ^ 2 + c‖
        ≤ ‖2 * conj c * v ^ 2 + (conj c) ^ 2‖ + ‖c‖ := norm_add_le _ _
      _ ≤ (‖2 * conj c * v ^ 2‖ + ‖(conj c) ^ 2‖) + ‖c‖ := by
            linarith [norm_add_le (2 * conj c * v ^ 2) ((conj c) ^ 2)]
      _ = 2 * ‖c‖ * ‖v‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖ := by rw [h1, h2]
  have hden : ‖v ^ 4‖ = ‖v‖ ^ 4 := norm_pow v 4
  have hstep : ‖nfG c v‖ ≤ 2 * ‖c‖ / ‖v‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖v‖ ^ 4 := by
    have h4 : (0 : ℝ) < ‖v‖ ^ 4 := by positivity
    have hdiv := div_le_div_of_nonneg_right hnum h4.le
    calc ‖nfG c v‖ = ‖2 * conj c * v ^ 2 + (conj c) ^ 2 + c‖ / ‖v‖ ^ 4 := by
          rw [nfG, norm_div, hden]
      _ ≤ (2 * ‖c‖ * ‖v‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖)) / ‖v‖ ^ 4 := by
          simpa only [add_assoc] using hdiv
      _ = 2 * ‖c‖ / ‖v‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖v‖ ^ 4 := by
          field_simp
  have hmono : 2 * ‖c‖ / ‖v‖ ^ 2 + (‖c‖ ^ 2 + ‖c‖) / ‖v‖ ^ 4 ≤
      2 * ‖c‖ / (1 + ‖c‖) ^ 2 + (‖c‖ ^ 2 + ‖c‖) / (1 + ‖c‖) ^ 4 := by
    have h1 : (0 : ℝ) < 1 + ‖c‖ := by linarith
    have h2 : (1 + ‖c‖) ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ h1.le hv 2
    have h3 : (1 + ‖c‖) ^ 4 ≤ ‖v‖ ^ 4 := pow_le_pow_left₀ h1.le hv 4
    have ha : (0 : ℝ) ≤ 2 * ‖c‖ := by positivity
    have hb : (0 : ℝ) ≤ ‖c‖ ^ 2 + ‖c‖ := by positivity
    have h4 := div_le_div_of_nonneg_left ha (by positivity : (0 : ℝ) < (1 + ‖c‖) ^ 2) h2
    have h5 := div_le_div_of_nonneg_left hb (by positivity : (0 : ℝ) < (1 + ‖c‖) ^ 4) h3
    linarith
  refine hstep.trans (hmono.trans ?_)
  have := two_t_div_sq_add_div_pow_le ht
  linarith

/-! ## `normFactor` near infinity: value, plane, and derivatives -/

lemma normFactor_eq_one_add_nfG (c v : ℂ) (hv : v ≠ 0) :
    Work.Bottcher.normFactor c v = 1 + nfG c v := by
  rw [Work.Bottcher.normFactor, nfG, Work.Bottcher.pMap_apply]
  field_simp
  ring

lemma ne_zero_of_one_add_le_norm (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) : v ≠ 0 := by
  intro h
  rw [h, norm_zero] at hv
  have : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  linarith

lemma normFactor_mem_slitPlane (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) :
    Work.Bottcher.normFactor c v ∈ Complex.slitPlane := by
  rw [normFactor_eq_one_add_nfG c v (ne_zero_of_one_add_le_norm c v hv)]
  exact Complex.mem_slitPlane_of_norm_lt_one
    (lt_of_le_of_lt (norm_nfG_le c v hv) (by norm_num))

lemma norm_normFactor_ge (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) :
    1 / 4 ≤ ‖Work.Bottcher.normFactor c v‖ := by
  rw [normFactor_eq_one_add_nfG c v (ne_zero_of_one_add_le_norm c v hv)]
  have h := norm_nfG_le c v hv
  have h2 : (1 : ℝ) - ‖nfG c v‖ ≤ ‖(1 : ℂ) + nfG c v‖ := by
    have h3 := norm_sub_le ((1 : ℂ) + nfG c v) (nfG c v)
    have h4 : ((1 : ℂ) + nfG c v) - nfG c v = 1 := by ring
    rw [h4, norm_one] at h3
    linarith
  linarith

lemma norm_dnf_le (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) :
    ‖dnf c v‖ ≤ (8 * ‖c‖ + 8) / ‖v‖ ^ 3 := by
  have ht : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hv1 : (1 : ℝ) ≤ ‖v‖ := by linarith
  have hv0 : (0 : ℝ) < ‖v‖ := by linarith
  have h1 : ‖(-4 * conj c) / v ^ 3‖ = 4 * ‖c‖ / ‖v‖ ^ 3 := by
    rw [norm_div, norm_mul, norm_neg, Complex.norm_conj, norm_pow]
    norm_num
  have h2 : ‖4 * ((conj c) ^ 2 + c) / v ^ 5‖ ≤ 4 * ‖c‖ / ‖v‖ ^ 3 := by
    have hh : ‖(conj c) ^ 2 + c‖ ≤ ‖c‖ ^ 2 + ‖c‖ := by
      calc ‖(conj c) ^ 2 + c‖ ≤ ‖(conj c) ^ 2‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
    have h5 : ‖c‖ ^ 2 + ‖c‖ ≤ ‖c‖ * ‖v‖ := by
      have h6 : ‖c‖ + 1 ≤ ‖v‖ := by linarith
      nlinarith [norm_nonneg c]
    have h4 : ‖(4 : ℂ)‖ = 4 := by norm_num
    have hA : ‖4 * ((conj c) ^ 2 + c) / v ^ 5‖ ≤ 4 * (‖c‖ * ‖v‖) / ‖v‖ ^ 5 := by
      rw [norm_div, norm_mul, h4, norm_pow]
      gcongr
      exact hh.trans h5
    have hB : 4 * (‖c‖ * ‖v‖) / ‖v‖ ^ 5 = 4 * ‖c‖ / ‖v‖ ^ 4 := by
      rw [div_eq_div_iff (pow_ne_zero 5 (ne_of_gt hv0)) (pow_ne_zero 4 (ne_of_gt hv0))]
      ring
    have hC : 4 * ‖c‖ / ‖v‖ ^ 4 ≤ 4 * ‖c‖ / ‖v‖ ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hv1 (by norm_num : (3 : ℕ) ≤ 4))
    linarith [hA, hB, hC]
  rw [dnf]
  calc ‖(-4 * conj c) / v ^ 3 - 4 * ((conj c) ^ 2 + c) / v ^ 5‖
      ≤ ‖(-4 * conj c) / v ^ 3‖ + ‖4 * ((conj c) ^ 2 + c) / v ^ 5‖ := norm_sub_le _ _
    _ ≤ 4 * ‖c‖ / ‖v‖ ^ 3 + 4 * ‖c‖ / ‖v‖ ^ 3 := by rw [h1]; linarith
    _ = 8 * ‖c‖ / ‖v‖ ^ 3 := by ring
    _ ≤ (8 * ‖c‖ + 8) / ‖v‖ ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [norm_nonneg c]

lemma norm_dlognf_le (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) :
    ‖dlognf c v‖ ≤ (32 * ‖c‖ + 32) / ‖v‖ ^ 3 := by
  rw [dlognf, norm_div]
  have h1 := norm_dnf_le c v hv
  have h2 := norm_normFactor_ge c v hv
  have hvpos : (0 : ℝ) < ‖v‖ := by linarith [norm_nonneg c]
  have h3 : (0 : ℝ) < ‖Work.Bottcher.normFactor c v‖ := by linarith
  rw [div_le_iff₀ h3]
  calc ‖dnf c v‖ ≤ (8 * ‖c‖ + 8) / ‖v‖ ^ 3 := h1
    _ = ((32 * ‖c‖ + 32) / ‖v‖ ^ 3) * (1 / 4) := by ring
    _ ≤ ((32 * ‖c‖ + 32) / ‖v‖ ^ 3) * ‖Work.Bottcher.normFactor c v‖ :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The logarithm of `normFactor` is bounded on the same region. -/
lemma norm_log_normFactor_le (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) :
    ‖Complex.log (Work.Bottcher.normFactor c v)‖ ≤ 15 / 8 := by
  rw [normFactor_eq_one_add_nfG c v (ne_zero_of_one_add_le_norm c v hv)]
  have h := norm_nfG_le c v hv
  have h1 : ‖Complex.log (1 + nfG c v)‖ ≤
      ‖nfG c v‖ ^ 2 * (1 - ‖nfG c v‖)⁻¹ / 2 + ‖nfG c v‖ :=
    Complex.norm_log_one_add_le (lt_of_le_of_lt h (by norm_num))
  have h2 : (1 - ‖nfG c v‖)⁻¹ ≤ 4 := by
    have h2' : (0 : ℝ) < 1 - ‖nfG c v‖ := by linarith
    rw [inv_le_comm₀ h2' (by norm_num)]
    linarith
  have h3 : ‖nfG c v‖ ^ 2 ≤ (3 / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have h6 : ‖nfG c v‖ ^ 2 * (1 - ‖nfG c v‖)⁻¹ ≤ (3 / 4) ^ 2 * 4 := by
    exact mul_le_mul h3 h2 (inv_nonneg.mpr (by linarith)) (by norm_num)
  have h7 : (0 : ℝ) ≤ ‖nfG c v‖ := norm_nonneg _
  linarith [h1, h6, h, h7]

/-! ## Derivatives -/

lemma hasDerivAt_pMap (c u : ℂ) :
    HasDerivAt (fun z : ℂ => Work.Bottcher.pMap c z) (pDeriv c u) u := by
  have h2 : HasDerivAt (fun z : ℂ => z ^ 2 + conj c) (2 * u) u := by
    have h := (hasDerivAt_id u).pow 2
    simpa using h.add_const (conj c)
  have h4 : HasDerivAt (fun z : ℂ => (z ^ 2 + conj c) ^ 2 + c)
      (4 * u * (u ^ 2 + conj c)) u := by
    have h := (h2.pow 2).add_const c
    convert h using 1
    simp only [Nat.reduceSub, pow_one]
    ring
  have h5 : (4 * u * (u ^ 2 + conj c)) = pDeriv c u := by rw [pDeriv]
  rw [h5] at h4
  show HasDerivAt (fun z : ℂ => (z ^ 2 + conj c) ^ 2 + c) (pDeriv c u) u
  exact h4

lemma hasDerivAt_normFactor (c v : ℂ) (hv : v ≠ 0) :
    HasDerivAt (fun u : ℂ => Work.Bottcher.normFactor c u) (dnf c v) v := by
  have h1 : HasDerivAt (fun u : ℂ => Work.Bottcher.pMap c u) (pDeriv c v) v :=
    hasDerivAt_pMap c v
  have h2 : HasDerivAt (fun u : ℂ => u ^ 4) (4 * v ^ 3) v := hasDerivAt_pow 4 v
  have h3 : HasDerivAt (fun u : ℂ => Work.Bottcher.pMap c u / u ^ 4)
      ((pDeriv c v * v ^ 4 - Work.Bottcher.pMap c v * (4 * v ^ 3)) / (v ^ 4) ^ 2) v :=
    h1.div h2 (pow_ne_zero 4 hv)
  have h4 : (pDeriv c v * v ^ 4 - Work.Bottcher.pMap c v * (4 * v ^ 3)) / (v ^ 4) ^ 2
      = dnf c v := by
    rw [pDeriv, dnf, Work.Bottcher.pMap_apply]
    field_simp
    ring
  rw [h4] at h3
  show HasDerivAt (fun u : ℂ => Work.Bottcher.pMap c u / u ^ 4) (dnf c v) v
  exact h3

lemma hasDerivAt_log_normFactor (c v : ℂ) (hv : 1 + ‖c‖ ≤ ‖v‖) :
    HasDerivAt (fun u => Complex.log (Work.Bottcher.normFactor c u)) (dlognf c v) v := by
  have h := (hasDerivAt_normFactor c v (ne_zero_of_one_add_le_norm c v hv)).clog
    (normFactor_mem_slitPlane c v hv)
  simpa only [dlognf] using h

lemma hasDerivAt_pMap_iterate (c : ℂ) (n : ℕ) (w : ℂ) :
    HasDerivAt (fun z => (Work.Bottcher.pMap c)^[n] z) (Pd c n w) w := by
  induction n with
  | zero =>
      simp only [Function.iterate_zero_apply, Pd_zero]
      exact hasDerivAt_id w
  | succ n ih =>
      have h1 : HasDerivAt
          (fun z => Work.Bottcher.pMap c ((Work.Bottcher.pMap c)^[n] z))
          (pDeriv c ((Work.Bottcher.pMap c)^[n] w) * Pd c n w) w :=
        (hasDerivAt_pMap c ((Work.Bottcher.pMap c)^[n] w)).comp w ih
      rw [Pd_succ]
      have h2 : (fun z => Work.Bottcher.pMap c ((Work.Bottcher.pMap c)^[n] z))
          = (Work.Bottcher.pMap c)^[n + 1] := by
        funext z
        rw [Function.iterate_succ_apply']
      rw [h2] at h1
      exact h1

lemma norm_Pd_le (c : ℂ) (w : ℂ)
    (h : ∀ k, 1 + ‖c‖ ≤ ‖(Work.Bottcher.pMap c)^[k] w‖) (n : ℕ) :
    ‖Pd c n w‖ ≤ 8 ^ n * ∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Pd_succ, norm_mul]
      have h1 := norm_pDeriv_le c _ (h n)
      refine (mul_le_mul h1 ih (norm_nonneg _) (by positivity)).trans_eq ?_
      rw [Finset.prod_range_succ, pow_succ]
      ring

/-! ## Orbit growth for `w` in the region `‖w‖ > 2 + ‖c‖` -/

/-- One step of the growth of the `p_c`-orbit. -/
lemma pMap_norm_step (c u : ℂ) (hu : 2 + ‖c‖ ≤ ‖u‖) :
    ‖u‖ ≤ ‖Work.Bottcher.pMap c u‖ ∧ ‖u‖ ^ 4 / 2 ≤ ‖Work.Bottcher.pMap c u‖ ∧
      2 + ‖c‖ ≤ ‖Work.Bottcher.pMap c u‖ := by
  have ht : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hu1 : (2 : ℝ) ≤ ‖u‖ := by linarith
  have h2 : max 1 ‖c‖ ≤ ‖u‖ := by
    rw [max_le_iff]
    exact ⟨by linarith, by linarith⟩
  have hge := norm_pMap_ge c u h2
  have h3 : ‖u‖ ^ 4 / 2 ≤ (‖u‖ ^ 2 - ‖c‖) ^ 2 - ‖c‖ := pow_four_div_two_le_sub ht hu
  have h4 : ‖u‖ ≤ ‖u‖ ^ 4 / 2 := le_pow_four_div_two hu1
  have h5 : 2 + ‖c‖ ≤ ‖u‖ ^ 4 / 2 := two_add_le_pow_four_div_two ht hu
  exact ⟨h4.trans (h3.trans hge), h3.trans hge, h5.trans (h3.trans hge)⟩

lemma pMap_norm_iterate_ge (c w : ℂ) (hw : 2 + ‖c‖ ≤ ‖w‖) (n : ℕ) :
    2 + ‖c‖ ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ := by
  induction n with
  | zero => simpa using hw
  | succ n ih => rw [Function.iterate_succ_apply']; exact (pMap_norm_step c _ ih).2.2

lemma Tantibar_norm_ge (c u : ℂ) (hu : 1 + ‖c‖ ≤ ‖u‖) : 1 + ‖c‖ ≤ ‖Tantibar c u‖ := by
  have ht : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have h1 := norm_Tantibar_ge c u
  have h2 := one_add_le_sq_sub ht hu
  linarith

lemma pMap_norm_iterate_ge' (c w : ℂ) (hw : 1 + ‖c‖ ≤ ‖w‖) (n : ℕ) :
    1 + ‖c‖ ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ := by
  have ht : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  induction n with
  | zero => simpa using hw
  | succ n ih =>
      have h2 : Work.Bottcher.pMap c ((Work.Bottcher.pMap c)^[n] w) =
          Tantibar c (Tantibar c ((Work.Bottcher.pMap c)^[n] w)) := by
        rw [Work.Bottcher.pMap_eq_iterate_two, Function.iterate_succ_apply', Function.iterate_one]
      rw [Function.iterate_succ_apply', h2]
      exact Tantibar_norm_ge c _ (Tantibar_norm_ge c _ ih)

lemma pMap_norm_iterate_succ (c w : ℂ) (hw : 2 + ‖c‖ ≤ ‖w‖) (n : ℕ) :
    (‖(Work.Bottcher.pMap c)^[n] w‖) ^ 4 / 2 ≤ ‖(Work.Bottcher.pMap c)^[n + 1] w‖ := by
  rw [Function.iterate_succ_apply']
  exact (pMap_norm_step c _ (pMap_norm_iterate_ge c w hw n)).2.1

/-! ## The terms of the Böttcher series and their derivatives -/

/-- The `n`-th term of the Böttcher series is holomorphic on the region where all
`p_c`-iterates stay large. -/
lemma hasDerivAt_bottcherTerm (c : ℂ) (w : ℂ) (n : ℕ)
    (h : ∀ k, 1 + ‖c‖ ≤ ‖(Work.Bottcher.pMap c)^[k] w‖) :
    HasDerivAt (fun z => Work.Bottcher.bottcherTerm c n z) (btDeriv c n w) w := by
  have h1 : HasDerivAt (fun z => (Work.Bottcher.pMap c)^[n] z) (Pd c n w) w :=
    hasDerivAt_pMap_iterate c n w
  have h2 : HasDerivAt
      (fun z => Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] z)))
      (dlognf c ((Work.Bottcher.pMap c)^[n] w) * Pd c n w) w :=
    (hasDerivAt_log_normFactor c ((Work.Bottcher.pMap c)^[n] w) (h n)).comp w h1
  have h3 := h2.const_mul (((1 / 4 : ℝ) ^ (n + 1) : ℂ))
  show HasDerivAt (fun z => Work.Bottcher.bottcherTerm c n z) (btDeriv c n w) w
  exact h3

/-- The uniform bound on a single term, used for the pointwise summability of the series. -/
lemma norm_term_le (c : ℂ) (w : ℂ) (hw : 1 + ‖c‖ ≤ ‖w‖) (n : ℕ) :
    ‖Work.Bottcher.bottcherTerm c n w‖ ≤ (15 / 8) * (1 / 4) ^ n := by
  have h : 1 + ‖c‖ ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ :=
    pMap_norm_iterate_ge' c w hw n
  have h1 : ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] w))‖ ≤ 15 / 8 :=
    norm_log_normFactor_le c _ h
  have h2 : ‖(((1 / 4 : ℝ) ^ (n + 1) : ℂ))‖ = (1 / 4) ^ (n + 1) := by simp
  rw [Work.Bottcher.bottcherTerm, norm_mul, h2]
  have h3 : (1 / 4 : ℝ) ^ (n + 1) ≤ (1 / 4) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)
  calc (1 / 4 : ℝ) ^ (n + 1) *
        ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n] w))‖
      ≤ (1 / 4 : ℝ) ^ (n + 1) * (15 / 8) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (1 / 4 : ℝ) ^ n * (15 / 8) := mul_le_mul_of_nonneg_right h3 (by norm_num)
    _ = (15 / 8) * (1 / 4) ^ n := by ring

/-- The derivative of the `n`-th term is dominated by the summable sequence `uSeq c`. -/
lemma norm_btDeriv_le (c : ℂ) (w : ℂ) (hw : 2 + ‖c‖ ≤ ‖w‖) (n : ℕ) :
    ‖btDeriv c n w‖ ≤ uSeq c n := by
  have hv : ∀ k, 1 + ‖c‖ ≤ ‖(Work.Bottcher.pMap c)^[k] w‖ := fun k => by
    have := pMap_norm_iterate_ge c w hw k
    linarith [norm_nonneg c]
  have hr0 : (0 : ℝ) < ‖(Work.Bottcher.pMap c)^[n] w‖ := by linarith [hv n, norm_nonneg c]
  have hconst : ‖(((1 / 4 : ℝ) ^ (n + 1) : ℂ))‖ = (1 / 4) ^ (n + 1) := by simp
  have hdl := norm_dlognf_le c ((Work.Bottcher.pMap c)^[n] w) (hv n)
  have hPd := norm_Pd_le c w hv n
  have h1 : ‖dlognf c ((Work.Bottcher.pMap c)^[n] w) * Pd c n w‖ ≤
      ((32 * ‖c‖ + 32) / ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3) *
        (8 ^ n * ∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3) := by
    rw [norm_mul]
    exact mul_le_mul hdl hPd (norm_nonneg _) (div_nonneg (by positivity) (by positivity))
  rw [btDeriv, norm_mul, hconst]
  refine (mul_le_mul_of_nonneg_left h1 (by positivity)).trans ?_
  have hW : (∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3) /
      ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 2 ≤ (1 / 2) ^ n :=
    prod_div_le_aux (fun k => ‖(Work.Bottcher.pMap c)^[k] w‖)
      (fun k => by
        have := pMap_norm_iterate_ge c w hw k
        linarith [norm_nonneg c])
      (fun k => pMap_norm_iterate_succ c w hw k) n
  have h2p : (2 : ℝ) ^ (2 * n) ≤ ‖(Work.Bottcher.pMap c)^[n] w‖ :=
    two_pow_sq_le_aux (fun k => ‖(Work.Bottcher.pMap c)^[k] w‖)
      (by rw [Function.iterate_zero_apply]; linarith [hw, norm_nonneg c])
      (fun k => pMap_norm_iterate_succ c w hw k) n
  have hWmul : (2 : ℝ) ^ n *
      ((∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3) /
        ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 2) ≤ 1 := by
    have h1 : (2 : ℝ) ^ n * (1 / 2) ^ n = 1 := by rw [← mul_pow]; norm_num
    calc (2 : ℝ) ^ n * ((∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3) /
            ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 2)
        ≤ (2 : ℝ) ^ n * (1 / 2) ^ n := mul_le_mul_of_nonneg_left hW (by positivity)
      _ = 1 := h1
  have hpow : (1 / 4 : ℝ) ^ (n + 1) * 8 ^ n = (1 / 4) * 2 ^ n := by
    have h1 : (1 / 4 : ℝ) ^ n * 8 ^ n = 2 ^ n := by rw [← mul_pow]; norm_num
    calc (1 / 4 : ℝ) ^ (n + 1) * 8 ^ n = ((1 / 4) ^ n * (1 / 4)) * 8 ^ n := by rw [pow_succ]
      _ = (1 / 4) * ((1 / 4) ^ n * 8 ^ n) := by ring
      _ = (1 / 4) * 2 ^ n := by rw [h1]
  have hsplit : (1 / 4 : ℝ) ^ (n + 1) * ((32 * ‖c‖ + 32) / ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3 *
        (8 ^ n * ∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3))
      = (8 * ‖c‖ + 8) * ((2 : ℝ) ^ n *
          ((∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3) /
            ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 2)) / ‖(Work.Bottcher.pMap c)^[n] w‖ := by
    rw [show (1 / 4 : ℝ) ^ (n + 1) * ((32 * ‖c‖ + 32) / ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3 *
          (8 ^ n * ∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3))
        = (32 * ‖c‖ + 32) * ((1 / 4) ^ (n + 1) * 8 ^ n) *
          (∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3) /
          ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 3 by ring]
    rw [hpow]
    field_simp
    ring
  rw [hsplit]
  have h4n : (1 / 4 : ℝ) ^ n * (2 : ℝ) ^ (2 * n) = 1 := by
    have h2n : (2 : ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
    rw [h2n, ← mul_pow]
    norm_num
  have hfin : (8 * ‖c‖ + 8) * ((2 : ℝ) ^ n *
        ((∏ k ∈ Finset.range n, ‖(Work.Bottcher.pMap c)^[k] w‖ ^ 3) /
          ‖(Work.Bottcher.pMap c)^[n] w‖ ^ 2)) / ‖(Work.Bottcher.pMap c)^[n] w‖
      ≤ (8 * ‖c‖ + 8) * (1 / 4) ^ n := by
    have h8 : (0 : ℝ) ≤ 8 * ‖c‖ + 8 := by positivity
    rw [div_le_iff₀ hr0]
    have h9 : (1 / 4 : ℝ) ^ n * ‖(Work.Bottcher.pMap c)^[n] w‖ ≥ 1 := by
      have h10 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n := by positivity
      have h11 := mul_le_mul_of_nonneg_left h2p h10
      linarith
    nlinarith [hWmul, h8, h9]
  rw [uSeq]
  exact hfin

/-! ## The case `c = 0`

For the parameter `c = 0` the second iterate is just `z ↦ z^4`, `normFactor 0 v = 1` for
`v ≠ 0`, and the Böttcher coordinate is the identity. -/

lemma pMap_zero (z : ℂ) : Work.Bottcher.pMap 0 z = z ^ 4 := by
  rw [Work.Bottcher.pMap_apply]
  simp only [map_zero]
  ring

lemma pMap_zero_iterate (w : ℂ) (n : ℕ) : (Work.Bottcher.pMap 0)^[n] w = w ^ (4 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, pMap_zero, ← pow_mul, ← pow_succ]

lemma normFactor_zero (v : ℂ) (hv : v ≠ 0) : Work.Bottcher.normFactor 0 v = 1 := by
  rw [Work.Bottcher.normFactor, pMap_zero]
  exact div_self (pow_ne_zero 4 hv)

lemma bottcher_zero (w : ℂ) (hw : w ≠ 0) : Work.Bottcher.bottcher 0 w = w := by
  have hterm : ∀ n, Work.Bottcher.bottcherTerm 0 n w = 0 := by
    intro n
    have hne : w ^ (4 ^ n) ≠ 0 := pow_ne_zero _ hw
    rw [Work.Bottcher.bottcherTerm, pMap_zero_iterate, normFactor_zero _ hne, Complex.log_one,
      mul_zero]
  rw [Work.Bottcher.bottcher, Work.Bottcher.bottcherSeries]
  simp only [hterm]
  rw [tsum_zero, Complex.exp_zero, mul_one]

/-! ## The main theorem -/

theorem analyticAt_bottcher (c z : ℂ) (hz : Work.Bottcher.escapeRadius c ≤ ‖z‖) :
    AnalyticAt ℂ (Work.Bottcher.bottcher c) z := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · have hz2 : (2 : ℝ) ≤ ‖z‖ := by simpa [Work.Bottcher.escapeRadius] using hz
    have hzne : z ≠ 0 := by
      intro h
      rw [h] at hz2
      simp only [norm_zero] at hz2
      linarith
    refine (analyticAt_id (𝕜 := ℂ) (z := z)).congr ?_
    filter_upwards [isOpen_ne.mem_nhds hzne] with w hw
    exact (bottcher_zero w hw).symm
  · have ht : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    have hz' : 2 * (1 + ‖c‖) ≤ ‖z‖ := hz
    set ρ : ℝ := ‖c‖ / 2 with hρdef
    set q : ℝ := 2 * (1 + ‖c‖) - ‖c‖ / 2 with hqdef
    have hρpos : 0 < ρ := by rw [hρdef]; linarith
    have hq2 : 2 + ‖c‖ ≤ q := by rw [hqdef]; linarith
    set s : Set ℂ := Metric.ball z ρ with hsdef
    have hs_open : IsOpen s := by rw [hsdef]; exact Metric.isOpen_ball
    have hs_pre : IsPreconnected s := by rw [hsdef]; exact (convex_ball z ρ).isPreconnected
    have hs_nhds : s ∈ 𝓝 z := by rw [hsdef]; exact Metric.ball_mem_nhds z hρpos
    have hzs : z ∈ s := by rw [hsdef]; exact Metric.mem_ball_self hρpos
    have hlow : ∀ w ∈ s, q < ‖w‖ := by
      intro w hw
      rw [hsdef, Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hw
      have h1 : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
        have h := norm_add_le w (z - w)
        rwa [add_sub_cancel] at h
      rw [hρdef] at hw
      linarith
    have hmem2 : ∀ w ∈ s, 2 + ‖c‖ ≤ ‖w‖ := fun w hw => by linarith [hlow w hw, hq2]
    have hmem1 : ∀ w ∈ s, 1 + ‖c‖ ≤ ‖w‖ := fun w hw => by linarith [hmem2 w hw]
    have hderiv : ∀ n y, y ∈ s →
        HasDerivAt (fun z => Work.Bottcher.bottcherTerm c n z) (btDeriv c n y) y :=
      fun n y hy => hasDerivAt_bottcherTerm c y n (fun k => by
        have h := pMap_norm_iterate_ge c y (hmem2 y hy) k
        linarith [norm_nonneg c])
    have hbound : ∀ n y, y ∈ s → ‖btDeriv c n y‖ ≤ uSeq c n :=
      fun n y hy => norm_btDeriv_le c y (hmem2 y hy) n
    have hu : Summable (uSeq c) :=
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (8 * ‖c‖ + 8)
    have hg0 : Summable (fun n => Work.Bottcher.bottcherTerm c n z) := by
      refine Summable.of_norm_bounded (g := fun n => (15 / 8) * (1 / 4) ^ n) ?_ ?_
      · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (15 / 8)
      · intro n
        exact norm_term_le c z (hmem1 z hzs) n
    have hSeriesAt : ∀ y ∈ s, DifferentiableAt ℂ (Work.Bottcher.bottcherSeries c) y := fun y hy =>
      (hasDerivAt_tsum_of_isPreconnected hu hs_open hs_pre hderiv hbound hzs hg0 hy).differentiableAt
    have hbott : DifferentiableOn ℂ (Work.Bottcher.bottcher c) s := fun y hy =>
      (differentiableAt_id.mul (hSeriesAt y hy).cexp).differentiableWithinAt
    exact hbott.analyticAt hs_nhds

end

end Work.Bottcher.Core
