import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Escape.mem_escapeRegion_iterate
import Submission.Work.Escape.geom_le_norm_iterate
import Submission.Work.Escape.norm_le_norm_iterate
import Submission.Work.Escape.norm_iterate_le_geomSum
import Submission.Work.Escape.tendsto_norm_iterate_atTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Continuity of the Green function

For a map `f : ℂ → ℂ` with monic degree-`d` growth (`MonicGrowth f d A`, `d ≥ 2`) the Green
function `green f d z = lim_n d^{-n} log⁺ ‖f^[n] z‖` is continuous on `ℂ`.

The proof is the classical one: **the partial Green functions converge uniformly**, and a uniform
limit of continuous functions is continuous.

Fix the escape radius `R = max 2 A` and put `B_k = ‖f^[k] z‖`.  The two regimes of the orbit give
the uniform increment bound

`|greenIter f d z (k+1) - greenIter f d z k| ≤ d^{-k} (log⁺ R + log (2 R^d))`,

valid for every `z ∈ ℂ`:

* if `B_k ≤ R`, then `B_{k+1} ≤ B_k^d + A ≤ R^d + A ≤ 2 R^d` (using `A ≤ R ≤ R^d`), so
  `log⁺ B_{k+1} ≤ log (2 R^d)` and `log⁺ B_k ≤ log⁺ R`, whence
  `|greenIter (k+1) - greenIter k| ≤ d^{-(k+1)} log (2 R^d) + d^{-k} log⁺ R`;
* if `B_k > R ≥ max 2 A`, the orbit has escaped the escape radius; the norms increase and the
  ratios `B_{k+1} / B_k^d` stay in `[1/2, 3/2]`, so the difference is at most `d^{-(k+1)} log 2`.

Summing the increments along the orbit (a geometric series of ratio `d^{-1} ≤ 1/2`) gives the
uniform tail bound, valid for every `z ∈ ℂ` and every `n`,

`|green f d z - greenIter f d z n| ≤ 2 (log⁺ R + log (2 R^d)) d^{-n}`,

i.e. `TendstoUniformlyOn` of the partial Green functions on all of `ℂ` (and a fortiori on every
ball).
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

/-! ## The elementary ratio bound -/

/-- Elementary logarithmic bound: if `r ≥ 2`, `A < r` and `r^d - A ≤ s ≤ r^d + A` with `d ≥ 2`,
then `|log (s / r^d)| ≤ log 2`, i.e. the ratio `s / r^d` stays within a factor `2` of `1`. -/
private lemma log_ratio_abs_le' {d : ℕ} (hd : 2 ≤ d) {A r s : ℝ}
    (hr2 : 2 < r) (hrA : A < r) (hs1 : r ^ d - A ≤ s) (hs2 : s ≤ r ^ d + A) :
    |Real.log (s / r ^ d)| ≤ Real.log 2 := by
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hrd_pos : 0 < r ^ d := pow_pos (by linarith) d
  have hsq : r ^ 2 ≤ r ^ d := pow_le_pow_right₀ hr1 hd
  have hrd_half : r ≤ r ^ d / 2 := by nlinarith
  have hA_lt : A < r ^ d / 2 := by linarith
  have hlo : r ^ d / 2 < s := by linarith
  have hhi : s < 3 / 2 * r ^ d := by linarith
  have hratio_pos : 0 < s / r ^ d := div_pos (by linarith) hrd_pos
  have h1 : (r ^ d / 2) / r ^ d = (1 : ℝ) / 2 := by field_simp
  have h2 : (3 / 2 * r ^ d) / r ^ d = (3 : ℝ) / 2 := by
    rw [mul_div_cancel_right₀ _ hrd_pos.ne']
  have hlo' : (1 : ℝ) / 2 < s / r ^ d := by
    rw [← h1]; exact div_lt_div_of_pos_right hlo hrd_pos
  have hhi' : s / r ^ d < 3 / 2 := by
    rw [← h2]; exact div_lt_div_of_pos_right hhi hrd_pos
  have hloglo : Real.log (1 / 2) ≤ Real.log (s / r ^ d) :=
    Real.log_le_log (by norm_num) hlo'.le
  have hloghi : Real.log (s / r ^ d) ≤ Real.log (3 / 2) :=
    Real.log_le_log hratio_pos hhi'.le
  have h32 : Real.log (3 / 2) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
  have hhalf : Real.log (1 / 2) = - Real.log 2 := by
    rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
  rw [abs_le]
  constructor <;> linarith

/-! ## Increment bounds for the partial Green functions -/

/-- **Increment bound on the escaping region.**  If the `n`-th iterate of `z` lies in the escaping
region `{w | max 2 A < ‖w‖}` then the successive differences of the partial Green functions are
bounded by `d^{-(n+1)} log 2`. -/
private lemma greenIter_step_le_escape (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) {z : ℂ} {n : ℕ} (hz : (f^[n]) z ∈ escapeRegion A) :
    |greenIter f d z (n + 1) - greenIter f d z n| ≤ ((d : ℝ) ^ (n + 1))⁻¹ * Real.log 2 := by
  have hstep : (f^[n + 1]) z = f ((f^[n]) z) := Function.iterate_succ_apply' f n z
  have hr2 : 2 < ‖(f^[n]) z‖ := two_lt_norm_of_mem_escapeRegion hz
  have hrA : A < ‖(f^[n]) z‖ := lt_norm_of_mem_escapeRegion hz
  have hr1 : (1 : ℝ) ≤ ‖(f^[n]) z‖ := by linarith
  have hr_pos : 0 < ‖(f^[n]) z‖ := by linarith
  have hsq : ‖(f^[n]) z‖ ^ 2 ≤ ‖(f^[n]) z‖ ^ d := pow_le_pow_right₀ hr1 hd
  have hA_lt : A < ‖(f^[n]) z‖ ^ d / 2 := by nlinarith
  have hs_ge : ‖(f^[n]) z‖ ^ d - A ≤ ‖(f^[n + 1]) z‖ := by
    rw [hstep]; exact h.le_norm _
  have hs_le : ‖(f^[n + 1]) z‖ ≤ ‖(f^[n]) z‖ ^ d + A := by
    rw [hstep]; exact h.norm_le _
  have hs_pos : 0 < ‖(f^[n + 1]) z‖ := by
    have : (0 : ℝ) < ‖(f^[n]) z‖ ^ d := pow_pos hr_pos d
    linarith
  have hs1 : (1 : ℝ) ≤ ‖(f^[n + 1]) z‖ := by
    have : (1 : ℝ) ≤ ‖(f^[n]) z‖ ^ d := by nlinarith [hsq, hr2, pow_pos hr_pos d]
    nlinarith
  have hlogr : logPos ‖(f^[n]) z‖ = Real.log ‖(f^[n]) z‖ := logPos_eq_log hr1
  have hlogs : logPos ‖(f^[n + 1]) z‖ = Real.log ‖(f^[n + 1]) z‖ := logPos_eq_log hs1
  have hratio : |Real.log (‖(f^[n + 1]) z‖ / ‖(f^[n]) z‖ ^ d)| ≤ Real.log 2 :=
    log_ratio_abs_le' hd hr2 hrA hs_ge hs_le
  have hid : greenIter f d z (n + 1) - greenIter f d z n
      = ((d : ℝ) ^ (n + 1))⁻¹ * Real.log (‖(f^[n + 1]) z‖ / ‖(f^[n]) z‖ ^ d) := by
    rw [greenIter_def, greenIter_def, hlogr, hlogs]
    have hlogdiv : Real.log (‖(f^[n + 1]) z‖ / ‖(f^[n]) z‖ ^ d)
        = Real.log ‖(f^[n + 1]) z‖ - (d : ℝ) * Real.log ‖(f^[n]) z‖ := by
      rw [Real.log_div hs_pos.ne' (pow_ne_zero d hr_pos.ne'), Real.log_pow]
    rw [hlogdiv]
    rw [pow_succ, mul_inv]
    field_simp
  rw [hid, abs_mul]
  have hnn : 0 ≤ ((d : ℝ) ^ (n + 1))⁻¹ := by positivity
  rw [abs_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_left hratio hnn

/-- **Increment bound while the orbit stays inside the ball of radius `R`.**  If `max 2 A ≤ R` and
the `k`-th iterate of `z` satisfies `‖f^[k] z‖ ≤ R`, then one step of the orbit cannot overshoot
`2 R^d`, and the successive differences of the partial Green functions are bounded by
`d^{-(k+1)} log (2 R^d) + d^{-k} log⁺ R`. -/
private lemma greenIter_step_le_bounded (f : ℂ → ℂ) (d : ℕ) (A R : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) (hR : max 2 A ≤ R) {z : ℂ} {k : ℕ} (hk : ‖(f^[k]) z‖ ≤ R) :
    |greenIter f d z (k + 1) - greenIter f d z k| ≤
      ((d : ℝ) ^ (k + 1))⁻¹ * Real.log (2 * R ^ d) + ((d : ℝ) ^ k)⁻¹ * logPos R := by
  have hR2 : (2 : ℝ) ≤ R := (le_max_left 2 A).trans hR
  have hA : A ≤ R := (le_max_right 2 A).trans hR
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hRd : R ≤ R ^ d := by
    calc R = R ^ 1 := (pow_one R).symm
      _ ≤ R ^ d := pow_le_pow_right₀ hR1 (by omega)
  have hB : ‖(f^[k + 1]) z‖ ≤ 2 * R ^ d := by
    rw [Function.iterate_succ_apply']
    have h1 : ‖f ((f^[k]) z)‖ ≤ ‖(f^[k]) z‖ ^ d + A := h.norm_le _
    have h2 : ‖(f^[k]) z‖ ^ d ≤ R ^ d := pow_le_pow_left₀ (norm_nonneg _) hk d
    linarith
  have hlogb : logPos ‖(f^[k + 1]) z‖ ≤ Real.log (2 * R ^ d) :=
    (logPos_mono hB).trans
      (le_of_eq (logPos_eq_log (by nlinarith [one_le_pow₀ hR1 (n := d)])))
  have hloga : logPos ‖(f^[k]) z‖ ≤ logPos R := logPos_mono hk
  have hstep1 : greenIter f d z (k + 1) ≤ ((d : ℝ) ^ (k + 1))⁻¹ * Real.log (2 * R ^ d) := by
    rw [greenIter_def]
    exact mul_le_mul_of_nonneg_left hlogb (by positivity)
  have hstep0 : greenIter f d z k ≤ ((d : ℝ) ^ k)⁻¹ * logPos R := by
    rw [greenIter_def]
    exact mul_le_mul_of_nonneg_left hloga (by positivity)
  have hnn1 : 0 ≤ greenIter f d z (k + 1) := greenIter_nonneg f d z (k + 1)
  have hnn0 : 0 ≤ greenIter f d z k := greenIter_nonneg f d z k
  have habs : |greenIter f d z (k + 1) - greenIter f d z k| ≤
      greenIter f d z (k + 1) + greenIter f d z k := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  linarith

/-- **Uniform increment bound.**  For `R ≥ max 2 A` and every `z : ℂ` the successive differences of
the partial Green functions are bounded by `d^{-k} (log⁺ R + log (2 R^d))`, uniformly in `z`. -/
theorem greenIter_step_abs_le (f : ℂ → ℂ) (d : ℕ) (A R : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) (hR : max 2 A ≤ R) (z : ℂ) (k : ℕ) :
    |greenIter f d z (k + 1) - greenIter f d z k| ≤
      ((d : ℝ) ^ k)⁻¹ * (logPos R + Real.log (2 * R ^ d)) := by
  have hR2 : (2 : ℝ) ≤ R := (le_max_left 2 A).trans hR
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlogpos : 0 ≤ Real.log (2 * R ^ d) :=
    Real.log_nonneg (by nlinarith [one_le_pow₀ hR1 (n := d)])
  have hlog2R : Real.log 2 ≤ Real.log (2 * R ^ d) :=
    Real.log_le_log (by norm_num) (by nlinarith [one_le_pow₀ hR1 (n := d)])
  have hInv : ((d : ℝ) ^ (k + 1))⁻¹ ≤ ((d : ℝ) ^ k)⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity), pow_succ]
    exact le_mul_of_one_le_right (by positivity) (by linarith : (1 : ℝ) ≤ (d : ℝ))
  rcases le_or_gt ‖(f^[k]) z‖ R with hk | hk
  · have hb := greenIter_step_le_bounded f d A R h hd hR hk
    have hb' : ((d : ℝ) ^ (k + 1))⁻¹ * Real.log (2 * R ^ d) + ((d : ℝ) ^ k)⁻¹ * logPos R
        ≤ ((d : ℝ) ^ k)⁻¹ * (logPos R + Real.log (2 * R ^ d)) := by
      have h1 : ((d : ℝ) ^ (k + 1))⁻¹ * Real.log (2 * R ^ d)
          ≤ ((d : ℝ) ^ k)⁻¹ * Real.log (2 * R ^ d) :=
        mul_le_mul_of_nonneg_right hInv hlogpos
      have h2 : ((d : ℝ) ^ k)⁻¹ * (logPos R + Real.log (2 * R ^ d))
          = ((d : ℝ) ^ k)⁻¹ * Real.log (2 * R ^ d) + ((d : ℝ) ^ k)⁻¹ * logPos R := by ring
      linarith
    linarith
  · have hEsc : (f^[k]) z ∈ escapeRegion A := lt_of_le_of_lt hR hk
    have hb := greenIter_step_le_escape f d A h hd hEsc
    have hb' : ((d : ℝ) ^ (k + 1))⁻¹ * Real.log 2
        ≤ ((d : ℝ) ^ k)⁻¹ * (logPos R + Real.log (2 * R ^ d)) := by
      have h1 : ((d : ℝ) ^ (k + 1))⁻¹ * Real.log 2 ≤ ((d : ℝ) ^ k)⁻¹ * Real.log 2 :=
        mul_le_mul_of_nonneg_right hInv (Real.log_nonneg (by norm_num))
      have h2 : ((d : ℝ) ^ k)⁻¹ * Real.log 2 ≤ ((d : ℝ) ^ k)⁻¹ * Real.log (2 * R ^ d) :=
        mul_le_mul_of_nonneg_left hlog2R (by positivity)
      have h3 : ((d : ℝ) ^ k)⁻¹ * Real.log (2 * R ^ d)
          ≤ ((d : ℝ) ^ k)⁻¹ * (logPos R + Real.log (2 * R ^ d)) :=
        mul_le_mul_of_nonneg_left (by linarith [logPos_nonneg R]) (by positivity)
      linarith
    linarith

/-! ## The uniform tail bound -/

/-- **Telescoping bound.**  Summing the increments along the orbit: for `R ≥ max 2 A`, every
`z : ℂ` and every `n ≤ m`,

`|greenIter m - greenIter n| ≤ 2 (log⁺ R + log (2 R^d)) (d^{-n} - d^{-m})`. -/
private lemma greenIter_sub_le' (f : ℂ → ℂ) (d : ℕ) (A R : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) (hR : max 2 A ≤ R) (z : ℂ) :
    ∀ n m : ℕ, n ≤ m →
      |greenIter f d z m - greenIter f d z n| ≤
        (2 * (logPos R + Real.log (2 * R ^ d))) * (((d : ℝ) ^ n)⁻¹ - ((d : ℝ) ^ m)⁻¹) := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hR2 : (2 : ℝ) ≤ R := (le_max_left 2 A).trans hR
  have hR1 : (1 : ℝ) ≤ R := by linarith
  set K : ℝ := logPos R + Real.log (2 * R ^ d) with hKdef
  set C : ℝ := 2 * K with hCdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have h1 := logPos_nonneg R
    have h2 : 0 ≤ Real.log (2 * R ^ d) := Real.log_nonneg (by nlinarith [one_le_pow₀ hR1 (n := d)])
    linarith
  have hC0 : 0 ≤ C := by rw [hCdef]; linarith
  have hkey : K ≤ C * (1 - (d : ℝ)⁻¹) := by
    have h1 : (d : ℝ)⁻¹ ≤ 1 / 2 := by
      have h := (inv_le_inv₀ hdpos (by norm_num : (0 : ℝ) < 2)).mpr hdR
      simpa using h
    have h2 : C * (1 / 2) ≤ C * (1 - (d : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    rw [hCdef] at h2
    linarith
  have hstep : ∀ k : ℕ, |greenIter f d z (k + 1) - greenIter f d z k| ≤ ((d : ℝ) ^ k)⁻¹ * K := by
    intro k
    have hthis := greenIter_step_abs_le f d A R h hd hR z k
    rw [← hKdef] at hthis
    exact hthis
  have key : ∀ m : ℕ, ∀ n : ℕ, n ≤ m →
      |greenIter f d z m - greenIter f d z n| ≤ C * (((d : ℝ) ^ n)⁻¹ - ((d : ℝ) ^ m)⁻¹) := by
    intro m
    induction m with
    | zero =>
      intro n hn
      have hn0 : n = 0 := Nat.le_zero.mp hn
      subst hn0
      simp
    | succ m ih =>
      intro n hn
      rcases Nat.eq_or_lt_of_le hn with h' | h'
      · subst h'
        simp
      · have hnm : n ≤ m := Nat.lt_succ_iff.mp h'
        have hih := ih n hnm
        have hstepm := hstep m
        have hA : ((d : ℝ) ^ (m + 1))⁻¹ = ((d : ℝ) ^ m)⁻¹ * (d : ℝ)⁻¹ := by
          rw [pow_succ, mul_inv]
        have hpos : (0 : ℝ) < ((d : ℝ) ^ m)⁻¹ := by positivity
        have harith : ((d : ℝ) ^ m)⁻¹ * K + C * (((d : ℝ) ^ n)⁻¹ - ((d : ℝ) ^ m)⁻¹)
            ≤ C * (((d : ℝ) ^ n)⁻¹ - ((d : ℝ) ^ (m + 1))⁻¹) := by
          rw [hA]
          have hmul := mul_le_mul_of_nonneg_right hkey hpos.le
          nlinarith [hmul]
        have htri := abs_sub_le (greenIter f d z (m + 1)) (greenIter f d z m) (greenIter f d z n)
        linarith
  intro n m hnm
  exact key m n hnm

/-- **Uniform tail bound.**  For `R ≥ max 2 A` the partial Green functions approximate `green f d`
uniformly on all of `ℂ`:

`|green f d z - greenIter f d z n| ≤ 2 (log⁺ R + log (2 R^d)) d^{-n}`. -/
theorem abs_green_sub_greenIter_le (f : ℂ → ℂ) (d : ℕ) (A R : ℝ) (h : MonicGrowth f d A)
    (hd : 2 ≤ d) (hR : max 2 A ≤ R) (z : ℂ) (n : ℕ) :
    |green f d z - greenIter f d z n| ≤
      (2 * (logPos R + Real.log (2 * R ^ d))) * ((d : ℝ) ^ n)⁻¹ := by
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hR2 : (2 : ℝ) ≤ R := (le_max_left 2 A).trans hR
  have hR1 : (1 : ℝ) ≤ R := by linarith
  set K : ℝ := logPos R + Real.log (2 * R ^ d) with hKdef
  set C : ℝ := 2 * K with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef, hKdef]
    have h1 := logPos_nonneg R
    have h2 : 0 ≤ Real.log (2 * R ^ d) := Real.log_nonneg (by nlinarith [one_le_pow₀ hR1 (n := d)])
    linarith
  have hCe : C = 2 * (logPos R + Real.log (2 * R ^ d)) := by rw [hCdef, hKdef]
  have htail : ∀ m : ℕ, n ≤ m →
      |greenIter f d z m - greenIter f d z n| ≤
        C * (((d : ℝ) ^ n)⁻¹ - ((d : ℝ) ^ m)⁻¹) := by
    intro m hm
    have hthis := greenIter_sub_le' f d A R h hd hR z n m hm
    rw [hCe]
    exact hthis
  have hred : ∀ m : ℕ, n ≤ m →
      C * (((d : ℝ) ^ n)⁻¹ - ((d : ℝ) ^ m)⁻¹) ≤ C * ((d : ℝ) ^ n)⁻¹ := by
    intro m _
    apply mul_le_mul_of_nonneg_left _ hC0
    have h1 : 0 ≤ ((d : ℝ) ^ m)⁻¹ := by positivity
    linarith
  have hlim := tendsto_greenIter f d A h hd z
  have hub : green f d z ≤ greenIter f d z n + C * ((d : ℝ) ^ n)⁻¹ := by
    refine le_of_tendsto hlim ?_
    rw [Filter.eventually_atTop]
    refine ⟨n, fun m hm => ?_⟩
    have h1 := (abs_le.mp (htail m hm)).2
    have h2 := hred m hm
    linarith
  have hlb : greenIter f d z n - C * ((d : ℝ) ^ n)⁻¹ ≤ green f d z := by
    refine ge_of_tendsto hlim ?_
    rw [Filter.eventually_atTop]
    refine ⟨n, fun m hm => ?_⟩
    have h1 := (abs_le.mp (htail m hm)).1
    have h2 := hred m hm
    linarith
  have hgoal : |green f d z - greenIter f d z n| ≤ C * ((d : ℝ) ^ n)⁻¹ := by
    rw [abs_le]
    constructor <;> linarith
  rwa [hCe] at hgoal

/-! ## Continuity -/

/-- **The Green function is continuous.**  For a map `f` with `MonicGrowth f d A` and `d ≥ 2`, the
partial Green functions `greenIter f d · n` converge uniformly on `ℂ` to `green f d` (the uniform
tail bound above with `R = max 2 A`, and `n → ∞`), and each of them is continuous.  A uniform limit
of continuous functions is continuous. -/
theorem continuous_green (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d) :
    Continuous (green f d) := by
  have hd2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hunif : TendstoUniformlyOn (fun n z => greenIter f d z n) (green f d) atTop Set.univ := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hpow : Tendsto (fun n : ℕ => ((d : ℝ) ^ n)⁻¹) atTop (nhds 0) := by
      have hlt : ((d : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith : (1 : ℝ) < (d : ℝ))
      have h' := tendsto_pow_atTop_nhds_zero_of_lt_one
        (show (0 : ℝ) ≤ ((d : ℝ))⁻¹ by positivity) hlt
      simpa [inv_pow] using h'
    have hmul : Tendsto
        (fun n : ℕ => (2 * (logPos (max 2 A) + Real.log (2 * (max 2 A) ^ d))) * ((d : ℝ) ^ n)⁻¹)
        atTop (nhds 0) := by
      have h' := hpow.const_mul (2 * (logPos (max 2 A) + Real.log (2 * (max 2 A) ^ d)))
      simpa using h'
    filter_upwards [hmul.eventually_lt_const hε] with n hn
    intro z _
    have hb := abs_green_sub_greenIter_le f d A (max 2 A) h hd le_rfl z n
    rw [Real.dist_eq]
    calc |green f d z - greenIter f d z n|
        ≤ 2 * (logPos (max 2 A) + Real.log (2 * (max 2 A) ^ d)) * ((d : ℝ) ^ n)⁻¹ := hb
      _ < ε := hn
  have hcont : ContinuousOn (green f d) Set.univ :=
    hunif.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n =>
      (continuous_greenIter h.continuous d n).continuousOn))
  rwa [continuousOn_univ] at hcont

end Work.Escape
