import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Escape.mem_escapeRegion_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Positivity of the parameter Green function `G_c(0)`

For the tricorn family `T_c(z) = z̄² + c` the parameter Green function is the
Green function of the map at the critical point:
`greenParam c = G_c(0) = lim_n 2^{-n} log⁺ ‖T_c^[n] 0‖`
(`Work.Bottcher.greenParam_def`).

The **critical orbit of `c` is bounded exactly on the mandelbar** `M*`
(`LeanEval.ComplexAnalysis.Mandelbar`), which is defined as the set of parameters
with bounded critical orbit.  Since the Green function of an escaping orbit is
strictly positive and that of a bounded orbit vanishes, we get

`0 < greenParam c ↔ c ∉ M*`,

i.e. `G_c(0) > 0` is a "smooth" indicator function of the complement of `M*`.

## Contents

All auxiliary lemmas below are local to this file; the only exported statement is
the target theorem `greenParam_pos_iff`.

* `green_nonneg_aux` : `0 ≤ G_c(z)` for all `c, z`.
* `green_eq_zero_of_bounded` : a bounded orbit has `G_c(z) = 0`.
* `green_pos_of_escapeRegion` : once the orbit enters the escaping region
  `{w | max 2 ‖c‖ < ‖w‖}` the Green function is strictly positive.  This is the
  quantitative heart: after the orbit has entered the escaping region, the
  successive differences of the partial Green functions are dominated by the
  summable sequence `2^{-(n+1)} log 2`, so the tail stays above a positive
  constant.
* `greenParam_pos_iff` : the target statement.
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.Green

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Positivity of the Green function -/

/-- If `r ≥ 2`, `A < r` and `r^d - A ≤ s ≤ r^d + A` with `d ≥ 2`, then the ratio
`s / r^d` stays within a factor `2` of `1`, so `|log (s / r^d)| ≤ log 2`.  This is
the estimate that makes the successive differences of the partial Green functions
summable. -/
private lemma log_ratio_abs_le {d : ℕ} (hd : 2 ≤ d) {A r s : ℝ}
    (hr2 : 2 < r) (hrA : A < r) (hs1 : r ^ d - A ≤ s) (hs2 : s ≤ r ^ d + A) :
    |Real.log (s / r ^ d)| ≤ Real.log 2 := by
  have hr1 : (1:ℝ) ≤ r := by linarith
  have hrd_pos : 0 < r ^ d := pow_pos (by linarith) d
  have hsq : r ^ 2 ≤ r ^ d := pow_le_pow_right₀ hr1 hd
  have hrd_half : r ≤ r ^ d / 2 := by nlinarith
  have hA_lt : A < r ^ d / 2 := by linarith
  have hlo : r ^ d / 2 < s := by linarith
  have hhi : s < 3 / 2 * r ^ d := by linarith
  have hratio_pos : 0 < s / r ^ d := div_pos (by linarith) hrd_pos
  have h1 : (r^d/2)/r^d = (1:ℝ)/2 := by field_simp
  have h2 : (3/2 * r^d)/r^d = (3:ℝ)/2 := by
    rw [mul_div_cancel_right₀ _ hrd_pos.ne']
  have hlo' : (1:ℝ)/2 < s / r ^ d := by
    rw [← h1]; exact div_lt_div_of_pos_right hlo hrd_pos
  have hhi' : s / r ^ d < 3 / 2 := by
    rw [← h2]; exact div_lt_div_of_pos_right hhi hrd_pos
  have hloglo : Real.log (1/2) ≤ Real.log (s / r ^ d) :=
    Real.log_le_log (by norm_num) hlo'.le
  have hloghi : Real.log (s / r ^ d) ≤ Real.log (3/2) :=
    Real.log_le_log hratio_pos hhi'.le
  have h32 : Real.log (3/2) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
  have hhalf : Real.log (1/2) = - Real.log 2 := by
    rw [show (1:ℝ)/2 = 2⁻¹ by norm_num, Real.log_inv]
  rw [abs_le]
  constructor <;> linarith

/-- **Increment bound.**  Once the orbit of `z` is in the escaping region, the
successive differences of the partial Green functions are bounded by
`d^{-(n+1)} log 2`. -/
private lemma greenIter_step_le (f : ℂ → ℂ) (d : ℕ) (A : ℝ)
    (h : Work.Escape.MonicGrowth f d A) (hd : 2 ≤ d)
    {z : ℂ} {n : ℕ} (hz : (f^[n]) z ∈ Work.Escape.escapeRegion A) :
    |Work.Escape.greenIter f d z (n+1) - Work.Escape.greenIter f d z n|
      ≤ ((d:ℝ)^(n+1))⁻¹ * Real.log 2 := by
  have hstep : (f^[n+1]) z = f ((f^[n]) z) := Function.iterate_succ_apply' f n z
  have hr2 : 2 < ‖(f^[n]) z‖ := Work.Escape.two_lt_norm_of_mem_escapeRegion hz
  have hrA : A < ‖(f^[n]) z‖ := Work.Escape.lt_norm_of_mem_escapeRegion hz
  have hr1 : (1:ℝ) ≤ ‖(f^[n]) z‖ := by linarith
  have hr_pos : 0 < ‖(f^[n]) z‖ := by linarith
  have hsq : ‖(f^[n]) z‖ ^ 2 ≤ ‖(f^[n]) z‖ ^ d := pow_le_pow_right₀ hr1 hd
  have hA_lt : A < ‖(f^[n]) z‖ ^ d / 2 := by nlinarith
  have hs_ge : ‖(f^[n]) z‖ ^ d - A ≤ ‖(f^[n+1]) z‖ := by
    rw [hstep]; exact h.le_norm _
  have hs_le : ‖(f^[n+1]) z‖ ≤ ‖(f^[n]) z‖ ^ d + A := by
    rw [hstep]; exact h.norm_le _
  have hs_pos : 0 < ‖(f^[n+1]) z‖ := by
    have : (0:ℝ) < ‖(f^[n]) z‖ ^ d := pow_pos hr_pos d
    linarith
  have hs1 : (1:ℝ) ≤ ‖(f^[n+1]) z‖ := by
    have : (1:ℝ) ≤ ‖(f^[n]) z‖ ^ d := by nlinarith [hsq, hr2, pow_pos hr_pos d]
    nlinarith
  have hlogr : Work.Escape.logPos ‖(f^[n]) z‖ = Real.log ‖(f^[n]) z‖ :=
    Work.Escape.logPos_eq_log hr1
  have hlogs : Work.Escape.logPos ‖(f^[n+1]) z‖ = Real.log ‖(f^[n+1]) z‖ :=
    Work.Escape.logPos_eq_log hs1
  have hratio : |Real.log (‖(f^[n+1]) z‖ / ‖(f^[n]) z‖ ^ d)| ≤ Real.log 2 :=
    log_ratio_abs_le hd hr2 hrA hs_ge hs_le
  have hid : Work.Escape.greenIter f d z (n+1) - Work.Escape.greenIter f d z n
      = ((d:ℝ)^(n+1))⁻¹ * Real.log (‖(f^[n+1]) z‖ / ‖(f^[n]) z‖ ^ d) := by
    rw [Work.Escape.greenIter_def, Work.Escape.greenIter_def, hlogr, hlogs]
    have hlogdiv : Real.log (‖(f^[n+1]) z‖ / ‖(f^[n]) z‖ ^ d)
        = Real.log ‖(f^[n+1]) z‖ - (d:ℝ) * Real.log ‖(f^[n]) z‖ := by
      rw [Real.log_div hs_pos.ne' (pow_ne_zero d hr_pos.ne'), Real.log_pow]
    rw [hlogdiv]
    rw [pow_succ, mul_inv]
    field_simp
  rw [hid, abs_mul]
  have hnn : 0 ≤ ((d:ℝ)^(n+1))⁻¹ := by positivity
  rw [abs_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_left hratio hnn

/-- The partial sums `∑_{i<j} q^{i+1}` of the geometric series with ratio
`q ∈ [0, 1/2]` are bounded by `1` (indeed by `1 - q^j`). -/
private lemma geom_partial_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (j : ℕ) :
    ∑ i ∈ Finset.range j, q ^ (i + 1) ≤ 1 := by
  have key : ∀ j : ℕ, ∑ i ∈ Finset.range j, q ^ (i + 1) ≤ 1 - q ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Finset.sum_range_succ, pow_succ q j]
        have hqj : 0 ≤ q ^ j := pow_nonneg hq0 j
        have hh : 0 ≤ q ^ j * (1 - 2 * q) := mul_nonneg hqj (by linarith)
        nlinarith [ih]
  have h1 := key j
  have h2 : 0 ≤ q ^ j := pow_nonneg hq0 j
  linarith

/-- **Tail lower bound.**  If the orbit of `z` has entered the escaping region at
time `N`, then from time `N` on the partial Green functions stay above
`greenIter f d z N - d^{-N} log 2`. -/
private lemma greenIter_tail_ge (f : ℂ → ℂ) (d : ℕ) (A : ℝ)
    (h : Work.Escape.MonicGrowth f d A) (hd : 2 ≤ d)
    {z : ℂ} {N : ℕ} (hN : (f^[N]) z ∈ Work.Escape.escapeRegion A) (j : ℕ) :
    Work.Escape.greenIter f d z N - ((d:ℝ)^N)⁻¹ * Real.log 2
      ≤ Work.Escape.greenIter f d z (N + j) := by
  have hstep : ∀ i : ℕ,
      |Work.Escape.greenIter f d z (N+i+1) - Work.Escape.greenIter f d z (N+i)|
        ≤ ((d:ℝ)^(N+i+1))⁻¹ * Real.log 2 := by
    intro i
    have hz' : (f^[N+i]) z ∈ Work.Escape.escapeRegion A := by
      have h1 : (f^[N+i]) z = (f^[i]) ((f^[N]) z) := by
        rw [show N + i = i + N by omega, Function.iterate_add_apply]
      rw [h1]
      exact Work.Escape.mem_escapeRegion_iterate f d A h hd hN i
    exact greenIter_step_le f d A h hd hz'
  have htel : ∀ j : ℕ, Work.Escape.greenIter f d z (N+j) - Work.Escape.greenIter f d z N
      = ∑ i ∈ Finset.range j,
          (Work.Escape.greenIter f d z (N+i+1) - Work.Escape.greenIter f d z (N+i)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Finset.sum_range_succ, ← ih]
        ring
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hq0 : (0:ℝ) ≤ (d:ℝ)⁻¹ := inv_nonneg.mpr hdR.le
  have hqhalf : (d:ℝ)⁻¹ ≤ 1 / 2 := by
    have h2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have h3 : (1:ℝ) / (d:ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    simpa using h3
  have hsumbound : ∑ i ∈ Finset.range j, ((d:ℝ)^(N+i+1))⁻¹ ≤ ((d:ℝ)^N)⁻¹ := by
    have hfac : ∀ i : ℕ, ((d:ℝ)^(N+i+1))⁻¹ = ((d:ℝ)^N)⁻¹ * ((d:ℝ)^(i+1))⁻¹ := by
      intro i
      have hpow : (d:ℝ)^(N+i+1) = (d:ℝ)^N * (d:ℝ)^(i+1) := by
        rw [Nat.add_assoc]
        exact pow_add (d:ℝ) N (i+1)
      rw [hpow, mul_inv]
    have hsum1 : ∑ i ∈ Finset.range j, ((d:ℝ)^(i+1))⁻¹ ≤ 1 := by
      have h1 : ∑ i ∈ Finset.range j, ((d:ℝ)^(i+1))⁻¹
          = ∑ i ∈ Finset.range j, ((d:ℝ)⁻¹)^(i+1) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [inv_pow]
      rw [h1]
      exact geom_partial_le hq0 hqhalf j
    calc ∑ i ∈ Finset.range j, ((d:ℝ)^(N+i+1))⁻¹
        = ∑ i ∈ Finset.range j, ((d:ℝ)^N)⁻¹ * ((d:ℝ)^(i+1))⁻¹ :=
          Finset.sum_congr rfl (fun i _ => hfac i)
      _ = ((d:ℝ)^N)⁻¹ * ∑ i ∈ Finset.range j, ((d:ℝ)^(i+1))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ ((d:ℝ)^N)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr (pow_nonneg hdR.le N))
      _ = ((d:ℝ)^N)⁻¹ := mul_one _
  have hterm : ∀ i ∈ Finset.range j,
      -(((d:ℝ)^(N+i+1))⁻¹ * Real.log 2)
        ≤ Work.Escape.greenIter f d z (N+i+1) - Work.Escape.greenIter f d z (N+i) := by
    intro i _
    have hi := hstep i
    rw [abs_le] at hi
    linarith [hi.1]
  have hsum_lower : ∑ i ∈ Finset.range j, -(((d:ℝ)^(N+i+1))⁻¹ * Real.log 2)
      ≤ ∑ i ∈ Finset.range j,
          (Work.Escape.greenIter f d z (N+i+1) - Work.Escape.greenIter f d z (N+i)) :=
    Finset.sum_le_sum hterm
  have hsum_neg : ∑ i ∈ Finset.range j, -(((d:ℝ)^(N+i+1))⁻¹ * Real.log 2)
      = -(∑ i ∈ Finset.range j, ((d:ℝ)^(N+i+1))⁻¹) * Real.log 2 := by
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul]
    ring
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hbound2 : -(((d:ℝ)^N)⁻¹) * Real.log 2
      ≤ -(∑ i ∈ Finset.range j, ((d:ℝ)^(N+i+1))⁻¹) * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith [hsumbound]) hlog2
  have hmain : -(((d:ℝ)^N)⁻¹ * Real.log 2)
      ≤ Work.Escape.greenIter f d z (N + j) - Work.Escape.greenIter f d z N := by
    rw [htel j, show -(((d:ℝ)^N)⁻¹ * Real.log 2) = -(((d:ℝ)^N)⁻¹) * Real.log 2 by ring]
    exact hbound2.trans (hsum_neg.symm.trans_le hsum_lower)
  linarith [hmain]

/-- A bound on the orbit gives a vanishing Green function: the partial Green
functions are dominated by `d^{-n} log⁺ M`, which tends to `0`. -/
private lemma green_eq_zero_of_bounded (f : ℂ → ℂ) (d : ℕ) (A : ℝ)
    (h : Work.Escape.MonicGrowth f d A) (hd : 2 ≤ d) {z : ℂ}
    (hm : ∃ M : ℝ, ∀ n : ℕ, ‖(f^[n]) z‖ ≤ M) : Work.Escape.green f d z = 0 := by
  obtain ⟨M, hM⟩ := hm
  have htend := Work.Escape.tendsto_greenIter f d A h hd z
  have hbound : ∀ n : ℕ,
      Work.Escape.greenIter f d z n ≤ ((d:ℝ)^n)⁻¹ * Real.log (max M 1) := fun n =>
    Work.Escape.greenIter_le_of_norm_le (le_max_right M 1) (le_trans (hM n) (le_max_left M 1))
  have hlim : Filter.Tendsto (fun n : ℕ => ((d:ℝ)^n)⁻¹ * Real.log (max M 1))
      Filter.atTop (nhds 0) := by
    have hdR : (1:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 1 < d)
    have hq0 : (0:ℝ) ≤ (d:ℝ)⁻¹ := by positivity
    have hq1 : (d:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hdR
    have hgeom : Filter.Tendsto (fun n : ℕ => ((d:ℝ)⁻¹)^n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have h2 : (fun n : ℕ => ((d:ℝ)^n)⁻¹ * Real.log (max M 1))
        = fun n : ℕ => ((d:ℝ)⁻¹)^n * Real.log (max M 1) := by
      funext n
      rw [inv_pow]
    rw [h2]
    simpa using hgeom.mul_const (Real.log (max M 1))
  have hz0 : Filter.Tendsto (fun n : ℕ => Work.Escape.greenIter f d z n)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => Work.Escape.greenIter_nonneg f d z n) hbound hlim
  exact tendsto_nhds_unique htend hz0

/-- The Green function is nonnegative. -/
private lemma green_nonneg_aux (c z : ℂ) : 0 ≤ Work.Bottcher.green c z := by
  have htend := Work.Escape.tendsto_greenIter (Tantibar c) 2 ‖c‖
    (Work.Escape.monicGrowth_Tantibar c) le_rfl z
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htend
    (Filter.Eventually.of_forall fun n => Work.Escape.greenIter_nonneg _ _ _ _)

/-- An unbounded orbit eventually enters the escaping region of the map. -/
private lemma exists_mem_escapeRegion_of_not_bounded (f : ℂ → ℂ) (A : ℝ) {z : ℂ}
    (hz : ¬ ∃ M : ℝ, ∀ n : ℕ, ‖(f^[n]) z‖ ≤ M) :
    ∃ N : ℕ, (f^[N]) z ∈ Work.Escape.escapeRegion A := by
  by_contra hcon
  refine hz ⟨max 2 A, fun n => ?_⟩
  by_contra hlt
  exact hcon ⟨n, by rw [Work.Escape.mem_escapeRegion]; exact not_le.mp hlt⟩

/-- **Positivity of the Green function on escaping orbits.**  If some iterate of
`z` lies in the escaping region `{w | max 2 A < ‖w‖}`, then `G_f(z) > 0`. -/
private lemma green_pos_of_escapeRegion (f : ℂ → ℂ) (d : ℕ) (A : ℝ)
    (h : Work.Escape.MonicGrowth f d A) (hd : 2 ≤ d) {z : ℂ}
    (hz : ∃ N : ℕ, (f^[N]) z ∈ Work.Escape.escapeRegion A) :
    0 < Work.Escape.green f d z := by
  obtain ⟨N, hN⟩ := hz
  have hr2 : 2 < ‖(f^[N]) z‖ := Work.Escape.two_lt_norm_of_mem_escapeRegion hN
  have hr1 : (1:ℝ) ≤ ‖(f^[N]) z‖ := by linarith
  have hrpos : 0 < ‖(f^[N]) z‖ := by linarith
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hgN : Work.Escape.greenIter f d z N = ((d:ℝ)^N)⁻¹ * Real.log ‖(f^[N]) z‖ :=
    Work.Escape.greenIter_eq_of_one_le hr1
  have hεpos : 0 < ((d:ℝ)^N)⁻¹ * Real.log ‖(f^[N]) z‖ - ((d:ℝ)^N)⁻¹ * Real.log 2 := by
    have hdinv : (0:ℝ) < ((d:ℝ)^N)⁻¹ := inv_pos.mpr (pow_pos hdR N)
    have hlogpos : 0 < Real.log ‖(f^[N]) z‖ - Real.log 2 := by
      have hlog : Real.log ‖(f^[N]) z‖ - Real.log 2 = Real.log (‖(f^[N]) z‖ / 2) := by
        rw [Real.log_div hrpos.ne' (by norm_num : (2:ℝ) ≠ 0)]
      rw [hlog]
      exact Real.log_pos (by linarith)
    rw [← mul_sub]
    exact mul_pos hdinv hlogpos
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ((d:ℝ)^N)⁻¹ * Real.log ‖(f^[N]) z‖ - ((d:ℝ)^N)⁻¹ * Real.log 2
        ≤ Work.Escape.greenIter f d z n := by
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have htail := greenIter_tail_ge f d A h hd hN (n - N)
    have hNn : N + (n - N) = n := by omega
    rw [hNn] at htail
    rwa [hgN] at htail
  exact lt_of_lt_of_le hεpos (le_of_tendsto_of_tendsto tendsto_const_nhds
    (Work.Escape.tendsto_greenIter f d A h hd z) hev)

/-! ## The parameter statement -/

/-- **`G_c(0) > 0` exactly outside the mandelbar.**  The parameter Green function
of the tricorn family is strictly positive precisely for the parameters whose
critical orbit escapes, i.e. for `c ∉ M*`. -/
theorem greenParam_pos_iff (c : ℂ) :
    0 < Work.Bottcher.greenParam c ↔ c ∉ LeanEval.ComplexAnalysis.Mandelbar := by
  have hdiff : Work.Bottcher.greenParam c = Work.Bottcher.green c 0 :=
    Work.Bottcher.greenParam_def c
  have hnonneg : 0 ≤ Work.Bottcher.green c 0 := green_nonneg_aux c 0
  have hzero : Work.Bottcher.green c 0 = 0 ↔ c ∈ Mandelbar := by
    constructor
    · intro h0
      by_contra hcon
      obtain ⟨N, hN⟩ := exists_mem_escapeRegion_of_not_bounded (Tantibar c) ‖c‖ hcon
      exact absurd h0 (ne_of_gt (green_pos_of_escapeRegion (Tantibar c) 2 ‖c‖
        (Work.Escape.monicGrowth_Tantibar c) le_rfl ⟨N, hN⟩))
    · intro hc
      exact green_eq_zero_of_bounded (Tantibar c) 2 ‖c‖
        (Work.Escape.monicGrowth_Tantibar c) le_rfl hc
  rw [hdiff]
  constructor
  · intro h hc
    have h1 : Work.Bottcher.green c 0 = 0 := hzero.mpr hc
    rw [h1] at h
    exact lt_irrefl 0 h
  · intro hc
    rcases eq_or_lt_of_le hnonneg with h | h
    · exact absurd (hzero.mp h.symm) hc
    · exact h

end Work.Bottcher.Green
