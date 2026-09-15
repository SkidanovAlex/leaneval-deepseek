import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Commons.Measure.Integral.holder_pow_le_mul
import ChallengeDeps
import Submission.Vinogradov.Core
import Submission.Vinogradov.Asymptotic
import Submission.Commons.Analysis.Metric.separated_points_count
import Submission.Commons.Analysis.Real.dyadic_between
import Submission.Commons.Analysis.Real.two_pow_collapse_bound
import Submission.Commons.Analysis.Real.inv_pow_prod_two
import Submission.Commons.Analysis.Real.rpow_dominate
import Submission.Commons.Analysis.Complex.abs_sum_unit_le_sqrt
import Submission.Commons.Analysis.Complex.norm_exp_mul_I_ofReal
import Submission.Commons.Analysis.Integral.ball_weight_integrable_expr
import Submission.Commons.Analysis.Real.mul_rpow_interp_bound

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped Real BigOperators
open MeasureTheory

set_option autoImplicit false

/-!
# Decoupling route: ball weights and the discretisation bound

This module lays the foundation of the Bourgain–Demeter–Guth route to the deep
core (`3 ≤ k`, `s ≥ k+1`): the passage from the torus orthogonality identities of
`Orthogonality.lean` / `OrthogonalityF.lean` to the sharp bound via ℓ²-decoupling
for the moment curve.

The role of the pieces here (notation follows BDG, "Proof of the main conjecture
in Vinogradov's mean value theorem for degrees higher than three", Ann. Math.
184 (2016)):

* `E k` — the Euclidean space `ℝᵏ` on which the extension/decoupling estimates
  live (x-coordinates); the moment curve is `γ(t) = (t, t², …, tᵏ)`, `0 < t ≤ 1`.
* `ballWeight k c R x` — the ball weight `w_B(x) = (1 + ‖x − c‖/R)^{−100k}` of
  BDG §2; `wPow`-type integrals against it are the `Lᵖ(v)` objects of their §2.
* `momChar k x t` — the character `e(x·γ(t)) = exp(2πi Σ_j x_j t^{j+1})`.
* `Separated N t` — the separation condition: the `N` points `tᵢ` lie one per
  interval `((i−1)/N, i/N]` (BDG Thm 4.1).  The integer point set `{1,…,X}`
  (with `N = X`, `tᵢ = i/X`) satisfies it; the discrete object over integers is
  `Jsep`, the natural embedding of `J s k X`.
* `bdg_Jsep` (BDG Cor. 4.2 for the integer point set `{1,…,X}`, proved in
  `Submission.Vinogradov.Discretisation`) bounds `Jsep` by
  `X^{s+ε} + X^{2s − k(k+1)/2 + ε}`; together with the (proved) inclusion
  `J_le_Jsep` and the (proved) assembly `vmvt_of_Jsep_bound` this reduces the
  whole deep core to the ℓ²-decoupling theorem for the moment curve, BDG
  Thm 1.2, which is the single remaining hypothesis of the project (stated as
  `bdg_thm_ntmain` in `Submission.Vinogradov.DecouplingThm12`).

Remark on decoupling itself (BDG Thm 1.2): for `0 < δ ≤ 1`, any ball `B ⊂ ℝᵏ`
of radius `δ^{−k}`, any `g : [0,1] → ℂ`, and the partition of `[0,1]` into
intervals `J` of length `δ`,

    ‖E_{[0,1]} g‖_{L^{k(k+1)}(w_B)} ≪_ε δ^{−ε} (Σ_J ‖E_J g‖²_{L^{k(k+1)}(w_B)})^{1/2},

`E_J g(x) = ∫_J g(t) e(x·γ(t)) dt`.  Formalising the extension operator, the
multilinear/ball-inflation machinery, and the induction proving this theorem is
the long-term core of the decoupling route (see `ROADMAP.lean`); the present
module fixes the surrounding vocabulary, and the passage from Thm 1.2 to the
discrete restriction estimate (BDG §4) is carried out in
`Submission.Vinogradov.DecouplingThm12`.
-/

namespace Submission.Vinogradov

noncomputable section
open Classical

/-- The ambient Euclidean space `ℝᵏ` (frequencies / extension-variable space). -/
abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The ball weight `w_B(x) = (1 + ‖x − c‖/R)^{−100k} = 1/(1 + ‖x−c‖/R)^{100k}` of BDG §2
(reciprocal of a natural power, for proof friendliness; `x ↦ 1/(1+u)^{100k}` with `u = ‖x−c‖/R`). -/
def ballWeight (k : ℕ) (c : E k) (R : ℝ) (x : E k) : ℝ :=
  ((1 + ‖x - c‖ / R) ^ (100 * k))⁻¹

/-- The ball weight is positive for `R > 0`. -/
lemma ballWeight_pos (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) (x : E k) : 0 < ballWeight k c R x := by
  unfold ballWeight
  have hnr : 0 ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg _) (le_of_lt hR)
  have hb : 0 < 1 + ‖x - c‖ / R := by linarith
  exact inv_pos.mpr (pow_pos hb _)

/-- The ball weight is at most `1`. -/
lemma ballWeight_le_one (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) (x : E k) : ballWeight k c R x ≤ 1 := by
  unfold ballWeight
  have hnr : 0 ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg _) (le_of_lt hR)
  have hb : 1 ≤ 1 + ‖x - c‖ / R := by linarith
  have hp : 1 ≤ (1 + ‖x - c‖ / R) ^ (100 * k) := one_le_pow₀ hb
  exact inv_le_one_of_one_le₀ hp

/-- On the ball `‖x − c‖ ≤ R` the weight is comparable to `1`: it is at least `2^{−100k}`. -/
lemma ballWeight_ge_on_ball (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {x : E k} (hx : ‖x - c‖ ≤ R) :
    ((2 : ℝ) ^ (100 * k))⁻¹ ≤ ballWeight k c R x := by
  unfold ballWeight
  have hnr : 0 ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg _) (le_of_lt hR)
  have hle1 : ‖x - c‖ / R ≤ 1 := (div_le_one hR).mpr hx
  have hb0 : 0 < 1 + ‖x - c‖ / R := by linarith
  have hb2 : 1 + ‖x - c‖ / R ≤ (2 : ℝ) := by linarith
  have hp : (1 + ‖x - c‖ / R) ^ (100 * k) ≤ (2 : ℝ) ^ (100 * k) :=
    pow_le_pow_left₀ (le_of_lt hb0) hb2 _
  exact (inv_le_inv₀ (pow_pos (by norm_num) _) (pow_pos hb0 _)).mpr hp


/-- Inverse of the power of a ratio: `((a/b)^n)⁻¹ = (b/a)^n`. -/
lemma inv_pow_div (a b : ℝ) (hb : b ≠ 0) (n : ℕ) : ((a / b) ^ n)⁻¹ = (b / a) ^ n := by
  calc
    ((a / b) ^ n)⁻¹ = ((a / b)⁻¹) ^ n := by rw [← inv_pow]
    _ = (b / a) ^ n := by
      congr 1
      field_simp [hb]

/-- Near lower bound: for `‖x−c‖ ≤ 2R` the ball weight is at least `3^{−100k}`
(a constant), so inside/near `B(c,2R)` the weight is comparable to `1`. -/
lemma ballWeight_lower_near (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {x : E k} (hx : ‖x - c‖ ≤ 2 * R) :
    ((3 : ℝ) ^ (100 * k))⁻¹ ≤ ballWeight k c R x := by
  unfold ballWeight
  have hnr : 0 ≤ ‖x - c‖ / R := div_nonneg (norm_nonneg _) (le_of_lt hR)
  have hb0 : 0 < 1 + ‖x - c‖ / R := by linarith
  have hb3 : 1 + ‖x - c‖ / R ≤ (3 : ℝ) := by
    have hle2 : ‖x - c‖ / R ≤ 2 := (div_le_iff₀ hR).mpr hx
    linarith
  have hp : (1 + ‖x - c‖ / R) ^ (100 * k) ≤ (3 : ℝ) ^ (100 * k) :=
    pow_le_pow_left₀ (le_of_lt hb0) hb3 _
  exact (inv_le_inv₀ (pow_pos (by norm_num) _) (pow_pos hb0 _)).mpr hp

/-- **Decay comparison (BDG §2, eq. (3) building block)**: if the smaller ball
`B(c′, r)` has centre inside `B(c, R)` (`‖c′−c‖ ≤ R`, `r ≤ R`) then outside
`B(c, 2R)` its weight is at most `4^{100k}` times the weight of `B(c, R)`:
`w_{B(c′,r)}(x) ≤ 4^{100k} · w_{B(c,R)}(x)` for `‖x−c‖ ≥ 2R`.  This is the
per-ball estimate used to sum the local weights over finitely-overlapping
covers (BDG eq. (3), the bridge from Thm 1.2 to Thm 4.1). -/
lemma ballWeight_decay_outside (k : ℕ) (c : E k) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R) {c' : E k} (hc' : ‖c' - c‖ ≤ R) {x : E k} (hx : 2 * R ≤ ‖x - c‖) :
    ballWeight k c' r x ≤ (4 : ℝ) ^ (100 * k) * ballWeight k c R x := by
  unfold ballWeight
  let t : ℝ := ‖x - c‖
  let u : ℝ := ‖x - c'‖
  have ht0 : 0 < t := by
    dsimp [t]
    linarith
  have htri : t ≤ u + R := by
    dsimp [t, u]
    have hn := dist_triangle x c' c
    have hn' : ‖x - c‖ ≤ ‖x - c'‖ + ‖c' - c‖ := by
      simpa [dist_eq_norm] using hn
    linarith [hc']
  have hu : t / 2 ≤ u := by
    have h1 : t - R ≤ u := by linarith
    linarith
  have hu0 : 0 < u := by linarith [ht0]
  have hBr_ge : t / (2 * r) ≤ 1 + u / r := by
    have h1 : (t / 2) / r ≤ u / r := div_le_div_of_nonneg_right hu (le_of_lt hr)
    have hEq : (t / 2) / r = t / (2 * r) := by ring
    have h2 : 0 ≤ u / r := div_nonneg (le_of_lt hu0) (le_of_lt hr)
    rw [hEq] at h1
    linarith
  have hBR_le : 1 + t / R ≤ 2 * t / R := by
    have htR : R ≤ t := by linarith
    have h1 : (1 : ℝ) ≤ t / R := (le_div_iff₀ hR).mpr (by simpa using htR)
    have hsum : t / R + t / R = 2 * t / R := by ring
    linarith
  have hBr0 : 0 < 1 + u / r := by
    have h2 : 0 ≤ u / r := div_nonneg (le_of_lt hu0) (le_of_lt hr)
    linarith
  have hBR0 : 0 < 1 + t / R := by
    have h2 : 0 ≤ t / R := div_nonneg (le_of_lt ht0) (le_of_lt hR)
    linarith
  have hY0 : 0 < t / (2 * r) := by positivity
  have hZ0 : 0 < 2 * t / R := by positivity
  have h1p : (t / (2 * r)) ^ (100 * k) ≤ (1 + u / r) ^ (100 * k) :=
    pow_le_pow_left₀ (le_of_lt hY0) hBr_ge _
  have hL : ((1 + u / r) ^ (100 * k))⁻¹ ≤ ((t / (2 * r)) ^ (100 * k))⁻¹ :=
    (inv_le_inv₀ (pow_pos hBr0 _) (pow_pos hY0 _)).mpr h1p
  have h2p : (1 + t / R) ^ (100 * k) ≤ (2 * t / R) ^ (100 * k) :=
    pow_le_pow_left₀ (le_of_lt hBR0) hBR_le _
  have hRhs_ge : (4 : ℝ) ^ (100 * k) * ((2 * t / R) ^ (100 * k))⁻¹ ≤
      (4 : ℝ) ^ (100 * k) * ((1 + t / R) ^ (100 * k))⁻¹ := by
    have hi : ((2 * t / R) ^ (100 * k))⁻¹ ≤ ((1 + t / R) ^ (100 * k))⁻¹ :=
      (inv_le_inv₀ (pow_pos hZ0 _) (pow_pos hBR0 _)).mpr h2p
    exact mul_le_mul_of_nonneg_left hi (pow_nonneg (by norm_num) _)
  have hEqR : (4 : ℝ) ^ (100 * k) * ((2 * t / R) ^ (100 * k))⁻¹ = (2 * R / t) ^ (100 * k) := by
    calc
      (4 : ℝ) ^ (100 * k) * ((2 * t / R) ^ (100 * k))⁻¹
          = (4 : ℝ) ^ (100 * k) * (R / (2 * t)) ^ (100 * k) := by
            rw [inv_pow_div (2 * t) R (ne_of_gt hR) (100 * k)]
      _ = ((4 : ℝ) * (R / (2 * t))) ^ (100 * k) := by rw [← mul_pow]
      _ = (2 * R / t) ^ (100 * k) := by congr 1; field_simp [ht0.ne']; ring
  have hmid : ((t / (2 * r)) ^ (100 * k))⁻¹ ≤ (4 : ℝ) ^ (100 * k) * ((2 * t / R) ^ (100 * k))⁻¹ := by
    rw [inv_pow_div t (2 * r) (by positivity : (2 * r) ≠ 0) _, hEqR]
    have hc : 2 * r ≤ 2 * R := by nlinarith
    have h2r : (0 : ℝ) ≤ 2 * r := by positivity
    have h2R : (0 : ℝ) ≤ 2 * R := by positivity
    have hdiv : (2 * r) / t ≤ (2 * R) / t := div_le_div_of_nonneg_right hc (le_of_lt ht0)
    exact pow_le_pow_left₀ (div_nonneg h2r (le_of_lt ht0)) hdiv _
  calc
    ((1 + u / r) ^ (100 * k))⁻¹ ≤ ((t / (2 * r)) ^ (100 * k))⁻¹ := hL
    _ ≤ (4 : ℝ) ^ (100 * k) * ((2 * t / R) ^ (100 * k))⁻¹ := hmid
    _ ≤ (4 : ℝ) ^ (100 * k) * ((1 + t / R) ^ (100 * k))⁻¹ := hRhs_ge

/-- **Sharp per-ball decay**: `w_{B(c,r)}(x) ≤ (r/‖x−c‖)^{100k}` away from the
center — the estimate that makes the far-field / shell contributions of eq. (3)
telescope. -/
lemma ballWeight_le_pow_ratio (k : ℕ) (c : E k) {r : ℝ} (hr : 0 < r) {x : E k} (hx : 0 < ‖x - c‖) :
    ballWeight k c r x ≤ (r / ‖x - c‖) ^ (100 * k) := by
  unfold ballWeight
  have hd : 0 < ‖x - c‖ / r := div_pos hx hr
  -- 1 + u ≥ u, so (1+u)^N ≥ u^N and the reciprocal is ≤
  have hp : (‖x - c‖ / r) ^ (100 * k) ≤ (1 + ‖x - c‖ / r) ^ (100 * k) := by
    have h1 : ‖x - c‖ / r ≤ 1 + ‖x - c‖ / r := by linarith
    exact pow_le_pow_left₀ (le_of_lt hd) h1 _
  have hinv : ((1 + ‖x - c‖ / r) ^ (100 * k))⁻¹ ≤ ((‖x - c‖ / r) ^ (100 * k))⁻¹ :=
    (inv_le_inv₀ (pow_pos (by linarith) _) (pow_pos hd _)).mpr hp
  -- ((d/r)^N)⁻¹ = (r/d)^N
  calc
    ((1 + ‖x - c‖ / r) ^ (100 * k))⁻¹ ≤ ((‖x - c‖ / r) ^ (100 * k))⁻¹ := hinv
    _ = (r / ‖x - c‖) ^ (100 * k) := by
      rw [inv_pow_div (‖x - c‖) r (ne_of_gt hr) (100 * k)]

/-- Lower bound on the ball weight away from the centre: for `‖x−c‖ ≥ R`,
`w_B(x) ≥ (R/(2‖x−c‖))^{100k}`. -/
lemma ballWeight_lower_far (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {x : E k} (hx : R ≤ ‖x - c‖) :
    (R / (2 * ‖x - c‖)) ^ (100 * k) ≤ ballWeight k c R x := by
  unfold ballWeight
  let t : ℝ := ‖x - c‖
  have ht0 : 0 < t := by dsimp [t]; linarith
  have hnr : 0 ≤ t / R := div_nonneg (le_of_lt ht0) (le_of_lt hR)
  have hb0 : 0 < 1 + t / R := by linarith
  have hle : 1 + t / R ≤ 2 * t / R := by
    have h1 : (1 : ℝ) ≤ t / R := (le_div_iff₀ hR).mpr (by simpa [t] using hx)
    have hsum : t / R + t / R = 2 * t / R := by ring
    linarith
  have hpow : (1 + t / R) ^ (100 * k) ≤ (2 * t / R) ^ (100 * k) :=
    pow_le_pow_left₀ (le_of_lt hb0) hle _
  have hZ0 : 0 < 2 * t / R := by positivity
  have hi : ((2 * t / R) ^ (100 * k))⁻¹ ≤ ((1 + t / R) ^ (100 * k))⁻¹ :=
    (inv_le_inv₀ (pow_pos hZ0 _) (pow_pos hb0 _)).mpr hpow
  calc
    (R / (2 * t)) ^ (100 * k) = ((2 * t / R) ^ (100 * k))⁻¹ := by
      rw [inv_pow_div (2 * t) R (ne_of_gt hR) (100 * k)]
    _ ≤ ((1 + t / R) ^ (100 * k))⁻¹ := hi
    _ = ballWeight k c R x := by simp [ballWeight, t]

/-- For `a ≥ 1` and `M ≤ N`: `a^M · (a^N)⁻¹ ≤ 1` (the factor that makes the
exponent `100k` beat the `k`-dimensional multiplicity in BDG eq. (3)). -/
lemma pow_mul_inv_le_one {a : ℝ} (ha1 : 1 ≤ a) {M N : ℕ} (hMN : M ≤ N) :
    a ^ M * (a ^ N)⁻¹ ≤ 1 := by
  have ha0 : a ≠ 0 := by nlinarith
  have hsplit : (a⁻¹) ^ N = (a⁻¹) ^ M * (a⁻¹) ^ (N - M) := by
    rw [← pow_add]
    congr 1
    exact (Nat.add_sub_of_le hMN).symm
  have hEq : a ^ M * (a ^ N)⁻¹ = (a⁻¹) ^ (N - M) := by
    calc
      a ^ M * (a ^ N)⁻¹ = a ^ M * (a⁻¹) ^ N := by rw [← inv_pow]
      _ = a ^ M * ((a⁻¹) ^ M * (a⁻¹) ^ (N - M)) := by rw [hsplit]
      _ = (a * a⁻¹) ^ M * (a⁻¹) ^ (N - M) := by
        rw [← mul_assoc]
        rw [← mul_pow]
      _ = (a⁻¹) ^ (N - M) := by
        rw [mul_inv_cancel₀ ha0, one_pow, one_mul]
  have h0inv : 0 ≤ a⁻¹ := inv_nonneg.mpr (by nlinarith)
  have h1inv : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha1
  calc
    a ^ M * (a ^ N)⁻¹ = (a⁻¹) ^ (N - M) := hEq
    _ ≤ 1 := pow_le_one₀ h0inv h1inv

/-- The dyadic shell of `a > 1` (via `Commons.Analysis.Real.dyadic_between`) lies
below `L` whenever `a ≤ B < 2^L`.  This is the "shells beyond `⌈3R/r⌉` are
empty" step of the near case of eq. (3). -/
lemma dyadic_shell_lt {a B : ℝ} (ha : 1 < a) (hB : a ≤ B) {L : ℕ} (hL : B < (2 : ℝ) ^ L) :
    (Classical.choose (Commons.Analysis.Real.dyadic_between ha)) < L := by
  let ell : ℕ := Classical.choose (Commons.Analysis.Real.dyadic_between ha)
  have hspec := Classical.choose_spec (Commons.Analysis.Real.dyadic_between ha)
  have hpowlt : (2 : ℝ) ^ ell < (2 : ℝ) ^ L := lt_trans (lt_of_lt_of_le hspec.1 hB) hL
  exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpowlt

/-- Geometric partial sums are bounded by the full series: for `0 ≤ q < 1`,
`Σ_{i<n} q^i ≤ (1−q)⁻¹`.  This bounds the dyadic shell series of eq. (3) with
`q = 2^{k−100k} ≤ 1/2`. -/
lemma geom_sum_le_inv_one_sub {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ i ∈ Finset.range n, q ^ i) ≤ (1 - q)⁻¹ := by
  have hq : q - 1 ≠ 0 := by linarith
  have h1q : 1 - q ≠ 0 := by linarith
  have h1qpos : 0 < 1 - q := by linarith
  have hle1 : q ≤ 1 := le_of_lt hq1
  have hqn0 : 0 ≤ q ^ n := pow_nonneg hq0 _
  have h1qn : 1 - q ^ n ≤ 1 := by linarith
  have hgm := geom_sum_mul q n
  have h1 : (∑ i ∈ Finset.range n, q ^ i) = (q ^ n - 1) / (q - 1) := by
    calc
      (∑ i ∈ Finset.range n, q ^ i)
          = ((∑ i ∈ Finset.range n, q ^ i) * (q - 1)) * (q - 1)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hq, mul_one]
      _ = (q ^ n - 1) * (q - 1)⁻¹ := by rw [hgm]
      _ = (q ^ n - 1) / (q - 1) := by rw [div_eq_mul_inv]
  have hid : (∑ i ∈ Finset.range n, q ^ i) = (1 - q ^ n) / (1 - q) := by
    calc
      (∑ i ∈ Finset.range n, q ^ i) = (q ^ n - 1) / (q - 1) := h1
      _ = (1 - q ^ n) / (1 - q) := by
        field_simp [hq, h1q]
        ring
  calc
    (∑ i ∈ Finset.range n, q ^ i) = (1 - q ^ n) / (1 - q) := hid
    _ ≤ (1 - q)⁻¹ := by
      rw [div_eq_mul_inv]
      have hmul : (1 - q ^ n) * (1 - q)⁻¹ ≤ (1 : ℝ) * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_right h1qn (le_of_lt (inv_pos.mpr h1qpos))
      simpa using hmul

lemma inner_count_le (k : ℕ) {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 < r)
    (c' : ι → E k) (x : E k)
    (hsep : ∀ i j : ι, i ≠ j → r ≤ ‖c' i - c' j‖) :
    ∃ Ccnt : ℝ, 0 < Ccnt ∧
      (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ r)).card : ℕ) : ℝ) ≤ Ccnt * (2 : ℝ) ^ k := by
  classical
  rcases Commons.Analysis.Metric.separated_points_count k with ⟨Ccnt, hCcnt, hcnt⟩
  let ι₀ := {i : ι // ‖c' i - x‖ ≤ r}
  have hcnt0 : (Fintype.card ι₀ : ℝ) ≤ Ccnt * (((1 : ℝ) + 1) ^ k) := by
    have h := hcnt (ι := ι₀) hr (c := fun i : ι₀ => c' i.1) (x := x) (m := 1)
      (by
        intro i j hij
        exact hsep i.1 j.1 (by
          intro hval
          exact hij (Subtype.ext hval)))
      (by
        intro i
        simpa using i.2)
    simpa using h
  have hc : Fintype.card ι₀ = (Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ r)).card := by
    exact Fintype.card_of_subtype (s := Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ r))
      (H := by intro y; simp)
  have hrel : (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ r)).card : ℕ) : ℝ) = (Fintype.card ι₀ : ℝ) := by
    exact_mod_cast hc.symm
  refine ⟨Ccnt, hCcnt, ?_⟩
  calc
    (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ r)).card : ℕ) : ℝ) = (Fintype.card ι₀ : ℝ) := hrel
    _ ≤ Ccnt * (((1 : ℝ) + 1) ^ k) := hcnt0
    _ = Ccnt * (2 : ℝ) ^ k := by norm_num

lemma shell_count_le (k : ℕ) {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 < r)
    (c' : ι → E k) (x : E k)
    (hsep : ∀ i j : ι, i ≠ j → r ≤ ‖c' i - c' j‖) (m : ℕ) :
    ∃ Ccnt : ℝ, 0 < Ccnt ∧
      (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (m : ℝ) * r)).card : ℕ) : ℝ)
        ≤ Ccnt * (((m : ℝ) + 1) ^ k) := by
  classical
  rcases Commons.Analysis.Metric.separated_points_count k with ⟨Ccnt, hCcnt, hcnt⟩
  let ι₀ := {i : ι // ‖c' i - x‖ ≤ (m : ℝ) * r}
  have hcnt0 : (Fintype.card ι₀ : ℝ) ≤ Ccnt * (((m : ℝ) + 1) ^ k) := by
    have h := hcnt (ι := ι₀) hr (c := fun i : ι₀ => c' i.1) (x := x) (m := m)
      (by
        intro i j hij
        exact hsep i.1 j.1 (by
          intro hval
          exact hij (Subtype.ext hval)))
      (by
        intro i
        exact i.2)
    simpa using h
  have hc : Fintype.card ι₀ = (Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (m : ℝ) * r)).card := by
    exact Fintype.card_of_subtype (s := Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (m : ℝ) * r))
      (H := by intro y; simp)
  have hrel : (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (m : ℝ) * r)).card : ℕ) : ℝ) = (Fintype.card ι₀ : ℝ) := by
    exact_mod_cast hc.symm
  refine ⟨Ccnt, hCcnt, ?_⟩
  rw [hrel]
  exact hcnt0

-- per-shell decay: from 2^ℓ < d/r, (r/d)^N ≤ ((2:ℝ)^(ℓ·N))⁻¹
lemma pow_div_le_inv_pow (r d : ℝ) (hr : 0 < r) (hd : 0 < d) {ℓ N : ℕ}
    (h : (2 : ℝ) ^ ℓ < d / r) :
    (r / d) ^ N ≤ ((2 : ℝ) ^ (ℓ * N))⁻¹ := by
  have hrd0 : 0 ≤ r / d := div_nonneg (le_of_lt hr) (le_of_lt hd)
  have ha' : 0 < d / r := div_pos hd hr
  have hb' : 0 < (2 : ℝ) ^ ℓ := pow_pos (by norm_num) _
  have hrd_eq : r / d = (d / r)⁻¹ := by field_simp [hr.ne', hd.ne']
  have hlt : r / d < ((2 : ℝ) ^ ℓ)⁻¹ := by
    rw [hrd_eq]
    exact (inv_lt_inv₀ ha' hb').mpr h
  have hpow0 : (r / d) ^ N ≤ (((2 : ℝ) ^ ℓ)⁻¹) ^ N :=
    pow_le_pow_left₀ hrd0 (le_of_lt hlt) _
  calc
    (r / d) ^ N ≤ (((2 : ℝ) ^ ℓ)⁻¹) ^ N := hpow0
    _ = (((2 : ℝ) ^ ℓ) ^ N)⁻¹ := by rw [inv_pow]
    _ = ((2 : ℝ) ^ (ℓ * N))⁻¹ := by
      congr 1
      rw [pow_mul]


/-- **Outside case of BDG eq. (3)**: for `2R ≤ ‖x−c‖`, the sum of the weights of the
`r`-balls covering `B(c,R)` is bounded by `C·w_B(x)`. Uses `ballWeight_le_pow_ratio`
on every ball, the far lower bound `ballWeight_lower_far`, and the counting lemma
`Commons.Analysis.Metric.separated_points_count` (with `m = ⌈R/r⌉`). -/
lemma cover_sum_outside_uniform (k : ℕ) (hk : 1 ≤ k) (c : E k) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R) {ι : Type*} [Fintype ι] (c' : ι → E k)
    (hcen : ∀ i, ‖c' i - c‖ ≤ R) (hsep : ∀ i j : ι, i ≠ j → r ≤ ‖c' i - c' j‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E k, 2 * R ≤ ‖x - c‖ →
      (∑ i : ι, ballWeight k (c' i) r x) ≤ C * ballWeight k c R x := by
  classical
  rcases Commons.Analysis.Metric.separated_points_count k with ⟨Ccnt, hCcnt, hcnt⟩
  let C0 : ℝ := Ccnt * (3 : ℝ) ^ k * (2 : ℝ) ^ (100 * k) * (2 : ℝ) ^ (100 * k)
  have hC0 : 0 < C0 := by positivity
  refine ⟨C0, hC0, ?_⟩
  intro x hx
  let t : ℝ := ‖x - c‖
  let N : ℕ := 100 * k
  have ht0 : 0 < t := by
    dsimp [t]
    linarith
  have htR : R ≤ t := by dsimp [t]; linarith
  have htR' : R / r ≤ (Nat.ceil (R / r) : ℝ) := Nat.le_ceil (R / r)
  have hm_ok : R ≤ (Nat.ceil (R / r) : ℝ) * r := by
    exact (div_le_iff₀ hr).mp htR'
  -- counting bound for the whole family
  have hcount : (Fintype.card ι : ℝ) ≤ Ccnt * (((Nat.ceil (R / r) : ℝ) + 1) ^ k) := by
    exact hcnt hr (c := c') (x := c) (m := Nat.ceil (R / r)) hsep (by intro i; exact le_trans (hcen i) hm_ok)
  -- per-ball decay: w_i ≤ (r/d_i)^N ≤ (2r/t)^N
  have hper : ∀ i : ι, ballWeight k (c' i) r x ≤ (2 * r / t) ^ (100 * k) := by
    intro i
    have htri : ‖x - c‖ ≤ ‖x - c' i‖ + ‖c' i - c‖ := by
      have hn := dist_triangle x (c' i) c
      have hn' : ‖x - c‖ ≤ ‖x - c' i‖ + ‖c' i - c‖ := by
        simpa [dist_eq_norm] using hn
      exact hn'
    have hd_half : t / 2 ≤ ‖x - c' i‖ := by
      dsimp [t]
      linarith [htri, hcen i]
    have hdpos : 0 < ‖x - c' i‖ := by linarith [ht0]
    have h1 : ballWeight k (c' i) r x ≤ (r / ‖x - c' i‖) ^ (100 * k) :=
      ballWeight_le_pow_ratio k (c' i) hr hdpos
    have hdiv : r / ‖x - c' i‖ ≤ r / (t / 2) := by
      apply div_le_div_of_nonneg_left
      · exact le_of_lt hr
      · positivity
      · dsimp [t]; linarith
    have hpow : (r / ‖x - c' i‖) ^ (100 * k) ≤ (r / (t / 2)) ^ (100 * k) :=
      pow_le_pow_left₀ (div_nonneg (le_of_lt hr) (le_of_lt hdpos)) hdiv _
    calc
      ballWeight k (c' i) r x ≤ (r / ‖x - c' i‖) ^ (100 * k) := h1
      _ ≤ (r / (t / 2)) ^ (100 * k) := hpow
      _ = (2 * r / t) ^ (100 * k) := by congr 1; ring
  -- sum the per-ball bounds
  have hsum1 : (∑ i : ι, ballWeight k (c' i) r x) ≤ (Fintype.card ι : ℝ) * (2 * r / t) ^ (100 * k) := by
    calc
      (∑ i : ι, ballWeight k (c' i) r x) ≤ ∑ i : ι, (2 * r / t) ^ (100 * k) :=
        Finset.sum_le_sum (fun i hi => hper i)
      _ = (Fintype.card ι : ℝ) * (2 * r / t) ^ (100 * k) := by simp
  -- (R/r)^k · (r/R)^N ≤ 1 kills the R/r factor
  have hu1 : (1 : ℝ) ≤ R / r := (one_le_div hr).mpr hrR
  have hceil_le : (Nat.ceil (R / r) : ℝ) + 1 ≤ 3 * (R / r) := by
    have h1 : (Nat.ceil (R / r) : ℝ) < R / r + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (Nat.ceil (R / r) : ℝ) + 1 < R / r + 2 := by linarith
    have h3 : R / r + 2 ≤ 3 * (R / r) := by nlinarith [hu1]
    linarith
  have hcnt3 : (Fintype.card ι : ℝ) ≤ Ccnt * (3 ^ k) * (R / r) ^ k := by
    calc
      (Fintype.card ι : ℝ) ≤ Ccnt * (((Nat.ceil (R / r) : ℝ) + 1) ^ k) := hcount
      _ ≤ Ccnt * ((3 * (R / r)) ^ k) := by
        have hnon : 0 ≤ (Nat.ceil (R / r) : ℝ) + 1 := by positivity
        have hp := pow_le_pow_left₀ hnon hceil_le k
        exact mul_le_mul_of_nonneg_left hp (le_of_lt hCcnt)
      _ = Ccnt * (3 ^ k) * (R / r) ^ k := by
        rw [mul_pow]
        ring
  -- w_B lower bound in the far field
  have hlow := ballWeight_lower_far k c hR htR
  -- (R/r)^k · (r/R)^N ≤ 1 kills the R/r factor (N = 100k)
  have hkill : (R / r) ^ k * (r / R) ^ (100 * k) ≤ 1 := by
    have hinv : (r / R) ^ (100 * k) = ((R / r) ^ (100 * k))⁻¹ := by
      calc
        (r / R) ^ (100 * k) = ((R / r)⁻¹) ^ (100 * k) := by
          congr 1
          field_simp [hr.ne', hR.ne']
        _ = ((R / r) ^ (100 * k))⁻¹ := by rw [inv_pow]
    rw [hinv]
    exact pow_mul_inv_le_one hu1 (by omega)
  -- (R/t)^N ≤ 2^N · w_B  (from the far lower bound)
  have hRt : (R / t) ^ (100 * k) ≤ (2 : ℝ) ^ (100 * k) * ballWeight k c R x := by
    have hsplit : R / t = (2 : ℝ) * (R / (2 * t)) := by
      field_simp [ht0.ne']
    calc
      (R / t) ^ (100 * k) = (2 * (R / (2 * t))) ^ (100 * k) := by rw [hsplit]
      _ = (2 : ℝ) ^ (100 * k) * (R / (2 * t)) ^ (100 * k) := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ (100 * k) * ballWeight k c R x := by
        exact mul_le_mul_of_nonneg_left hlow (pow_nonneg (by norm_num) _)
  -- (2r/t)^N = 2^N·(r/R)^N·(R/t)^N
  have hsplit2 : (2 * r / t) ^ (100 * k) =
      (2 : ℝ) ^ (100 * k) * (r / R) ^ (100 * k) * (R / t) ^ (100 * k) := by
    have hEq : 2 * r / t = 2 * (r / R) * (R / t) := by
      field_simp [hR.ne', ht0.ne']
    rw [hEq, mul_pow, mul_pow]
  -- combine: (R/r)^k · (2r/t)^N ≤ 2^N · (R/t)^N
  have hL2 : (R / r) ^ k * (2 * r / t) ^ (100 * k) ≤ (2 : ℝ) ^ (100 * k) * (R / t) ^ (100 * k) := by
    calc
      (R / r) ^ k * (2 * r / t) ^ (100 * k)
          = (R / r) ^ k * ((2 : ℝ) ^ (100 * k) * (r / R) ^ (100 * k) * (R / t) ^ (100 * k)) := by rw [hsplit2]
      _ = (2 : ℝ) ^ (100 * k) * ((R / r) ^ k * (r / R) ^ (100 * k)) * (R / t) ^ (100 * k) := by ring
      _ ≤ (2 : ℝ) ^ (100 * k) * (1 : ℝ) * (R / t) ^ (100 * k) := by
        have hA : (2 : ℝ) ^ (100 * k) * ((R / r) ^ k * (r / R) ^ (100 * k)) ≤ (2 : ℝ) ^ (100 * k) * 1 := by
          exact mul_le_mul_of_nonneg_left hkill (pow_nonneg (by norm_num) _)
        have hN : 0 ≤ (R / t) ^ (100 * k) := pow_nonneg (div_nonneg (le_of_lt hR) (le_of_lt ht0)) _
        exact mul_le_mul_of_nonneg_right hA hN
      _ = (2 : ℝ) ^ (100 * k) * (R / t) ^ (100 * k) := by ring
  calc
      (∑ i : ι, ballWeight k (c' i) r x) ≤ (Fintype.card ι : ℝ) * (2 * r / t) ^ (100 * k) := hsum1
      _ ≤ (Ccnt * (3 : ℝ) ^ k * (R / r) ^ k) * (2 * r / t) ^ (100 * k) := by
        exact mul_le_mul_of_nonneg_right hcnt3 (pow_nonneg (div_nonneg (by positivity : 0 ≤ 2 * r) (le_of_lt ht0)) _)
      _ ≤ (Ccnt * (3 : ℝ) ^ k) * ((2 : ℝ) ^ (100 * k) * (R / t) ^ (100 * k)) := by
        -- distribute: use hL2 multiplied by Ccnt·3^k ≥ 0
        have hL2' : (Ccnt * (3 : ℝ) ^ k) * ((R / r) ^ k * (2 * r / t) ^ (100 * k)) ≤
            (Ccnt * (3 : ℝ) ^ k) * ((2 : ℝ) ^ (100 * k) * (R / t) ^ (100 * k)) := by
          exact mul_le_mul_of_nonneg_left hL2 (mul_nonneg (le_of_lt hCcnt) (pow_nonneg (by norm_num) _))
        -- need left side = (Ccnt·3^k·(R/r)^k)·(2r/t)^N: rw [← mul_assoc]
        simpa [mul_assoc] using hL2'
      _ ≤ (Ccnt * (3 : ℝ) ^ k) * ((2 : ℝ) ^ (100 * k) * ((2 : ℝ) ^ (100 * k) * ballWeight k c R x)) := by
        have hL3 : (2 : ℝ) ^ (100 * k) * (R / t) ^ (100 * k) ≤
            (2 : ℝ) ^ (100 * k) * ((2 : ℝ) ^ (100 * k) * ballWeight k c R x) := by
          exact mul_le_mul_of_nonneg_left hRt (pow_nonneg (by norm_num) _)
        exact mul_le_mul_of_nonneg_left hL3 (mul_nonneg (le_of_lt hCcnt) (pow_nonneg (by norm_num) _))
      _ = C0 * ballWeight k c R x := by
        ring



-- fiber partition: Σ_o g(ℓ o) = Σ_{n<L} g n · #{o : ℓ o = n}  when ℓ o < L for all o
lemma sum_fiber_partition {O : Type*} [Fintype O] (ℓ : O → ℕ) {L : ℕ}
    (hℓL : ∀ o : O, ℓ o < L) (g : ℕ → ℝ) :
    (∑ o : O, g (ℓ o)) = ∑ n ∈ Finset.range L, g n * (((Finset.univ.filter (fun o : O => ℓ o = n)).card : ℕ) : ℝ) := by
  classical
  -- per o: g(ℓ o) = Σ_{n < L} (if n = ℓ o then g n else 0)
  have hper : ∀ o : O, (∑ n ∈ Finset.range L, if n = ℓ o then g n else 0) = g (ℓ o) := by
    intro o
    rw [Finset.sum_ite_eq']
    simp [hℓL o]
  calc
    (∑ o : O, g (ℓ o)) = ∑ o : O, (∑ n ∈ Finset.range L, if n = ℓ o then g n else 0) := by
      apply Finset.sum_congr rfl
      intro o ho
      exact (hper o).symm
    _ = ∑ n ∈ Finset.range L, (∑ o : O, if n = ℓ o then g n else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.range L, g n * (((Finset.univ.filter (fun o : O => ℓ o = n)).card : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hsplit : (∑ o : O, if n = ℓ o then g n else 0) =
          ∑ o : O, g n * (if n = ℓ o then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro o ho
        by_cases h : n = ℓ o <;> simp [h]
      calc
        (∑ o : O, if n = ℓ o then g n else 0) = ∑ o : O, g n * (if n = ℓ o then 1 else 0) := hsplit
        _ = g n * (∑ o : O, (if n = ℓ o then 1 else 0)) := by rw [Finset.mul_sum]
        _ = g n * (((Finset.univ.filter (fun o : O => ℓ o = n)).card : ℕ) : ℝ) := by
          have hf : (Finset.univ.filter (fun o : O => n = ℓ o)) = (Finset.univ.filter (fun o : O => ℓ o = n)) := by
            ext o
            simp [eq_comm]
          rw [Finset.sum_boole]
          rw [hf]

/-- Cardinal monotonicity of filters: if `p` implies `q`, the `p`-filter of the
whole type has at most as many elements as the `q`-filter. -/
lemma card_filter_le_card_of_imp {α : Type*} [Fintype α] (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] (hpq : ∀ a : α, p a → q a) :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card := by
  have hsub : (Finset.univ.filter p) ⊆ (Finset.univ.filter q) := by
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, hpq a ha.2⟩
  exact Finset.card_le_card hsub


/-- **Outside case of BDG eq. (3)** (per-`x` form): for `2R ≤ ‖x−c‖`, the sum of
the weights of the `r`-balls covering `B(c,R)` is bounded by `C·w_B(x)`.  A
direct corollary of the uniform form `cover_sum_outside_uniform`. -/
lemma cover_sum_outside (k : ℕ) (hk : 1 ≤ k) (c : E k) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R) {ι : Type*} [Fintype ι] (c' : ι → E k)
    (hcen : ∀ i, ‖c' i - c‖ ≤ R) (hsep : ∀ i j : ι, i ≠ j → r ≤ ‖c' i - c' j‖)
    (x : E k) (hx : 2 * R ≤ ‖x - c‖) :
    ∃ C : ℝ, 0 < C ∧ (∑ i : ι, ballWeight k (c' i) r x) ≤ C * ballWeight k c R x := by
  obtain ⟨C, hC, hU⟩ := cover_sum_outside_uniform k hk c hR hr hrR c' hcen hsep
  exact ⟨C, hC, hU x hx⟩

-- uniform bound on the near-centre filters, for all scales m, with one constant
lemma near_count_uniform (k : ℕ) {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 < r)
    (c' : ι → E k) (x : E k) (hsep : ∀ i j : ι, i ≠ j → r ≤ ‖c' i - c' j‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (m : ℝ) * r)).card : ℕ) : ℝ)
        ≤ C * (((m : ℝ) + 1) ^ k) := by
  classical
  rcases Commons.Analysis.Metric.separated_points_count k with ⟨Ccnt, hCcnt, hcnt⟩
  refine ⟨Ccnt, hCcnt, ?_⟩
  intro m
  let ι₀ := {i : ι // ‖c' i - x‖ ≤ (m : ℝ) * r}
  have hcnt0 : (Fintype.card ι₀ : ℝ) ≤ Ccnt * (((m : ℝ) + 1) ^ k) := by
    have h := hcnt (ι := ι₀) hr (c := fun i : ι₀ => c' i.1) (x := x) (m := m)
      (by intro i j hij; exact hsep i.1 j.1 (by intro hval; exact hij (Subtype.ext hval)))
      (by intro i; exact i.2)
    simpa using h
  have hc : Fintype.card ι₀ = (Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (m : ℝ) * r)).card := by
    exact Fintype.card_of_subtype (s := Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (m : ℝ) * r))
      (H := by intro y; simp)
  calc
    (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (m : ℝ) * r)).card : ℕ) : ℝ)
        = (Fintype.card ι₀ : ℝ) := by exact_mod_cast hc.symm
    _ ≤ Ccnt * (((m : ℝ) + 1) ^ k) := hcnt0




-- q0 := 2^k·(2^{100k})⁻¹ ≤ 1/2 for k ≥ 1
lemma q0_le_half (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) ^ k * ((2 : ℝ) ^ (100 * k))⁻¹ ≤ (1 / 2 : ℝ) := by
  have hke : k + 1 ≤ 100 * k := by omega
  have hle : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (100 * k) := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hke
  have hmul : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    rw [pow_succ']
  have hmain : (2 : ℝ) * ((2 : ℝ) ^ k * ((2 : ℝ) ^ (100 * k))⁻¹) ≤ 1 := by
    calc
      (2 : ℝ) * ((2 : ℝ) ^ k * ((2 : ℝ) ^ (100 * k))⁻¹)
          = (2 * (2 : ℝ) ^ k) * ((2 : ℝ) ^ (100 * k))⁻¹ := by ring
      _ = (2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (100 * k))⁻¹ := by rw [hmul]
      _ ≤ (2 : ℝ) ^ (100 * k) * ((2 : ℝ) ^ (100 * k))⁻¹ := by
            exact mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
      _ = 1 := by
            rw [mul_inv_cancel₀ (pow_ne_zero _ (by norm_num))]
  nlinarith

-- uniform bound on the near-centre filters, for all scales m, with one constant
/-- **Near/inside case of BDG eq. (3)**: for `‖x−c‖ ≤ 2R` the sum of the
weights of the `r`-balls is `≤ C·w_{B(c,R)}(x)`.

Proof plan (dyadic shells; all ingredients are proven or in the commons):
  * `t := ‖x−c‖ ≤ 2R` gives `d_i := ‖x−c_i‖ ≤ 3R` for every centre, and
    `w_B(x) ≥ 3^{−100k}` (`ballWeight_lower_near`), so it suffices to bound the
    weight sum by a constant `C(k)`.
  * Innermost bucket `d_i ≤ r`: each `w_i ≤ 1`, multiplicity ≤ `Ccnt·2^k`
    (`separated_points_count`, `m = 1`).
  * Outer centres (`d_i > r`): `w_i ≤ (r/d_i)^{100k}` (`ballWeight_le_pow_ratio`);
    `d_i/r > 1` lies in a dyadic interval `2^ℓ < d_i/r ≤ 2^{ℓ+1}` for a unique
    `ℓ` (`Commons.Analysis.Real.dyadic_between`), giving `w_i ≤ 2^{−ℓ·100k}`
    and `ℓ < ⌈3R/r⌉ + 1` (since `2^ℓ < d_i/r ≤ 3R/r`); multiplicity of shell
    `ℓ` ≤ `Ccnt·2^{(ℓ+2)k}` (`separated_points_count`, `m = 2^{ℓ+1}`);
    summing the (finite) shells and the geometric series
    `Σ_ℓ 2^{ℓ(k−100k)} ≤ 2` (as `100k ≥ k+1`) yields the constant. -/
lemma cover_sum_near (k : ℕ) (hk : 1 ≤ k) (c : E k) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R) {ι : Type*} [Fintype ι] (c' : ι → E k)
    (hcen : ∀ i, ‖c' i - c‖ ≤ R) (hsep : ∀ i j : ι, i ≠ j → r ≤ ‖c' i - c' j‖)
    (x : E k) (hnear : ‖x - c‖ ≤ 2 * R) :
    ∃ C : ℝ, 0 < C ∧ (∑ i : ι, ballWeight k (c' i) r x) ≤ C * ballWeight k c R x := by
  classical
  let N : ℕ := 100 * k
  let pIn : ι → Prop := fun i => ‖c' i - x‖ ≤ r
  let d : ι → ℝ := fun i => ‖x - c' i‖
  have hwB : ((3 : ℝ) ^ N)⁻¹ ≤ ballWeight k c R x := by
    have hw := ballWeight_lower_near k c hR hnear
    simpa [N] using hw
  have hd3 : ∀ i, d i ≤ 3 * R := by
    intro i
    have hn := dist_triangle (c' i) c x
    have hn' : ‖c' i - x‖ ≤ ‖c' i - c‖ + ‖c - x‖ := by simpa [dist_eq_norm] using hn
    have hcx : ‖c - x‖ ≤ 2 * R := by
      simpa [norm_sub_rev] using hnear
    dsimp [d]
    rw [norm_sub_rev]
    linarith [hcx, hcen i]
  -- pointwise majorant: w_i ≤ 1 if inner, else (r/d_i)^N
  have hwle : ∀ i : ι, ballWeight k (c' i) r x ≤ (if pIn i then 1 else (r / d i) ^ N) := by
    intro i
    by_cases hi : pIn i
    · have hw1 := ballWeight_le_one k (c' i) hr x
      simpa [hi] using hw1
    · have hp : ¬ pIn i := hi
      have hgr : r < ‖c' i - x‖ := lt_of_not_ge (by
        intro hg
        exact hp hg)
      have hdpos : 0 < ‖x - c' i‖ := by
        rw [norm_sub_rev]
        linarith
      have hdec := ballWeight_le_pow_ratio k (c' i) hr hdpos
      -- hdec : w_i ≤ (r/‖x − c' i‖)^(100k) = (r/d i)^N
      simpa [pIn, hi, d, N] using hdec
  have hsumle : (∑ i : ι, ballWeight k (c' i) r x) ≤
      ∑ i : ι, (if pIn i then 1 else (r / d i) ^ N) := by
    exact Finset.sum_le_sum (fun i hi => hwle i)
  -- split majorant: inner (pIn) + outer (¬pIn)
  have hmaj : (fun i : ι => (if pIn i then 1 else (r / d i) ^ N)) =
      (fun i : ι => (if pIn i then 1 else 0) + (if ¬ pIn i then (r / d i) ^ N else 0)) := by
    funext i
    by_cases hi : pIn i
    · simp [hi]
    · simp [hi]
  have hsplit : (∑ i : ι, (if pIn i then 1 else (r / d i) ^ N)) =
      (∑ i ∈ (Finset.univ : Finset ι) with pIn i, (1 : ℝ)) +
      (∑ i ∈ (Finset.univ : Finset ι) with ¬ pIn i, (r / d i) ^ N) := by
    calc
      (∑ i : ι, (if pIn i then 1 else (r / d i) ^ N))
          = ∑ i : ι, ((if pIn i then 1 else 0) + (if ¬ pIn i then (r / d i) ^ N else 0)) := by
              rw [hmaj]
      _ = (∑ i : ι, (if pIn i then 1 else 0)) + ∑ i : ι, (if ¬ pIn i then (r / d i) ^ N else 0) := by
              rw [Finset.sum_add_distrib]
      _ = (∑ i ∈ (Finset.univ : Finset ι) with pIn i, (1 : ℝ)) +
          (∑ i ∈ (Finset.univ : Finset ι) with ¬ pIn i, (r / d i) ^ N) := by
              rw [Finset.sum_filter]
              rw [Finset.sum_filter]
  -- inner part: ≤ C1·2^k
  rcases inner_count_le k hr c' x hsep with ⟨C1, hC1, hb1⟩
  have hinner : (∑ i ∈ (Finset.univ : Finset ι) with pIn i, (1 : ℝ)) ≤ C1 * (2 : ℝ) ^ k := by
    have hb1' : (((Finset.univ.filter pIn).card : ℕ) : ℝ) ≤ C1 * (2 : ℝ) ^ k := by
      simpa [pIn] using hb1
    calc
      (∑ i ∈ (Finset.univ : Finset ι) with pIn i, (1 : ℝ))
          = (((Finset.univ.filter pIn).card : ℕ) : ℝ) := by
              rw [Finset.sum_filter]
              exact (Finset.sum_boole pIn (Finset.univ : Finset ι))
      _ ≤ C1 * (2 : ℝ) ^ k := hb1'
  -- OUTER part: i with ¬ pIn i (r < ‖c' i − x‖), each term (r / d i)^N.
  let O := {i : ι // ¬ pIn i}
  -- outer subtype sum = filtered sum
  have hout0 : (∑ i ∈ (Finset.univ : Finset ι) with ¬ pIn i, (r / d i) ^ N)
      = ∑ o : O, (r / d (o : ι)) ^ N := by
    exact Finset.sum_subtype (s := Finset.univ.filter (fun i => ¬ pIn i))
      (h := by intro y; simp) (f := fun i => (r / d i) ^ N)
  -- per outer centre facts
  have hgr : ∀ o : O, r < ‖c' o.1 - x‖ := by
    intro o
    exact lt_of_not_ge (by simpa [pIn] using o.2)
  have hdpos : ∀ o : O, 0 < ‖x - c' o.1‖ := by
    intro o
    rw [norm_sub_rev]
    linarith [hgr o]
  have ha1 : ∀ o : O, (1 : ℝ) < ‖x - c' o.1‖ / r := by
    intro o
    exact (one_lt_div hr).mpr (by simpa [norm_sub_rev] using hgr o)
  -- dyadic shell index of each outer centre
  let ℓ : O → ℕ := fun o => Classical.choose (Commons.Analysis.Real.dyadic_between (a := ‖x - c' o.1‖ / r) (ha1 o))
  have hℓ : ∀ o : O, (2 : ℝ) ^ ℓ o < ‖x - c' o.1‖ / r ∧ ‖x - c' o.1‖ / r ≤ (2 : ℝ) ^ (ℓ o + 1) := by
    intro o
    exact Classical.choose_spec (Commons.Analysis.Real.dyadic_between (a := ‖x - c' o.1‖ / r) (ha1 o))
  -- each outer centre lies within 3R of x, so ℓ o < L (L := ⌈3R/r⌉ + 1)
  let L : ℕ := Nat.ceil (3 * R / r) + 1
  have hd3 : ∀ o : O, ‖x - c' o.1‖ ≤ 3 * R := by
    intro o
    have hcx : ‖c - x‖ ≤ 2 * R := by simpa [norm_sub_rev] using hnear
    have hn := dist_triangle (c' o.1) c x
    have hn' : ‖c' o.1 - x‖ ≤ ‖c' o.1 - c‖ + ‖c - x‖ := by simpa [dist_eq_norm] using hn
    rw [norm_sub_rev]
    linarith [hcx, hcen o.1]
  have hmm_pow : (Nat.ceil (3 * R / r) : ℝ) < (2 : ℝ) ^ L := by
    have hnat : Nat.ceil (3 * R / r) < 2 ^ L := by
      have h1 : Nat.ceil (3 * R / r) < Nat.ceil (3 * R / r) + 1 := Nat.lt_succ_self _
      have h2 : Nat.ceil (3 * R / r) + 1 < 2 ^ (Nat.ceil (3 * R / r) + 1) := Nat.lt_two_pow_self
      exact h1.trans h2
    exact_mod_cast hnat
  have hℓL : ∀ o : O, ℓ o < L := by
    intro o
    have hb : ‖x - c' o.1‖ / r ≤ 3 * R / r := by
      exact div_le_div_of_nonneg_right (hd3 o) (le_of_lt hr)
    have h3 : 3 * R / r ≤ (Nat.ceil (3 * R / r) : ℝ) := Nat.le_ceil (3 * R / r)
    have hlt : (2 : ℝ) ^ ℓ o < (2 : ℝ) ^ L := by
      exact lt_trans (lt_of_lt_of_le (lt_of_lt_of_le (hℓ o).1 hb) h3) hmm_pow
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlt
  -- per-o decay: (r/‖x−c' o.1‖)^N ≤ ((2:ℝ)^(ℓ o·N))⁻¹
  have hdec_o : ∀ o : O, (r / ‖x - c' o.1‖) ^ N ≤ ((2 : ℝ) ^ (ℓ o * N))⁻¹ := by
    intro o
    exact pow_div_le_inv_pow r (‖x - c' o.1‖) hr (hdpos o) (hℓ o).1
  -- per-o decay: (r/‖x−c' o.1‖)^N ≤ ((2:ℝ)^(ℓ o·N))⁻¹
  have hdec_o : ∀ o : O, (r / ‖x - c' o.1‖) ^ N ≤ ((2 : ℝ) ^ (ℓ o * N))⁻¹ := by
    intro o
    exact pow_div_le_inv_pow r (‖x - c' o.1‖) hr (hdpos o) (hℓ o).1
  -- outer-chain step 1: Σ_o (r/d)^N ≤ Σ_o g(ℓ o)  (hdec_o summed)
  have hdec_sum : (∑ o : O, (r / ‖x - c' o.1‖) ^ N) ≤ ∑ o : O, ((2 : ℝ) ^ (ℓ o * N))⁻¹ := by
    exact Finset.sum_le_sum (fun o ho => hdec_o o)
  -- outer-chain step 2: fiber partition with g n := ((2:ℝ)^(n·N))⁻¹
  have hfib : (∑ o : O, ((2 : ℝ) ^ (ℓ o * N))⁻¹) =
      ∑ n ∈ Finset.range L, ((2 : ℝ) ^ (n * N))⁻¹ * (((Finset.univ.filter (fun o : O => ℓ o = n)).card : ℕ) : ℝ) := by
    exact sum_fiber_partition (ℓ := ℓ) (L := L) hℓL (g := fun n : ℕ => ((2 : ℝ) ^ (n * N))⁻¹)
  -- fiber-card ≤ near-centre count (via the injective inclusion O ↪ ι)
  have hfib_le : ∀ n : ℕ,
      (((Finset.univ.filter (fun o : O => ℓ o = n)).card : ℕ) : ℝ) ≤
      (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (2 : ℝ) ^ (n + 1) * r)).card : ℕ) : ℝ) := by
    intro n
    let sO : Finset O := Finset.univ.filter (fun o : O => ℓ o = n)
    have hsub : sO.image (fun o : O => (o : ι)) ⊆
        (Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (2 : ℝ) ^ (n + 1) * r)) := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨o, ho, rfl⟩
      rw [Finset.mem_filter]
      have ho2 : ℓ o = n := (Finset.mem_filter.mp ho).2
      have hupper := (hℓ o).2
      have hupper' : ‖x - c' o.1‖ / r ≤ (2 : ℝ) ^ (n + 1) := by
        simpa [ho2] using hupper
      have hlen : ‖x - c' o.1‖ ≤ (2 : ℝ) ^ (n + 1) * r := by
        exact (div_le_iff₀ hr).mp hupper'
      refine ⟨by simp, ?_⟩
      rw [norm_sub_rev]
      exact hlen
    have hcard_eq : sO.card = (sO.image (fun o : O => (o : ι))).card := by
      exact (Finset.card_image_of_injOn (s := sO) (f := fun o : O => (o : ι)) (by
        intro a ha b hb hab
        exact Subtype.ext hab)).symm
    have hcard_le : sO.card ≤
        (Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (2 : ℝ) ^ (n + 1) * r)).card := by
      calc
        sO.card = (sO.image (fun o : O => (o : ι))).card := hcard_eq
        _ ≤ (Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (2 : ℝ) ^ (n + 1) * r)).card :=
              Finset.card_le_card hsub
    exact_mod_cast hcard_le
  -- feed the fiber-card bound into the fiber sum (termwise, g n ≥ 0)
  have hfib_sum : (∑ n ∈ Finset.range L,
        ((2 : ℝ) ^ (n * N))⁻¹ * (((Finset.univ.filter (fun o : O => ℓ o = n)).card : ℕ) : ℝ)) ≤
      (∑ n ∈ Finset.range L,
        ((2 : ℝ) ^ (n * N))⁻¹ * (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (2 : ℝ) ^ (n + 1) * r)).card : ℕ) : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left (hfib_le n) (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
  -- near filters at m = 2^(n+1), uniformly bounded by one constant C
  rcases near_count_uniform k hr c' x hsep with ⟨C, hC, hnc⟩
  have hnearb : ∀ n : ℕ,
      (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (2 : ℝ) ^ (n + 1) * r)).card : ℕ) : ℝ)
        ≤ C * (((2 : ℝ) ^ (n + 1) + 1) ^ k) := by
    intro n
    have h1 := hnc (2 ^ (n + 1))
    have hfc : (Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ ((2 ^ (n + 1) : ℕ) : ℝ) * r))
        = (Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (2 : ℝ) ^ (n + 1) * r)) := by
      ext i
      simp [Nat.cast_pow]
    have he : (((2 ^ (n + 1) : ℕ) : ℝ) + 1) = ((2 : ℝ) ^ (n + 1) + 1) := by
      rw [Nat.cast_pow]
      norm_num
    calc
      (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (2 : ℝ) ^ (n + 1) * r)).card : ℕ) : ℝ)
          = (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ ((2 ^ (n + 1) : ℕ) : ℝ) * r)).card : ℕ) : ℝ) := by
              rw [← hfc]
      _ ≤ C * ((((2 ^ (n + 1) : ℕ) : ℝ) + 1) ^ k) := h1
      _ = C * (((2 : ℝ) ^ (n + 1) + 1) ^ k) := by rw [he]
  -- feed the uniform near bound into the fiber sum
  have hnear_sum : (∑ n ∈ Finset.range L,
        ((2 : ℝ) ^ (n * N))⁻¹ * (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (2 : ℝ) ^ (n + 1) * r)).card : ℕ) : ℝ)) ≤
      (∑ n ∈ Finset.range L, ((2 : ℝ) ^ (n * N))⁻¹ * (C * (((2 : ℝ) ^ (n + 1) + 1) ^ k))) := by
    apply Finset.sum_le_sum
    intro n hn
    exact mul_le_mul_of_nonneg_left (hnearb n) (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
  -- per-term collapse with the fleet's two_pow_collapse_bound
  have hcol_sum : (∑ n ∈ Finset.range L,
        ((2 : ℝ) ^ (n * N))⁻¹ * (C * (((2 : ℝ) ^ (n + 1) + 1) ^ k))) ≤
      (∑ n ∈ Finset.range L,
        ((2 : ℝ) ^ (n * N))⁻¹ * (C * ((4 : ℝ) ^ k * (2 : ℝ) ^ (n * k)))) := by
    apply Finset.sum_le_sum
    intro n hn
    have hc := Commons.Analysis.Real.two_pow_collapse_bound n k
    have hx : C * (((2 : ℝ) ^ (n + 1) + 1) ^ k) ≤ C * ((4 : ℝ) ^ k * (2 : ℝ) ^ (n * k)) := by
      exact mul_le_mul_of_nonneg_left hc (le_of_lt hC)
    exact mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
  -- rewrite collapsed terms into C·4^k·q0^n
  let q0 : ℝ := (2 : ℝ) ^ k * ((2 : ℝ) ^ N)⁻¹
  have hterm : ∀ n : ℕ, ((2 : ℝ) ^ (n * N))⁻¹ * (C * ((4 : ℝ) ^ k * (2 : ℝ) ^ (n * k))) =
      C * (4 : ℝ) ^ k * (q0 ^ n) := by
    intro n
    have hq := Commons.Analysis.Real.inv_pow_prod_two n N k
    -- hq : q0^n = 2^(n*k)·(2^(n*N))⁻¹  (up to the definition of q0)
    calc
      ((2 : ℝ) ^ (n * N))⁻¹ * (C * ((4 : ℝ) ^ k * (2 : ℝ) ^ (n * k)))
          = C * (4 : ℝ) ^ k * ((2 : ℝ) ^ (n * N))⁻¹ * (2 : ℝ) ^ (n * k) := by ring
      _ = C * (4 : ℝ) ^ k * ((2 : ℝ) ^ (n * k) * ((2 : ℝ) ^ (n * N))⁻¹) := by ring
      _ = C * (4 : ℝ) ^ k * (q0 ^ n) := by
          rw [← hq]
  -- geometric partial sum of q0 is at most 2
  have hq0half : q0 ≤ 1 / 2 := by
    simpa [q0, N] using q0_le_half k hk
  have hq00 : 0 ≤ q0 := by
    dsimp [q0]
    exact mul_nonneg (pow_nonneg (by norm_num) _) (inv_nonneg.mpr (pow_nonneg (by norm_num) _))
  have hq0lt : q0 < 1 := by nlinarith [hq0half]
  have hden : (1 - q0)⁻¹ ≤ 2 := by
    have hpos : 0 < 1 - q0 := by nlinarith [hq0half]
    have hb : (1 : ℝ) / 2 ≤ 1 - q0 := by nlinarith [hq0half]
    have h1 : (1 - q0)⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := (inv_le_inv₀ hpos (by norm_num : 0 < (1:ℝ)/2)).mpr hb
    exact h1.trans (by norm_num)
  have hgeom : (∑ n ∈ Finset.range L, q0 ^ n) ≤ 2 := by
    have hg := geom_sum_le_inv_one_sub hq00 hq0lt L
    exact le_trans hg hden
  -- sum-level collapse: Σ g n·(C·4^k·2^{nk}) = C·4^k·Σ q0^n ≤ 2·C·4^k
  have hgeo_sum : (∑ n ∈ Finset.range L,
        ((2 : ℝ) ^ (n * N))⁻¹ * (C * ((4 : ℝ) ^ k * (2 : ℝ) ^ (n * k)))) ≤ 2 * C * (4 : ℝ) ^ k := by
    calc
      (∑ n ∈ Finset.range L, ((2 : ℝ) ^ (n * N))⁻¹ * (C * ((4 : ℝ) ^ k * (2 : ℝ) ^ (n * k))))
          = ∑ n ∈ Finset.range L, C * (4 : ℝ) ^ k * (q0 ^ n) := by
              apply Finset.sum_congr rfl
              intro n hn
              exact hterm n
      _ = C * (4 : ℝ) ^ k * (∑ n ∈ Finset.range L, q0 ^ n) := by
              rw [← Finset.mul_sum]
      _ ≤ C * (4 : ℝ) ^ k * 2 := by
              exact mul_le_mul_of_nonneg_left hgeom (mul_nonneg (le_of_lt hC) (pow_nonneg (by norm_num) _))
      _ = 2 * C * (4 : ℝ) ^ k := by ring
  -- outer total (filtered sum of (r/d)^N) ≤ 2·C·4^k
  have houter_total : (∑ i ∈ (Finset.univ : Finset ι) with ¬ pIn i, (r / d i) ^ N) ≤ 2 * C * (4 : ℝ) ^ k := by
    calc
      (∑ i ∈ (Finset.univ : Finset ι) with ¬ pIn i, (r / d i) ^ N)
          = ∑ o : O, (r / d (o : ι)) ^ N := hout0
      _ = ∑ o : O, (r / ‖x - c' o.1‖) ^ N := by
              apply Finset.sum_congr rfl
              intro o ho
              congr 1
      _ ≤ ∑ o : O, ((2 : ℝ) ^ (ℓ o * N))⁻¹ := hdec_sum
      _ = ∑ n ∈ Finset.range L, ((2 : ℝ) ^ (n * N))⁻¹ * (((Finset.univ.filter (fun o : O => ℓ o = n)).card : ℕ) : ℝ) := hfib
      _ ≤ ∑ n ∈ Finset.range L,
            ((2 : ℝ) ^ (n * N))⁻¹ * (((Finset.univ.filter (fun i : ι => ‖c' i - x‖ ≤ (2 : ℝ) ^ (n + 1) * r)).card : ℕ) : ℝ) := hfib_sum
      _ ≤ ∑ n ∈ Finset.range L, ((2 : ℝ) ^ (n * N))⁻¹ * (C * (((2 : ℝ) ^ (n + 1) + 1) ^ k)) := hnear_sum
      _ ≤ ∑ n ∈ Finset.range L, ((2 : ℝ) ^ (n * N))⁻¹ * (C * ((4 : ℝ) ^ k * (2 : ℝ) ^ (n * k))) := hcol_sum
      _ ≤ 2 * C * (4 : ℝ) ^ k := hgeo_sum
  -- total: Σ w ≤ inner + outer ≤ (C1·2^k + 2·C·4^k)·3^N·wB
  have htot0 : (∑ i : ι, ballWeight k (c' i) r x) ≤ C1 * (2 : ℝ) ^ k + 2 * C * (4 : ℝ) ^ k := by
    calc
      (∑ i : ι, ballWeight k (c' i) r x) ≤ ∑ i : ι, (if pIn i then 1 else (r / d i) ^ N) := hsumle
      _ = (∑ i ∈ (Finset.univ : Finset ι) with pIn i, (1 : ℝ)) +
          (∑ i ∈ (Finset.univ : Finset ι) with ¬ pIn i, (r / d i) ^ N) := hsplit
      _ ≤ C1 * (2 : ℝ) ^ k + 2 * C * (4 : ℝ) ^ k := by
            exact add_le_add hinner houter_total
  -- constant chase: 3^N·wB ≥ 1
  have hw1 : (1 : ℝ) ≤ (3 : ℝ) ^ N * ballWeight k c R x := by
    have h := hwB
    have h3 : 0 < (3 : ℝ) ^ N := pow_pos (by norm_num) _
    have hm := mul_le_mul_of_nonneg_left h (le_of_lt h3)
    simpa using hm
  let CB : ℝ := C1 * (2 : ℝ) ^ k + 2 * C * (4 : ℝ) ^ k
  have hCB0 : 0 < CB := by
    have h1 : 0 < C1 * (2 : ℝ) ^ k := mul_pos hC1 (pow_pos (by norm_num) _)
    have h2 : 0 < 2 * C * (4 : ℝ) ^ k := by positivity
    dsimp [CB]
    linarith
  refine ⟨CB * (3 : ℝ) ^ N, ?_, ?_⟩
  · positivity
  · calc
      (∑ i : ι, ballWeight k (c' i) r x) ≤ CB := by
        simpa [CB] using htot0
      _ ≤ CB * ((3 : ℝ) ^ N * ballWeight k c R x) := by
        simpa using (mul_le_mul_of_nonneg_left hw1 (le_of_lt hCB0))
      _ = (CB * (3 : ℝ) ^ N) * ballWeight k c R x := by ring

/-- **BDG eq. (3), cover-sum form**: for a finitely-overlapping cover of `B(c,R)`
by balls of radius `r ≤ R` with centres inside `B(c,R)` (`r`-separated), the
weights sum boundedly:
`Σ_i w_{B(c_i,r)}(x) ≤ C · w_{B(c,R)}(x)` with `C` independent of `x, R, r`.
The proof splits into the *outside case* `2R ≤ ‖x−c‖` (proved:
`cover_sum_outside`) and the *near/inside case* `‖x−c‖ ≤ 2R`
(`cover_sum_near`). -/
lemma ballWeight_sum_cover_le (k : ℕ) (hk : 1 ≤ k) (c : E k) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R) {ι : Type*} [Fintype ι] (c' : ι → E k)
    (hcen : ∀ i, ‖c' i - c‖ ≤ R) (hsep : ∀ i j : ι, i ≠ j → r ≤ ‖c' i - c' j‖)
    (x : E k) :
    ∃ C : ℝ, 0 < C ∧ (∑ i : ι, ballWeight k (c' i) r x) ≤ C * ballWeight k c R x := by
  classical
  by_cases hfar : 2 * R ≤ ‖x - c‖
  · -- outside case
    exact cover_sum_outside k hk c hR hr hrR c' hcen hsep x hfar
  · -- near/inside case
    have hnear : ‖x - c‖ ≤ 2 * R := by linarith
    exact cover_sum_near k hk c hR hr hrR c' hcen hsep x hnear


/-- **BDG eq. (3), uniform cover-sum form** (the form needed for the
`extended_decoupling` cover step): there is a single constant `C`, depending
only on `k`, `R`, `r` and the number of centres, such that
`Σ_i w_{B(c_i,r)}(x) ≤ C·w_{B(c,R)}(x)` for **all** `x` simultaneously.
(Unlike `ballWeight_sum_cover_le`, whose `C` is allowed to depend on `x`.)
Outside the near region this is `cover_sum_outside_uniform`; near `c` we use
the crude bound `Σ_i w_i ≤ #centres` together with
`w_{B(c,R)}(x) ≥ 3^{-100k}` (`ballWeight_lower_near`). -/
lemma ballWeight_sum_cover_le_uniform (k : ℕ) (hk : 1 ≤ k) (c : E k) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R) {ι : Type*} [Fintype ι] (c' : ι → E k)
    (hcen : ∀ i, ‖c' i - c‖ ≤ R) (hsep : ∀ i j : ι, i ≠ j → r ≤ ‖c' i - c' j‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E k, (∑ i : ι, ballWeight k (c' i) r x) ≤ C * ballWeight k c R x := by
  obtain ⟨C0, hC0, hfar⟩ := cover_sum_outside_uniform k hk c hR hr hrR c' hcen hsep
  refine ⟨max C0 ((Fintype.card ι : ℝ) * (3 : ℝ) ^ (100 * k)), ?_, ?_⟩
  · exact lt_of_lt_of_le hC0 (le_max_left _ _)
  · intro x
    by_cases hx : 2 * R ≤ ‖x - c‖
    · calc
        (∑ i : ι, ballWeight k (c' i) r x) ≤ C0 * ballWeight k c R x := hfar x hx
        _ ≤ max C0 ((Fintype.card ι : ℝ) * (3 : ℝ) ^ (100 * k)) * ballWeight k c R x :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (ballWeight_pos k c hR x))
    · have hx2 : ‖x - c‖ ≤ 2 * R := le_of_lt (lt_of_not_ge hx)
      have hwlow : ((3 : ℝ) ^ (100 * k))⁻¹ ≤ ballWeight k c R x := ballWeight_lower_near k c hR hx2
      have hsum : (∑ i : ι, ballWeight k (c' i) r x) ≤ (Fintype.card ι : ℝ) := by
        calc
          (∑ i : ι, ballWeight k (c' i) r x) ≤ ∑ _i : ι, (1 : ℝ) :=
                Finset.sum_le_sum (fun i _hi => ballWeight_le_one k (c' i) hr x)
          _ = (Fintype.card ι : ℝ) := by simp
      have hw0 : 0 ≤ ballWeight k c R x := le_of_lt (ballWeight_pos k c hR x)
      have h3pos : 0 < (3 : ℝ) ^ (100 * k) := pow_pos (by norm_num) _
      have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ (100 * k) * ballWeight k c R x := by
        have hm := mul_le_mul_of_nonneg_left hwlow (le_of_lt h3pos)
        rwa [mul_inv_cancel₀ (ne_of_gt h3pos)] at hm
      calc
        (∑ i : ι, ballWeight k (c' i) r x) ≤ (Fintype.card ι : ℝ) := hsum
        _ ≤ (Fintype.card ι : ℝ) * ((3 : ℝ) ^ (100 * k) * ballWeight k c R x) :=
              le_mul_of_one_le_right (by positivity) h3
        _ = ((Fintype.card ι : ℝ) * (3 : ℝ) ^ (100 * k)) * ballWeight k c R x := by ring
        _ ≤ max C0 ((Fintype.card ι : ℝ) * (3 : ℝ) ^ (100 * k)) * ballWeight k c R x :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hw0


/-- The character `e(x·γ(t))` with `γ(t) = (t, t², …, tᵏ)`. -/
def momChar (k : ℕ) (x : E k) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * ((∑ j : Fin k, x j * t ^ (j.val + 1) : ℝ) : ℂ))

/-- Separation condition of BDG Thm 4.1: `N` real points, one in each interval
`((i−1)/N, i/N]`. -/
def Separated (N : ℕ) (t : Fin N → ℝ) : Prop :=
  ∀ i : Fin N, (i.1 : ℝ) / N < t i ∧ t i ≤ ((i.1 : ℝ) + 1) / N

/-- The integer moment of degree `j` of a tuple (its ℕ-power sum, as an integer).
(The tuple type `Fin s → Finset.Icc 1 X` is the first component of
`Core.PairSpace s X`.) -/
def zmom {s X : ℕ} (j : ℕ) (x : Fin s → Finset.Icc 1 X) : ℤ :=
  (((∑ i : Fin s, (x i).1 ^ j) : ℕ) : ℤ)

/-- BDG's separated bound at scale `X` for degree `j ≤ k`: `X^{j−k}`. -/
def sepBound (X j k : ℕ) : ℝ := (X : ℝ) ^ ((j : ℝ) - (k : ℝ))

/-- The discrete count of BDG's Corollary 4.2 for the integer point set
`{1,…,X}` (`N = X`, point `i` ↦ value `i`): tuples in `[1,X]^{2s}` whose
degree-`j` moment difference `Z_j` satisfies `|Z_j| ≤ X^{j−k}` for `1 ≤ j ≤ k`. -/
def Jsep (s k X : ℕ) : ℕ :=
  ((Finset.univ : Finset (PairSpace s X)).filter fun xy =>
    ∀ j : ℕ, 1 ≤ j → j ≤ k → |((zmom j xy.1 - zmom j xy.2) : ℝ)| ≤ sepBound X j k).card

/-- Exact solutions are among the separated (near-)solutions: `J s k X ≤ Jsep s k X`. -/
lemma J_le_Jsep (s k X : ℕ) : J s k X ≤ (Jsep s k X : ℝ) := by
  rw [J_eq_filter_card]
  have hsub : (Finset.univ.filter (Matches s k X)) ⊆
      (Finset.univ.filter (fun xy : PairSpace s X =>
        ∀ j : ℕ, 1 ≤ j → j ≤ k → |((zmom j xy.1 - zmom j xy.2) : ℝ)| ≤ sepBound X j k)) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨hp.1, ?_⟩
    intro j hj1 hjk
    have heqN : (∑ i : Fin s, (p.1 i).1 ^ j) = (∑ i : Fin s, (p.2 i).1 ^ j) := hp.2 j hjk
    have hz : zmom j p.1 = zmom j p.2 := by
      unfold zmom
      exact_mod_cast heqN
    rw [hz]
    simp
    exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le X)) _
  unfold Jsep
  exact_mod_cast Finset.card_le_card hsub

/-! ## Weighted `L^p` vocabulary and the Hölder/trivial-bound reduction
(towards BDG Thm 4.1)

BDG Theorem 4.1 (discrete restriction) is proved from its critical case
`p₀ = k(k+1)` by invoking Hölder and the trivial `L∞` bound.  Concretely, with
the pointwise trivial bound `|f(x)| ≤ √N ‖a‖₂` and the power domination

    |f(x)|^p ≤ (√N ‖a‖₂)^{p−p₀} · |f(x)|^{p₀}      (p₀ ≤ p)

(which is `Commons.Analysis.Real.rpow_dominate` applied to `a := |f x|`,
`M := √N‖a‖₂`), one obtains for the weighted powers

    wLpPow p f ≤ M^(p−p₀) · wLpPow p₀ f

and hence, taking `(1/p)`-th powers, `‖f‖_{L^p(w)} ≤ ‖f‖_{L^{p₀}(w)}^{p₀/p} ·
M^{1−p₀/p}`, reducing the general-`p` discrete restriction bound to the
critical one.  The weighted-power integral is `wLpPow`; the integral-level
domination (monotonicity of the Bochner integral for the pointwise-dominated,
nonnegative integrands) is the target `weighted_pow_dominate`, whose proof
uses `Commons.Analysis.Real.rpow_dominate` pointwise and
`MeasureTheory.integral_mono`-type reasoning (integrability of the two
nonnegative integrands is the side condition to manage). -/

/-- Weighted `L^p`-power of `f` against the ball weight `w_B`:
`∫_{ℝᵏ} ‖f(x)‖^p · w_B(x) dx` (real exponents). -/
def wLpPow (k : ℕ) (c : E k) (R : ℝ) (p : ℝ) (f : E k → ℂ) : ℝ :=
  ∫ x : E k, ‖f x‖ ^ p * ballWeight k c R x

/-- Volume of the Euclidean ball `B(c,R) ⊂ ℝᵏ` (Lebesgue). -/
def ballVol (k : ℕ) (c : E k) (R : ℝ) : ℝ := (volume (Metric.ball c R)).toReal

/-- The Euclidean ball `B(c,R)` has positive finite volume for `k ≥ 1`, `R > 0`. -/
lemma ballVol_pos (k : ℕ) (_hk : 1 ≤ k) (c : E k) {R : ℝ} (hR : 0 < R) :
    0 < ballVol k c R := by
  unfold ballVol
  have hne : (volume : Measure (E k)) (Metric.ball c R) ≠ 0 := by
    exact IsOpen.measure_ne_zero (μ := (volume : Measure (E k))) Metric.isOpen_ball
      (Metric.nonempty_ball.mpr hR)
  exact ENNReal.toReal_pos hne measure_ball_lt_top.ne

/-- The **ball-averaged** weighted `Lᵖ`-power `(1/|B_R|)∫_{ℝᵏ} ‖f‖^p w_B`
(BDG's normalisation): the quantity whose `1/p`-th power BDG's discrete
restriction theorem (Thm 4.1) bounds uniformly in `N`, `R`, `a`. -/
def wLpPowAvg (k : ℕ) (c : E k) (R : ℝ) (p : ℝ) (f : E k → ℂ) : ℝ :=
  wLpPow k c R p f / ballVol k c R

/-- **Hölder/trivial-bound reduction (integral level)**: if `|f| ≤ M` pointwise
and `p₀ ≤ p`, the `p`-th weighted power is dominated by
`M^(p−p₀)` times the `p₀`-th weighted power.  This is the engine that reduces
BDG Thm 4.1 for general `p ≥ 2` to its critical case `p₀ = k(k+1)`;
`Commons.Analysis.Real.rpow_dominate` supplies the pointwise step. -/
lemma weighted_pow_dominate (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {p p₀ : ℝ}
    (hp₀ : 0 ≤ p₀) (hp₀p : p₀ ≤ p) {M : ℝ} (hM : 0 ≤ M) (f : E k → ℂ)
    (hb : ∀ x : E k, ‖f x‖ ≤ M)
    (hintp : Integrable (fun x : E k => ‖f x‖ ^ p * ballWeight k c R x) volume)
    (hintp0 : Integrable (fun x : E k => ‖f x‖ ^ p₀ * ballWeight k c R x) volume) :
    wLpPow k c R p f ≤ M ^ (p - p₀) * wLpPow k c R p₀ f := by
  unfold wLpPow
  let g : E k → ℝ := fun x => M ^ (p - p₀) * (‖f x‖ ^ p₀ * ballWeight k c R x)
  have hpt : (fun x : E k => ‖f x‖ ^ p * ballWeight k c R x) ≤ g := by
    intro x
    have hd := Commons.Analysis.Real.rpow_dominate (norm_nonneg (f x)) (hb x) hM hp₀ hp₀p
    have hw : 0 ≤ ballWeight k c R x := le_of_lt (ballWeight_pos k c hR x)
    calc
      ‖f x‖ ^ p * ballWeight k c R x ≤ (M ^ (p - p₀) * ‖f x‖ ^ p₀) * ballWeight k c R x :=
            mul_le_mul_of_nonneg_right hd hw
      _ = M ^ (p - p₀) * (‖f x‖ ^ p₀ * ballWeight k c R x) := by ring
  have hintg : Integrable g volume := by
    exact hintp0.const_mul (M ^ (p - p₀))
  have hmono := MeasureTheory.integral_mono hintp hintg hpt
  have hconst : (∫ x : E k, g x) = M ^ (p - p₀) * (∫ x : E k, ‖f x‖ ^ p₀ * ballWeight k c R x) := by
    simpa [g] using (integral_const_mul (M ^ (p - p₀)) (fun x : E k => ‖f x‖ ^ p₀ * ballWeight k c R x))
  calc
    (∫ x : E k, ‖f x‖ ^ p * ballWeight k c R x) ≤ ∫ x : E k, g x := hmono
    _ = M ^ (p - p₀) * (∫ x : E k, ‖f x‖ ^ p₀ * ballWeight k c R x) := hconst

lemma lp_norm_reduction (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) {p p₀ : ℝ}
    (hp₀ : 0 < p₀) (hp₀p : p₀ ≤ p) (hp : 0 < p) {M : ℝ} (hM : 0 ≤ M) (f : E k → ℂ)
    (hb : ∀ x : E k, ‖f x‖ ≤ M)
    (hintp : Integrable (fun x : E k => ‖f x‖ ^ p * ballWeight k c R x) volume)
    (hintp0 : Integrable (fun x : E k => ‖f x‖ ^ p₀ * ballWeight k c R x) volume) :
    (wLpPow k c R p f) ^ (1 / p) ≤ M ^ (1 - p₀ / p) * (wLpPow k c R p₀ f) ^ (1 / p) := by
  have hdom := weighted_pow_dominate k c hR (le_of_lt hp₀) hp₀p hM f hb hintp hintp0
  have hw0 : ∀ q : ℝ, 0 ≤ wLpPow k c R q f := by
    intro q
    unfold wLpPow
    apply integral_nonneg
    intro x
    have hw : 0 ≤ ballWeight k c R x := le_of_lt (ballWeight_pos k c hR x)
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) q) hw
  have hw0p : 0 ≤ wLpPow k c R p f := hw0 p
  have hw0p0 : 0 ≤ wLpPow k c R p₀ f := hw0 p₀
  have h1p : 0 ≤ 1 / p := div_nonneg (by norm_num) (le_of_lt hp)
  have hmono : (wLpPow k c R p f) ^ (1 / p) ≤ (M ^ (p - p₀) * wLpPow k c R p₀ f) ^ (1 / p) :=
    Real.rpow_le_rpow hw0p hdom h1p
  have hb0 : 0 ≤ M ^ (p - p₀) := Real.rpow_nonneg hM _
  have hmain : (M ^ (p - p₀) * wLpPow k c R p₀ f) ^ (1 / p) =
      M ^ (1 - p₀ / p) * (wLpPow k c R p₀ f) ^ (1 / p) := by
    calc
      (M ^ (p - p₀) * wLpPow k c R p₀ f) ^ (1 / p)
          = (M ^ (p - p₀)) ^ (1 / p) * (wLpPow k c R p₀ f) ^ (1 / p) := Real.mul_rpow hb0 hw0p0
      _ = M ^ ((p - p₀) * (1 / p)) * (wLpPow k c R p₀ f) ^ (1 / p) := by
            congr 1
            rw [Real.rpow_mul hM (p - p₀) (1 / p)]
      _ = M ^ (1 - p₀ / p) * (wLpPow k c R p₀ f) ^ (1 / p) := by
            congr 1
            field_simp [hp.ne']
  exact le_trans hmono (le_of_eq hmain)

/-- **Ball-averaged Hölder/trivial-bound reduction**: the same reduction as
`lp_norm_reduction` for the BDG-normalised weighted powers
(`wLpPowAvg = wLpPow / |B_R|`).  By `(1/p)`-homogeneity it follows from
`lp_norm_reduction` by dividing both sides by `|B_R|^{1/p}`; this is the form
used to pass from the (normalised) critical `p₀` bound to general `p ≥ p₀` in
the proof of `bdg_discrete_restriction`. -/
lemma wLpAvg_reduction (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) (hvol : 0 < ballVol k c R)
    {p p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀p : p₀ ≤ p) (hp : 0 < p) {M : ℝ} (hM : 0 ≤ M)
    (f : E k → ℂ) (hb : ∀ x : E k, ‖f x‖ ≤ M)
    (hintp : Integrable (fun x : E k => ‖f x‖ ^ p * ballWeight k c R x) volume)
    (hintp0 : Integrable (fun x : E k => ‖f x‖ ^ p₀ * ballWeight k c R x) volume) :
    (wLpPowAvg k c R p f) ^ (1 / p) ≤ M ^ (1 - p₀ / p) * (wLpPowAvg k c R p₀ f) ^ (1 / p) := by
  have hred := lp_norm_reduction k c hR hp₀ hp₀p hp hM f hb hintp hintp0
  let v : ℝ := ballVol k c R
  have hvw : 0 ≤ v := le_of_lt hvol
  have hw0 (q : ℝ) : 0 ≤ wLpPow k c R q f := by
    unfold wLpPow
    apply integral_nonneg
    intro x
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) q) (le_of_lt (ballWeight_pos k c hR x))
  have hvp : 0 < v ^ (1 / p) := Real.rpow_pos_of_pos hvol (1 / p)
  have hvd : (wLpPow k c R p f) ^ (1 / p) / v ^ (1 / p) ≤
      (M ^ (1 - p₀ / p) * (wLpPow k c R p₀ f) ^ (1 / p)) / v ^ (1 / p) := by
    exact div_le_div_of_nonneg_right hred (le_of_lt hvp)
  have hstep1 : (wLpPow k c R p f) ^ (1 / p) / v ^ (1 / p) =
      (wLpPowAvg k c R p f) ^ (1 / p) := by
    unfold wLpPowAvg
    dsimp [v]
    rw [Real.div_rpow (hw0 p) hvw (1 / p)]
  have hstep2 : (M ^ (1 - p₀ / p) * (wLpPow k c R p₀ f) ^ (1 / p)) / v ^ (1 / p) =
      M ^ (1 - p₀ / p) * (wLpPowAvg k c R p₀ f) ^ (1 / p) := by
    unfold wLpPowAvg
    dsimp [v]
    calc
      M ^ (1 - p₀ / p) * (wLpPow k c R p₀ f) ^ (1 / p) / ballVol k c R ^ (1 / p)
          = M ^ (1 - p₀ / p) * (((wLpPow k c R p₀ f) ^ (1 / p)) / ballVol k c R ^ (1 / p)) := by ring
      _ = M ^ (1 - p₀ / p) * ((wLpPow k c R p₀ f / ballVol k c R) ^ (1 / p)) := by
            rw [Real.div_rpow (hw0 p₀) hvw (1 / p)]
  rw [hstep1, hstep2] at hvd
  exact hvd

/-! ## BDG Theorem 4.1 (discrete restriction) — the uniform target

Faithful form of BDG, "Proof of the main conjecture in Vinogradov's mean value
theorem for degrees higher than three", Ann. Math. 184 (2016), §"From
decouplings to exponential sums" (first theorem): for `N` separated points
`tᵢ ∈ ((i−1)/N, i/N]`, ball radius `R ≳ Nᵏ`, coefficients `aᵢ ∈ ℂ`, and
`p ≥ 2`,

    ((1/|B_R|) ∫ |Σᵢ aᵢ e(x·γ(tᵢ))|^p w_{B_R}(x) dx)^{1/p}
        ≤ C_ε · (N^ε + N^{½(1−k(k+1)/p)+ε}) · ‖a‖₂ ,        (uniform in N, R, a)

i.e. with the normalisation `1/|B_R|` of the paper.  **The normalisation is
essential**: a uniform-in-`N,R` bound for the unnormalised integral would be
false, since a single frequency `a = (1,0,…,0)` has
`(∫ |e(x·γ)|^p w_B)^{1/p} ≍ |B_R|^{1/p} ≥ c·N^{k²/p}`, which for `2 ≤ p ≤
k(k+1)` exceeds `‖a‖₂·N^{ε} = N^ε`.  The uniform target theorems below are
therefore stated for the averaged weighted power `wLpPowAvg` (`wLpPow` divided
by `ballVol`); the algebraic interpolation lemmas `weighted_pow_dominate`,
`lp_norm_reduction`, `dr41_high_bound` are recorded for the unnormalised
`wLpPow` — by `(1/p)`-homogeneity the same identities hold verbatim after
normalising by the positive constant `|B_R|`, and that averaged form is what
the proof of `bdg_discrete_restriction` uses.  The proof of BDG's theorem has
three ingredients, each isolated below:

  * the pointwise trivial bound `|Σᵢ aᵢ e(x·γ(tᵢ))| ≤ √N‖a‖₂`
    (`sepCharSum_trivial_bound`, proved here from `‖momChar‖ = 1` and
    `Commons.Analysis.Complex.abs_sum_unit_le_sqrt`);
  * the **critical case `p₀ = k(k+1)`** — the ℓ²-decoupling theorem for the
    moment curve (BDG Thm 1.2), the deep harmonic-analysis core.  It is *not*
    assumed here: the whole critical case is *derived* from BDG Thm 1.2 in the
    module `Submission.Vinogradov.DecouplingThm12`, which states Thm 1.2 as
    its single hypothesis and runs the discretisation argument
    (`g_τ → Σᵢ aᵢ e(x·γ(tᵢ))` as `τ → 0⁺`) on top of it;
  * the interpolation: for `p ≥ p₀`, Hölder + trivial `L∞` bound
    (`lp_norm_reduction` → `dr41_high_bound`: `‖f‖_{Lᵖ(w)} ≤ C‖a‖₂·
    N^{½(1−p₀/p)+ε·p₀/p}`); for `2 ≤ p ≤ p₀`, the weighted Hölder inequality
    `Commons.Measure.Integral.holder_pow_le_mul` together with the uniform
    weight-average bound `ballWeight_integral_ratio_bound`.

The uniform `bdg_discrete_restriction` (BDG Thm 4.1) and its critical case
`bdg_critical` live in the module `Submission.Vinogradov.DecouplingThm12`;
from there the whole of the Vinogradov mean value theorem is one more step
away, `bdg_Jsep` (BDG Cor. 4.2, discretised by the Schwartz-function
argument, done in `Submission.Vinogradov.Discretisation`) plus the assembly
`vmvt_of_Jsep_bound` (here).  See `ROADMAP.lean`. -/

/-- The exponential sum `Σᵢ aᵢ e(x·γ(tᵢ))` over the separated frequencies `tᵢ`. -/
def sepCharSum (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) (x : E k) : ℂ :=
  ∑ i : Fin N, a i * momChar k x (t i)

/-- The moment-curve character `momChar k x t = e(x·γ(t))` has modulus one. -/
lemma momChar_norm_one (k : ℕ) (x : E k) (t : ℝ) : ‖momChar k x t‖ = 1 := by
  unfold momChar
  let S : ℝ := ∑ j : Fin k, x j * t ^ (j.val + 1)
  have harg : ((2 * Real.pi : ℂ) * Complex.I) * (S : ℂ) =
      Complex.I * (((2 * Real.pi * S : ℝ) : ℂ)) := by
    norm_num [Complex.ofReal_mul]
    ring
  calc
    ‖Complex.exp (((2 * Real.pi : ℂ) * Complex.I) * (S : ℂ))‖
        = ‖Complex.exp (Complex.I * (((2 * Real.pi * S : ℝ) : ℂ)))‖ := by rw [harg]
    _ = 1 := by
      rw [Commons.Analysis.Complex.norm_exp_mul_I_ofReal (2 * Real.pi * S)]

/-- **Pointwise trivial bound** for the separated character sum:
`‖Σᵢ aᵢ e(x·γ(tᵢ))‖ ≤ √N · ‖a‖₂` (independent of `x`). -/
lemma sepCharSum_trivial_bound (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) :
    ∀ x : E k, ‖sepCharSum k a t x‖ ≤ Real.sqrt (N : ℝ) * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) := by
  intro x
  unfold sepCharSum
  calc
    ‖∑ i : Fin N, a i * momChar k x (t i)‖
        ≤ Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * Real.sqrt (N : ℝ) := by
          exact Commons.Analysis.Complex.abs_sum_unit_le_sqrt N a (fun i => momChar k x (t i))
            (by intro i; exact momChar_norm_one k x (t i))
    _ = Real.sqrt (N : ℝ) * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) := by ring

/-- The separated character sum is continuous in the extension variable `x`. -/
lemma sepCharSum_continuous (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) :
    Continuous (fun x : E k => sepCharSum k a t x) := by
  unfold sepCharSum momChar
  fun_prop

/-- The ball weight `w_B(x)` is continuous in `x`. -/
lemma ballWeight_continuous (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) :
    Continuous (fun x : E k => ballWeight k c R x) := by
  unfold ballWeight
  have hb : ∀ x : E k, 0 < 1 + ‖x - c‖ / R := by
    intro x
    positivity
  have hpow : Continuous (fun x : E k => (1 + ‖x - c‖ / R) ^ (100 * k)) := by
    fun_prop
  exact hpow.inv₀ (fun x => ne_of_gt (pow_pos (hb x) (100 * k)))

/-- The BDG ball weight `w_B(x) = (1 + ‖x−c‖/R)^{−100k}` is integrable on
`ℝᵏ` for `k ≥ 1`, `R > 0` (Commons: `ball_weight_integrable_expr`). -/
lemma ballWeight_integrable (k : ℕ) (hk : 1 ≤ k) (c : E k) {R : ℝ} (hR : 0 < R) :
    Integrable (fun x : E k => ballWeight k c R x) volume := by
  unfold ballWeight
  exact Commons.Analysis.Integral.ball_weight_integrable_expr k hk c hR

/-- The weighted `Lᵖ`-power integrand of the separated character sum is
integrable: for `p ≥ 0`, `x ↦ ‖f x‖^p · w_B(x)` with `f = sepCharSum k a t` is
integrable (trivial bound `|f| ≤ √N‖a‖₂` times the integrability of `w_B`;
this discharges the integrability side conditions `hintp₀`/`hintp` of
`lp_norm_reduction` in every uniform application). -/
lemma sepCharSum_wLp_integrable (k : ℕ) (hk : 1 ≤ k) {N : ℕ}
    (a : Fin N → ℂ) (t : Fin N → ℝ) {p : ℝ} (hp : 0 ≤ p) {R : ℝ} (hR : 0 < R)
    (c : E k) :
    Integrable (fun x : E k => ‖sepCharSum k a t x‖ ^ p * ballWeight k c R x) volume := by
  let f : E k → ℂ := sepCharSum k a t
  let M : ℝ := Real.sqrt (N : ℝ) * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2)
  have hM₀ : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hb : ∀ x : E k, ‖f x‖ ≤ M := by
    intro x
    dsimp [f, M]
    exact sepCharSum_trivial_bound k a t x
  have hMp : Integrable (fun x : E k => M ^ p * ballWeight k c R x) volume := by
    exact (ballWeight_integrable k hk c hR).const_mul (M ^ p)
  have hpt : ∀ x : E k, ‖f x‖ ^ p * ballWeight k c R x ≤ M ^ p * ballWeight k c R x := by
    intro x
    have hle : ‖f x‖ ^ p ≤ M ^ p := Real.rpow_le_rpow (norm_nonneg (f x)) (hb x) hp
    exact mul_le_mul_of_nonneg_right hle (le_of_lt (ballWeight_pos k c hR x))
  have hcNorm : Continuous (fun x : E k => ‖f x‖) := by
    dsimp [f]
    exact continuous_norm.comp (sepCharSum_continuous k a t)
  have hcPow : Continuous (fun x : E k => ‖f x‖ ^ p) := by
    exact hcNorm.rpow_const (fun x => Or.inr hp)
  have hcw : Continuous (fun x : E k => ballWeight k c R x) := ballWeight_continuous k c hR
  have hmeas : AEStronglyMeasurable
      (fun x : E k => ‖f x‖ ^ p * ballWeight k c R x) volume :=
    (hcPow.mul hcw).measurable.aestronglyMeasurable
  have hnn_ae : (∀ᵐ x ∂volume, 0 ≤ ‖f x‖ ^ p * ballWeight k c R x) := by
    filter_upwards with x
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) p) (le_of_lt (ballWeight_pos k c hR x))
  have hle_ae : (∀ᵐ x ∂volume, ‖f x‖ ^ p * ballWeight k c R x ≤ M ^ p * ballWeight k c R x) := by
    filter_upwards with x
    exact hpt x
  exact hMp.mono_nonneg hmeas hnn_ae hle_ae

/-! ## The normalised ball-weight integral (uniform in `R`, `c`)

For the `2 ≤ p ≤ p₀` half of BDG's discrete restriction theorem (see
`bdg_discrete_restriction`) one needs the uniform bound
`∫ w_B ≤ K · |B_R|`: the weight has bounded average over the ball, uniformly in
centre and radius.  We prove the *exact* scaling identities

    ∫_{ℝᵏ} w_{B(c,R)} = Rᵏ · ∫_{ℝᵏ} w_{B(0,1)} ,      |B(c,R)| = Rᵏ · |B(0,1)|,

by translation and dilation invariance of Lebesgue measure (`volume` on
`E k = EuclideanSpace ℝ (Fin k)` is additive Haar), and derive the ratio bound.
The proof is pure measure theory on the finite-dimensional real vector space
`E k` (Mathlib's `integral_comp_inv_smul_of_nonneg`, `map_add_left_eq_self`,
`addHaar_ball`). -/

/-- Volume of the ball scales as `Rᵏ`: `|B(c,R)| = Rᵏ·|B(0,1)|` (Lebesgue). -/
lemma ballVol_smul (k : ℕ) (hk : 1 ≤ k) (c : E k) {R : ℝ} (hR : 0 ≤ R) :
    ballVol k c R = R ^ k * ballVol k 0 1 := by
  haveI : Nontrivial (E k) := by
    haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
    infer_instance
  unfold ballVol
  have hfin : Module.finrank ℝ (E k) = k := by simp [finrank_euclideanSpace]
  calc
    (volume (Metric.ball c R)).toReal
        = (ENNReal.ofReal (R ^ k) * volume (Metric.ball (0 : E k) 1)).toReal := by
          rw [Measure.addHaar_ball (μ := (volume : Measure (E k))) c hR, hfin]
    _ = R ^ k * (volume (Metric.ball (0 : E k) 1)).toReal := by
          rw [ENNReal.toReal_ofReal_mul (R ^ k) _ (pow_nonneg hR k)]

/-- Lebesgue measure is translation invariant: `∫ x, f (a + x) = ∫ x, f x`. -/
lemma integral_translate (k : ℕ) (a : E k) (f : E k → ℝ) (hf : Continuous f) :
    (∫ x : E k, f (a + x)) = ∫ x : E k, f x := by
  let φ : E k → E k := fun x => a + x
  have hmeas : AEMeasurable φ (volume : Measure (E k)) := by
    dsimp [φ]
    exact (continuous_const.add continuous_id).aemeasurable
  have hmap : Measure.map φ (volume : Measure (E k)) = volume := by
    dsimp [φ]
    exact MeasureTheory.map_add_left_eq_self (μ := (volume : Measure (E k))) a
  have hsm : AEStronglyMeasurable f (Measure.map φ (volume : Measure (E k))) := by
    rw [hmap]
    exact hf.aestronglyMeasurable
  calc
    (∫ x : E k, f (a + x)) = ∫ y : E k, f y ∂Measure.map φ (volume : Measure (E k)) := by
      dsimp [φ]
      rw [MeasureTheory.integral_map hmeas hsm]
    _ = ∫ x : E k, f x := by
      rw [hmap]

/-- Pointwise translation: `w_{B(0,R)}(−c + x) = w_{B(c,R)}(x)`. -/
lemma ballWeight_translate (k : ℕ) (c : E k) (R : ℝ) (x : E k) :
    ballWeight k 0 R ((-c) + x) = ballWeight k c R x := by
  unfold ballWeight
  apply congrArg (fun t : ℝ => (t ^ (100 * k))⁻¹)
  apply congrArg (fun t : ℝ => 1 + t)
  have hsub : ‖(-c) + x - 0‖ / R = ‖x - c‖ / R := by
    congr 1
    have hv : (-c) + x - 0 = x - c := by abel
    rw [hv]
  exact hsub

/-- Pointwise scaling: `w_{B(0,R)}(u) = w_{B(0,1)}(R⁻¹·u)` for `R > 0`. -/
lemma ballWeight_smul_arg (k : ℕ) {R : ℝ} (hR : 0 < R) (u : E k) :
    ballWeight k 0 R u = ballWeight k 0 1 (R⁻¹ • u) := by
  unfold ballWeight
  apply congrArg (fun t : ℝ => (t ^ (100 * k))⁻¹)
  apply congrArg (fun t : ℝ => 1 + t)
  have hL : ‖u - 0‖ / R = ‖u‖ / R := by rw [sub_zero]
  have hR' : ‖R⁻¹ • u - 0‖ / (1 : ℝ) = ‖R⁻¹ • u‖ := by rw [sub_zero, div_one]
  have hnorm : ‖u‖ / R = ‖R⁻¹ • u‖ := by
    symm
    calc
      ‖R⁻¹ • u‖ = |R⁻¹| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = R⁻¹ * ‖u‖ := by rw [abs_of_nonneg (inv_nonneg.mpr (le_of_lt hR))]
      _ = ‖u‖ / R := by rw [div_eq_inv_mul]
  calc
    ‖u - 0‖ / R = ‖u‖ / R := hL
    _ = ‖R⁻¹ • u‖ := hnorm
    _ = ‖R⁻¹ • u - 0‖ / (1 : ℝ) := hR'.symm

/-- Scaling identity for the ball weight: `∫ w_{B(c,R)} = Rᵏ · ∫ w_{B(0,1)}`. -/
lemma ballWeight_integral_smul (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R) :
    (∫ x : E k, ballWeight k c R x) = R ^ k * (∫ y : E k, ballWeight k 0 1 y) := by
  have hcont : Continuous (fun u : E k => ballWeight k 0 R u) := ballWeight_continuous k 0 hR
  have h1 : (∫ x : E k, ballWeight k c R x) = ∫ u : E k, ballWeight k 0 R u := by
    calc
      (∫ x : E k, ballWeight k c R x) = ∫ x : E k, ballWeight k 0 R ((-c) + x) := by
        apply integral_congr_ae
        filter_upwards with x
        exact (ballWeight_translate k c R x).symm
      _ = ∫ u : E k, ballWeight k 0 R u := integral_translate k (-c) (fun u => ballWeight k 0 R u) hcont
  have h2 : (∫ u : E k, ballWeight k 0 R u) = R ^ k * (∫ y : E k, ballWeight k 0 1 y) := by
    let g : E k → ℝ := fun y => ballWeight k 0 1 y
    have hs : (∫ u : E k, ballWeight k 0 R u) = ∫ u : E k, g (R⁻¹ • u) := by
      apply integral_congr_ae
      filter_upwards with u
      exact ballWeight_smul_arg k hR u
    calc
      (∫ u : E k, ballWeight k 0 R u) = ∫ u : E k, g (R⁻¹ • u) := hs
      _ = R ^ k * ∫ y : E k, g y := by
        rw [MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure (E k))) g (le_of_lt hR)]
        simp [finrank_euclideanSpace]
  calc
    (∫ x : E k, ballWeight k c R x) = ∫ u : E k, ballWeight k 0 R u := h1
    _ = R ^ k * (∫ y : E k, ballWeight k 0 1 y) := h2

/-- The ball weight has positive unit-mass average: for `k ≥ 1` there is a
constant `K > 0` (independent of `c`, `R`) with `∫ w_{B(c,R)} ≤ K·|B(c,R)|`. -/
lemma ballWeight_integral_ratio_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : E k) {R : ℝ}, 0 < R →
      (∫ x : E k, ballWeight k c R x) ≤ K * ballVol k c R := by
  let I₀ : ℝ := ∫ y : E k, ballWeight k 0 1 y
  let V₀ : ℝ := ballVol k 0 1
  have hI₀ : 0 ≤ I₀ := by
    dsimp [I₀]
    exact integral_nonneg (fun y => le_of_lt (ballWeight_pos k 0 (by norm_num) y))
  have hV : 0 < V₀ := by
    dsimp [V₀]
    exact ballVol_pos k hk 0 (by norm_num)
  refine ⟨I₀ / V₀ + 1, ?_, ?_⟩
  · have hdiv : 0 ≤ I₀ / V₀ := div_nonneg hI₀ (le_of_lt hV)
    linarith
  · intro c R hR
    have hI : (∫ x : E k, ballWeight k c R x) = R ^ k * I₀ := by
      dsimp [I₀]
      exact ballWeight_integral_smul k c hR
    have hV' : ballVol k c R = R ^ k * V₀ := by
      dsimp [V₀]
      exact ballVol_smul k hk c (le_of_lt hR)
    rw [hI, hV']
    have hRk : 0 ≤ R ^ k := pow_nonneg (le_of_lt hR) k
    calc
      R ^ k * I₀ = (R ^ k * V₀) * (I₀ / V₀) := by
        rw [mul_assoc]
        congr 1
        field_simp [hV.ne']
      _ ≤ (R ^ k * V₀) * (I₀ / V₀ + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hRk (le_of_lt hV))
      _ = (I₀ / V₀ + 1) * (R ^ k * V₀) := by ring


/-! ## The uniform discrete restriction theorem (BDG Thm 4.1)

`bdg_discrete_restriction` (BDG's discrete restriction theorem, and its
critical case `bdg_critical` at `p₀ = k(k+1)`) is proved in the module
`Submission.Vinogradov.DecouplingThm12`, which derives it from BDG Thm 1.2
(the ℓ²-decoupling theorem for the moment curve).  The two routine halves of
that reduction use the tools proved *here*:

* `2 ≤ p ≤ p₀` (`bdg_low_half`): Hölder's inequality for the weighted measure
  `w_B dx` (`wLpAvg_low_half`, built on
  `Commons.Measure.Integral.holder_pow_le_mul`) together with the uniform
  weight-average bound `ballWeight_integral_ratio_bound`;
* `p₀ ≤ p` (`bdg_high_half`): the Hölder/trivial-bound reduction
  `dr41_avg_high_bound` (`wLpAvg_reduction` + `mul_rpow_interp_bound`). -/

/-- **Ball-averaged high-half bound** (`p₀ ≤ p`, uniform constant): from the
normalised critical bound at `p₀` and the pointwise trivial bound
`|f| ≤ M ≤ √N‖a‖₂`, one gets for `p ≥ p₀`

    (wLpPowAvg p)^{1/p} ≤ C₀^{p₀/p} · ‖a‖₂ · N^{½(1−p₀/p) + ε₀·(p₀/p)} .

Obtained from `wLpAvg_reduction` (the ball-averaged Hölder/trivial-bound
reduction) exactly as `dr41_high_bound` is obtained from `lp_norm_reduction`,
with the same real-algebra engine
`Commons.Analysis.Real.mul_rpow_interp_bound`.  This is the `p ≥ p₀` half of
BDG's discrete restriction theorem. -/
lemma dr41_avg_high_bound (k : ℕ) (_hk : 1 ≤ k) (c : E k) {R : ℝ} (hR : 0 < R)
    (hvol : 0 < ballVol k c R) {p p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀p : p₀ ≤ p)
    (hp : 0 < p) {N : ℕ} (_hN : 1 ≤ N) (a : Fin N → ℂ) (t : Fin N → ℝ)
    {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    (M : ℝ) (hM₀ : 0 ≤ M)
    (hMbound : ∀ x : E k, ‖sepCharSum k a t x‖ ≤ M)
    (hMle : M ≤ Real.sqrt (N : ℝ) * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2))
    (hintp₀ : Integrable (fun x : E k => ‖sepCharSum k a t x‖ ^ p₀ * ballWeight k c R x) volume)
    (hintp : Integrable (fun x : E k => ‖sepCharSum k a t x‖ ^ p * ballWeight k c R x) volume)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hcrit : (wLpPowAvg k c R p₀ (sepCharSum k a t)) ^ (1 / p₀) ≤
        C₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀) :
    (wLpPowAvg k c R p (sepCharSum k a t)) ^ (1 / p) ≤
        C₀ ^ (p₀ / p) * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^
          (((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀ * (p₀ / p)) := by
  let f : E k → ℂ := sepCharSum k a t
  let A : ℝ := ∑ i : Fin N, ‖a i‖ ^ 2
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖a i‖)
  have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hw0p0 : 0 ≤ wLpPowAvg k c R p₀ f := by
    unfold wLpPowAvg
    exact div_nonneg (by
      unfold wLpPow
      apply integral_nonneg
      intro x
      exact mul_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) p₀) (le_of_lt (ballWeight_pos k c hR x)))
      (le_of_lt hvol)
  have hcritpow : ((wLpPowAvg k c R p₀ f) ^ (1 / p₀)) ^ (p₀ / p) ≤
      (C₀ * Real.sqrt A * (N : ℝ) ^ ε₀) ^ (p₀ / p) := by
    have h₁ : 0 ≤ (wLpPowAvg k c R p₀ f) ^ (1 / p₀) := Real.rpow_nonneg hw0p0 (1 / p₀)
    have h₂ : 0 ≤ p₀ / p := div_nonneg (le_of_lt hp₀) (le_of_lt hp)
    exact Real.rpow_le_rpow h₁ hcrit h₂
  have hpowid : (wLpPowAvg k c R p₀ f) ^ (1 / p) =
      ((wLpPowAvg k c R p₀ f) ^ (1 / p₀)) ^ (p₀ / p) := by
    calc
      (wLpPowAvg k c R p₀ f) ^ (1 / p) = (wLpPowAvg k c R p₀ f) ^ ((1 / p₀) * (p₀ / p)) := by
        congr 1
        field_simp [hp₀.ne', hp.ne']
      _ = ((wLpPowAvg k c R p₀ f) ^ (1 / p₀)) ^ (p₀ / p) := by
        rw [Real.rpow_mul hw0p0 (1 / p₀) (p₀ / p)]
  have hcrit1 : (wLpPowAvg k c R p₀ f) ^ (1 / p) ≤ (C₀ * Real.sqrt A * (N : ℝ) ^ ε₀) ^ (p₀ / p) := by
    rw [hpowid]
    exact hcritpow
  have hred := wLpAvg_reduction k c hR hvol hp₀ hp₀p hp hM₀ f hMbound hintp hintp₀
  have hcomb : M ^ (1 - p₀ / p) * (wLpPowAvg k c R p₀ f) ^ (1 / p) ≤
      M ^ (1 - p₀ / p) * (C₀ * Real.sqrt A * (N : ℝ) ^ ε₀) ^ (p₀ / p) := by
    exact mul_le_mul_of_nonneg_left hcrit1 (Real.rpow_nonneg hM₀ (1 - p₀ / p))
  have hα : 0 ≤ 1 - p₀ / p := by
    have h : p₀ / p ≤ 1 := (div_le_one hp).mpr hp₀p
    linarith
  have hβ : 0 ≤ p₀ / p := div_nonneg (le_of_lt hp₀) (le_of_lt hp)
  have hαβ : (1 - p₀ / p) + p₀ / p = 1 := by ring
  have hmain := Commons.Analysis.Real.mul_rpow_interp_bound C₀ (N : ℝ) A M hC₀.le hN0 hA0 hM₀ ε₀ hε₀
      (1 - p₀ / p) (p₀ / p) hα hβ hαβ hMle
  have htrans : (wLpPowAvg k c R p f) ^ (1 / p) ≤
      C₀ ^ (p₀ / p) * Real.sqrt A * (N : ℝ) ^ ((1 - p₀ / p) / 2 + ε₀ * (p₀ / p)) := by
    calc
      (wLpPowAvg k c R p f) ^ (1 / p) ≤ M ^ (1 - p₀ / p) * (wLpPowAvg k c R p₀ f) ^ (1 / p) := hred
      _ ≤ M ^ (1 - p₀ / p) * (C₀ * Real.sqrt A * (N : ℝ) ^ ε₀) ^ (p₀ / p) := hcomb
      _ ≤ C₀ ^ (p₀ / p) * Real.sqrt A * (N : ℝ) ^ ((1 - p₀ / p) / 2 + ε₀ * (p₀ / p)) := hmain
  have hexp : (1 - p₀ / p) / 2 + ε₀ * (p₀ / p) =
      ((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀ * (p₀ / p) := by ring
  calc
    (wLpPowAvg k c R p f) ^ (1 / p)
        ≤ C₀ ^ (p₀ / p) * Real.sqrt A * (N : ℝ) ^ ((1 - p₀ / p) / 2 + ε₀ * (p₀ / p)) := htrans
    _ = C₀ ^ (p₀ / p) * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) *
          (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀ * (p₀ / p)) := by
      simp [A, hexp]



/-- Real-algebra engine for the low half: after substituting the critical power
`I₀ = A₀·v` and dividing the Hölder bound by `v^{1/p}`, the leftover exponent
arithmetic collapses to `A₀^{1/p₀}·(W/v)^{1/p−1/p₀}`. -/
lemma avg_low_algebra {p p₀ : ℝ} (hp : 0 < p) (hp₀ : 0 < p₀) (hpp₀ : p ≤ p₀)
    {A₀ I₀ W v : ℝ} (hA₀ : 0 ≤ A₀) (hI₀id : I₀ = A₀ * v)
    (hW : 0 ≤ W) (hv : 0 < v) :
    I₀ ^ (1 / p₀) * W ^ (1 / p - 1 / p₀) / v ^ (1 / p) =
      A₀ ^ (1 / p₀) * (W / v) ^ (1 / p - 1 / p₀) := by
  let e : ℝ := 1 / p - 1 / p₀
  have he_def : e = 1 / p - 1 / p₀ := rfl
  have hvle : 0 ≤ v := le_of_lt hv
  have hneg : 1 / p₀ - 1 / p = -e := by dsimp [e]; ring
  have hWv : W ^ e * v ^ (-e) = (W / v) ^ e := by
    rw [Real.rpow_neg hvle]
    rw [← div_eq_mul_inv]
    exact (Real.div_rpow hW hvle e).symm
  calc
    I₀ ^ (1 / p₀) * W ^ e / v ^ (1 / p)
        = (A₀ * v) ^ (1 / p₀) * W ^ e / v ^ (1 / p) := by rw [hI₀id]
    _ = A₀ ^ (1 / p₀) * v ^ (1 / p₀) * W ^ e / v ^ (1 / p) := by
          rw [Real.mul_rpow hA₀ hvle]
    _ = A₀ ^ (1 / p₀) * (W ^ e * (v ^ (1 / p₀) / v ^ (1 / p))) := by ring
    _ = A₀ ^ (1 / p₀) * (W ^ e * v ^ (1 / p₀ - 1 / p)) := by
          rw [Real.rpow_sub hv (1 / p₀) (1 / p)]
    _ = A₀ ^ (1 / p₀) * (W ^ e * v ^ (-e)) := by
          rw [hneg]
    _ = A₀ ^ (1 / p₀) * (W / v) ^ e := by
          rw [hWv]
    _ = A₀ ^ (1 / p₀) * (W / v) ^ (1 / p - 1 / p₀) := by rw [he_def]


/-- **Low half (`2 ≤ p ≤ p₀`)**: for `0 < p ≤ p₀`, the ball-averaged `Lᵖ`-power
of `f` is dominated by the ball-averaged critical `p₀`-power times the uniform
factor `((∫w_B)/|B_R|)^{1/p−1/p₀}`.  This is Hölder's inequality for the
weighted measure `w_B dx`
(`Commons.Measure.Integral.holder_pow_le_mul`) divided by `|B_R|^{1/p}`
(`avg_low_algebra`); with `ballWeight_integral_ratio_bound` the factor is
uniformly bounded in `R`, giving the `2 ≤ p ≤ p₀` half of BDG's discrete
restriction theorem from its critical case. -/
lemma wLpAvg_low_half (k : ℕ) (c : E k) {R : ℝ} (hR : 0 < R)
    (hvol : 0 < ballVol k c R)
    {p p₀ : ℝ} (hp₀ : 0 < p₀) (hp : 0 < p) (hpp₀ : p ≤ p₀)
    (f : E k → ℂ)
    (hfmeas : AEMeasurable f (volume : Measure (E k)))
    (hintp : Integrable (fun x : E k => ‖f x‖ ^ p * ballWeight k c R x) volume)
    (hintp₀ : Integrable (fun x : E k => ‖f x‖ ^ p₀ * ballWeight k c R x) volume)
    (hwint : Integrable (fun x : E k => ballWeight k c R x) volume) :
    (wLpPowAvg k c R p f) ^ (1 / p) ≤
      (wLpPowAvg k c R p₀ f) ^ (1 / p₀) *
        ((∫ x : E k, ballWeight k c R x) / ballVol k c R) ^ (1 / p - 1 / p₀) := by
  let v : ℝ := ballVol k c R
  let A₀ : ℝ := wLpPowAvg k c R p₀ f
  let I₀ : ℝ := wLpPow k c R p₀ f
  let W : ℝ := ∫ x : E k, ballWeight k c R x
  have hvw : 0 ≤ v := le_of_lt hvol
  have hW : 0 ≤ W := by
    dsimp [W]
    apply integral_nonneg
    intro x
    exact le_of_lt (ballWeight_pos k c hR x)
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀, v]
    unfold wLpPowAvg
    exact div_nonneg (by
      unfold wLpPow
      apply integral_nonneg
      intro x
      exact mul_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) p₀) (le_of_lt (ballWeight_pos k c hR x)))
      (le_of_lt hvol)
  have hI₀id : I₀ = A₀ * v := by
    dsimp [I₀, A₀, v]
    unfold wLpPowAvg
    field_simp [hvol.ne']
  have hIp : 0 ≤ wLpPow k c R p f := by
    unfold wLpPow
    apply integral_nonneg
    intro x
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) p) (le_of_lt (ballWeight_pos k c hR x))
  have hwmeas : AEMeasurable (fun x : E k => ballWeight k c R x) volume :=
    (ballWeight_continuous k c hR).aemeasurable
  have hwpos : ∀ x : E k, 0 ≤ ballWeight k c R x := fun x => le_of_lt (ballWeight_pos k c hR x)
  have hholder := Commons.Measure.Integral.holder_pow_le_mul (volume : Measure (E k)) hp hp₀ hpp₀ f
    (fun x => ballWeight k c R x) hwpos hfmeas hwmeas hintp hintp₀ hwint
  have hstep : (wLpPow k c R p f) ^ (1 / p) ≤ I₀ ^ (1 / p₀) * W ^ (1 / p - 1 / p₀) := by
    dsimp [I₀, W]
    exact hholder
  have hdiv : (wLpPowAvg k c R p f) ^ (1 / p) =
      (wLpPow k c R p f) ^ (1 / p) / v ^ (1 / p) := by
    dsimp [v]
    unfold wLpPowAvg
    rw [Real.div_rpow hIp hvw (1 / p)]
  have hdivle : (wLpPow k c R p f) ^ (1 / p) / v ^ (1 / p) ≤
      (I₀ ^ (1 / p₀) * W ^ (1 / p - 1 / p₀)) / v ^ (1 / p) := by
    exact div_le_div_of_nonneg_right hstep (le_of_lt (Real.rpow_pos_of_pos hvol (1 / p)))
  have hcomb := avg_low_algebra hp hp₀ hpp₀ hA₀ hI₀id hW hvol
  calc
    (wLpPowAvg k c R p f) ^ (1 / p)
        ≤ (I₀ ^ (1 / p₀) * W ^ (1 / p - 1 / p₀)) / v ^ (1 / p) := by
          rw [hdiv]
          exact hdivle
    _ = (wLpPowAvg k c R p₀ f) ^ (1 / p₀) *
          ((∫ x : E k, ballWeight k c R x) / ballVol k c R) ^ (1 / p - 1 / p₀) := by
          dsimp [v, A₀, W]
          exact hcomb


/-- **`p ≥ p₀` high-half reduction (uniform constant)**.  If the critical
`p₀`-bound holds for the separated character sum `f` and `|f| ≤ M ≤ √N‖a‖₂`
pointwise, then for `p₀ ≤ p`,

    ‖f‖_{Lᵖ(w)} ≤ C₀^{p₀/p} · ‖a‖₂ · N^{½(1−p₀/p) + ε₀·(p₀/p)} .

Obtained from `lp_norm_reduction` (Hölder + trivial `L∞` bound) by substituting
the critical bound and the trivial bound, with the constant `C₀^{p₀/p}`
independent of `N`, `R`, `a`, `t` — this is the uniform-constant form used
for the `p ≥ p₀` half of BDG's discrete restriction theorem.  Stated for the
unnormalised weighted integrals `wLpPow`; by `(1/p)`-homogeneity it transfers
verbatim to the BDG ball-averaged powers `wLpPowAvg` (see `wLpAvg_reduction`),
which is the form used together with a *normalised* critical bound in the proof
of `bdg_discrete_restriction`.  (Proof: pure real arithmetic,
`Commons.Analysis.Real.mul_rpow_interp_bound`; the integrability hypotheses
`hintp₀`/`hintp` are discharged in the application by boundedness of `f` and
integrability of `w_B`.) -/
lemma dr41_high_bound (k : ℕ) (_hk : 1 ≤ k) {p p₀ : ℝ} (hp₀ : 0 < p₀) (hp₀p : p₀ ≤ p)
    (hp : 0 < p) {N : ℕ} (_hN : 1 ≤ N) (a : Fin N → ℂ) (t : Fin N → ℝ)
    {R : ℝ} (hR : 0 < R) (c : E k) {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀)
    (M : ℝ) (hM₀ : 0 ≤ M)
    (hMbound : ∀ x : E k, ‖sepCharSum k a t x‖ ≤ M)
    (hMle : M ≤ Real.sqrt (N : ℝ) * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2))
    (hintp₀ : Integrable (fun x : E k => ‖sepCharSum k a t x‖ ^ p₀ * ballWeight k c R x) volume)
    (hintp : Integrable (fun x : E k => ‖sepCharSum k a t x‖ ^ p * ballWeight k c R x) volume)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hcrit : (wLpPow k c R p₀ (sepCharSum k a t)) ^ (1 / p₀) ≤
        C₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀) :
    (wLpPow k c R p (sepCharSum k a t)) ^ (1 / p) ≤
        C₀ ^ (p₀ / p) * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^
          (((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀ * (p₀ / p)) := by
  let f : E k → ℂ := sepCharSum k a t
  let A : ℝ := ∑ i : Fin N, ‖a i‖ ^ 2
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg ‖a i‖)
  have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hw0p0 : 0 ≤ wLpPow k c R p₀ f := by
    unfold wLpPow
    apply integral_nonneg
    intro x
    exact mul_nonneg (Real.rpow_nonneg (norm_nonneg (f x)) p₀) (le_of_lt (ballWeight_pos k c hR x))
  have hcritpow : ((wLpPow k c R p₀ f) ^ (1 / p₀)) ^ (p₀ / p) ≤
      (C₀ * Real.sqrt A * (N : ℝ) ^ ε₀) ^ (p₀ / p) := by
    have h₁ : 0 ≤ (wLpPow k c R p₀ f) ^ (1 / p₀) := Real.rpow_nonneg hw0p0 (1 / p₀)
    have h₂ : 0 ≤ p₀ / p := div_nonneg (le_of_lt hp₀) (le_of_lt hp)
    exact Real.rpow_le_rpow h₁ hcrit h₂
  have hpowid : (wLpPow k c R p₀ f) ^ (1 / p) =
      ((wLpPow k c R p₀ f) ^ (1 / p₀)) ^ (p₀ / p) := by
    calc
      (wLpPow k c R p₀ f) ^ (1 / p) = (wLpPow k c R p₀ f) ^ ((1 / p₀) * (p₀ / p)) := by
        congr 1
        field_simp [hp₀.ne', hp.ne']
      _ = ((wLpPow k c R p₀ f) ^ (1 / p₀)) ^ (p₀ / p) := by
        rw [Real.rpow_mul hw0p0 (1 / p₀) (p₀ / p)]
  have hcrit1 : (wLpPow k c R p₀ f) ^ (1 / p) ≤ (C₀ * Real.sqrt A * (N : ℝ) ^ ε₀) ^ (p₀ / p) := by
    rw [hpowid]
    exact hcritpow
  have hred := lp_norm_reduction k c hR hp₀ hp₀p hp hM₀ f hMbound hintp hintp₀
  have hcomb : M ^ (1 - p₀ / p) * (wLpPow k c R p₀ f) ^ (1 / p) ≤
      M ^ (1 - p₀ / p) * (C₀ * Real.sqrt A * (N : ℝ) ^ ε₀) ^ (p₀ / p) := by
    exact mul_le_mul_of_nonneg_left hcrit1 (Real.rpow_nonneg hM₀ (1 - p₀ / p))
  have hα : 0 ≤ 1 - p₀ / p := by
    have h : p₀ / p ≤ 1 := (div_le_one hp).mpr hp₀p
    linarith
  have hβ : 0 ≤ p₀ / p := div_nonneg (le_of_lt hp₀) (le_of_lt hp)
  have hαβ : (1 - p₀ / p) + p₀ / p = 1 := by ring
  have hε0 : 0 ≤ ε₀ := hε₀
  have hC0 : 0 ≤ C₀ := le_of_lt hC₀
  have hM0' : 0 ≤ M := hM₀
  have hmain := Commons.Analysis.Real.mul_rpow_interp_bound C₀ (N : ℝ) A M hC0 hN0 hA0 hM0' ε₀ hε0
      (1 - p₀ / p) (p₀ / p) hα hβ hαβ hMle
  have htrans : (wLpPow k c R p f) ^ (1 / p) ≤
      C₀ ^ (p₀ / p) * Real.sqrt A * (N : ℝ) ^ ((1 - p₀ / p) / 2 + ε₀ * (p₀ / p)) := by
    calc
      (wLpPow k c R p f) ^ (1 / p) ≤ M ^ (1 - p₀ / p) * (wLpPow k c R p₀ f) ^ (1 / p) := hred
      _ ≤ M ^ (1 - p₀ / p) * (C₀ * Real.sqrt A * (N : ℝ) ^ ε₀) ^ (p₀ / p) := hcomb
      _ ≤ C₀ ^ (p₀ / p) * Real.sqrt A * (N : ℝ) ^ ((1 - p₀ / p) / 2 + ε₀ * (p₀ / p)) := hmain
  have hexp : (1 - p₀ / p) / 2 + ε₀ * (p₀ / p) =
      ((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀ * (p₀ / p) := by ring
  calc
    (wLpPow k c R p f) ^ (1 / p)
        ≤ C₀ ^ (p₀ / p) * Real.sqrt A * (N : ℝ) ^ ((1 - p₀ / p) / 2 + ε₀ * (p₀ / p)) := htrans
    _ = C₀ ^ (p₀ / p) * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) *
          (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀ * (p₀ / p)) := by
      simp [A, hexp]/-! ## The discretisation bound (BDG Cor. 4.2, integer point set)

`bdg_Jsep_core` — the discretisation bound `Jsep ≤ C·rhs` in the regime
`1 ≤ s`, `1 ≤ k` — is PROVEN in `Discretisation.lean` (BDG Cor. 4.2 for the
integer point set `{1,…,X}`, via the Gaussian–Fourier/Schwartz argument from
the discrete restriction theorem `bdg_discrete_restriction`).  The assembly
below shows how the analytic inequality implies the mean value theorem. -/

/-- `bdg_Jsep` plus `J_le_Jsep` yields the eventual bound of `J` by the target
comparison function. -/
lemma vmvt_of_Jsep_bound (s k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hsep : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X → (Jsep s k X : ℝ) ≤ C * rhs s k ε X) :
    VMVT s k ε hε := by
  rcases hsep with ⟨C, hC, hb⟩
  apply vmvt_of_eventually_le_mul s k ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with X hX
  calc
    J s k X ≤ (Jsep s k X : ℝ) := J_le_Jsep s k X
    _ ≤ C * rhs s k ε X := hb X hX



/-! ## The cover/gluing step for `extended_decoupling`

The two uses of the uniform cover inequality `ballWeight_sum_cover_le_uniform`
in BDG's cover step (extending decoupling from radius-`Nᵏ` balls to all balls
of radius `R ≥ Nᵏ`) are instances of the following gluing lemma: a pointwise
cover inequality `Σ_i w_{B_i} ≤ C·w_B` transfers to the weighted `Lᵖ`-powers
(as `Σ_i wLpPow w_{B_i} ≤ C·wLpPow w_B`), by distributing the nonnegative
integrand over the finite sum and applying `integral_mono`. -/

/-- **Gluing lemma for the cover step**: a pointwise bound
`Σ_i w_{B(c_i,r)}(x) ≤ C·w_{B(c,R)}(x)` (all `x`) implies the corresponding
weighted-`Lᵖ`-power inequality `Σ_i wLpPow k (c_i) r p h ≤ C·wLpPow k c R p h`. -/
lemma wLpPow_sum_le_of_cover (k : ℕ) (c : E k) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    {ι : Type*} [Fintype ι] (c' : ι → E k) {C : ℝ} (hC : 0 < C)
    (hcover : ∀ x : E k, (∑ i : ι, ballWeight k (c' i) r x) ≤ C * ballWeight k c R x)
    {p : ℝ} (hp : 0 ≤ p) (h : E k → ℂ)
    (hint : ∀ i : ι, Integrable (fun x : E k => ‖h x‖ ^ p * ballWeight k (c' i) r x) volume)
    (hintR : Integrable (fun x : E k => ‖h x‖ ^ p * ballWeight k c R x) volume) :
    ∑ i : ι, wLpPow k (c' i) r p h ≤ C * wLpPow k c R p h := by
  -- Σ_i ∫ ‖h‖^p w_i = ∫ ‖h‖^p (Σ_i w_i)
  have hsum_eq : (∑ i : ι, wLpPow k (c' i) r p h)
      = ∫ x : E k, ‖h x‖ ^ p * (∑ i : ι, ballWeight k (c' i) r x) := by
    unfold wLpPow
    rw [← MeasureTheory.integral_finset_sum Finset.univ (fun i _hi => hint i)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [Finset.mul_sum]
  rw [hsum_eq]
  -- integrability of the two sides
  have hint_sum : Integrable (fun x : E k => ‖h x‖ ^ p * (∑ i : ι, ballWeight k (c' i) r x)) volume := by
    have : (fun x : E k => ‖h x‖ ^ p * (∑ i : ι, ballWeight k (c' i) r x))
        = fun x : E k => ∑ i : ι, ‖h x‖ ^ p * ballWeight k (c' i) r x := by
      funext x; rw [Finset.mul_sum]
    rw [this]
    exact integrable_finset_sum Finset.univ (fun i _hi => hint i)
  have hint_R : Integrable (fun x : E k => ‖h x‖ ^ p * (C * ballWeight k c R x)) volume := by
    have : (fun x : E k => ‖h x‖ ^ p * (C * ballWeight k c R x))
        = fun x : E k => C * (‖h x‖ ^ p * ballWeight k c R x) := by
      funext x; ring
    rw [this]
    exact hintR.const_mul C
  -- pointwise bound
  have hpt : (fun x : E k => ‖h x‖ ^ p * (∑ i : ι, ballWeight k (c' i) r x))
      ≤ fun x : E k => ‖h x‖ ^ p * (C * ballWeight k c R x) := by
    intro x
    have hw : 0 ≤ ‖h x‖ ^ p := Real.rpow_nonneg (norm_nonneg _) p
    exact mul_le_mul_of_nonneg_left (hcover x) hw
  have hmono := MeasureTheory.integral_mono hint_sum hint_R hpt
  refine le_trans hmono ?_
  -- ∫ ‖h‖^p (C w) = C ∫ ‖h‖^p w
  have : (∫ x : E k, ‖h x‖ ^ p * (C * ballWeight k c R x)) = C * wLpPow k c R p h := by
    unfold wLpPow
    rw [show (∫ x : E k, ‖h x‖ ^ p * (C * ballWeight k c R x))
        = ∫ x : E k, C * (‖h x‖ ^ p * ballWeight k c R x) from by
          apply MeasureTheory.integral_congr_ae; filter_upwards with x; ring]
    rw [MeasureTheory.integral_const_mul]
  exact le_of_eq this

end
end Submission.Vinogradov
