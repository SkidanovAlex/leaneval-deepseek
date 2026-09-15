import Submission.Vinogradov.Decoupling
import Submission.Vinogradov.Sec4Bootstrap
import Submission.Vinogradov.Extension
import Submission.Vinogradov.DecouplesBridge
import Submission.Commons.Analysis.Integral.intervalIntegral_indicator_Ioo
import Submission.Commons.Analysis.Integral.interval_avg_tendsto
import Submission.Commons.Analysis.Integral.interval_avg_left_tendsto
import Submission.Commons.Measure.Integral.intervalIntegral_indicator_Ioo_eq_zero
import Submission.Commons.Measure.Integral.integrable_const_mul_indicator_Ioo
import Submission.Commons.Measure.Integral.tendsto_integral_norm_rpow_mul

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Interval Topology
open LeanEval.NumberTheory.VinogradovMeanValue

set_option autoImplicit false

/-!
# The discrete restriction theorem from ℓ²-decoupling (BDG §4)

This module carries out BDG's passage *from decoupling to exponential sums*
(Bourgain–Demeter–Guth, *Proof of the main conjecture in Vinogradov's mean
value theorem for degrees higher than three*, Ann. of Math. 184 (2016), §4).

The single hypothesis is BDG's **Theorem 1.2** (`ntmain`): the ℓ²-decoupling
inequality for the truncated moment curve `γ(t) = (t, t², …, tᵏ)`,
`0 < t ≤ 1`, at `δ = 1/N` and ball radius `δ^{-k} = Nᵏ`, with the ball weight
`w_B` of `Decoupling.lean`:

    ‖E_{[0,1]} g‖_{L^{k(k+1)}(w_{B(c,Nᵏ)})}
      ≲_ε N^ε ( Σ_{i} ‖E_{((i)/N,(i+1)/N]} g‖²_{L^{k(k+1)}(w_{B(c,Nᵏ)})} )^{1/2} .

This is stated as `bdg_thm_ntmain` (the statement is the paper's Thm 1.2; for
`k = 1` it is the elementary almost-orthogonality of the frequency intervals,
and the paper's proof covers `k ≥ 2`).

From it we derive, in this file:

* `bdg_critical` — the **critical case** of BDG's discrete restriction
  theorem at `p₀ = k(k+1)` and radius `Nᵏ` (BDG Thm 4.1 at `p = k(k+1)`);
* `bdg_low_half` / `bdg_high_half` — the two routine halves reducing general
  `p ≥ 2` to the critical case (weighted Hölder `Commons.Measure.Integral.
  holder_pow_le_mul` + the uniform weight average
  `ballWeight_integral_ratio_bound`; Hölder/trivial-bound reduction
  `dr41_avg_high_bound` + `Commons.Analysis.Real.mul_rpow_interp_bound`);
* `bdg_discrete_restriction` — BDG Thm 4.1, for all `p ≥ 2`, in the
  ball-averaged form used by the rest of the project.

Note on the radius.  These statements are given for the *single* radius
`R = Nᵏ` (`δ = 1/N`, `δ^{-k} = Nᵏ`), which is exactly the radius used by the
discretisation bound `bdg_valSum_bound` in `Discretisation.lean` (`Xᵏ` with
`X = N`).  BDG state Thm 4.1 for all `R ≳ Nⁿ`; the passage from `R = Nᵏ` to
`R ≳ Nᵏ` is their finitely-overlapping cover argument (eq. (fek20) in the
paper, the machinery for which is `ballWeight_sum_cover_le[_uniform]` /
`wLpPow_sum_le_of_cover` in `Decoupling.lean`) and is not needed here.

## The proof of `bdg_critical` (BDG §4)

Apply the decoupling inequality to the **one-sided** step function

    g_τ = Σᵢ aᵢ · (1/τ) · 1_{(tᵢ-τ, tᵢ]}          (tᵢ ∈ ((i)/N, (i+1)/N] separated)

(`bumpFun`, `stepFun`) and let `τ → 0⁺`.  The one-sided bump is supported
inside its own `1/N`-cell, which makes the cell computations exact (no
boundary corrections at `tᵢ = (i+1)/N`):

* `extOp_stepFun_full`  : `E_{[0,1]} g_τ (x) = Σᵢ aᵢ (1/τ)∫_{tᵢ-τ}^{tᵢ} e(x·γ)`;
* `extOp_stepFun_cell`  : `E_{((i)/N,(i+1)/N]} g_τ (x) = aᵢ (1/τ)∫_{tᵢ-τ}^{tᵢ} e(x·γ)`;
* `extOp_stepFun_full_tendsto` / `extOp_stepFun_cell_tendsto`: these tend
  pointwise to `sepCharSum k a t` / `aᵢ e(x·γ(tᵢ))` as `τ → 0⁺`;
* `wLpPow_tendsto_real` (dominated convergence, uniform bound `Σᵢ‖aᵢ‖`)
  passes the weighted `L^{p₀}` norms to the limit.

Taking `τ → 0⁺` in the decoupling inequality and normalising by the ball
volume (`ballWeight_integral_ratio_bound`, `Real.div_rpow`) gives the
critical bound. -/

namespace Submission.Vinogradov

/-- **The enlarged GLYZ ℓ²-decoupling theorem.**

This is Guo–Li–Yung–Zorin-Kranich, *A short proof of ℓ² decoupling for the moment curve*
(arXiv:1912.09798), Theorem 1.1, in the formulation used by the reduction
`bdg_thm_ntmain_of_decLinScale` below: at every scale `N`, with the plate of each piece
enlarged by the factor `λ = 2`, ℓ²-decoupling holds with an `N^ε` loss.

It is the end product of the §4 exponent bootstrap: `Sec4Bootstrap.etaLin_nonpos` shows that the
decoupling exponent `etaLin k` of GLYZ §4 is `≤ 0` (strong induction on `k`, with the base case
`k = 1` from the `L²` orthogonality of the line, `L2BaseCase.etaLin_one_le_zero`), and
`Section4Exp.exists_decLinScale_of_etaLin_nonpos` converts that into the ε-form below. -/
theorem glyz_decoupling (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N →
      DecLinScale k N 2 (ENNReal.ofReal (K * (N : ℝ) ^ ε)) :=
  exists_decLinScale_of_etaLin_nonpos hk (etaLin_nonpos k hk) hε

/-- **BDG Theorem 1.2** (`ntmain`), the ℓ²-decoupling theorem for the truncated
moment curve, in the form used for the discrete restriction theorem.

For `k ≥ 1`, every `ε > 0` there is `C > 0` such that for all `N ≥ 1`, every
centre `c ∈ ℝᵏ` and every measurable integrable `g : ℝ → ℂ`,

    ‖E_{[0,1]} g‖_{L^{k(k+1)}(w_{B(c,Nᵏ)})}
      ≤ C · N^ε · ( Σ_{i<N} ‖E_{((i)/N,(i+1)/N]} g‖²_{L^{k(k+1)}(w_{B(c,Nᵏ)})} )^{1/2} ,

where `E_J g(x) = ∫_J g(t) e(x·γ(t)) dt` (`extOp`) and `w_{B(c,Nᵏ)}` is the
ball weight `ballWeight` of radius `Nᵏ` (this is BDG Thm 1.2 with `δ = 1/N`,
noting `δ^{-k} = Nᵏ`; the paper's implicit constant is independent of `δ, B, g`). -/
theorem bdg_thm_ntmain (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : E k, ∀ g : ℝ → ℂ, Measurable g →
      Integrable g volume →
      (wLpPow k c ((N : ℝ) ^ k) ((k : ℝ) * ((k : ℝ) + 1)) (extOp k g 0 1))
          ^ (1 / ((k : ℝ) * ((k : ℝ) + 1)))
        ≤ C * (N : ℝ) ^ ε *
          (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) ((k : ℝ) * ((k : ℝ) + 1))
              (extOp k g (((i : ℕ) : ℝ) / (N : ℝ)) ((((i : ℕ) : ℝ) + 1) / (N : ℝ))))
                ^ (2 / ((k : ℝ) * ((k : ℝ) + 1)))) ^ ((1 : ℝ) / 2) := by
  obtain ⟨K, hK, hD⟩ := glyz_decoupling k hk ε hε
  exact bdg_thm_ntmain_of_decLinScale k hk ε hε hK hD

/-! ## The step-function discretisation family

The one-sided bump `(1/τ)·1_{(t−τ,t)}` and the step function
`g_τ = Σᵢ aᵢ·(1/τ)·1_{(tᵢ−τ,tᵢ)}` whose extension operator, as `τ → 0⁺`,
converges to the separated character sum `Σᵢ aᵢ e(x·γ(tᵢ))`.  The one-sided
form is chosen so that each bump is *supported inside its own cell*
`((i−1)/N, i/N]` of the `1/N`-partition (BDG apply decoupling to the symmetric
bump `1_{(tᵢ−τ,tᵢ+τ)}` and let `τ → 0`; the one-sided bump makes the boundary
case `tᵢ = i/N` harmless and the cell computations exact). -/

/-- The one-sided bump `u ↦ (1/τ)·1_{(t−τ,t)}(u)` (real inverse cast). -/
def bumpFun (t τ : ℝ) : ℝ → ℂ :=
  fun u => ((1 / τ : ℝ) : ℂ) * Set.indicator (Set.Ioo (t - τ) t) (fun _ : ℝ => (1 : ℂ)) u

/-- The step function `g_τ = Σᵢ aᵢ·bumpFun (tᵢ) τ`. -/
def stepFun {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) (τ : ℝ) : ℝ → ℂ :=
  fun u => ∑ i : Fin N, a i * bumpFun (t i) τ u

/-- The bump is measurable. -/
lemma measurable_bumpFun (t τ : ℝ) : Measurable (bumpFun t τ) := by
  unfold bumpFun
  exact measurable_const.mul (Measurable.indicator measurable_const measurableSet_Ioo)

/-- The step function is measurable. -/
lemma measurable_stepFun {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) (τ : ℝ) :
    Measurable (stepFun a t τ) := by
  unfold stepFun
  exact Finset.measurable_sum Finset.univ (fun i _ => (measurable_const.mul (measurable_bumpFun _ _)))

/-- A cell integral of a bump against the character: for `a ≤ t − τ` and `t ≤ b`,
`∫_a^b (1/τ)1_{(t−τ,t)}·e(x·γ) = (1/τ)·∫_{t−τ}^{t} e(x·γ)`. -/
lemma intervalIntegral_bumpFun_mul (k : ℕ) (x : E k) {t τ a b : ℝ}
    (hτ : 0 ≤ τ) (h1 : a ≤ t - τ) (h2 : t ≤ b) :
    (∫ u in a..b, bumpFun t τ u * momChar k x u)
      = ((1 / τ : ℝ) : ℂ) * ∫ u in (t - τ)..t, momChar k x u := by
  have hpq : t - τ ≤ t := by linarith
  have hconst : (∫ u in a..b, bumpFun t τ u * momChar k x u)
      = ((1 / τ : ℝ) : ℂ) * (∫ u in a..b,
          Set.indicator (Set.Ioo (t - τ) t) (fun _ : ℝ => (1 : ℂ)) u * momChar k x u) := by
    unfold bumpFun
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _hu
    ring
  rw [hconst, Commons.Analysis.Integral.intervalIntegral_indicator_Ioo h1 hpq h2
      ((momChar_continuous_t k x).intervalIntegrable a b)]

/-- The extension of the step function over `[0,1]`, for `τ > 0` with all bumps
inside `[0,1]`, is the finite sum of the per-bump interval averages of the
character. -/
lemma extOp_stepFun_full (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (hlo : ∀ i, τ ≤ t i) (hhi : ∀ i, t i ≤ 1) (x : E k) :
    extOp k (stepFun a t τ) 0 1 x
      = ∑ i : Fin N, a i * (((1 / τ : ℝ) : ℂ) * ∫ u in (t i - τ)..t i, momChar k x u) := by
  have hpt : ∀ u : ℝ, stepFun a t τ u * momChar k x u
      = ∑ i : Fin N, a i * (bumpFun (t i) τ u * momChar k x u) := by
    intro u
    unfold stepFun
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hint : ∀ i : Fin N, IntervalIntegrable
      (fun u : ℝ => a i * (bumpFun (t i) τ u * momChar k x u)) volume 0 1 := by
    intro i
    have h := Commons.Analysis.Integral.intervalIntegrable_indicator_mul_continuous
      (f := momChar k x) (momChar_continuous_t k x) (a i * ((1 / τ : ℝ) : ℂ))
      (a := 0) (b := 1) (p := t i - τ) (q := t i)
    simpa [bumpFun, mul_assoc] using h
  unfold extOp
  rw [show (fun u : ℝ => stepFun a t τ u * momChar k x u)
        = (fun u : ℝ => ∑ i : Fin N, a i * (bumpFun (t i) τ u * momChar k x u)) from
      funext hpt]
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun i _ => hint i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact intervalIntegral_bumpFun_mul k x (le_of_lt hτ) (by linarith [hlo i]) (hhi i)

/-- The extension of the step function over the cell `(i/N, (i+1)/N]` equals the
`i`-th bump average alone (the other bumps are supported outside the cell,
using one-sidedness of the bumps and the separation `tᵢ ∈ (i/N, (i+1)/N]`). -/
lemma extOp_stepFun_cell (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (hN : 1 ≤ N) (hsep : Separated N t)
    (hτs : ∀ i : Fin N, τ ≤ t i - (((i : ℕ) : ℝ) / (N : ℝ)))
    (i : Fin N) (x : E k) :
    extOp k (stepFun a t τ) (((i : ℕ) : ℝ) / (N : ℝ)) ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) x
      = a i * (((1 / τ : ℝ) : ℂ) * ∫ u in (t i - τ)..t i, momChar k x u) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hpt : ∀ u : ℝ, stepFun a t τ u * momChar k x u
      = ∑ j : Fin N, a j * (bumpFun (t j) τ u * momChar k x u) := by
    intro u
    unfold stepFun
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hint : ∀ j : Fin N, IntervalIntegrable
      (fun u : ℝ => a j * (bumpFun (t j) τ u * momChar k x u)) volume
        (((i : ℕ) : ℝ) / (N : ℝ)) ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) := by
    intro j
    have h := Commons.Analysis.Integral.intervalIntegrable_indicator_mul_continuous
      (f := momChar k x) (momChar_continuous_t k x) (a j * ((1 / τ : ℝ) : ℂ))
      (a := ((i : ℕ) : ℝ) / (N : ℝ)) (b := (((i : ℕ) : ℝ) + 1) / (N : ℝ))
      (p := t j - τ) (q := t j)
    simpa [bumpFun, mul_assoc] using h
  unfold extOp
  rw [show (fun u : ℝ => stepFun a t τ u * momChar k x u)
        = (fun u : ℝ => ∑ j : Fin N, a j * (bumpFun (t j) τ u * momChar k x u)) from
      funext hpt]
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun j _ => hint j)]
  have hzero : ∀ j : Fin N, j ≠ i →
      (∫ u in (((i : ℕ) : ℝ) / (N : ℝ))..((((i : ℕ) : ℝ) + 1) / (N : ℝ)),
          a j * (bumpFun (t j) τ u * momChar k x u)) = 0 := by
    intro j hj
    rw [intervalIntegral.integral_const_mul]
    have hdisj : ∀ u ∈ Set.uIcc (((i : ℕ) : ℝ) / (N : ℝ)) ((((i : ℕ) : ℝ) + 1) / (N : ℝ)),
        u ∉ Set.Ioo (t j - τ) (t j) := by
      intro u hu huIoo
      rw [Set.uIcc_of_le (by
        have : ((i : ℕ) : ℝ) ≤ (((i : ℕ) : ℝ) + 1) := by linarith
        exact div_le_div_of_nonneg_right this (le_of_lt hNpos))] at hu
      have hjsep := hsep j
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · -- j < i
        have hji : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by
          have : (j : ℕ) + 1 ≤ (i : ℕ) := by
            have := Fin.lt_def.mp hlt
            omega
          exact_mod_cast this
        have htj : t j ≤ ((i : ℕ) : ℝ) / (N : ℝ) := by
          calc t j ≤ (((j : ℕ) : ℝ) + 1) / (N : ℝ) := hjsep.2
            _ = (((j : ℕ) : ℝ) + 1) / (N : ℝ) := rfl
            _ ≤ ((i : ℕ) : ℝ) / (N : ℝ) := div_le_div_of_nonneg_right hji (le_of_lt hNpos)
        linarith [hu.1, huIoo.2, htj]
      · -- j > i
        have hji : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
          have : (i : ℕ) + 1 ≤ (j : ℕ) := by
            have := Fin.lt_def.mp hgt
            omega
          exact_mod_cast this
        have htj : (((i : ℕ) : ℝ) + 1) / (N : ℝ) ≤ t j - τ := by
          have h1 : τ ≤ t j - ((j : ℕ) : ℝ) / (N : ℝ) := hτs j
          have h2 : (((i : ℕ) : ℝ) + 1) / (N : ℝ) ≤ ((j : ℕ) : ℝ) / (N : ℝ) :=
            div_le_div_of_nonneg_right hji (le_of_lt hNpos)
          linarith
        linarith [hu.2, huIoo.1, htj]
    have h := Commons.Measure.Integral.intervalIntegral_indicator_Ioo_eq_zero
      (f := momChar k x) (a := ((i : ℕ) : ℝ) / (N : ℝ)) (b := (((i : ℕ) : ℝ) + 1) / (N : ℝ))
      (p := t j - τ) (q := t j) hdisj
    -- h : ∫ indicator * momChar = 0 ; relate to bumpFun
    have hrew : (∫ u in (((i : ℕ) : ℝ) / (N : ℝ))..((((i : ℕ) : ℝ) + 1) / (N : ℝ)),
        bumpFun (t j) τ u * momChar k x u)
        = ((1 / τ : ℝ) : ℂ) * (∫ u in (((i : ℕ) : ℝ) / (N : ℝ))..((((i : ℕ) : ℝ) + 1) / (N : ℝ)),
            Set.indicator (Set.Ioo (t j - τ) (t j)) (fun _ : ℝ => (1 : ℂ)) u * momChar k x u) := by
      unfold bumpFun
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u _hu
      ring
    rw [hrew, h]
    simp
  rw [Finset.sum_eq_single i]
  · rw [intervalIntegral.integral_const_mul]
    congr 1
    exact intervalIntegral_bumpFun_mul k x (le_of_lt hτ)
      (by have := (hsep i).1; have := hτs i; linarith) (hsep i).2
  · intro j _ hj
    exact hzero j hj
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Basic consequences of the separation condition: `0 < tᵢ ≤ 1` and the
lower bound `(i/N) ≤ tᵢ`. -/
lemma sep_pos {N : ℕ} {t : Fin N → ℝ} (hsep : Separated N t) (i : Fin N) : 0 < t i := by
  have h := (hsep i).1
  have h2 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) / (N : ℝ) := by positivity
  linarith

lemma sep_le_one {N : ℕ} {t : Fin N → ℝ} (hsep : Separated N t) (hN : 1 ≤ N) (i : Fin N) :
    t i ≤ 1 := by
  have h := (hsep i).2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hi : (((i : ℕ) : ℝ) + 1) ≤ (N : ℝ) := by
    have : (i : ℕ) + 1 ≤ N := by have := i.2; omega
    exact_mod_cast this
  calc t i ≤ (((i : ℕ) : ℝ) + 1) / (N : ℝ) := h
    _ ≤ (N : ℝ) / (N : ℝ) := div_le_div_of_nonneg_right hi (le_of_lt hNpos)
    _ = 1 := div_self (ne_of_gt hNpos)

/-- The separation bound `τ ≤ tᵢ − i/N` holds eventually at `0⁺`. -/
lemma eventually_tau_le_sep {N : ℕ} (t : Fin N → ℝ) (hsep : Separated N t) :
    ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < τ ∧ ∀ i : Fin N, τ ≤ t i - (((i : ℕ) : ℝ) / (N : ℝ)) := by
  have h1 : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < τ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ using hτ
  have h2 : ∀ i : Fin N, ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      τ ≤ t i - (((i : ℕ) : ℝ) / (N : ℝ)) := by
    intro i
    have hpos : 0 < t i - (((i : ℕ) : ℝ) / (N : ℝ)) := by
      have h := (hsep i).1
      linarith
    filter_upwards [Ioo_mem_nhdsGT hpos] with τ hτ
    exact le_of_lt (Set.mem_Ioo.mp hτ).2
  filter_upwards [h1, Filter.eventually_all.mpr h2] with τ hτ0 hτi
  exact ⟨hτ0, hτi⟩

/-- Pointwise convergence of the extension of the step function to the
separated character sum. -/
lemma extOp_stepFun_full_tendsto (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ)
    (hN : 1 ≤ N) (hsep : Separated N t) (x : E k) :
    Filter.Tendsto (fun τ : ℝ => extOp k (stepFun a t τ) 0 1 x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sepCharSum k a t x)) := by
  have hev := eventually_tau_le_sep t hsep
  have hlim : Filter.Tendsto
      (fun τ : ℝ => ∑ i : Fin N, a i * (((1 / τ : ℝ) : ℂ) *
        ∫ u in (t i - τ)..t i, momChar k x u))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∑ i : Fin N, a i * momChar k x (t i))) := by
    refine tendsto_finsetSum Finset.univ (fun i _ => ?_)
    have h := Commons.Analysis.Integral.interval_avg_left_tendsto (momChar k x)
      (momChar_continuous_t k x) (t i)
    have h' : Filter.Tendsto (fun τ : ℝ => (((1 / τ : ℝ)) : ℂ) *
        ∫ u in (t i - τ)..t i, momChar k x u)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (momChar k x (t i))) := by
      simpa [Algebra.smul_def] using h
    exact h'.const_mul (a i)
  have heq : (fun τ : ℝ => ∑ i : Fin N, a i * (((1 / τ : ℝ) : ℂ) *
        ∫ u in (t i - τ)..t i, momChar k x u))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun τ : ℝ => extOp k (stepFun a t τ) 0 1 x) := by
    filter_upwards [hev] with τ hτ
    refine (extOp_stepFun_full k a t hτ.1 ?_ ?_ x).symm
    · intro i
      have h := hτ.2 i
      have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) / (N : ℝ) := by positivity
      linarith
    · intro i
      exact sep_le_one hsep hN i
  exact Filter.Tendsto.congr' heq (by simpa [sepCharSum] using hlim)

/-- Pointwise convergence of the extension of the step function over the cell
`(i/N, (i+1)/N]` to the `i`-th character. -/
lemma extOp_stepFun_cell_tendsto (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ)
    (hN : 1 ≤ N) (hsep : Separated N t) (i : Fin N) (x : E k) :
    Filter.Tendsto
      (fun τ : ℝ => extOp k (stepFun a t τ) (((i : ℕ) : ℝ) / (N : ℝ)) ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (a i * momChar k x (t i))) := by
  have hev := eventually_tau_le_sep t hsep
  have hlim : Filter.Tendsto
      (fun τ : ℝ => a i * (((1 / τ : ℝ) : ℂ) * ∫ u in (t i - τ)..t i, momChar k x u))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (a i * momChar k x (t i))) := by
    have h := Commons.Analysis.Integral.interval_avg_left_tendsto (momChar k x)
      (momChar_continuous_t k x) (t i)
    have h' : Filter.Tendsto (fun τ : ℝ => (((1 / τ : ℝ)) : ℂ) *
        ∫ u in (t i - τ)..t i, momChar k x u)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (momChar k x (t i))) := by
      simpa [Algebra.smul_def] using h
    exact h'.const_mul (a i)
  have heq : (fun τ : ℝ => a i * (((1 / τ : ℝ) : ℂ) *
        ∫ u in (t i - τ)..t i, momChar k x u))
      =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun τ : ℝ => extOp k (stepFun a t τ) (((i : ℕ) : ℝ) / (N : ℝ))
          ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) x) := by
    filter_upwards [hev] with τ hτ
    exact (extOp_stepFun_cell k a t hτ.1 hN hsep hτ.2 i x).symm
  exact Filter.Tendsto.congr' heq hlim


/-- Continuity in `x` of the extension of the step function over `[0,1]`. -/
lemma continuous_extOp_stepFun_full (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (hlo : ∀ i, τ ≤ t i) (hhi : ∀ i, t i ≤ 1) :
    Continuous (fun x : E k => extOp k (stepFun a t τ) 0 1 x) := by
  rw [show (fun x : E k => extOp k (stepFun a t τ) 0 1 x)
      = fun x : E k => ∑ i : Fin N,
          a i * (((1 / τ : ℝ) : ℂ) * ∫ u in (t i - τ)..t i, momChar k x u) from
    funext (fun x => extOp_stepFun_full k a t hτ hlo hhi x)]
  refine continuous_finsetSum Finset.univ (fun i _ => ?_)
  have h1 : Continuous (fun x : E k => ∫ u in (t i - τ)..t i, momChar k x u) :=
    intervalIntegral_momChar_continuous k (by linarith [hlo i])
  exact (h1.const_mul (((1 / τ : ℝ)) : ℂ)).const_mul (a i)

/-- Continuity in `x` of the extension of the step function over the cell. -/
lemma continuous_extOp_stepFun_cell (k : ℕ) {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (hN : 1 ≤ N) (hsep : Separated N t)
    (hτs : ∀ i, τ ≤ t i - (((i : ℕ) : ℝ) / (N : ℝ))) (i : Fin N) :
    Continuous (fun x : E k => extOp k (stepFun a t τ) (((i : ℕ) : ℝ) / (N : ℝ))
      ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) x) := by
  rw [show (fun x : E k => extOp k (stepFun a t τ) (((i : ℕ) : ℝ) / (N : ℝ))
        ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) x)
      = fun x : E k => a i * (((1 / τ : ℝ) : ℂ) * ∫ u in (t i - τ)..t i, momChar k x u) from
    funext (fun x => extOp_stepFun_cell k a t hτ hN hsep hτs i x)]
  have h1 : Continuous (fun x : E k => ∫ u in (t i - τ)..t i, momChar k x u) :=
    intervalIntegral_momChar_continuous k (by linarith [hτs i])
  exact (h1.const_mul (((1 / τ : ℝ)) : ℂ)).const_mul (a i)

/-- **Dominated-convergence lemma for `wLpPow` (real exponent).**  If `F τ → f`
pointwise, `F τ` is eventually continuous and uniformly bounded by `M ≥ 0`, and
`p > 0`, then the weighted `Lᵖ` powers converge. -/
lemma wLpPow_tendsto_real (k : ℕ) (hk : 1 ≤ k) {R : ℝ} (hR : 0 < R) (c : E k)
    {p : ℝ} (hp : 0 < p)
    {F : ℝ → E k → ℂ} {f : E k → ℂ} {M : ℝ} (_hM0 : 0 ≤ M)
    (hcont : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0), Continuous (F τ))
    (hbdd : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ x, ‖F τ x‖ ≤ M)
    (hlim : ∀ x : E k, Filter.Tendsto (fun τ : ℝ => F τ x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x))) :
    Filter.Tendsto (fun τ : ℝ => wLpPow k c R p (F τ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (wLpPow k c R p f)) := by
  simpa [wLpPow] using Commons.Measure.Integral.tendsto_integral_norm_rpow_mul
    (volume : Measure (E k)) _hM0 hp (ballWeight_integrable k hk c hR)
    (Filter.Eventually.of_forall (fun x => le_of_lt (ballWeight_pos k c hR x)))
    (by filter_upwards [hcont] with τ hτ; exact hτ.aemeasurable)
    (by filter_upwards [hbdd] with τ hτ; filter_upwards with x; exact hτ x)
    (by filter_upwards with x; exact hlim x)

/-- The step function is integrable. -/
lemma integrable_stepFun {N : ℕ} (a : Fin N → ℂ) (t : Fin N → ℝ) (τ : ℝ) :
    Integrable (stepFun a t τ) volume := by
  unfold stepFun
  refine MeasureTheory.integrable_finsetSum (s := Finset.univ) (fun i _ => ?_)
  simpa [bumpFun, mul_assoc] using
    Commons.Measure.Integral.integrable_const_mul_indicator_Ioo (a i * ((1 / τ : ℝ) : ℂ)) (t i - τ) (t i)

/-- The normalised one-sided average of the character has modulus at most one. -/
lemma abs_inv_mul_intervalIntegral_momChar_le_one (k : ℕ) (x : E k) {τ t : ℝ} (hτ : 0 < τ) :
    ‖(((1 / τ : ℝ)) : ℂ) * ∫ u in (t - τ)..t, momChar k x u‖ ≤ 1 := by
  rw [norm_mul]
  have hc : ‖(((1 / τ : ℝ)) : ℂ)‖ = 1 / τ := by
    rw [norm_ofReal_complex, abs_of_nonneg (by positivity)]
  have hint : ‖∫ u in (t - τ)..t, momChar k x u‖ ≤ τ := by
    have h1 := norm_intervalIntegral_momChar_le k x (t - τ) t (by linarith)
    linarith
  rw [hc]
  calc (1 / τ) * ‖∫ u in (t - τ)..t, momChar k x u‖ ≤ (1 / τ) * τ :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = 1 := by field_simp

/-- **Critical case `p₀ = k(k+1)` of the discrete restriction theorem** at the
sharp radius `R = Nᵏ` (BDG Thm 4.1 at `p = k(k+1)`, radius `Nᵏ`).

Proved from BDG Thm 1.2 (`bdg_thm_ntmain`) by applying the ℓ²-decoupling
inequality to the one-sided step function
`g_τ = Σᵢ aᵢ·(1/τ)·1_{(tᵢ−τ,tᵢ)}` and passing to the limit `τ → 0⁺`: the
extension `E_{[0,1]}g_τ` tends pointwise to the separated character sum
`Σᵢ aᵢ e(x·γ(tᵢ))`, each cell extension `E_{((i−1)/N,i/N]}g_τ` tends to
`aᵢ e(x·γ(tᵢ))`, and the domination `‖E_J g_τ‖ ≤ Σᵢ‖aᵢ‖` allows the weighted
`L^{p₀}` norms to pass to the limit (`wLpPow_tendsto_real`).  The final
normalisation uses `∫ w_B ≤ K·|B|` (`ballWeight_integral_ratio_bound`). -/
theorem bdg_critical (k : ℕ) (hk : 1 ≤ k) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (t : Fin N → ℝ), Separated N t → ∀ a : Fin N → ℂ,
        ∀ c : E k,
          (wLpPowAvg k c ((N : ℝ) ^ k) ((k : ℝ) * ((k : ℝ) + 1)) (sepCharSum k a t))
              ^ (1 / ((k : ℝ) * ((k : ℝ) + 1)))
            ≤ C₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀ := by
  let p₀ : ℝ := (k : ℝ) * ((k : ℝ) + 1)
  have hp₀ : 0 < p₀ := by dsimp [p₀]; positivity
  have h1p₀ : 0 < 1 / p₀ := by positivity
  have h2p₀ : 0 < 2 / p₀ := by positivity
  rcases bdg_thm_ntmain k hk ε₀ hε₀ with ⟨C, hC, hdec⟩
  rcases ballWeight_integral_ratio_bound k hk with ⟨K, hK, hKle⟩
  refine ⟨C * K ^ (1 / p₀), by positivity, ?_⟩
  intro N hN t hsep a c
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hR : 0 < (N : ℝ) ^ k := pow_pos hN0 k
  have hvol : 0 < ballVol k c ((N : ℝ) ^ k) := ballVol_pos k hk c hR
  have hW0 : 0 ≤ ∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x :=
    integral_nonneg (fun x => le_of_lt (ballWeight_pos k c hR x))
  have hs : 0 ≤ ∑ i : Fin N, ‖a i‖ ^ 2 := Finset.sum_nonneg (fun i _ => by positivity)
  have hA0 : 0 ≤ wLpPow k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t) := by
    unfold wLpPow
    exact integral_nonneg (fun x => mul_nonneg
      (Real.rpow_nonneg (norm_nonneg _) p₀) (le_of_lt (ballWeight_pos k c hR x)))
  -- the decoupling inequality, for every `τ`
  have hdecτ : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (wLpPow k c ((N : ℝ) ^ k) p₀ (fun x : E k => extOp k (stepFun a t τ) 0 1 x))
          ^ (1 / p₀)
        ≤ C * (N : ℝ) ^ ε₀ *
          (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) p₀
              (fun x : E k => extOp k (stepFun a t τ) (((i : ℕ) : ℝ) / (N : ℝ))
                ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) x)) ^ (2 / p₀)) ^ ((1 : ℝ) / 2) := by
    filter_upwards with τ
    have h := hdec N hN c (stepFun a t τ) (measurable_stepFun a t τ) (integrable_stepFun a t τ)
    simpa [p₀] using h
  -- the two eventual regularity statements for the left-hand side
  have hcont_full : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      Continuous (fun x : E k => extOp k (stepFun a t τ) 0 1 x) := by
    filter_upwards [eventually_tau_le_sep t hsep] with τ hτ
    refine continuous_extOp_stepFun_full k a t hτ.1 ?_ ?_
    · intro i
      have h := hτ.2 i
      have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) / (N : ℝ) := by positivity
      linarith
    · intro i
      exact sep_le_one hsep hN i
  have hbdd_full : ∀ᶠ τ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ x : E k, ‖extOp k (stepFun a t τ) 0 1 x‖ ≤ ∑ i : Fin N, ‖a i‖ := by
    filter_upwards [eventually_tau_le_sep t hsep] with τ hτ
    intro x
    have hlo : ∀ i : Fin N, τ ≤ t i := by
      intro i
      have h := hτ.2 i
      have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) / (N : ℝ) := by positivity
      linarith
    rw [extOp_stepFun_full k a t hτ.1 hlo (fun i => sep_le_one hsep hN i) x]
    calc ‖∑ i : Fin N, a i * (((1 / τ : ℝ) : ℂ) *
            ∫ u in (t i - τ)..t i, momChar k x u)‖
        ≤ ∑ i : Fin N, ‖a i * (((1 / τ : ℝ) : ℂ) *
            ∫ u in (t i - τ)..t i, momChar k x u)‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin N, ‖a i‖ := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [norm_mul]
          calc ‖a i‖ * ‖(((1 / τ : ℝ)) : ℂ) * ∫ u in (t i - τ)..t i, momChar k x u‖
              ≤ ‖a i‖ * 1 := mul_le_mul_of_nonneg_left
                  (abs_inv_mul_intervalIntegral_momChar_le_one k x hτ.1) (norm_nonneg _)
            _ = ‖a i‖ := mul_one _
  -- left-hand side limit
  have hLlim : Tendsto (fun τ : ℝ => wLpPow k c ((N : ℝ) ^ k) p₀
      (fun x : E k => extOp k (stepFun a t τ) 0 1 x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (wLpPow k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t))) :=
    wLpPow_tendsto_real k hk hR c hp₀ (Finset.sum_nonneg (fun i _ => norm_nonneg _))
      hcont_full hbdd_full
      (fun x => extOp_stepFun_full_tendsto k a t hN hsep x)
  have hA : Tendsto (fun τ : ℝ => (wLpPow k c ((N : ℝ) ^ k) p₀
        (fun x : E k => extOp k (stepFun a t τ) 0 1 x)) ^ (1 / p₀))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((wLpPow k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t)) ^ (1 / p₀))) :=
    ((Real.continuous_rpow_const (le_of_lt h1p₀)).continuousAt.tendsto).comp hLlim
  -- right-hand side limits, cell by cell
  have hcell : ∀ i : Fin N, Tendsto (fun τ : ℝ => wLpPow k c ((N : ℝ) ^ k) p₀
      (fun x : E k => extOp k (stepFun a t τ) (((i : ℕ) : ℝ) / (N : ℝ))
        ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) x))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (wLpPow k c ((N : ℝ) ^ k) p₀ (fun x : E k => a i * momChar k x (t i)))) := by
    intro i
    refine wLpPow_tendsto_real k hk hR c hp₀ (norm_nonneg (a i)) ?_ ?_ ?_
    · filter_upwards [eventually_tau_le_sep t hsep] with τ hτ
      exact continuous_extOp_stepFun_cell k a t hτ.1 hN hsep hτ.2 i
    · filter_upwards [eventually_tau_le_sep t hsep] with τ hτ
      intro x
      rw [extOp_stepFun_cell k a t hτ.1 hN hsep hτ.2 i x, norm_mul]
      calc ‖a i‖ * ‖(((1 / τ : ℝ)) : ℂ) * ∫ u in (t i - τ)..t i, momChar k x u‖
          ≤ ‖a i‖ * 1 := mul_le_mul_of_nonneg_left
              (abs_inv_mul_intervalIntegral_momChar_le_one k x hτ.1) (norm_nonneg _)
        _ = ‖a i‖ := mul_one _
    · intro x
      exact extOp_stepFun_cell_tendsto k a t hN hsep i x
  have hsum : Tendsto (fun τ : ℝ => ∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) p₀
        (fun x : E k => extOp k (stepFun a t τ) (((i : ℕ) : ℝ) / (N : ℝ))
          ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) x)) ^ (2 / p₀))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) p₀
        (fun x : E k => a i * momChar k x (t i))) ^ (2 / p₀))) := by
    refine tendsto_finsetSum Finset.univ (fun i _ => ?_)
    exact ((Real.continuous_rpow_const (le_of_lt h2p₀)).continuousAt.tendsto).comp (hcell i)
  have hB : Tendsto (fun τ : ℝ => C * (N : ℝ) ^ ε₀ *
        (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) p₀
          (fun x : E k => extOp k (stepFun a t τ) (((i : ℕ) : ℝ) / (N : ℝ))
            ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) x)) ^ (2 / p₀)) ^ ((1 : ℝ) / 2))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (C * (N : ℝ) ^ ε₀ *
        (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) p₀
          (fun x : E k => a i * momChar k x (t i))) ^ (2 / p₀)) ^ ((1 : ℝ) / 2))) := by
    have hsqrt : Tendsto (fun τ : ℝ => (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) p₀
          (fun x : E k => extOp k (stepFun a t τ) (((i : ℕ) : ℝ) / (N : ℝ))
            ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) x)) ^ (2 / p₀)) ^ ((1 : ℝ) / 2))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) p₀
          (fun x : E k => a i * momChar k x (t i))) ^ (2 / p₀)) ^ ((1 : ℝ) / 2))) :=
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).continuousAt.tendsto).comp hsum
    have h2 := hsqrt.const_mul (C * (N : ℝ) ^ ε₀)
    simpa [mul_assoc] using h2
  -- take the limit of the inequality
  have hineq : (wLpPow k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t)) ^ (1 / p₀)
      ≤ C * (N : ℝ) ^ ε₀ *
        (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) p₀
          (fun x : E k => a i * momChar k x (t i))) ^ (2 / p₀)) ^ ((1 : ℝ) / 2) :=
    le_of_tendsto_of_tendsto hA hB hdecτ
  -- evaluate the cell powers
  have hcellval : ∀ i : Fin N,
      wLpPow k c ((N : ℝ) ^ k) p₀ (fun x : E k => a i * momChar k x (t i))
        = ‖a i‖ ^ p₀ * (∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x) := by
    intro i
    unfold wLpPow
    have hcongr : (fun x : E k => ‖a i * momChar k x (t i)‖ ^ p₀ * ballWeight k c ((N : ℝ) ^ k) x)
        = fun x : E k => ‖a i‖ ^ p₀ * ballWeight k c ((N : ℝ) ^ k) x := by
      funext x
      rw [norm_mul, momChar_norm_one, mul_one]
    rw [hcongr, integral_const_mul]
  have hterm : ∀ i : Fin N,
      (wLpPow k c ((N : ℝ) ^ k) p₀ (fun x : E k => a i * momChar k x (t i))) ^ (2 / p₀)
        = ‖a i‖ ^ 2 * (∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x) ^ (2 / p₀) := by
    intro i
    have hexp : p₀ * (2 / p₀) = 2 := by rw [mul_comm, div_mul_cancel₀ 2 (ne_of_gt hp₀)]
    rw [hcellval i, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg (a i)) p₀) hW0,
      ← Real.rpow_mul (norm_nonneg (a i)), hexp]
    rw [Real.rpow_ofNat]
  have hsumval : (∑ i : Fin N, (wLpPow k c ((N : ℝ) ^ k) p₀
        (fun x : E k => a i * momChar k x (t i))) ^ (2 / p₀))
      = (∑ i : Fin N, ‖a i‖ ^ 2) * (∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x) ^ (2 / p₀) := by
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_mul]
  have hineq' : (wLpPow k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t)) ^ (1 / p₀)
      ≤ C * (N : ℝ) ^ ε₀ * (Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) *
          (∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x) ^ (1 / p₀)) := by
    rw [hsumval] at hineq
    have hsqrt : ((∑ i : Fin N, ‖a i‖ ^ 2) *
        (∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x) ^ (2 / p₀)) ^ ((1 : ℝ) / 2)
        = Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) *
          (∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x) ^ (1 / p₀) := by
      rw [Real.mul_rpow (z := (1 : ℝ) / 2) hs (Real.rpow_nonneg hW0 (2 / p₀)),
        ← Real.rpow_mul hW0 (2 / p₀) (1 / 2)]
      rw [show (2 / p₀) * (1 / 2) = 1 / p₀ by ring_nf]
      rw [Real.sqrt_eq_rpow]
    rw [hsqrt] at hineq
    exact hineq
  -- divide by the ball volume and normalise
  have hdiv : (wLpPowAvg k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t)) ^ (1 / p₀)
      = (wLpPow k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t)) ^ (1 / p₀)
          / (ballVol k c ((N : ℝ) ^ k)) ^ (1 / p₀) := by
    unfold wLpPowAvg
    rw [Real.div_rpow hA0 (le_of_lt hvol)]
  have hWK : (∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x) / ballVol k c ((N : ℝ) ^ k) ≤ K :=
    (div_le_iff₀ hvol).mpr (hKle c hR)
  have hmain : (wLpPowAvg k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t)) ^ (1 / p₀)
      ≤ C * (N : ℝ) ^ ε₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * K ^ (1 / p₀) := by
    rw [hdiv]
    calc (wLpPow k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t)) ^ (1 / p₀)
            / (ballVol k c ((N : ℝ) ^ k)) ^ (1 / p₀)
        ≤ (C * (N : ℝ) ^ ε₀ * (Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) *
              (∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x) ^ (1 / p₀)))
            / (ballVol k c ((N : ℝ) ^ k)) ^ (1 / p₀) :=
          div_le_div_of_nonneg_right hineq' (Real.rpow_nonneg (le_of_lt hvol) _)
      _ = C * (N : ℝ) ^ ε₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) *
            ((∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x) / ballVol k c ((N : ℝ) ^ k)) ^ (1 / p₀) := by
          rw [Real.div_rpow hW0 (le_of_lt hvol)]
          ring
      _ ≤ C * (N : ℝ) ^ ε₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * K ^ (1 / p₀) := by
          gcongr
  calc (wLpPowAvg k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t)) ^ (1 / p₀)
      ≤ C * (N : ℝ) ^ ε₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * K ^ (1 / p₀) := hmain
    _ = C * K ^ (1 / p₀) * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀ := by ring

/-- **Low half** (`2 ≤ p ≤ p₀`) of the discrete restriction theorem: from the
critical bound and the uniform weight-average bound it follows with constant
`max C₀ 1 * max K 1` and power `N^{ε₀}`. -/
lemma bdg_low_half (k : ℕ) (hk : 1 ≤ k) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (t : Fin N → ℝ), Separated N t → ∀ a : Fin N → ℂ,
        ∀ c : E k,
          ∀ p : ℝ, 2 ≤ p → p ≤ ((k : ℝ) * ((k : ℝ) + 1)) →
            (wLpPowAvg k c ((N : ℝ) ^ k) p (sepCharSum k a t)) ^ (1 / p) ≤
              C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀ := by
  let p₀ : ℝ := (k : ℝ) * ((k : ℝ) + 1)
  have hp₀ : 0 < p₀ := by
    dsimp [p₀]
    positivity
  rcases ballWeight_integral_ratio_bound k hk with ⟨K, hK, hKle⟩
  rcases bdg_critical k hk ε₀ hε₀ with ⟨C₀, hC₀, hcrit⟩
  let C : ℝ := max C₀ 1 * max K 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N hN t hsep a c p hp2 hple
  have hR : 0 < (N : ℝ) ^ k := pow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) k
  have hcritN := hcrit N hN t hsep a c
  have hintp (q : ℝ) (hq0 : 0 ≤ q) :
      Integrable (fun x : E k => ‖sepCharSum k a t x‖ ^ q * ballWeight k c ((N : ℝ) ^ k) x) volume :=
    sepCharSum_wLp_integrable k hk a t hq0 hR c
  have hwint : Integrable (fun x : E k => ballWeight k c ((N : ℝ) ^ k) x) volume :=
    ballWeight_integrable k hk c hR
  have hfmeas : AEMeasurable (sepCharSum k a t) (volume : Measure (E k)) :=
    (sepCharSum_continuous k a t).aemeasurable
  have hpp : 0 < p := by linarith
  have hlow := wLpAvg_low_half k c hR (ballVol_pos k hk c hR) hp₀ hpp hple
      (sepCharSum k a t) hfmeas (hintp p (by linarith)) (hintp p₀ (le_of_lt hp₀)) hwint
  -- factor: ((∫w)/ballVol)^{1/p−1/p₀} ≤ max K 1
  let W : ℝ := ∫ x : E k, ballWeight k c ((N : ℝ) ^ k) x
  let v : ℝ := ballVol k c ((N : ℝ) ^ k)
  have hW0 : 0 ≤ W := by
    dsimp [W]
    apply integral_nonneg
    intro x
    exact le_of_lt (ballWeight_pos k c hR x)
  have hv : 0 < v := by
    dsimp [v]
    exact ballVol_pos k hk c hR
  have hKle' : W / v ≤ K := by
    have h := hKle c hR
    dsimp [W, v] at h ⊢
    exact (div_le_iff₀ hv).mpr h
  have hWv0 : 0 ≤ W / v := div_nonneg hW0 (le_of_lt hv)
  have ha0 : 0 ≤ 1 / p - 1 / p₀ := by
    have h₁ : (1 : ℝ) / p₀ ≤ 1 / p := one_div_le_one_div_of_le hpp hple
    linarith
  have ha12 : 1 / p - 1 / p₀ ≤ (1 / 2 : ℝ) := by
    have h₁ : 1 / p ≤ (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
    have h₂ : 0 ≤ 1 / p₀ := by positivity
    linarith
  have hfac0 : ∀ {x : ℝ}, 0 ≤ x → x ≤ K → x ^ (1 / p - 1 / p₀) ≤ max K 1 := by
    intro x hx0 hxK
    have h1 : x ^ (1 / p - 1 / p₀) ≤ K ^ (1 / p - 1 / p₀) := Real.rpow_le_rpow hx0 hxK ha0
    by_cases hKge : 1 ≤ K
    · have h2 : K ^ (1 / p - 1 / p₀) ≤ K ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hKge ha12
      have h3 : K ^ (1 / 2 : ℝ) ≤ K ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hKge (by norm_num : (1 / 2 : ℝ) ≤ 1)
      have h4 : K ^ (1 : ℝ) = K := Real.rpow_one K
      have h5 : K ≤ max K 1 := le_max_left K 1
      calc
        x ^ (1 / p - 1 / p₀) ≤ K ^ (1 / p - 1 / p₀) := h1
        _ ≤ K ^ (1 / 2 : ℝ) := h2
        _ ≤ K ^ (1 : ℝ) := h3
        _ = K := h4
        _ ≤ max K 1 := h5
    · have hKle1 : K ≤ 1 := le_of_not_ge hKge
      have h6 : K ^ (1 / p - 1 / p₀) ≤ (1 : ℝ) ^ (1 / p - 1 / p₀) :=
        Real.rpow_le_rpow (le_of_lt hK) hKle1 ha0
      have h7 : (1 : ℝ) ^ (1 / p - 1 / p₀) = 1 := Real.one_rpow _
      have h8 : (1 : ℝ) ≤ max K 1 := le_max_right K 1
      calc
        x ^ (1 / p - 1 / p₀) ≤ K ^ (1 / p - 1 / p₀) := h1
        _ ≤ (1 : ℝ) ^ (1 / p - 1 / p₀) := h6
        _ = 1 := h7
        _ ≤ max K 1 := h8
  have hfac := hfac0 hWv0 hKle'
  have hwavg : (wLpPowAvg k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t)) ^ (1 / p₀) ≤
      C₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀ := by
    simpa [p₀] using hcritN
  have hfac0nn : 0 ≤ (W / v) ^ (1 / p - 1 / p₀) := Real.rpow_nonneg hWv0 _
  have hwavg0 : 0 ≤ C₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀ := by
    positivity
  have hlow' : (wLpPowAvg k c ((N : ℝ) ^ k) p (sepCharSum k a t)) ^ (1 / p) ≤
      (C₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀) * max K 1 := by
    calc
      (wLpPowAvg k c ((N : ℝ) ^ k) p (sepCharSum k a t)) ^ (1 / p)
          ≤ (wLpPowAvg k c ((N : ℝ) ^ k) p₀ (sepCharSum k a t)) ^ (1 / p₀) * (W / v) ^ (1 / p - 1 / p₀) := hlow
      _ ≤ (C₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀) * max K 1 :=
            mul_le_mul hwavg hfac hfac0nn hwavg0
  have hfact : 0 ≤ Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀ := by
    positivity
  have hprod : C₀ * max K 1 ≤ max C₀ 1 * max K 1 := by
    exact mul_le_mul (le_max_left C₀ 1) le_rfl (le_trans (le_of_lt hK) (le_max_left K 1))
      (le_trans (le_of_lt hC₀) (le_max_left C₀ 1))
  have hasm : (C₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀) * max K 1
      ≤ C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀ := by
    calc
      (C₀ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀) * max K 1
          = (C₀ * max K 1) * (Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀) := by ring
      _ ≤ (max C₀ 1 * max K 1) * (Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀) := by
            exact mul_le_mul_of_nonneg_right hprod hfact
      _ = C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε₀ := by
            dsimp [C]
            ring
  exact le_trans hlow' hasm


/-- **High half** (`p₀ ≤ p`) of the discrete restriction theorem: from the
critical bound and the trivial bound, with constant `max C₀ 1` and power
`N^{½(1−p₀/p)+ε₀}` (via `dr41_avg_high_bound`). -/
lemma bdg_high_half (k : ℕ) (hk : 1 ≤ k) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (t : Fin N → ℝ), Separated N t → ∀ a : Fin N → ℂ,
        ∀ c : E k,
          ∀ p : ℝ, 2 ≤ p → ((k : ℝ) * ((k : ℝ) + 1)) ≤ p →
            (wLpPowAvg k c ((N : ℝ) ^ k) p (sepCharSum k a t)) ^ (1 / p) ≤
              C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) *
                (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - ((k : ℝ) * ((k : ℝ) + 1)) / p) + ε₀) := by
  let p₀ : ℝ := (k : ℝ) * ((k : ℝ) + 1)
  have hp₀ : 0 < p₀ := by
    dsimp [p₀]
    positivity
  rcases bdg_critical k hk ε₀ hε₀ with ⟨C₀, hC₀, hcrit⟩
  let C : ℝ := max C₀ 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N hN t hsep a c p hp2 hp₀p
  have hR : 0 < (N : ℝ) ^ k := pow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) k
  have hcritN := hcrit N hN t hsep a c
  have hintp (q : ℝ) (hq0 : 0 ≤ q) :
      Integrable (fun x : E k => ‖sepCharSum k a t x‖ ^ q * ballWeight k c ((N : ℝ) ^ k) x) volume :=
    sepCharSum_wLp_integrable k hk a t hq0 hR c
  have hpp : 0 < p := by linarith
  let A : ℝ := ∑ i : Fin N, ‖a i‖ ^ 2
  have hM : 0 ≤ Real.sqrt (N : ℝ) * Real.sqrt A := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hMbound : ∀ x : E k, ‖sepCharSum k a t x‖ ≤ Real.sqrt (N : ℝ) * Real.sqrt A := by
    intro x
    dsimp [A]
    simpa [mul_comm] using sepCharSum_trivial_bound k a t x
  have hMle : Real.sqrt (N : ℝ) * Real.sqrt A ≤
      Real.sqrt (N : ℝ) * Real.sqrt A := le_rfl
  have hdr := dr41_avg_high_bound k hk c hR (ballVol_pos k hk c hR) hp₀ hp₀p hpp hN a t (le_of_lt hε₀)
    (Real.sqrt (N : ℝ) * Real.sqrt A) hM hMbound hMle
    (hintp p₀ (le_of_lt hp₀)) (hintp p (by linarith)) C₀ hC₀
    (by simpa [A, p₀] using hcritN)
  -- exponent: ½(1−p₀/p) + ε₀·(p₀/p) ≤ ½(1−p₀/p) + ε₀  (N ≥ 1)
  have h1 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have h1N : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hα0 : 0 ≤ (1 : ℝ) / 2 * (1 - p₀ / p) := by
    have hp₀p1 : p₀ / p ≤ 1 := (div_le_one hpp).mpr hp₀p
    nlinarith
  have hβle : ε₀ * (p₀ / p) ≤ ε₀ := by
    have hpp0 : p₀ / p ≤ 1 := (div_le_one hpp).mpr hp₀p
    have hε₀nn : 0 ≤ ε₀ := le_of_lt hε₀
    nlinarith
  have hexp_le : (1 : ℝ) / 2 * (1 - p₀ / p) + ε₀ * (p₀ / p) ≤
      (1 : ℝ) / 2 * (1 - p₀ / p) + ε₀ := by linarith
  have hpow_le : (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀ * (p₀ / p)) ≤
      (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀) :=
    Real.rpow_le_rpow_of_exponent_le h1N hexp_le
  have hC0pow : C₀ ^ (p₀ / p) ≤ max C₀ 1 := by
    have h01 : 0 ≤ p₀ / p := div_nonneg (le_of_lt hp₀) (le_of_lt hpp)
    have h11 : p₀ / p ≤ 1 := (div_le_one hpp).mpr hp₀p
    by_cases hCge : 1 ≤ C₀
    · have h1a : C₀ ^ (p₀ / p) ≤ C₀ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hCge h11
      rw [Real.rpow_one C₀] at h1a
      exact le_trans h1a (le_max_left C₀ 1)
    · have hC0pos : 0 < C₀ := hC₀
      have hCle1 : C₀ ≤ 1 := le_of_not_ge hCge
      have h2a : C₀ ^ (p₀ / p) ≤ (1 : ℝ) ^ (p₀ / p) := Real.rpow_le_rpow (le_of_lt hC0pos) hCle1 h01
      rw [Real.one_rpow] at h2a
      exact le_trans h2a (le_max_right C₀ 1)
  have hsqrt : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  have hdr' : (wLpPowAvg k c ((N : ℝ) ^ k) p (sepCharSum k a t)) ^ (1 / p) ≤
      max C₀ 1 * Real.sqrt A * (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀) := by
    calc
      (wLpPowAvg k c ((N : ℝ) ^ k) p (sepCharSum k a t)) ^ (1 / p)
          ≤ C₀ ^ (p₀ / p) * Real.sqrt A *
              (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀ * (p₀ / p)) := by
            simpa [A, p₀] using hdr
      _ ≤ max C₀ 1 * Real.sqrt A * (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε₀) := by
            gcongr
  simpa [A, p₀, C] using hdr'


/-- **BDG Theorem 4.1 (discrete restriction), uniform form**: for every
`ε > 0` there is a constant `C` (independent of `N`, `a`, `t`, `p`) such
that for all `N ≥ 1`, all `N`-separated points `t`, all coefficients `a`,
all centres `c`, and all `p ≥ 2`,

    ‖Σᵢ aᵢ e(x·γ(tᵢ))‖_{Lᵖ(avg, w_{B(c,Nᵏ)})}
        = (wLpPowAvg k c ((N : ℝ) ^ k) p (sepCharSum k a t))^{1/p}
        ≤ C · ‖a‖₂ · (N^ε + N^{½(1−k(k+1)/p)+ε}) .

**Proof status: proved, from `bdg_critical`.**  The two halves are both
routine once the critical `p₀ = k(k+1)` bound holds:

* `2 ≤ p ≤ p₀` — `bdg_low_half`: Hölder on the weighted measure `w_B dx`
  (`wLpAvg_low_half`, from `Commons.Measure.Integral.holder_pow_le_mul`) plus
  the uniform weight average `∫w_B ≤ K·|B_R|`
  (`ballWeight_integral_ratio_bound`);
* `p₀ ≤ p` — `bdg_high_half`: the ball-averaged Hölder/trivial-bound reduction
  `dr41_avg_high_bound` (`wLpAvg_reduction` + `mul_rpow_interp_bound`).

The single analytic input left is `bdg_critical` (the ℓ²-decoupling critical
case, BDG Thm 1.2); everything else in this theorem — and in the whole
Vinogradov route — is proved in this module. -/
theorem bdg_discrete_restriction (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 1 ≤ N → ∀ (t : Fin N → ℝ), Separated N t → ∀ a : Fin N → ℂ,
        ∀ c : E k,
          ∀ p : ℝ, 2 ≤ p →
            (wLpPowAvg k c ((N : ℝ) ^ k) p (sepCharSum k a t)) ^ (1 / p)
              ≤ C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) *
                  ((N : ℝ) ^ ε + (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - ((k : ℝ) * ((k : ℝ) + 1)) / p) + ε)) := by
  let p₀ : ℝ := (k : ℝ) * ((k : ℝ) + 1)
  have hp₀ : 0 < p₀ := by
    dsimp [p₀]
    positivity
  rcases bdg_low_half k hk ε hε with ⟨C₁, hC₁, hlow⟩
  rcases bdg_high_half k hk ε hε with ⟨C₂, hC₂, hhigh⟩
  let C : ℝ := max C₁ C₂
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro N hN t hsep a c p hp2
  have hR : 0 < (N : ℝ) ^ k := pow_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)) k
  let A : ℝ := ∑ i : Fin N, ‖a i‖ ^ 2
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : 0 ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  have hsqrt : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  have hsqrt2 : 0 ≤ Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) := Real.sqrt_nonneg _
  have hε0 : 0 ≤ ε := le_of_lt hε
  have hN2 (q : ℝ) : 0 ≤ (N : ℝ) ^ q := Real.rpow_nonneg hN0 q
  by_cases hple : p ≤ p₀
  · -- low half: bound ≤ C₁·√A·N^ε  ≤ C·√A·(N^ε + N^{exp})
    have hlowN := hlow N hN t hsep a c p hp2 hple
    have hC1 : C₁ ≤ C := le_max_left C₁ C₂
    have hstep : C₁ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε ≤
        C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * ((N : ℝ) ^ ε + (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε)) := by
      have hnonneg : 0 ≤ (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε) := hN2 _
      have hplus : (N : ℝ) ^ ε ≤ (N : ℝ) ^ ε + (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε) := by linarith
      have hmid : C₁ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε ≤
          C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε := by
        gcongr
      calc
        C₁ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε
            ≤ C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε := hmid
        _ ≤ C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * ((N : ℝ) ^ ε + (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε)) := by
              exact mul_le_mul_of_nonneg_left hplus (mul_nonneg (le_of_lt hC) hsqrt2)
    calc
      (wLpPowAvg k c ((N : ℝ) ^ k) p (sepCharSum k a t)) ^ (1 / p)
          ≤ C₁ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ ε := hlowN
      _ ≤ C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * ((N : ℝ) ^ ε + (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε)) := hstep
  · -- high half: p₀ < p
    have hp₀p : p₀ ≤ p := le_of_not_ge hple
    have hhighN := hhigh N hN t hsep a c p hp2 hp₀p
    have hC2 : C₂ ≤ C := le_max_right C₁ C₂
    have hstep : C₂ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε) ≤
        C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * ((N : ℝ) ^ ε + (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε)) := by
      have hplus : (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε) ≤
          (N : ℝ) ^ ε + (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε) := by
        have hεnonneg : 0 ≤ (N : ℝ) ^ ε := hN2 ε
        linarith
      have hmid : C₂ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε) ≤
          C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε) := by
        gcongr
      calc
        C₂ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε)
            ≤ C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε) := hmid
        _ ≤ C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * ((N : ℝ) ^ ε + (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε)) := by
              exact mul_le_mul_of_nonneg_left hplus (mul_nonneg (le_of_lt hC) hsqrt2)
    calc
      (wLpPowAvg k c ((N : ℝ) ^ k) p (sepCharSum k a t)) ^ (1 / p)
          ≤ C₂ * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε) := hhighN
      _ ≤ C * Real.sqrt (∑ i : Fin N, ‖a i‖ ^ 2) * ((N : ℝ) ^ ε + (N : ℝ) ^ (((1 : ℝ) / 2) * (1 - p₀ / p) + ε)) := hstep


end Submission.Vinogradov
