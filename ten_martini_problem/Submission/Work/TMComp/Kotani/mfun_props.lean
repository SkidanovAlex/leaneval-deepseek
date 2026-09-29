import Mathlib
import Submission.Work.TMComp.Kotani.Defs

/-!
# Properties of the `m`-function `mfun` (AJ Theorem 3.1, "L0")

This file proves `Work.TMComp.Kotani.mfun_props`: the approximants
`approx α lam E n x = S(x-α)···S(x-nα)·i` converge locally uniformly to `mfun` on
`{0 < Im E}`, and the limit is the `ℍ`-valued holomorphic invariant section
(`0 < Im mfun`, `mfun = amoM`, `mfun(x+α) = E - pot x - 1/mfun x`, continuity,
holomorphy in `E`, `1`-periodicity in `x`).

The analytic core is the nested-disc/contraction argument of AJ Theorem 3.1: the Möbius
step `z ↦ E - pot y - 1/z` contracts the hyperbolic square distance
`delta z w = ‖z-w‖²/(im z · im w)` by the uniform factor `(1 + Im E · h)^{-2}` on
`{Im ≥ h}`, so that the approximants form a Cauchy sequence uniformly on
`{ε ≤ Im E} ∩ {‖E‖ ≤ R}`, uniformly in the phase.

The file is self-contained apart from `Defs.lean` (which fixes the vocabulary): the
per-approximant estimates (`delta` contraction, `im`/norm bounds) and the regularity of the
approximants are proved here from the definitions rather than imported, so that the statement
rests on no unproved input.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

namespace MfunProbs

variable {α lam : ℝ} {E : ℂ} {y : ℝ} {z w : ℂ}

/-! ## Estimates for one Möbius step -/

theorem step_im_eq (_hz : z ≠ 0) : (step lam E y z).im = E.im + z.im / ‖z‖ ^ 2 := by
  rw [step]
  have h1 : ((pot lam y : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
  rw [Complex.sub_im, Complex.sub_im, h1, one_div, Complex.inv_im, Complex.normSq_eq_norm_sq]
  ring

theorem step_im_pos (_hE : 0 < E.im) (hz : 0 < z.im) : 0 < (step lam E y z).im := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  rw [step_im_eq (lam := lam) (E := E) (y := y) hz0]
  positivity

theorem step_im_ge (_hE : 0 < E.im) (hz : 0 < z.im) : E.im ≤ (step lam E y z).im := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  rw [step_im_eq (lam := lam) (E := E) (y := y) hz0]
  have : 0 ≤ z.im / ‖z‖ ^ 2 := by positivity
  linarith

theorem step_norm_le (h : ℝ) (hh : 0 < h) (hz : h ≤ z.im) :
    ‖step lam E y z‖ ≤ ‖E‖ + 2 * |lam| + 1 / h := by
  have hnorm : h ≤ ‖z‖ := le_trans hz (Complex.im_le_norm z)
  have h1 : ‖((pot lam y : ℝ) : ℂ)‖ ≤ 2 * |lam| := by
    rw [show ‖((pot lam y : ℝ) : ℂ)‖ = |pot lam y| from RCLike.norm_ofReal _]
    exact pot_abs_le lam y
  have h2 : ‖(1 : ℂ) / z‖ ≤ 1 / h := by
    rw [norm_div, norm_one]
    simpa [one_div] using one_div_le_one_div_of_le hh hnorm
  calc ‖step lam E y z‖ = ‖E - ((pot lam y : ℝ) : ℂ) - 1 / z‖ := rfl
    _ ≤ ‖E - ((pot lam y : ℝ) : ℂ)‖ + ‖1 / z‖ := norm_sub_le _ _
    _ ≤ (‖E‖ + 2 * |lam|) + 1 / h :=
          add_le_add (le_trans (norm_sub_le _ _) (add_le_add le_rfl h1)) h2
    _ = ‖E‖ + 2 * |lam| + 1 / h := by ring

theorem step_sub_eq (hz : z ≠ 0) (hw : w ≠ 0) :
    step lam E y z - step lam E y w = (z - w) / (z * w) := by
  rw [step, step]
  rw [show E - ↑(pot lam y) - 1 / z - (E - ↑(pot lam y) - 1 / w) = 1 / w - 1 / z by ring]
  field_simp

theorem delta_step_eq (hE : 0 < E.im) (hz : 0 < z.im) (hw : 0 < w.im) :
    delta (step lam E y z) (step lam E y w)
      = delta z w / ((1 + E.im * ‖z‖ ^ 2 / z.im) * (1 + E.im * ‖w‖ ^ 2 / w.im)) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hsub := step_sub_eq (lam := lam) (E := E) (y := y) hz0 hw0
  have him1 := step_im_eq (lam := lam) (E := E) (y := y) hz0
  have him2 := step_im_eq (lam := lam) (E := E) (y := y) hw0
  rw [delta, delta, him1, him2, hsub, norm_div, div_pow, norm_mul, mul_pow]
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  field_simp
  ring

theorem one_div_sq_mul (a b : ℝ) : 1 / a ^ 2 * b = b / a ^ 2 := by ring

/-- The Möbius step contracts `delta` by `(1 + Im E · h)^{-2}` on `{Im ≥ h}`. -/
theorem delta_step_le (hE : 0 < E.im) (h : ℝ) (hh : 0 < h) (hz : h ≤ z.im) (hw : h ≤ w.im) :
    delta (step lam E y z) (step lam E y w) ≤ 1 / (1 + E.im * h) ^ 2 * delta z w := by
  have hzi : 0 < z.im := lt_of_lt_of_le hh hz
  have hwi : 0 < w.im := lt_of_lt_of_le hh hw
  rw [delta_step_eq (lam := lam) (E := E) (y := y) hE hzi hwi, one_div_sq_mul]
  refine div_le_div_of_nonneg_left ?_ ?_ ?_
  · rw [delta]; positivity
  · positivity
  · have hA : 1 + E.im * h ≤ 1 + E.im * ‖z‖ ^ 2 / z.im := by
      have h' : E.im * h ≤ E.im * ‖z‖ ^ 2 / z.im := by
        rw [le_div_iff₀ hzi]
        have h1 : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg z.re]
        have h2 : h * z.im ≤ z.im ^ 2 := by nlinarith
        nlinarith [h1, h2, hE]
      linarith
    have hB : 1 + E.im * h ≤ 1 + E.im * ‖w‖ ^ 2 / w.im := by
      have h' : E.im * h ≤ E.im * ‖w‖ ^ 2 / w.im := by
        rw [le_div_iff₀ hwi]
        have h1 : w.im ^ 2 ≤ ‖w‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; nlinarith [sq_nonneg w.re]
        have h2 : h * w.im ≤ w.im ^ 2 := by nlinarith
        nlinarith [h1, h2, hE]
      linarith
    have h0 : 0 ≤ 1 + E.im * h := by positivity
    nlinarith [hA, hB, h0]

/-! ## Estimates for the iterates -/

/-- Every iterate of a point with `im ≥ h` has `im ≥ min (Im E) h`. -/
theorem approxIt_im_ge {h : ℝ} (hh : 0 < h) (hE : h ≤ E.im) (n : ℕ) :
    ∀ x z, h ≤ z.im → 0 < (approxIt α lam E n x z).im ∧ h ≤ (approxIt α lam E n x z).im := by
  induction n with
  | zero => intro x z hz; rw [approxIt_zero]; exact ⟨lt_of_lt_of_le hh hz, hz⟩
  | succ n ih =>
    intro x z hz
    have hEpos : 0 < E.im := lt_of_lt_of_le hh hE
    obtain ⟨h1, _⟩ := ih (x - α) z hz
    simp only [approxIt_succ]
    exact ⟨step_im_pos hEpos h1, le_trans hE (step_im_ge hEpos h1)⟩

/-- Every iterate of a point with `im ≥ h` is bounded by one constant. -/
theorem approxIt_norm_le {h : ℝ} (hh : 0 < h) (hE : h ≤ E.im) (n : ℕ) :
    ∀ x z, h ≤ z.im →
      ‖approxIt α lam E n x z‖ ≤ max ‖z‖ (‖E‖ + 2 * |lam| + 1 / h) := by
  induction n with
  | zero => intro x z hz; rw [approxIt_zero]; exact le_max_left _ _
  | succ n ih =>
    intro x z hz
    have hEpos : 0 < E.im := lt_of_lt_of_le hh hE
    have h1 := (approxIt_im_ge (α := α) (lam := lam) (E := E) hh hE n (x - α) z hz).2
    simp only [approxIt_succ]
    exact le_trans (step_norm_le (lam := lam) (E := E) (y := x - α) h hh h1) (le_max_right _ _)

/-- The approximants of the `m`-function are `ℍ`-valued and bounded below. -/
theorem approx_im_ge {h : ℝ} (hh : 0 < h) (hE : h ≤ E.im) (h1 : h ≤ 1) (n : ℕ) (x : ℝ) :
    0 < (approx α lam E n x).im ∧ h ≤ (approx α lam E n x).im :=
  approxIt_im_ge (α := α) (lam := lam) (E := E) hh hE n x Complex.I (by simpa using h1)

/-- The approximants of the `m`-function are bounded. -/
theorem approx_norm_le {h : ℝ} (hh : 0 < h) (hE : h ≤ E.im) (h1 : h ≤ 1) (n : ℕ) (x : ℝ) :
    ‖approx α lam E n x‖ ≤ max 1 (‖E‖ + 2 * |lam| + 1 / h) := by
  have := approxIt_norm_le (α := α) (lam := lam) (E := E) hh hE n x Complex.I (by simpa using h1)
  simpa [approx, Complex.norm_I] using this

/-- `n` steps contract `delta` by `(1 + Im E · h)^{-2}` each. -/
theorem approxIt_delta_le {h : ℝ} (hE : h ≤ E.im) (hh : 0 < h) (n : ℕ) :
    ∀ x z w, h ≤ z.im → h ≤ w.im →
      delta (approxIt α lam E n x z) (approxIt α lam E n x w)
        ≤ (1 / (1 + E.im * h) ^ 2) ^ n * delta z w := by
  induction n with
  | zero => intro x z w hz hw; simp
  | succ n ih =>
    intro x z w hz hw
    have hEpos : 0 < E.im := lt_of_lt_of_le hh hE
    have hz' := (approxIt_im_ge (α := α) (lam := lam) (E := E) hh hE n (x - α) z hz).2
    have hw' := (approxIt_im_ge (α := α) (lam := lam) (E := E) hh hE n (x - α) w hw).2
    have key := delta_step_le (lam := lam) (E := E) (y := x - α) hEpos h hh hz' hw'
    simp only [approxIt_succ]
    calc delta (step lam E (x - α) (approxIt α lam E n (x - α) z))
            (step lam E (x - α) (approxIt α lam E n (x - α) w))
        ≤ 1 / (1 + E.im * h) ^ 2
            * delta (approxIt α lam E n (x - α) z) (approxIt α lam E n (x - α) w) := key
      _ ≤ 1 / (1 + E.im * h) ^ 2
            * ((1 / (1 + E.im * h) ^ 2) ^ n * delta z w) :=
          mul_le_mul_of_nonneg_left (ih (x - α) z w hz hw) (by positivity)
      _ = (1 / (1 + E.im * h) ^ 2) ^ (n + 1) * delta z w := by ring

/-! ## Composition of the iterates -/

/-- Splitting the iterate: `n + k` steps are `n` steps applied to the result of `k` steps
starting at the shifted phase `x - n α`. -/
theorem approxIt_add (α lam : ℝ) (E : ℂ) (k : ℕ) : ∀ (n : ℕ) (x : ℝ) (z : ℂ),
    approxIt α lam E (n + k) x z
      = approxIt α lam E n x (approxIt α lam E k (x - (n : ℝ) * α) z) := by
  intro n
  induction n with
  | zero => intro x z; simp
  | succ n ih =>
    intro x z
    rw [Nat.succ_add]
    simp only [approxIt_succ]
    rw [ih (x - α) z,
      show (x - α) - (n : ℝ) * α = x - ((Nat.succ n : ℕ) : ℝ) * α by push_cast; ring]

theorem approx_add (α lam : ℝ) (E : ℂ) (n k : ℕ) (x : ℝ) :
    approx α lam E (n + k) x
      = approxIt α lam E n x (approx α lam E k (x - (n : ℝ) * α)) :=
  approxIt_add α lam E k n x Complex.I

/-! ## The uniform contraction estimate -/

/-- The uniform contraction factor `(1 + ε · min 1 ε)^{-2}`. -/
def ccon (ε : ℝ) : ℝ := 1 / (1 + ε * min 1 ε) ^ 2

/-- The uniform bound for the approximants on `{Im E ≥ ε} ∩ {‖E‖ ≤ R}`. -/
def bnd (ε R lam : ℝ) : ℝ := max 1 (R + 2 * |lam| + 1 / min 1 ε)

/-- The uniform bound for the initial `delta`-difference on `{Im E ≥ ε} ∩ {‖E‖ ≤ R}`. -/
def dwei (ε R lam : ℝ) : ℝ := (1 + bnd ε R lam) ^ 2 / min 1 ε

theorem ccon_nonneg (ε : ℝ) : 0 ≤ ccon ε := by rw [ccon]; positivity

theorem ccon_lt_one {ε : ℝ} (hε : 0 < ε) : ccon ε < 1 := by
  rw [ccon]
  have h1 : 1 < 1 + ε * min 1 ε := by
    have : 0 < ε * min 1 ε := mul_pos hε (lt_min one_pos hε)
    linarith
  have h2 : (1 : ℝ) < (1 + ε * min 1 ε) ^ 2 := by nlinarith
  have := one_div_lt_one_div_of_lt (a := (1 : ℝ)) (b := (1 + ε * min 1 ε) ^ 2) one_pos h2
  simpa using this

theorem one_le_bnd (ε R lam : ℝ) : 1 ≤ bnd ε R lam := le_max_left _ _

theorem delta_nonneg' {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) : 0 ≤ delta z w := by
  rw [delta]
  exact div_nonneg (sq_nonneg _) (le_of_lt (mul_pos hz hw))

theorem bnd_nonneg (ε R lam : ℝ) : 0 ≤ bnd ε R lam := le_trans zero_le_one (one_le_bnd ε R lam)

theorem dwei_nonneg {ε : ℝ} (hε : 0 < ε) (R lam : ℝ) : 0 ≤ dwei ε R lam := by
  rw [dwei]
  exact div_nonneg (pow_nonneg (by linarith [one_le_bnd ε R lam]) 2)
    (le_of_lt (lt_min one_pos hε))

/-- The two-tail contraction estimate: the difference of two approximants is bounded
uniformly on `{Im E ≥ ε} ∩ {‖E‖ ≤ R}`, uniformly in the phase. -/
theorem approx_delta_bound (α lam : ℝ) {ε R : ℝ} (hε : 0 < ε) {E : ℂ} {x : ℝ}
    (hE : ε ≤ E.im) (hR : ‖E‖ ≤ R) (n k : ℕ) :
    delta (approx α lam E (n + k) x) (approx α lam E n x) ≤ ccon ε ^ n * dwei ε R lam := by
  have hh0 : 0 < min 1 ε := lt_min one_pos hε
  have hh1 : min 1 ε ≤ 1 := min_le_left _ _
  have hhε : min 1 ε ≤ ε := min_le_right _ _
  have hEim : 0 < E.im := lt_of_lt_of_le hε hE
  have hle : min 1 ε ≤ E.im := le_trans hhε hE
  have hIh : min 1 ε ≤ (Complex.I).im := by rw [Complex.I_im]; exact hh1
  obtain ⟨hwpos, hwh⟩ := approx_im_ge (α := α) (lam := lam) (E := E) hh0 hle hh1 k
    (x - (n : ℝ) * α)
  have hwnorm : ‖approx α lam E k (x - (n : ℝ) * α)‖ ≤ bnd ε R lam := by
    refine le_trans (approx_norm_le (α := α) (lam := lam) (E := E) hh0 hle hh1 k _) ?_
    exact max_le_max le_rfl (by linarith)
  have hDw : delta Complex.I (approx α lam E k (x - (n : ℝ) * α)) ≤ dwei ε R lam := by
    rw [dwei, delta, Complex.I_im, one_mul]
    refine div_le_div₀ ?_ ?_ hh0 hwh
    · positivity
    · have h1 : ‖Complex.I - approx α lam E k (x - (n : ℝ) * α)‖ ≤ 1 + bnd ε R lam := by
        refine le_trans (norm_sub_le _ _) ?_
        rw [Complex.norm_I]
        linarith [one_le_bnd ε R lam]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hbase : 1 / (1 + E.im * min 1 ε) ^ 2 ≤ ccon ε := by
    rw [ccon]
    have h1 : ε * min 1 ε ≤ E.im * min 1 ε :=
      mul_le_mul_of_nonneg_right hE (le_of_lt hh0)
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  have key := approxIt_delta_le (α := α) (lam := lam) (E := E) (h := min 1 ε) hle hh0 n
    x (approx α lam E k (x - (n : ℝ) * α)) Complex.I hwh hIh
  calc delta (approx α lam E (n + k) x) (approx α lam E n x)
      = delta (approxIt α lam E n x (approx α lam E k (x - (n : ℝ) * α)))
          (approxIt α lam E n x Complex.I) := by rw [approx_add]; rfl
    _ ≤ (1 / (1 + E.im * min 1 ε) ^ 2) ^ n
          * delta (approx α lam E k (x - (n : ℝ) * α)) Complex.I := key
    _ ≤ ccon ε ^ n * dwei ε R lam := by
        have hD0 : 0 ≤ dwei ε R lam := dwei_nonneg hε R lam
        have hc0 : 0 ≤ ccon ε := ccon_nonneg ε
        refine mul_le_mul (pow_le_pow_left₀ (by positivity) hbase n) ?_
          (delta_nonneg' hwpos (by rw [Complex.I_im]; norm_num)) (pow_nonneg hc0 n)
        · rw [delta_comm]; exact hDw

/-! ## Uniform Cauchy property -/

theorem approx_eventually_close (α lam : ℝ) {ε R δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ (E : ℂ) (x : ℝ), ε ≤ E.im → ‖E‖ ≤ R →
      dist (approx α lam E m x) (approx α lam E n x) < δ := by
  have hc0 := ccon_nonneg ε
  have hc1 := ccon_lt_one hε
  set B := bnd ε R lam with hB
  set D := dwei ε R lam with hD
  have hB0 : 0 ≤ B := by rw [hB]; exact bnd_nonneg ε R lam
  have hD0 : 0 ≤ D := by rw [hD]; exact dwei_nonneg hε R lam
  have hlim : Tendsto (fun n : ℕ => B ^ 2 * D * ccon ε ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul (B ^ 2 * D)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 (δ ^ 2) (by positivity))
  refine ⟨max N₀ 1, ?_⟩
  have hN₀' : ∀ n ≥ max N₀ 1, B ^ 2 * D * ccon ε ^ n < δ ^ 2 :=
    fun n hn => hN₀ n (le_trans (le_max_left _ _) hn)
  have aux : ∀ n k : ℕ, max N₀ 1 ≤ n → ∀ (E : ℂ) (x : ℝ), ε ≤ E.im → ‖E‖ ≤ R →
      dist (approx α lam E (n + k) x) (approx α lam E n x) < δ := by
    intro n k hn E x hE hR
    have hh0 : 0 < min 1 ε := lt_min one_pos hε
    have hle : min 1 ε ≤ E.im := le_trans (min_le_right _ _) hE
    have hu := approx_im_ge (α := α) (lam := lam) (E := E) hh0 hle (min_le_left _ _)
      (n + k) x
    have hv := approx_im_ge (α := α) (lam := lam) (E := E) hh0 hle (min_le_left _ _) n x
    have hBu : ‖approx α lam E (n + k) x‖ ≤ B := by
      rw [hB]
      refine le_trans (approx_norm_le (α := α) (lam := lam) (E := E) hh0 hle
        (min_le_left _ _) (n + k) x) ?_
      exact max_le_max le_rfl (by linarith)
    have hBv : ‖approx α lam E n x‖ ≤ B := by
      rw [hB]
      refine le_trans (approx_norm_le (α := α) (lam := lam) (E := E) hh0 hle
        (min_le_left _ _) n x) ?_
      exact max_le_max le_rfl (by linarith)
    have himu : (approx α lam E (n + k) x).im ≤ B := le_trans (Complex.im_le_norm _) hBu
    have himv : (approx α lam E n x).im ≤ B := le_trans (Complex.im_le_norm _) hBv
    have hsq : dist (approx α lam E (n + k) x) (approx α lam E n x) ^ 2
        = delta (approx α lam E (n + k) x) (approx α lam E n x)
            * ((approx α lam E (n + k) x).im * (approx α lam E n x).im) := by
      rw [dist_eq_norm, delta, div_mul_cancel₀]
      exact ne_of_gt (mul_pos hu.1 hv.1)
    have hmain : dist (approx α lam E (n + k) x) (approx α lam E n x) ^ 2
        ≤ B ^ 2 * D * ccon ε ^ (max N₀ 1) := by
      rw [hsq]
      have h1 := approx_delta_bound α lam (x := x) hε hE hR n k
      have h2 : (approx α lam E (n + k) x).im * (approx α lam E n x).im ≤ B * B :=
        mul_le_mul himu himv (le_of_lt hv.1) (le_trans (le_of_lt hu.1) himu)
      have hD0 : 0 ≤ dwei ε R lam := dwei_nonneg hε R lam
      have hc0 : 0 ≤ ccon ε := ccon_nonneg ε
      have h3 := mul_le_mul h1 h2 (mul_nonneg (le_of_lt hu.1) (le_of_lt hv.1))
        (mul_nonneg (pow_nonneg hc0 n) hD0)
      have hcN : ccon ε ^ n ≤ ccon ε ^ (max N₀ 1) :=
        pow_le_pow_of_le_one hc0 (le_of_lt hc1) hn
      calc delta (approx α lam E (n + k) x) (approx α lam E n x)
              * ((approx α lam E (n + k) x).im * (approx α lam E n x).im)
          ≤ (ccon ε ^ n * dwei ε R lam) * (B * B) := h3
        _ = B ^ 2 * dwei ε R lam * ccon ε ^ n := by ring
        _ ≤ B ^ 2 * D * ccon ε ^ (max N₀ 1) := by
            rw [hD]
            exact mul_le_mul_of_nonneg_left hcN (mul_nonneg (pow_nonneg hB0 2) hD0)
    have hfin := lt_of_le_of_lt hmain (hN₀' (max N₀ 1) le_rfl)
    have hs := sq_lt_sq.mp hfin
    rwa [abs_of_nonneg dist_nonneg, abs_of_pos hδ] at hs
  intro m hm n hn E x hE hR
  rcases le_total n m with hmn | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact aux n k hn E x hE hR
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [dist_comm]
    exact aux m k hm E x hE hR

/-! ## Convergence of the approximants -/

/-- Pointwise convergence of the approximants to `mfun` (the latter is the `limUnder`). -/
theorem approx_tendsto_mfun (α lam : ℝ) {ε R : ℝ} (hε : 0 < ε) {E : ℂ} {x : ℝ}
    (hE : ε ≤ E.im) (hR : ‖E‖ ≤ R) :
    Tendsto (fun n => approx α lam E n x) atTop (𝓝 (mfun α lam E x)) := by
  have hcauchy : CauchySeq (fun n => approx α lam E n x) := by
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := approx_eventually_close α lam hε hδ
    exact ⟨N, fun m hm n hn => hN m hm n hn E x hE hR⟩
  simpa only [mfun] using hcauchy.tendsto_limUnder

/-- Distance from the limit to an approximant, uniformly on the box. -/
theorem approx_dist_mfun (α lam : ℝ) {ε R δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ (E : ℂ) (x : ℝ), ε ≤ E.im → ‖E‖ ≤ R →
      dist (mfun α lam E x) (approx α lam E n x) < δ := by
  obtain ⟨N, hN⟩ := approx_eventually_close α lam hε (by linarith : 0 < δ / 2)
  refine ⟨N, fun n hn E x hE hR => ?_⟩
  have hconv : Tendsto (fun m : ℕ => approx α lam E m x) atTop (𝓝 (mfun α lam E x)) :=
    approx_tendsto_mfun α lam hε hE hR
  have hpair : Tendsto (fun m : ℕ => (approx α lam E m x, approx α lam E n x)) atTop
      (𝓝 (mfun α lam E x, approx α lam E n x)) :=
    Filter.Tendsto.prodMk_nhds hconv tendsto_const_nhds
  have hdist := (continuous_dist.tendsto _).comp hpair
  have hev : ∀ᶠ m in atTop, dist (approx α lam E m x) (approx α lam E n x) ≤ δ / 2 := by
    filter_upwards [eventually_ge_atTop N] with m hm
    exact le_of_lt (hN m hm n hn E x hE hR)
  have hle := le_of_tendsto hdist hev
  linarith

/-- Uniform convergence on `{ε ≤ Im E} ∩ {‖E‖ ≤ R} × ℝ`. -/
theorem approx_tendstoUniformlyOn (α lam : ℝ) (ε R : ℝ) (hε : 0 < ε) :
    TendstoUniformlyOn (fun n (p : ℂ × ℝ) => approx α lam p.1 n p.2)
      (fun p : ℂ × ℝ => mfun α lam p.1 p.2) atTop
      {p : ℂ × ℝ | ε ≤ p.1.im ∧ ‖p.1‖ ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := approx_dist_mfun α lam hε hδ
  filter_upwards [eventually_ge_atTop N] with n hn p hp
  exact hN n hn p.1 p.2 hp.1 hp.2

/-- Uniform convergence on `{ε ≤ Im E} ∩ {‖E‖ ≤ R}` for a fixed phase. -/
theorem approx_tendstoUniformlyOn_E (α lam : ℝ) (x : ℝ) (ε R : ℝ) (hε : 0 < ε) :
    TendstoUniformlyOn (fun n (E : ℂ) => approx α lam E n x)
      (fun E : ℂ => mfun α lam E x) atTop {E : ℂ | ε ≤ E.im ∧ ‖E‖ ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := approx_dist_mfun α lam hε hδ
  filter_upwards [eventually_ge_atTop N] with n hn E hE
  exact hN n hn E x hE.1 hE.2

/-! ## Immediate consequences -/

/-- Every iterate of an `ℍ`-point stays in `ℍ`. -/
theorem approxIt_im_pos (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    ∀ (n : ℕ) (x : ℝ) (z : ℂ), 0 < z.im → 0 < (approxIt α lam E n x z).im := by
  intro n
  induction n with
  | zero => intro x z hz; simpa using hz
  | succ n ih => intro x z hz; rw [approxIt_succ]; exact step_im_pos hE (ih (x - α) z hz)

/-- After one step the approximants have `im ≥ Im E`. -/
theorem approx_le_im (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) :
    ∀ (n : ℕ) (x : ℝ), 1 ≤ n → E.im ≤ (approx α lam E n x).im := by
  intro n
  induction n with
  | zero => intro x hn; omega
  | succ n ih =>
    intro x hn
    rw [approx_succ]
    exact step_im_ge hE (approxIt_im_pos α lam E hE n (x - α) Complex.I
      (by rw [Complex.I_im]; norm_num))

/-- `mfun` is `ℍ`-valued. -/
theorem mfun_im_pos (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (x : ℝ) :
    0 < (mfun α lam E x).im := by
  have hconv := approx_tendsto_mfun α lam (ε := E.im) (R := ‖E‖ + 1) (x := x) hE le_rfl
    (by linarith)
  have him : Tendsto (fun n => (approx α lam E n x).im) atTop (𝓝 ((mfun α lam E x).im)) :=
    (Complex.continuous_im.tendsto _).comp hconv
  have hev : ∀ᶠ n in atTop, E.im ≤ (approx α lam E n x).im := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact approx_le_im α lam hE n x hn
  exact lt_of_lt_of_le hE (ge_of_tendsto him hev)

/-! ## The Möbius action of  -/

theorem mob_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ)
    (h : B 1 0 * z + B 1 1 ≠ 0) : mob (A * B) z = mob A (mob B z) := by
  have hnum : (A * B) 0 0 * z + (A * B) 0 1
      = A 0 0 * (B 0 0 * z + B 0 1) + A 0 1 * (B 1 0 * z + B 1 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have hden : (A * B) 1 0 * z + (A * B) 1 1
      = A 1 0 * (B 0 0 * z + B 0 1) + A 1 1 * (B 1 0 * z + B 1 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  rw [mob, mob, mob, hnum, hden]
  set NB := B 0 0 * z + B 0 1
  set DB := B 1 0 * z + B 1 1
  have hDB : DB ≠ 0 := h
  rw [show A 0 0 * (NB / DB) + A 0 1 = (A 0 0 * NB + A 0 1 * DB) / DB by field_simp,
      show A 1 0 * (NB / DB) + A 1 1 = (A 1 0 * NB + A 1 1 * DB) / DB by field_simp,
      (div_div_div_cancel_right₀ hDB _ _).symm]

/-- The approximants peel off the last factor. -/
theorem approxIt_last (α lam : ℝ) (E : ℂ) : ∀ (n : ℕ) (x : ℝ) (z : ℂ),
    approxIt α lam E n x (step lam E (x - ((n : ℝ) + 1) * α) z)
      = approxIt α lam E (n + 1) x z := by
  intro n
  induction n with
  | zero => intro x z; simp
  | succ n ih =>
    intro x z
    simp only [approxIt_succ]
    rw [show x - (((Nat.succ n : ℕ) : ℝ) + 1) * α = (x - α) - ((n : ℝ) + 1) * α by
      push_cast; ring]
    rw [ih (x - α) z, approxIt_succ]

/-- `mob (backIterC n x)` is the `n`-fold iterate of the Möbius step. -/
theorem backIterC_mob (α lam : ℝ) (E : ℂ) (hE : 0 < E.im) :
    ∀ (n : ℕ) (x : ℝ) (z : ℂ), 0 < z.im →
      mob (backIterC α lam E n x) z = approxIt α lam E n x z := by
  intro n
  induction n with
  | zero => intro x z hz; simp [backIterC, approxIt, mob]
  | succ n ih =>
    intro x z hz
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
    have hbc : backIterC α lam E (n + 1) x
        = backIterC α lam E n x * tmC lam E (x - ((n : ℝ) + 1) * α) := rfl
    have hside : tmC lam E (x - ((n : ℝ) + 1) * α) 1 0 * z
        + tmC lam E (x - ((n : ℝ) + 1) * α) 1 1 ≠ 0 := by
      simp [tmC, hz0]
    rw [hbc, mob_mul _ _ _ hside, ← step_eq_mob lam E (x - ((n : ℝ) + 1) * α) z hz0]
    have hw : 0 < (step lam E (x - ((n : ℝ) + 1) * α) z).im := step_im_pos hE hz
    rw [ih x (step lam E (x - ((n : ℝ) + 1) * α) z) hw]
    exact approxIt_last α lam E n x z

/-- On the upper half plane `mfun` agrees with AJ's `m`-function `amoM`. -/
theorem mfun_eq_amoM (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (x : ℝ) :
    mfun α lam E x = amoM α lam E x := by
  have h : (fun n : ℕ => approx α lam E n x)
      = (fun n : ℕ => mob (backIterC α lam E n x) Complex.I) := by
    funext n
    exact (backIterC_mob α lam E hE n x Complex.I (by rw [Complex.I_im]; norm_num)).symm
  simp only [mfun, amoM]
  rw [h]

/-! ## Periodicity in the phase -/

theorem step_period (y : ℝ) (z : ℂ) : step lam E (y + 1) z = step lam E y z := by
  simp only [step, pot_periodic]

theorem approxIt_period (α lam : ℝ) (E : ℂ) :
    ∀ (n : ℕ) (x : ℝ) (z : ℂ),
      approxIt α lam E n (x + 1) z = approxIt α lam E n x z := by
  intro n
  induction n with
  | zero => intro x z; simp
  | succ n ih =>
    intro x z
    simp only [approxIt_succ]
    rw [show x + 1 - α = x - α + 1 by ring, ih (x - α) z, step_period]

/--  is -periodic in the phase. -/
theorem mfun_period (α lam : ℝ) (E : ℂ) (x : ℝ) :
    mfun α lam E (x + 1) = mfun α lam E x := by
  have h : (fun n : ℕ => approx α lam E n (x + 1))
      = (fun n : ℕ => approx α lam E n x) := by
    funext n
    simp only [approx]
    exact approxIt_period α lam E n x Complex.I
  simp only [mfun]
  rw [h]

/-! ## Regularity of the approximants -/

theorem approxIt_continuousOn (α lam : ℝ) (n : ℕ) (z : ℂ) (hz : 0 < z.im) :
    ContinuousOn (fun p : ℂ × ℝ => approxIt α lam p.1 n p.2 z) {p : ℂ × ℝ | 0 < p.1.im} := by
  induction n with
  | zero =>
    simpa only [approxIt_zero] using
      (continuousOn_const : ContinuousOn (fun _ : ℂ × ℝ => z) {p : ℂ × ℝ | 0 < p.1.im})
  | succ n ih =>
    have hφ : ContinuousOn (fun p : ℂ × ℝ => (p.1, p.2 - α)) {p : ℂ × ℝ | 0 < p.1.im} :=
      (continuous_fst.continuousOn).prodMk
        ((continuous_snd.sub continuous_const).continuousOn)
    have hmap : MapsTo (fun p : ℂ × ℝ => (p.1, p.2 - α)) {p : ℂ × ℝ | 0 < p.1.im}
        {q : ℂ × ℝ | 0 < q.1.im} := fun p hp => hp
    have hG : ContinuousOn (fun p : ℂ × ℝ => approxIt α lam p.1 n (p.2 - α) z)
        {p : ℂ × ℝ | 0 < p.1.im} := ih.comp hφ hmap
    have hne : ∀ p ∈ {p : ℂ × ℝ | 0 < p.1.im}, approxIt α lam p.1 n (p.2 - α) z ≠ 0 := by
      intro p hp h0
      have hpos := approxIt_im_pos α lam p.1 hp n (p.2 - α) z hz
      rw [h0] at hpos; simp at hpos
    have hinv : ContinuousOn (fun p : ℂ × ℝ => (approxIt α lam p.1 n (p.2 - α) z)⁻¹)
        {p : ℂ × ℝ | 0 < p.1.im} := hG.inv₀ hne
    have hpot : Continuous (fun p : ℂ × ℝ => ((pot lam (p.2 - α) : ℝ) : ℂ)) := by
      refine Complex.continuous_ofReal.comp ?_
      simp only [pot]
      exact continuous_const.mul
        (Real.continuous_cos.comp (continuous_const.mul (continuous_snd.sub continuous_const)))
    have hbase : ContinuousOn (fun p : ℂ × ℝ => p.1 - ((pot lam (p.2 - α) : ℝ) : ℂ))
        {p : ℂ × ℝ | 0 < p.1.im} := (continuous_fst.continuousOn).sub hpot.continuousOn
    refine (hbase.sub hinv).congr ?_
    intro p _
    simp only [approxIt_succ, step, Pi.sub_apply, one_div]

theorem approxIt_differentiableOn (α lam : ℝ) :
    ∀ (n : ℕ) (x : ℝ) (z : ℂ), 0 < z.im →
      DifferentiableOn ℂ (fun E : ℂ => approxIt α lam E n x z) {E : ℂ | 0 < E.im} := by
  intro n
  induction n with
  | zero => intro x z hz; simpa only [approxIt_zero] using differentiableOn_const (𝕜 := ℂ) z
  | succ n ih =>
    intro x z hz
    have hg : DifferentiableOn ℂ (fun E : ℂ => approxIt α lam E n (x - α) z)
        {E : ℂ | 0 < E.im} := ih (x - α) z hz
    have hne : ∀ E ∈ {E : ℂ | 0 < E.im}, approxIt α lam E n (x - α) z ≠ 0 := by
      intro E hE h0
      have hpos := approxIt_im_pos α lam E hE n (x - α) z hz
      rw [h0] at hpos; simp at hpos
    have h1 : DifferentiableOn ℂ (fun E : ℂ => (approxIt α lam E n (x - α) z)⁻¹)
        {E : ℂ | 0 < E.im} := hg.inv hne
    have h2 : DifferentiableOn ℂ (fun E : ℂ => E - ((pot lam (x - α) : ℝ) : ℂ))
        {E : ℂ | 0 < E.im} := differentiableOn_id.sub_const _
    refine (h2.sub h1).congr ?_
    intro E _
    simp only [approxIt_succ, step, Pi.sub_apply, one_div]

theorem approx_continuousOn_two (α lam : ℝ) (n : ℕ) :
    ContinuousOn (fun p : ℂ × ℝ => approx α lam p.1 n p.2) {p : ℂ × ℝ | 0 < p.1.im} :=
  approxIt_continuousOn α lam n Complex.I (by rw [Complex.I_im]; norm_num)

theorem approx_differentiableOn (α lam : ℝ) (n : ℕ) (x : ℝ) :
    DifferentiableOn ℂ (fun E : ℂ => approx α lam E n x) {E : ℂ | 0 < E.im} :=
  approxIt_differentiableOn α lam n x Complex.I (by rw [Complex.I_im]; norm_num)

/-! ## Local uniformity -/

theorem tendstoLocallyUniformlyOn_product (α lam : ℝ) :
    TendstoLocallyUniformlyOn (fun n (p : ℂ × ℝ) => approx α lam p.1 n p.2)
      (fun p : ℂ × ℝ => mfun α lam p.1 p.2) atTop {p : ℂ × ℝ | 0 < p.1.im} := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds ?_
  rintro ⟨E, y⟩ hE
  have hEpos : (0 : ℝ) < E.im := hE
  refine ⟨{q : ℂ × ℝ | E.im / 2 ≤ q.1.im ∧ ‖q.1‖ ≤ ‖E‖ + 1},
    Metric.mem_nhdsWithin_iff.mpr ⟨min (E.im / 2) 1, lt_min (by linarith) one_pos, ?_⟩,
    approx_tendstoUniformlyOn α lam (E.im / 2) (‖E‖ + 1) (by linarith)⟩
  rintro q ⟨hq1, _⟩
  rw [Metric.mem_ball, Prod.dist_eq] at hq1
  have hd : dist q.1 E < min (E.im / 2) 1 := lt_of_le_of_lt (le_max_left _ _) hq1
  have hd1 : dist q.1 E < E.im / 2 := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : dist q.1 E < 1 := lt_of_lt_of_le hd (min_le_right _ _)
  constructor
  · have h2 : |q.1.im - E.im| ≤ ‖q.1 - E‖ := by
      simpa using Complex.abs_im_le_norm (q.1 - E)
    have h3 : ‖q.1 - E‖ = dist q.1 E := by rw [dist_eq_norm]
    have h4 : |q.1.im - E.im| < E.im / 2 :=
      lt_of_le_of_lt h2 (by rw [h3]; exact hd1)
    linarith [(abs_lt.mp h4).1]
  · have h2 : ‖q.1‖ ≤ ‖E‖ + ‖q.1 - E‖ := by
      calc ‖q.1‖ = ‖E + (q.1 - E)‖ := by ring_nf
        _ ≤ ‖E‖ + ‖q.1 - E‖ := norm_add_le _ _
    have h3 : ‖q.1 - E‖ = dist q.1 E := by rw [dist_eq_norm]
    linarith

theorem tendstoLocallyUniformlyOn_E (α lam : ℝ) (x : ℝ) :
    TendstoLocallyUniformlyOn (fun n (E : ℂ) => approx α lam E n x)
      (fun E : ℂ => mfun α lam E x) atTop {E : ℂ | 0 < E.im} := by
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds ?_
  intro E hE
  have hEpos : (0 : ℝ) < E.im := hE
  refine ⟨{F : ℂ | E.im / 2 ≤ F.im ∧ ‖F‖ ≤ ‖E‖ + 1},
    Metric.mem_nhdsWithin_iff.mpr ⟨min (E.im / 2) 1, lt_min (by linarith) one_pos, ?_⟩,
    approx_tendstoUniformlyOn_E α lam x (E.im / 2) (‖E‖ + 1) (by linarith)⟩
  rintro F ⟨hF1, _⟩
  rw [Metric.mem_ball] at hF1
  have hd1 : dist F E < E.im / 2 := lt_of_lt_of_le hF1 (min_le_left _ _)
  have hd2 : dist F E < 1 := lt_of_lt_of_le hF1 (min_le_right _ _)
  constructor
  · have h2 : |F.im - E.im| ≤ ‖F - E‖ := by
      simpa using Complex.abs_im_le_norm (F - E)
    have h3 : ‖F - E‖ = dist F E := by rw [dist_eq_norm]
    have h4 : |F.im - E.im| < E.im / 2 :=
      lt_of_le_of_lt h2 (by rw [h3]; exact hd1)
    linarith [(abs_lt.mp h4).1]
  · calc ‖F‖ = ‖E + (F - E)‖ := by ring_nf
      _ ≤ ‖E‖ + ‖F - E‖ := norm_add_le _ _
      _ = ‖E‖ + dist F E := by rw [dist_eq_norm]
      _ ≤ ‖E‖ + 1 := by linarith

theorem mfun_continuousOn (α lam : ℝ) :
    ContinuousOn (fun p : ℂ × ℝ => mfun α lam p.1 p.2) {p : ℂ × ℝ | 0 < p.1.im} :=
  (tendstoLocallyUniformlyOn_product α lam).continuousOn
    (Eventually.of_forall fun n => approx_continuousOn_two α lam n).frequently

theorem mfun_differentiableOn (α lam : ℝ) (x : ℝ) :
    DifferentiableOn ℂ (fun E : ℂ => mfun α lam E x) {E : ℂ | 0 < E.im} :=
  (tendstoLocallyUniformlyOn_E α lam x).differentiableOn
    (Eventually.of_forall fun n => approx_differentiableOn α lam n x)
    (isOpen_lt continuous_const Complex.continuous_im)

/-! ## The covariance relation -/

theorem mfun_covariance (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (x : ℝ) :
    mfun α lam E (x + α) = E - ((pot lam x : ℝ) : ℂ) - 1 / mfun α lam E x := by
  have hconv := approx_tendsto_mfun α lam (ε := E.im) (R := ‖E‖ + 1) (x := x) hE le_rfl
    (by linarith)
  have hm0 : mfun α lam E x ≠ 0 := by
    intro h0
    have hpos := mfun_im_pos α lam hE x
    rw [h0] at hpos; simp at hpos
  have hstep : ContinuousAt (fun z : ℂ => step lam E x z) (mfun α lam E x) := by
    have heq : (fun z : ℂ => step lam E x z)
        = fun z => E - ((pot lam x : ℝ) : ℂ) - z⁻¹ := by
      funext z; rw [step, one_div]
    rw [heq]
    exact (continuousAt_const.sub continuousAt_const).sub (continuousAt_inv₀ hm0)
  have h2 : Tendsto (fun n : ℕ => step lam E x (approx α lam E n x)) atTop
      (𝓝 (step lam E x (mfun α lam E x))) := hstep.tendsto.comp hconv
  have h1 : Tendsto (fun n : ℕ => approx α lam E (n + 1) (x + α)) atTop
      (𝓝 (mfun α lam E (x + α))) := by
    have hc := approx_tendsto_mfun α lam (ε := E.im) (R := ‖E‖ + 1) (x := x + α) hE
      le_rfl (by linarith)
    exact hc.comp (Filter.tendsto_add_atTop_nat 1)
  have heq : (fun n : ℕ => approx α lam E (n + 1) (x + α))
      = (fun n : ℕ => step lam E x (approx α lam E n x)) := by
    funext n
    rw [approx_succ, show x + α - α = x by ring]
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

end MfunProbs

/-- **AJ Theorem 3.1 (`m`-function, "L0")**: the approximants
`S(x-α)···S(x-nα)·i` converge locally uniformly on the upper half plane to a function
`mfun` which is `ℍ`-valued, holomorphic in `E`, `1`-periodic in the phase, satisfies the
covariance relation `mfun E (x+α) = E - pot lam x - 1/mfun E x`, and agrees with AJ's
`m`-function `amoM` on `{0 < Im E}`. -/
theorem mfun_props (α lam : ℝ) :
    (∀ (ε R : ℝ), 0 < ε → TendstoUniformlyOn
      (fun n (p : ℂ × ℝ) => Work.TMComp.Kotani.approx α lam p.1 n p.2)
      (fun p : ℂ × ℝ => Work.TMComp.Kotani.mfun α lam p.1 p.2) atTop
      {p : ℂ × ℝ | ε ≤ p.1.im ∧ ‖p.1‖ ≤ R}) ∧
    (∀ E : ℂ, 0 < E.im → ∀ x : ℝ, 0 < (Work.TMComp.Kotani.mfun α lam E x).im) ∧
    (∀ E : ℂ, 0 < E.im → ∀ x : ℝ,
      Work.TMComp.Kotani.mfun α lam E x = Work.TMContract.amoM α lam E x) ∧
    (∀ E : ℂ, 0 < E.im → ∀ x : ℝ,
      Work.TMComp.Kotani.mfun α lam E (x + α)
        = E - ((Work.TMComp.Kotani.pot lam x : ℝ) : ℂ)
            - 1 / Work.TMComp.Kotani.mfun α lam E x) ∧
    (ContinuousOn (fun p : ℂ × ℝ => Work.TMComp.Kotani.mfun α lam p.1 p.2)
      {p : ℂ × ℝ | 0 < p.1.im}) ∧
    (∀ x : ℝ,
      DifferentiableOn ℂ (fun E : ℂ => Work.TMComp.Kotani.mfun α lam E x) {E : ℂ | 0 < E.im}) ∧
    (∀ E : ℂ, ∀ x : ℝ,
      Work.TMComp.Kotani.mfun α lam E (x + 1) = Work.TMComp.Kotani.mfun α lam E x) := by
  refine ⟨fun ε R hε => MfunProbs.approx_tendstoUniformlyOn α lam ε R hε, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · intro E hE x
    exact MfunProbs.mfun_im_pos α lam hE x
  · intro E hE x
    exact MfunProbs.mfun_eq_amoM α lam hE x
  · intro E hE x
    exact MfunProbs.mfun_covariance α lam hE x
  · exact MfunProbs.mfun_continuousOn α lam
  · intro x
    exact MfunProbs.mfun_differentiableOn α lam x
  · intro E x
    exact MfunProbs.mfun_period α lam E x

end Work.TMComp.Kotani
