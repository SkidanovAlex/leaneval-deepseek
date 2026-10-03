import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.leftCoord.sum_inv_norm_le_log

/-!
# Orbit estimates for the chart dynamics of a parabolic germ

For a parabolic germ `f z = z + z ^ 2 * h z` (`h z = 1 + a z + O(z^2)`) and its conjugate
chart dynamics `wMap f w = -1 / f (-1/w)` we prove that any orbit segment which stays outside
a large disc moves to the right at speed at least `1/2`:

`Re ((wMap f)^[k] ζ) ≥ Re ζ + k/2`,

and that its imaginary part drifts at most logarithmically:

`|Im ((wMap f)^[k] ζ) - Im ζ| ≤ C (1 + log (k+1))`.

Everything is phrased with the *norm* hypothesis `R < ‖ζ‖` (and the same for all iterates),
which is the form the downstream construction of the left chart coordinate needs; the estimates
of `FatouCoord/Estimate` are stated on right half-planes instead.

The proof has three steps.

* A one-step estimate in norm form (`wMap_step_bound_norm`): for `‖v‖` large,
  `wMap f v = v + 1 + O(1/‖v‖)` and `Re (wMap f v) ≥ Re v + 1/2`.  This uses the chart form
  `wMap f w = w / (1 + (-1/w) h (-1/w))` of the dynamics (`wMap_eq_norm`, `wMap_sub_eq_norm`)
  together with the quantitative bounds on `h`.
* Hence along any orbit whose iterates stay outside the disc of radius `N`,
  `Re ((wMap f)^[j] ζ) ≥ Re ζ + j/2`, and the imaginary increments are `O(1/‖w _ j‖)`.
* The harmonic-sum lemma `sum_inv_norm_le_log` (companion file): a sequence whose real part
  grows by a fixed amount per step satisfies `∑_{j<k} 1/‖w j‖ ≤ C (1 + log (k+1))`.  This is
  where the hypothesis that the orbit never enters the disc of radius `R` is used: a term
  `1/‖w j‖` can only be as large as `1/R` on the (bounded) window where `|Re w j| ≤ R`.
-/

set_option maxHeartbeats 1600000

namespace Work.Parab.leftCoord

open Work.FatouCoord
open scoped Topology
open Set Metric

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {v w : ℂ}

/-! ## The chart dynamics in norm form -/

/-- `wMap f w = w / (1 + (-1/w) h (-1/w))` as soon as `1/r < ‖w‖`.

This is `Work.FatouCoord.wMap_eq` with the hypothesis `0 < w.re` replaced by `1/r < ‖w‖`; that
hypothesis was only ever used to conclude `w ≠ 0`, which `1/r < ‖w‖` also gives. -/
theorem wMap_eq_norm (hr : 0 < r) (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ}
    (hN : 1 / r < ‖w‖) : wMap f w = w / (1 + (-1 / w) * h (-1 / w)) := by
  have hw0 : w ≠ 0 := by
    intro hw
    rw [hw, norm_zero] at hN
    have : 0 < 1 / r := by positivity
    linarith
  have hz : -1 / w ∈ ball 0 r := by
    simpa [mem_ball_zero_iff] using norm_neg_one_div_lt hr hw0 hN
  have hzw : -1 / (-1 / w) = w := by field_simp
  have h1 : f (-1 / w) = (-1 / w) * (1 + (-1 / w) * h (-1 / w)) := by
    rw [hf (-1 / w) hz]; ring
  simp only [wMap, chart]
  rw [h1, div_mul_eq_div_div, hzw]

/-- The defect form `wMap f w - w = h (-1/w) / (1 + (-1/w) h (-1/w))` under `1/r < ‖w‖`
(`Work.FatouCoord.wMap_sub_eq` with the real-part hypothesis weakened). -/
theorem wMap_sub_eq_norm (hr : 0 < r) (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ}
    (hN : 1 / r < ‖w‖) (hne : 1 + (-1 / w) * h (-1 / w) ≠ 0) :
    wMap f w - w = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by
  have hw0 : w ≠ 0 := by
    intro hw
    rw [hw, norm_zero] at hN
    have : 0 < 1 / r := by positivity
    linarith
  have key : w * ((-1 / w) * h (-1 / w)) = -h (-1 / w) := by field_simp
  have hsub : (wMap f w - w) * (1 + (-1 / w) * h (-1 / w)) = h (-1 / w) := by
    rw [wMap_eq_norm hr hf hN, sub_mul, div_mul_cancel₀ _ hne]
    rw [show w - w * (1 + (-1 / w) * h (-1 / w))
        = -(w * ((-1 / w) * h (-1 / w))) by ring, key, neg_neg]
  calc wMap f w - w
      = ((wMap f w - w) * (1 + (-1 / w) * h (-1 / w))) / (1 + (-1 / w) * h (-1 / w)) :=
        (mul_div_cancel_right₀ _ hne).symm
    _ = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by rw [hsub]

/-! ## The one-step estimate -/

/-- **One step of the chart dynamics.**  There is a level `N > 1/r > 0` and a constant `K ≥ 0`
such that for `‖v‖ > N`,

* `‖wMap f v - (v+1)‖ ≤ K/‖v‖`, and
* `Re (wMap f v) ≥ Re v + 1/2`.

Everything is uniform in the direction of `v`: only `‖v‖` is used. -/
theorem wMap_step_bound_norm (hb : ParabolicBounds f h a r A A') :
    ∃ N K : ℝ, 0 < N ∧ 1 / r < N ∧ 0 ≤ K ∧
      ∀ v : ℂ, N < ‖v‖ →
        ‖wMap f v - (v + 1)‖ ≤ K / ‖v‖ ∧ v.re + 1 / 2 ≤ (wMap f v).re := by
  set S : ℝ := ‖a‖ + A + 8 with hSdef
  have hSpos : 0 < S := by
    have h2 : 0 ≤ ‖a‖ + A := add_nonneg (norm_nonneg a) hb.hA
    simp only [hSdef]; linarith
  set ρ : ℝ := min (min (r / 2) (1 / 4)) (1 / (4 * S)) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min (lt_min (by linarith [hb.hr]) (by norm_num)) (by positivity)
  have hρr2 : ρ ≤ r / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρr : ρ < r := by linarith [hb.hr, hρr2]
  have hρ4 : ρ ≤ 1 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρS : ρ ≤ 1 / (4 * S) := by rw [hρdef]; exact min_le_right _ _
  have hρkey : (‖a‖ + A * ρ + 8) * ρ ≤ 1 / 4 := by
    have hAρ : A * ρ ≤ A := by
      have h1 : ρ ≤ 1 := le_trans hρ4 (by norm_num)
      nlinarith [hb.hA, hρpos, h1]
    have h2 : (‖a‖ + A * ρ + 8) ≤ S := by
      simp only [hSdef]; linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (le_of_lt hρpos)
    have h4 : S * (1 / (4 * S)) = 1 / 4 := by field_simp
    calc (‖a‖ + A * ρ + 8) * ρ ≤ S * ρ := h3
      _ ≤ S * (1 / (4 * S)) := mul_le_mul_of_nonneg_left hρS (le_of_lt hSpos)
      _ = 1 / 4 := h4
  have hNr : 1 / r < 1 / ρ := one_div_lt_one_div_of_lt hρpos hρr
  refine ⟨1 / ρ, 2 * (A * ρ + ‖a‖ + 2), ?_, hNr, ?_, ?_⟩
  · positivity
  · have h2 : 0 ≤ A * ρ := mul_nonneg hb.hA (le_of_lt hρpos)
    linarith [norm_nonneg a]
  · intro v hv
    have hvN : 0 < ‖v‖ := lt_of_lt_of_le (by positivity) (le_of_lt hv)
    have hv1r : 1 / r < ‖v‖ := lt_trans hNr hv
    set z : ℂ := -1 / v with hz
    set u : ℂ := z * h z with hu
    have hznorm : ‖z‖ = 1 / ‖v‖ := by
      rw [hz, norm_div, norm_neg, norm_one]
    have hzρ : ‖z‖ < ρ := by
      rw [hznorm, div_lt_iff₀ hvN]
      have h := (div_lt_iff₀ hρpos).mp hv
      linarith
    have hzρ' : ‖z‖ ≤ ρ := le_of_lt hzρ
    have hz4 : ‖z‖ ≤ 1 / 4 := le_trans hzρ' hρ4
    have hzr : ‖z‖ < r := lt_of_le_of_lt hzρ' hρr
    have hzball : z ∈ ball 0 r := by simpa [mem_ball_zero_iff] using hzr
    have hclose := hb.h_close z hzball
    have hbnd := hb.h_bound z hzball
    have hznn : 0 ≤ ‖z‖ := norm_nonneg z
    have hunorm : ‖u‖ ≤ 2 * ‖z‖ := by
      rw [hu, norm_mul]; nlinarith [hbnd, hznn]
    have hu4 : ‖u‖ ≤ 1 / 2 := by
      have h2 : 2 * ‖z‖ ≤ 2 * ρ := by linarith
      have h3 : 2 * ρ ≤ 1 / 2 := by linarith
      linarith
    have hden : (1 / 2 : ℝ) ≤ ‖1 + u‖ := by
      have h2 : (1 : ℝ) ≤ ‖1 + u‖ + ‖u‖ := by
        have h3 : ‖(1 : ℂ) + u - u‖ ≤ ‖1 + u‖ + ‖u‖ := norm_sub_le _ _
        rwa [add_sub_cancel_right, norm_one] at h3
      linarith
    have hposden : 0 < ‖(1 : ℂ) + u‖ := lt_of_lt_of_le (by norm_num) hden
    have hne : (1 : ℂ) + u ≠ 0 := norm_pos_iff.mp hposden
    have hdeninv : ‖((1 : ℂ) + u)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      calc (‖(1 : ℂ) + u‖)⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ :=
            (inv_le_inv₀ hposden (by norm_num : (0 : ℝ) < 1 / 2)).mpr hden
        _ = 2 := by norm_num
    have hsub : wMap f v - v = h z / (1 + u) := by
      have hne' : 1 + (-1 / v) * h (-1 / v) ≠ 0 := by
        rw [← hz, ← hu]
        exact hne
      have hstep := wMap_sub_eq_norm hb.hr hb.f_eq hv1r hne'
      simpa only [← hz, ← hu] using hstep
    have hnum : ‖h z - 1 - u‖ ≤ ‖z‖ * (A * ρ + ‖a‖ + 2) := by
      have h1 : h z - 1 - u = (h z - 1 - a * z) + (a * z - z * h z) := by
        rw [hu]; ring
      rw [h1]
      have h2 : ‖a * z - z * h z‖ ≤ ‖a‖ * ‖z‖ + ‖z‖ * 2 := by
        calc ‖a * z - z * h z‖ ≤ ‖a * z‖ + ‖z * h z‖ := norm_sub_le _ _
          _ ≤ ‖a‖ * ‖z‖ + ‖z‖ * 2 := by
              rw [norm_mul, norm_mul]
              nlinarith [hbnd, hznn, norm_nonneg a]
      have h3 : A * ‖z‖ ^ 2 ≤ A * ρ * ‖z‖ := by
        have h4 : ‖z‖ ^ 2 ≤ ρ * ‖z‖ := by nlinarith [hznn, hzρ']
        nlinarith [hb.hA]
      calc ‖(h z - 1 - a * z) + (a * z - z * h z)‖
          ≤ ‖h z - 1 - a * z‖ + ‖a * z - z * h z‖ := norm_add_le _ _
        _ ≤ A * ‖z‖ ^ 2 + (‖a‖ * ‖z‖ + ‖z‖ * 2) := by linarith [hclose]
        _ ≤ ‖z‖ * (A * ρ + ‖a‖ + 2) := by nlinarith [h3, hznn]
    constructor
    · -- the size estimate
      have hval : wMap f v - (v + 1) = (h z - 1 - u) / (1 + u) := by
        have h1 : (h z - 1 - u) / (1 + u) = h z / (1 + u) - 1 := by
          field_simp
          ring
        rw [h1, show wMap f v - (v + 1) = (wMap f v - v) - 1 by ring, hsub]
      have h6 : ‖h z - 1 - u‖ ≤ (A * ρ + ‖a‖ + 2) / ‖v‖ := by
        have h := hnum
        rw [hznorm] at h
        have h2 : (1 / ‖v‖) * (A * ρ + ‖a‖ + 2) = (A * ρ + ‖a‖ + 2) / ‖v‖ := by ring
        rw [h2] at h
        exact h
      have h7 : 0 ≤ (A * ρ + ‖a‖ + 2) / ‖v‖ :=
        div_nonneg (add_nonneg (add_nonneg (mul_nonneg hb.hA (le_of_lt hρpos))
          (norm_nonneg a)) (by norm_num)) (le_of_lt hvN)
      calc ‖wMap f v - (v + 1)‖
          = ‖h z - 1 - u‖ * ‖((1 : ℂ) + u)⁻¹‖ := by
            rw [hval, div_eq_mul_inv, norm_mul]
        _ ≤ ((A * ρ + ‖a‖ + 2) / ‖v‖) * 2 :=
            mul_le_mul h6 hdeninv (norm_nonneg _) h7
        _ = 2 * (A * ρ + ‖a‖ + 2) / ‖v‖ := by ring
    · -- the real part grows
      have hre : (wMap f v).re = v.re + (h z / (1 + u)).re := by
        rw [← hsub]; simp
      have hdecomp : h z / (1 + u) = h z - h z * u * (1 + u)⁻¹ := by
        field_simp
        ring
      have hreal : (h z).re ≥ 1 - ‖a‖ * ‖z‖ - A * ‖z‖ ^ 2 := by
        have hdec : h z = (1 : ℂ) + a * z + (h z - 1 - a * z) := by ring
        have hrec := congrArg Complex.re hdec
        rw [hrec]
        simp only [Complex.add_re, Complex.one_re]
        have h3 : -(a * z).re ≤ ‖a * z‖ := by
          have hh := Complex.abs_re_le_norm (a * z)
          rw [abs_le] at hh
          linarith [hh.1]
        have h4 : -(h z - 1 - a * z).re ≤ ‖h z - 1 - a * z‖ := by
          have hh := Complex.abs_re_le_norm (h z - 1 - a * z)
          rw [abs_le] at hh
          linarith [hh.1]
        have h5 : ‖a * z‖ = ‖a‖ * ‖z‖ := norm_mul a z
        linarith [h3, h4, h5, hclose]
      have hcorr : ‖h z * u * ((1 : ℂ) + u)⁻¹‖ ≤ 8 * ‖z‖ := by
        have hc1 : ‖h z * u‖ ≤ 2 * (2 * ‖z‖) := by
          rw [norm_mul]
          exact mul_le_mul hbnd hunorm (norm_nonneg _) (by norm_num)
        have hc2 : ‖h z * u * ((1 : ℂ) + u)⁻¹‖ ≤ (2 * (2 * ‖z‖)) * 2 := by
          rw [norm_mul]
          exact mul_le_mul hc1 hdeninv (norm_nonneg _) (by positivity)
        calc ‖h z * u * ((1 : ℂ) + u)⁻¹‖ ≤ (2 * (2 * ‖z‖)) * 2 := hc2
          _ = 8 * ‖z‖ := by ring
      have hcorrre : (h z * u * ((1 : ℂ) + u)⁻¹).re ≤ 8 * ‖z‖ := by
        have h := Complex.re_le_norm (h z * u * ((1 : ℂ) + u)⁻¹)
        linarith
      have hgoal : (1 / 2 : ℝ) ≤ (h z).re - (h z * u * ((1 : ℂ) + u)⁻¹).re := by
        have h1 : ‖a‖ * ‖z‖ + A * ‖z‖ ^ 2 + 8 * ‖z‖ ≤ (‖a‖ + A * ρ + 8) * ρ := by
          have e1 : ‖a‖ * ‖z‖ ≤ ‖a‖ * ρ := mul_le_mul_of_nonneg_left hzρ' (norm_nonneg a)
          have e2 : ‖z‖ ^ 2 ≤ ρ ^ 2 := by nlinarith [hznn, hzρ']
          have e3 : A * ‖z‖ ^ 2 ≤ A * ρ ^ 2 := mul_le_mul_of_nonneg_left e2 hb.hA
          have e4 : 8 * ‖z‖ ≤ 8 * ρ := by linarith [hzρ']
          nlinarith [e1, e3, e4]
        nlinarith [hreal, hcorrre, h1, hρkey]
      rw [hre, hdecomp, Complex.sub_re]
      linarith [hgoal]

/-! ## The orbit estimates -/

theorem wMap_orbit_estimates {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : Work.FatouCoord.ParabolicBounds f h a r A A') :
    ∃ R c C : ℝ, 0 < R ∧ 1 / r < R ∧ 0 < c ∧ 0 ≤ C ∧
      ∀ ζ : ℂ, R < ‖ζ‖ → ∀ k : ℕ,
        (∀ j ≤ k, R < ‖(Work.FatouCoord.wMap f)^[j] ζ‖) →
          (ζ.re + c * k ≤ ((Work.FatouCoord.wMap f)^[k] ζ).re ∧
           |((Work.FatouCoord.wMap f)^[k] ζ).im - ζ.im| ≤ C * (1 + Real.log (k + 1))) := by
  obtain ⟨N, K, hNpos, hNr, hKnn, hstep⟩ := wMap_step_bound_norm hb
  set R : ℝ := max N 1 with hRdef
  have hRN : N ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le hNpos hRN
  have hRr : 1 / r < R := lt_of_lt_of_le hNr hRN
  obtain ⟨CA, hCAnn, hCA⟩ := sum_inv_norm_le_log (c := 1 / 2) (R := R) (by norm_num) hRpos
  refine ⟨R, 1 / 2, K * CA, hRpos, hRr, by norm_num, mul_nonneg hKnn hCAnn, ?_⟩
  intro ζ hζ k hchain
  let w : ℕ → ℂ := fun j => (wMap f)^[j] ζ
  have hw0 : w 0 = ζ := rfl
  have hsucc : ∀ j, w (j + 1) = wMap f (w j) := by
    intro j
    show (wMap f)^[j + 1] ζ = wMap f ((wMap f)^[j] ζ)
    exact Function.iterate_succ_apply' (wMap f) j ζ
  have hnorm : ∀ j ≤ k, R ≤ ‖w j‖ := fun j hj => le_of_lt (hchain j hj)
  have hstepR : ∀ j < k, (w j).re + 1 / 2 ≤ (w (j + 1)).re := by
    intro j hj
    have h1 : N < ‖w j‖ := lt_of_le_of_lt hRN (hchain j (le_of_lt hj))
    have h2 := (hstep (w j) h1).2
    rw [hsucc j]
    exact h2
  have hstepN : ∀ j < k, ‖w (j + 1) - w j - 1‖ ≤ K / ‖w j‖ := by
    intro j hj
    have h1 : N < ‖w j‖ := lt_of_le_of_lt hRN (hchain j (le_of_lt hj))
    have h2 := (hstep (w j) h1).1
    rw [hsucc j]
    simpa only [sub_sub] using h2
  have hregrow : ζ.re + (k : ℝ) * (1 / 2) ≤ (w k).re := by
    have hgen : ∀ j, j ≤ k → ζ.re + (j : ℝ) * (1 / 2) ≤ (w j).re := by
      intro j
      induction j with
      | zero => intro _; simp [hw0]
      | succ j ih =>
          intro hj
          have hjk : j < k := Nat.lt_of_succ_le hj
          have h1 := ih (le_of_lt hjk)
          have h2 := hstepR j hjk
          rw [hsucc j] at h2 ⊢
          push_cast
          linarith
    exact hgen k le_rfl
  have hsum := hCA w k (fun j hj => hnorm j (le_of_lt hj)) hstepR
  have him : |(w k).im - ζ.im| ≤ K * CA * (1 + Real.log (k + 1)) := by
    have htel : (w k).im - ζ.im = ∑ j ∈ Finset.range k, (w (j + 1) - w j).im := by
      have h1 : ∑ j ∈ Finset.range k, (w (j + 1) - w j) = w k - w 0 := Finset.sum_range_sub w k
      rw [hw0] at h1
      have h2 : (w k - ζ).im = ∑ j ∈ Finset.range k, (w (j + 1) - w j).im := by
        rw [← h1, Complex.im_sum]
      simpa using h2
    rw [htel]
    calc |∑ j ∈ Finset.range k, (w (j + 1) - w j).im|
        ≤ ∑ j ∈ Finset.range k, |(w (j + 1) - w j).im| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range k, K / ‖w j‖ := by
          apply Finset.sum_le_sum
          intro j hj
          have hjlt : j < k := Finset.mem_range.mp hj
          have h4 := hstepN j hjlt
          calc |(w (j + 1) - w j).im| = |(w (j + 1) - w j - 1).im| := by simp
            _ ≤ ‖w (j + 1) - w j - 1‖ := Complex.abs_im_le_norm _
            _ ≤ K / ‖w j‖ := h4
      _ = K * ∑ j ∈ Finset.range k, 1 / ‖w j‖ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [div_eq_mul_one_div]
      _ ≤ K * (CA * (1 + Real.log (k + 1))) :=
          mul_le_mul_of_nonneg_left hsum hKnn
      _ = K * CA * (1 + Real.log (k + 1)) := by ring
  constructor
  · show ζ.re + (1 / 2) * (k : ℝ) ≤ (w k).re
    linarith [hregrow]
  · show |(w k).im - ζ.im| ≤ K * CA * (1 + Real.log (k + 1))
    exact him

end

end Work.Parab.leftCoord
