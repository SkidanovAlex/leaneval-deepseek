import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.EndDefect
import Submission.Work.Pert.Setup
import Submission.Work.Pert.gate_walk_drift_explicit
import Submission.Work.Pert.gate_walk_sum_y_le
import Submission.Work.Pert.tauC_norm_le_gate_five
import Submission.Work.Pert.sigma_le_half_rr
import Submission.Work.Pert.sigma_le_norm_alpha
import Submission.Work.Pert.norm_endDefect_le
import Submission.Work.Pert.iInf_dist_eq_norm_sub_round
import Submission.Work.Pert.GateDriftRate.waist_diam_le
import Submission.Work.Pert.gate_geom_facts

/-!
# The waist-band defect sum

The sum of the defects `d_j = F (w_j) - (w_j + 1)` (relative to the lower-end value
`D = endDefect u σ α`) over the *waist* indices `|Im (α w_j)| < 1` of a legal walk `w_j = F^[j] z`
in the lower gate `Qm Ξ α` is bounded by `2^30 (1 + Ξ + 1/Ξ + 1/rr) (1 + log (2+M) + log (2+‖z‖))`.

Ingredients:

* `Work.Pert.defect_sub_endDefect_le_full`: `‖d_j - D‖ ≤ 2^11 (1+1/rr) ‖τ_f w_j - σ‖`;
* the **middle band** `|Im (α w_j)| ≤ gateDelta` (`gateDelta = log 2 / 2π`), where
  `Work.Pert.band_term_le` gives `‖τ_f w_j - σ‖ ≤ (256/3)‖α‖ / max (15‖α‖) Δ_j` with
  `Δ_j = dist (α w_j, ℤ)`, while `Work.Pert.card_band_lattice_le` (with the span bound `9` and the
  cardinality bound `card · ‖α‖ ≤ 10` of `Work.Pert.band_facts_small`/`band_facts_large`) gives the
  counting hypothesis, so that `Work.Pert.sum_inv_max_le_count_finset` bounds the middle-band sum;
* the **outer band** `gateDelta < |Im (α w_j)| < 1`, where `Work.Pert.high_term_le` /
  `Work.Pert.low_term_le` give `‖τ_f w_j - σ‖ ≤ 2‖σ‖`, and the number of such indices is at most
  the total number of waist indices, which is `≤ 207/‖α‖ + 1` by
  `Work.Pert.GateDriftRate.waist_diam_le` (the waist walk points have `Re w` in a window of width
  `200/‖α‖` while `Re w` increases by `31/32` per step);
* the **room bound** `n ≤ (32/15)‖z‖` (`walk_gate_mono` + `gate_geom_facts`), which supplies the
  logarithm: the number of middle-band indices is at most `n + 1 ≤ (32/15)‖z‖ + 1`, so the
  logarithmic term of the layer cake is `≤ log (2 + ‖z‖)`.
-/

/-- `field_simp` with a `ring` finish when the former does not already close the goal. -/
macro "fsr" : tactic => `(tactic| first | (field_simp; ring) | field_simp)

namespace Work.Pert.GateDriftRate

open scoped Classical
open MandelDim Complex

noncomputable section

set_option maxHeartbeats 8000000

theorem waist_band_defect_sum_le {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hwalk : ∀ j ≤ n, (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α) :
    ∑ j ∈ (Finset.range n).filter
            (fun j => ¬ (1 ≤ (α * (Work.Pert.liftF u σ α)^[j] z).im)
              ∧ ¬ ((α * (Work.Pert.liftF u σ α)^[j] z).im ≤ -1)),
        ‖Work.Pert.liftF u σ α ((Work.Pert.liftF u σ α)^[j] z)
          - ((Work.Pert.liftF u σ α)^[j] z + 1) - Work.Pert.endDefect u σ α‖
      ≤ 2 ^ 30 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
  -- ## 0.  abbreviations and basic constants
  set F : ℂ → ℂ := Work.Pert.liftF u σ α with hFdef
  set D : ℂ := Work.Pert.endDefect u σ α with hDdef
  set J : Finset ℕ := (Finset.range n).filter
      (fun j => ¬ (1 ≤ (α * F^[j] z).im) ∧ ¬ ((α * F^[j] z).im ≤ -1)) with hJdef
  have hαne : α ≠ 0 := by
    intro h0
    have h1 : |α.im| < α.re := hInF1
    rw [h0] at h1
    simp at h1
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have hM1024 : (1024 : ℝ) ≤ M := by
    have h : (2 : ℝ) ^ 10 ≤ M := hM
    norm_num at h ⊢
    exact h
  have hα64 : ‖α‖ ≤ 1 / 64 := by
    have h1 : (64 : ℝ) ≤ 32 * (M + 2 + Ξ) := by nlinarith [hM1024, hΞ]
    exact le_trans hα (one_div_le_one_div_of_le (by norm_num) h1)
  have hσ32 : ‖σ‖ ≤ 32 * ‖α‖ :=
    sigma_le_norm_alpha hα64 (hu2 0 (Metric.mem_ball_self hrr)).1 hnorm
  have hσhalf : ‖σ‖ ≤ rr / 2 := sigma_le_half_rr hΞ hrr hM hInF1 hα hτQ
  have hDle : ‖D‖ ≤ 100 * ‖α‖ * (1 + 1 / rr) := by
    rw [hDdef]
    exact norm_endDefect_le hrr hα64 hαne hu hu2 hσhalf hnorm
  have hA0 : 0 < (1 + σ * u σ).re := by
    have hσmem : σ ∈ Metric.ball (0 : ℂ) rr := by
      rw [Metric.mem_ball, dist_zero_right]; linarith [hσhalf, hrr]
    have huσ2 : ‖u σ‖ ≤ 2 := (hu2 σ hσmem).2
    have h1 : ‖σ * u σ‖ < 1 := by
      rw [norm_mul]
      have h2 : ‖σ‖ * ‖u σ‖ ≤ (32 * ‖α‖) * 2 :=
        mul_le_mul hσ32 huσ2 (norm_nonneg _) (by positivity)
      have h3 : (32 * ‖α‖) * 2 < 1 := by
        have h4 : ‖α‖ * (32 * (M + 2 + Ξ)) ≤ 1 := by
          have h5 : (0 : ℝ) < 32 * (M + 2 + Ξ) := by nlinarith [hM1024, hΞ]
          have h6 := mul_le_mul_of_nonneg_right hα h5.le
          rwa [one_div, inv_mul_cancel₀ h5.ne'] at h6
        have h5 : (0 : ℝ) < M + 2 + Ξ := by nlinarith [hM1024, hΞ]
        nlinarith [h4, h5]
      linarith
    have h2 : (1 + σ * u σ).re = 1 + (σ * u σ).re := by simp
    have h3 : |(σ * u σ).re| ≤ ‖σ * u σ‖ := Complex.abs_re_le_norm _
    rw [h2]; linarith [(abs_le.mp h3).1, h1]
  -- ## 1.  the walk, in terms of `F`
  have hstepF : ∀ j < n, ‖F^[j+1] z - (F^[j] z + 1)‖ ≤ 1 / 32 := by
    intro j hj
    have h := hNT (F^[j] z) (by rw [hFdef]; exact hwalk j (le_of_lt hj))
    rw [show F^[j+1] z = F (F^[j] z) from Function.iterate_succ_apply' F j z]
    exact h
  have hgateF : ∀ j ≤ n, F^[j] z ∈ Work.Pert.Qm Ξ α := fun j hj => by
    rw [hFdef]; exact hwalk j hj
  have hJmem : ∀ j, j ∈ J ↔ j < n ∧ |(α * F^[j] z).im| < 1 := by
    intro j
    rw [hJdef, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [not_le] at h2 h3
      exact ⟨h1, abs_lt.mpr ⟨h3, h2⟩⟩
    · rintro ⟨h1, h2⟩
      rw [abs_lt] at h2
      exact ⟨h1, not_le.mpr h2.2, not_le.mpr h2.1⟩
  have hJwaist : ∀ j ∈ J, |(α * F^[j] z).im| < 1 := fun j hj => ((hJmem j).mp hj).2
  have hJlt : ∀ j ∈ J, j < n := fun j hj => ((hJmem j).mp hj).1
  have hmono := walk_gate_mono (Ξ := Ξ) (w := fun j => F^[j] z) (n := n) hstepF
  have hre_sep : ∀ j j' : ℕ, j < j' → j' ≤ n →
      (F^[j] z).re + (31 / 32) * ((j' - j : ℕ) : ℝ) ≤ (F^[j'] z).re := by
    have h1 : ∀ j < n, (F^[j] z).re + 31 / 32 ≤ (F^[j+1] z).re :=
      fun j hj => hmono.1 j hj
    have h2 : ∀ j < n, (F^[j+1] z).re ≤ (F^[j] z).re + 33 / 32 := by
      intro j hj
      have h := hstepF j hj
      have hle := Complex.abs_re_le_norm (F^[j+1] z - (F^[j] z + 1))
      have hre : (F^[j+1] z - (F^[j] z + 1)).re = (F^[j+1] z).re - ((F^[j] z).re + 1) := by
        simp
      have h2' : |(F^[j+1] z).re - ((F^[j] z).re + 1)| ≤ 1 / 32 := by
        rw [← hre]; exact le_trans hle h
      linarith [(abs_le.mp h2').2]
    exact fun j j' hlt hj' => (telescope_step (u := fun k => (F^[k] z).re) (n := n)
      (c := 31 / 32) (d := 33 / 32) (fun j hj => ⟨h1 j hj, h2 j hj⟩) j j' hlt hj').1
  -- ## 2.  the room bound `n ≤ (32/15)‖z‖` and the cardinality bound for `J`
  have hz0 : F^[0] z = z := rfl
  have hroom : (n : ℝ) ≤ (32 / 15) * ‖z‖ := by
    have h4 := hmono.2.2.2.1
    have hpos : 0 < |(F^[n] z).im| - (F^[n] z).re - Ξ :=
      (gate_geom_facts hInF1 (hgateF n le_rfl)).2.2.2.2.1
    have hn := h4 n le_rfl
    have hlt : 15 * (n : ℝ) / 16 < |(F^[0] z).im| - (F^[0] z).re - Ξ := by
      linarith
    have hb : |(F^[0] z).im| - (F^[0] z).re - Ξ ≤ 2 * ‖z‖ := by
      rw [hz0]
      have h1 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
      have h2 : -z.re ≤ ‖z‖ := by
        have h := Complex.abs_re_le_norm z
        rw [abs_le] at h
        linarith [h.1]
      linarith
    have : 15 * (n : ℝ) / 16 < 2 * ‖z‖ := lt_of_lt_of_le hlt hb
    linarith
  have hJcard : (J.card : ℝ) ≤ 207 / ‖α‖ + 1 := by
    rcases J.eq_empty_or_nonempty with h | h
    · rw [h]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · set j0 : ℕ := J.min' h with hj0def
      set j1 : ℕ := J.max' h with hj1def
      have hj0 : j0 ∈ J := J.min'_mem h
      have hj1 : j1 ∈ J := J.max'_mem h
      have hsub : ∀ j ∈ J, j0 ≤ j ∧ j ≤ j1 := by
        intro j hj
        exact ⟨J.min'_le j hj, J.le_max' j hj⟩
      have hcard : (J.card : ℝ) ≤ (j1 : ℝ) - (j0 : ℝ) + 1 := by
        have h1 : ∀ j ∈ J, j ≤ j1 := fun j hj => (hsub j hj).2
        have h2 : (J.card : ℝ) ≤ ((Finset.Icc j0 j1).card : ℝ) := by
          refine Nat.cast_le.mpr (Finset.card_le_card ?_)
          intro j hj
          rw [Finset.mem_Icc]
          exact hsub j hj
        rw [Nat.card_Icc] at h2
        have h3 : ((j1 + 1 - j0 : ℕ) : ℝ) = (j1 : ℝ) - (j0 : ℝ) + 1 := by
          have hle : j0 ≤ j1 := (hsub j1 hj1).1
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        linarith [h2, h3]
      have hd := waist_diam_le hΞ hInF1 hstepF hgateF j1 j0 (le_of_lt (hJlt j1 hj1))
        (le_of_lt (hJlt j0 hj0)) (hJwaist j1 hj1) (hJwaist j0 hj0)
      rcases lt_or_eq_of_le (hsub j1 hj1).1 with hlt | heq
      · have hsep := hre_sep j0 j1 hlt (le_of_lt (hJlt j1 hj1))
        have hdiff : (31 / 32) * ((j1 - j0 : ℕ) : ℝ) ≤ 200 / ‖α‖ := by
          have h1 : |(F^[j1] z).re - (F^[j0] z).re| ≤ 200 / ‖α‖ := hd.2
          linarith [hsep, h1, le_abs_self ((F^[j1] z).re - (F^[j0] z).re)]
        have hcast : ((j1 - j0 : ℕ) : ℝ) ≤ (32 / 31) * (200 / ‖α‖) := by
          have := mul_le_mul_of_nonneg_left hdiff (by norm_num : (0:ℝ) ≤ 32 / 31)
          have he : (32 / 31 : ℝ) * ((31 / 32) * ((j1 - j0 : ℕ) : ℝ))
              = ((j1 - j0 : ℕ) : ℝ) := by ring
          linarith [this, he.le, he.ge]
        have h32 : (32 / 31 : ℝ) * (200 / ‖α‖) ≤ 207 / ‖α‖ := by
          rw [show (32 / 31 : ℝ) * (200 / ‖α‖) = (6400 / 31) / ‖α‖ by ring]
          rw [div_le_div_iff₀ hαpos hαpos]
          nlinarith only [norm_nonneg α]
        have hfin : (j1 : ℝ) - (j0 : ℝ) + 1 ≤ 207 / ‖α‖ + 1 := by
          have hh : (j1 : ℝ) - (j0 : ℝ) = ((j1 - j0 : ℕ) : ℝ) := by
            rw [Nat.cast_sub (le_of_lt hlt)]
          linarith [hcast, h32, hh.le, hh.ge]
        linarith [hcard, hfin]
      · have h1 : j1 = j0 := heq.symm
        have hcard1 : J.card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          have h2 := (hsub a ha).1
          have h3 := (hsub a ha).2
          have h4 := (hsub b hb).1
          have h5 := (hsub b hb).2
          omega
        have : (J.card : ℝ) ≤ 1 := by exact_mod_cast hcard1
        have hpos2 : 0 < 207 / ‖α‖ := by positivity
        linarith

  -- ## 3.  the per-term defect bound
  have hdefect : ∀ j ∈ J, ‖F (F^[j] z) - (F^[j] z + 1) - D‖
      ≤ 2 ^ 11 * (1 + 1 / rr) * ‖tauC σ α (F^[j] z) - σ‖ := by
    intro j hj
    have hjlt := hJlt j hj
    have hmem : F^[j] z ∈ Work.Pert.Qm Ξ α := hgateF j (le_of_lt hjlt)
    rw [hFdef, hDdef]
    refine defect_sub_endDefect_le_full hrr hα64 hαne hσhalf hnorm hu hu2 hA0
      (hτQ _ hmem) ?_
    simpa only [hFdef] using hNT _ hmem
  -- ## 4.  middle-band and outer-band per-term bounds for `τ_f - σ`
  set Jm : Finset ℕ := J.filter (fun j => |(α * F^[j] z).im| ≤ gateDelta) with hJmdef
  have hJmmem : ∀ j, j ∈ Jm ↔ j ∈ J ∧ |(α * F^[j] z).im| ≤ gateDelta := by
    intro j; rw [hJmdef, Finset.mem_filter]
  have hτmid : ∀ j ∈ Jm, ‖tauC σ α (F^[j] z) - σ‖
      ≤ (256 / 3) * ‖α‖ / max (15 * ‖α‖) (⨅ k : ℤ, dist (α * F^[j] z) (k : ℂ)) := by
    intro j hj
    obtain ⟨hjJ, hjb⟩ := (hJmmem j).mp hj
    have hjlt := hJlt j hjJ
    have hmem : F^[j] z ∈ Work.Pert.Qm Ξ α := hgateF j (le_of_lt hjlt)
    have hcap : ‖tauC σ α (F^[j] z)‖ ≤ 5 :=
      tauC_norm_le_gate_five hΞ hα64 hσ hnorm hu2 hτQ hNT (F^[j] z) (by rw [hFdef]; exact hmem)
    have hΔ1 : (⨅ k : ℤ, dist (α * F^[j] z) (k : ℂ)) ≤ 1 := by
      obtain ⟨m, hm1, hm2⟩ := iInf_dist_eq_norm_sub_round (α * F^[j] z)
      rw [hm2]
      have him : |(α * F^[j] z - (m : ℂ)).im| ≤ 1 / 8 := by
        rw [Complex.sub_im, Complex.intCast_im, sub_zero]
        exact le_trans hjb gateDelta_le_one_eighth
      calc ‖α * F^[j] z - (m : ℂ)‖
          ≤ |(α * F^[j] z - (m : ℂ)).re| + |(α * F^[j] z - (m : ℂ)).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 1 / 2 + 1 / 8 := by linarith only [hm1, him]
        _ ≤ 1 := by norm_num
    exact band_term_le (W := fun k => F^[k] z) (j := j) hσ hσ32 hα64 hαpos hcap hjb hΔ1
  have hτout : ∀ j ∈ J, j ∉ Jm → ‖tauC σ α (F^[j] z) - σ‖ ≤ 2 * ‖σ‖ := by
    intro j hj hjnm
    have hb := hJwaist j hj
    have hgt : gateDelta < |(α * F^[j] z).im| := by
      by_contra hcon
      push_neg at hcon
      exact hjnm ((hJmmem j).mpr ⟨hj, hcon⟩)
    by_cases hpos : 0 ≤ (α * F^[j] z).im
    · have h2 : gateDelta ≤ (α * F^[j] z).im := by
        rw [abs_of_nonneg hpos] at hgt; exact le_of_lt hgt
      exact le_trans (high_term_le (W := fun k => F^[k] z) (j := j) hσ h2)
        (by linarith only [norm_nonneg σ])
    · have hneg : (α * F^[j] z).im < 0 := lt_of_not_ge hpos
      have h2 : (α * F^[j] z).im ≤ -gateDelta := by
        rw [abs_of_neg hneg] at hgt; linarith
      exact le_trans (low_term_le (W := fun k => F^[k] z) (j := j) hσ h2)
        (by linarith only [norm_nonneg σ])
  -- ## 5.  geometry of the middle band: span, separation, cardinality, counting
  set Bmid : Finset ℕ := (Finset.range n).filter (fun j => |(α * F^[j] z).im| ≤ gateDelta)
    with hBmiddef
  have hJmB : Jm = Bmid := by
    rw [hJmdef, hJdef, hBmiddef, Finset.filter_filter]
    apply Finset.filter_congr
    intro j _
    constructor
    · intro h; exact h.2
    · intro h
      refine ⟨?_, h⟩
      have hlt : |(α * F^[j] z).im| < 1 := by
        have h1 : gateDelta ≤ 1 / 8 := gateDelta_le_one_eighth
        linarith only [h, h1]
      have h2 := abs_lt.mp hlt
      exact ⟨not_le.mpr h2.2, not_le.mpr h2.1⟩
  have hspan9 : ∀ j ∈ Jm, ∀ j' ∈ Jm, |(α * F^[j] z).re - (α * F^[j'] z).re| ≤ 9 := by
    intro j hj j' hj'
    obtain ⟨hjJ, hjb⟩ := (hJmmem j).mp hj
    obtain ⟨hj'J, hj'b⟩ := (hJmmem j').mp hj'
    by_cases him : |α.im| < ‖α‖ / 16
    · exact (band_facts_small (W := fun k => F^[k] z) hΞ hInF1 hα64 hstepF hgateF him).1
        j (hJlt j hjJ) hjb j' (hJlt j' hj'J) hj'b
    · push_neg at him
      exact (band_facts_large (W := fun k => F^[k] z) hΞ hInF1 hα64 hstepF hgateF him).1
        j (hJlt j hjJ) hjb j' (hJlt j' hj'J) hj'b
  have hsepJm : ∀ j ∈ Jm, ∀ j' ∈ Jm, j < j' →
      (α * F^[j] z).re + (2 / 3) * ‖α‖ * ((j' - j : ℕ) : ℝ) ≤ (α * F^[j'] z).re := by
    intro j hj j' hj' hlt
    obtain ⟨hjJ, _⟩ := (hJmmem j).mp hj
    obtain ⟨hj'J, _⟩ := (hJmmem j').mp hj'
    have hs := (gate_walk_re_sep (α := α) hInF1 (w := fun k => F^[k] z) (n := n) hstepF
      j j' hlt (le_of_lt (hJlt j' hj'J))).1
    simpa using hs
  have hcardJm : (Jm.card : ℝ) * ‖α‖ ≤ 10 := by
    rw [hJmB]
    by_cases him : |α.im| < ‖α‖ / 16
    · exact (band_facts_small (W := fun k => F^[k] z) hΞ hInF1 hα64 hstepF hgateF him).2
    · push_neg at him
      exact (band_facts_large (W := fun k => F^[k] z) hΞ hInF1 hα64 hstepF hgateF him).2
  have hcount : ∀ t : ℝ, 0 < t →
      ((Jm.filter (fun j => (⨅ k : ℤ, dist (α * F^[j] z) (k : ℂ)) ≤ t)).card : ℝ)
        ≤ 26 * (3 / ‖α‖ * t + 1) := by
    intro t ht
    have hcl := card_band_lattice_le (B := Jm) (t := fun j => (α * F^[j] z).re)
      (γ := (2 / 3) * ‖α‖) (P := 9) (s := t) (by positivity) (by norm_num) (le_of_lt ht)
      hspan9 hsepJm
    by_cases ht1 : t ≤ 1
    · have hsub : Jm.filter (fun j => (⨅ k : ℤ, dist (α * F^[j] z) (k : ℂ)) ≤ t)
          ⊆ Jm.filter (fun j => (⨅ k : ℤ, dist ((α * F^[j] z).re) (k : ℝ)) ≤ t) := by
        intro j hj
        rw [Finset.mem_filter] at hj ⊢
        refine ⟨hj.1, ?_⟩
        have h1 : (⨅ k : ℤ, dist ((α * F^[j] z).re) (k : ℝ))
            ≤ (⨅ k : ℤ, dist (α * F^[j] z) (k : ℂ)) := iInf_re_le_iInf _
        linarith only [h1, hj.2]
      have h1 : ((Jm.filter (fun j => (⨅ k : ℤ, dist (α * F^[j] z) (k : ℂ)) ≤ t)).card : ℝ)
          ≤ ((Jm.filter (fun j =>
              (⨅ k : ℤ, dist ((α * F^[j] z).re) (k : ℝ)) ≤ t)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h2 : ((Jm.filter (fun j =>
              (⨅ k : ℤ, dist ((α * F^[j] z).re) (k : ℝ)) ≤ t)).card : ℝ)
          ≤ (9 + 2 * t + 2) * (2 * t / ((2 / 3) * ‖α‖) + 2) := hcl
      have h3 : (9 + 2 * t + 2) * (2 * t / ((2 / 3) * ‖α‖) + 2) ≤ 26 * (3 / ‖α‖ * t + 1) := by
        have h4 : 2 * t / ((2 / 3) * ‖α‖) = 3 / ‖α‖ * t := by fsr
        rw [h4]
        have h5 : 9 + 2 * t + 2 ≤ 13 := by linarith only [ht1]
        have h6 : 0 ≤ 3 / ‖α‖ * t + 2 := by positivity
        have h7 : 3 / ‖α‖ * t + 2 ≤ 2 * (3 / ‖α‖ * t + 1) := by
          have h8 : 0 ≤ 3 / ‖α‖ * t := by positivity
          linarith only [h8]
        calc (9 + 2 * t + 2) * (3 / ‖α‖ * t + 2) ≤ 13 * (3 / ‖α‖ * t + 2) :=
              mul_le_mul_of_nonneg_right h5 h6
          _ ≤ 13 * (2 * (3 / ‖α‖ * t + 1)) := mul_le_mul_of_nonneg_left h7 (by norm_num)
          _ = 26 * (3 / ‖α‖ * t + 1) := by ring
      linarith only [h1, h2, h3]
    · push_neg at ht1
      have h1 : ((Jm.filter (fun j => (⨅ k : ℤ, dist (α * F^[j] z) (k : ℂ)) ≤ t)).card : ℝ)
          ≤ (Jm.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have h2 : (Jm.card : ℝ) ≤ 10 / ‖α‖ := by
        rw [le_div_iff₀ hαpos]
        linarith only [hcardJm]
      have h3 : 10 / ‖α‖ ≤ 26 * (3 / ‖α‖ * t + 1) := by
        have h4 : (0 : ℝ) < 3 / ‖α‖ := by positivity
        have h5 : 3 / ‖α‖ ≤ 3 / ‖α‖ * t := by
          have h5' := mul_le_mul_of_nonneg_left (le_of_lt ht1) (le_of_lt h4)
          simpa using h5'
        have h6 : 10 / ‖α‖ ≤ 26 * (3 / ‖α‖) := by
          have h7 : 26 * (3 / ‖α‖) = 78 / ‖α‖ := by ring
          rw [h7]
          exact div_le_div_of_nonneg_right (by norm_num) hαpos.le
        nlinarith only [h5, h6, h4]
      linarith only [h1, h2, h3]
  -- ## 6.  the middle-band sum
  set dD : ℕ → ℝ := fun j => (⨅ k : ℤ, dist (α * F^[j] z) (k : ℂ)) with hdDdef
  have hdDnn : ∀ i ∈ Jm, 0 ≤ dD i := by
    intro i _
    rw [hdDdef]
    exact le_ciInf (fun k => dist_nonneg)
  have hh1170 : 26 * (3 / ‖α‖) * (15 * ‖α‖) = 1170 := by fsr
  have hJmcard_le : (Jm.card : ℝ) ≤ (n : ℝ) := by
    rw [hJmB]
    calc (((Finset.range n).filter (fun j => |(α * F^[j] z).im| ≤ gateDelta)).card : ℝ)
        ≤ ((Finset.range n).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (n : ℝ) := by rw [Finset.card_range]
  have hXlog : 1 + (Jm.card : ℝ) / (26 * (3 / ‖α‖) * (15 * ‖α‖)) ≤ 2 + ‖z‖ := by
    rw [hh1170]
    have h1 : (Jm.card : ℝ) / 1170 ≤ ((32 / 15) * ‖z‖) / 1170 :=
      div_le_div_of_nonneg_right (le_trans hJmcard_le hroom) (by norm_num)
    have h2 : ((32 / 15) * ‖z‖) / 1170 ≤ ‖z‖ := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1170)]
      nlinarith only [norm_nonneg z]
    linarith only [h1, h2]
  have hmid_sum : (∑ j ∈ Jm, ‖tauC σ α (F^[j] z) - σ‖)
      ≤ 6656 * (1 + Real.log (2 + ‖z‖)) + 7100 := by
    have h1 : (∑ j ∈ Jm, ‖tauC σ α (F^[j] z) - σ‖)
        ≤ (256 / 3) * ‖α‖ * (∑ j ∈ Jm, 1 / max (15 * ‖α‖) (dD j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hh := hτmid j hj
      have h2 : (256 / 3) * ‖α‖ * (1 / max (15 * ‖α‖) (dD j))
          = (256 / 3) * ‖α‖ / max (15 * ‖α‖) (dD j) := by
        rw [hdDdef]; ring
      rw [h2]
      exact hh
    have hlog : Real.log (1 + (Jm.card : ℝ) / (26 * (3 / ‖α‖) * (15 * ‖α‖)))
        ≤ Real.log (2 + ‖z‖) := by
      apply Real.log_le_log (by positivity)
      exact hXlog
    by_cases hsat : 26 * (3 / ‖α‖ * (15 * ‖α‖) + 1) ≤ (Jm.card : ℝ)
    · have hLC := sum_inv_max_le_count_finset (B := Jm) (d := dD) (A := 26) (C := 3 / ‖α‖)
        (H := 15 * ‖α‖) (by norm_num) (by positivity) (by positivity) hdDnn hcount hsat
      have hstep1 : (∑ j ∈ Jm, ‖tauC σ α (F^[j] z) - σ‖)
          ≤ (256 / 3) * ‖α‖ * (26 * (3 / ‖α‖) * (1 + Real.log (1 + (Jm.card : ℝ) /
              (26 * (3 / ‖α‖) * (15 * ‖α‖)))) + 26 / (15 * ‖α‖) + 26 * (3 / ‖α‖)) :=
        le_trans h1 (mul_le_mul_of_nonneg_left hLC (by positivity))
      have hstep2 : (256 / 3) * ‖α‖ * (26 * (3 / ‖α‖) * (1 + Real.log (1 + (Jm.card : ℝ) /
              (26 * (3 / ‖α‖) * (15 * ‖α‖)))) + 26 / (15 * ‖α‖) + 26 * (3 / ‖α‖))
          ≤ (256 / 3) * ‖α‖ * (26 * (3 / ‖α‖) * (1 + Real.log (2 + ‖z‖))
              + 26 / (15 * ‖α‖) + 26 * (3 / ‖α‖)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h4 : 26 * (3 / ‖α‖) * (1 + Real.log (1 + (Jm.card : ℝ) /
              (26 * (3 / ‖α‖) * (15 * ‖α‖)))) ≤ 26 * (3 / ‖α‖) * (1 + Real.log (2 + ‖z‖)) :=
          mul_le_mul_of_nonneg_left (by linarith only [hlog]) (by positivity)
        linarith only [h4]
      have hstep3 : (256 / 3) * ‖α‖ * (26 * (3 / ‖α‖) * (1 + Real.log (2 + ‖z‖))
              + 26 / (15 * ‖α‖) + 26 * (3 / ‖α‖))
          ≤ 6656 * (1 + Real.log (2 + ‖z‖)) + 7100 := by
        have e1 : (256 / 3 : ℝ) * ‖α‖ * (26 * (3 / ‖α‖) * (1 + Real.log (2 + ‖z‖)))
            = 6656 * (1 + Real.log (2 + ‖z‖)) := by fsr
        have e2 : (256 / 3 : ℝ) * ‖α‖ * (26 / (15 * ‖α‖) + 26 * (3 / ‖α‖))
            = (256 / 3) * (26 / 15) + (256 / 3) * 26 * 3 := by fsr
        have e3 : (256 / 3 : ℝ) * (26 / 15) + (256 / 3) * 26 * 3 ≤ 7100 := by norm_num
        have e4 : (256 / 3 : ℝ) * ‖α‖ * (26 * (3 / ‖α‖) * (1 + Real.log (2 + ‖z‖))
              + 26 / (15 * ‖α‖) + 26 * (3 / ‖α‖))
            = (256 / 3) * ‖α‖ * (26 * (3 / ‖α‖) * (1 + Real.log (2 + ‖z‖)))
              + (256 / 3) * ‖α‖ * (26 / (15 * ‖α‖) + 26 * (3 / ‖α‖)) := by ring
        rw [e4, e1, e2]
        linarith only [e3]
      exact le_trans hstep1 (le_trans hstep2 hstep3)
    · have h1' : (Jm.card : ℝ) < 26 * (3 / ‖α‖ * (15 * ‖α‖) + 1) := lt_of_not_ge hsat
      have h2' : (Jm.card : ℝ) < 1196 := by
        have h3 : 26 * (3 / ‖α‖ * (15 * ‖α‖) + 1) = 1196 := by fsr
        linarith only [h1', h3]
      have h4 : (∑ j ∈ Jm, 1 / max (15 * ‖α‖) (dD j)) ≤ (Jm.card : ℝ) / (15 * ‖α‖) := by
        calc (∑ j ∈ Jm, 1 / max (15 * ‖α‖) (dD j)) ≤ ∑ _j ∈ Jm, 1 / (15 * ‖α‖) := by
              apply Finset.sum_le_sum
              intro j hj
              exact one_div_le_one_div_of_le (by positivity) (le_max_left _ _)
          _ = (Jm.card : ℝ) / (15 * ‖α‖) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
      have h5 : (256 / 3 : ℝ) * ‖α‖ * ((Jm.card : ℝ) / (15 * ‖α‖)) ≤ 6804 := by
        have e : (256 / 3 : ℝ) * ‖α‖ * ((Jm.card : ℝ) / (15 * ‖α‖))
            = (256 / 45) * (Jm.card : ℝ) := by fsr
        rw [e]
        nlinarith only [h2', (show (0 : ℝ) ≤ (Jm.card : ℝ) by positivity)]
      have h7 : (256 / 3 : ℝ) * ‖α‖ * (∑ j ∈ Jm, 1 / max (15 * ‖α‖) (dD j))
          ≤ 6656 * (1 + Real.log (2 + ‖z‖)) + 7100 := by
        have h6 : (256 / 3 : ℝ) * ‖α‖ * (∑ j ∈ Jm, 1 / max (15 * ‖α‖) (dD j)) ≤ 6804 :=
          le_trans (mul_le_mul_of_nonneg_left h4 (by positivity)) h5
        have h8 : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith only [norm_nonneg z])
        linarith only [h6, h8]
      exact le_trans h1 h7
  -- ## 7.  the outer-band sum
  have houter_sum : (∑ j ∈ J \ Jm, ‖tauC σ α (F^[j] z) - σ‖) ≤ 13312 := by
    have h1 : (∑ j ∈ J \ Jm, ‖tauC σ α (F^[j] z) - σ‖) ≤ ∑ _j ∈ J \ Jm, 2 * ‖σ‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_sdiff] at hj
      exact hτout j hj.1 hj.2
    have h2 : (∑ _j ∈ J \ Jm, 2 * ‖σ‖) = ((J \ Jm).card : ℝ) * (2 * ‖σ‖) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : ((J \ Jm).card : ℝ) ≤ (J.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
    have h4 : (2 : ℝ) * ‖σ‖ ≤ 64 * ‖α‖ := by linarith only [hσ32]
    have h5 : ((J \ Jm).card : ℝ) * (2 * ‖σ‖) ≤ (207 / ‖α‖ + 1) * (64 * ‖α‖) := by
      have h5a : ((J \ Jm).card : ℝ) * (2 * ‖σ‖) ≤ (J.card : ℝ) * (64 * ‖α‖) :=
        mul_le_mul h3 h4 (by positivity) (by positivity)
      have h5b : (J.card : ℝ) * (64 * ‖α‖) ≤ (207 / ‖α‖ + 1) * (64 * ‖α‖) :=
        mul_le_mul_of_nonneg_right hJcard (by positivity)
      linarith only [h5a, h5b]
    have h6 : (207 / ‖α‖ + 1) * (64 * ‖α‖) ≤ 13312 := by
      have e : (207 / ‖α‖ + 1) * (64 * ‖α‖) = 207 * 64 + 64 * ‖α‖ := by fsr
      rw [e]
      have h8 : ‖α‖ ≤ 1 := by linarith only [hα64]
      linarith only [h8]
    linarith only [h1, h2, h5, h6]
  -- ## 8.  the `τ`-sum
  have hτsum : (∑ j ∈ J, ‖tauC σ α (F^[j] z) - σ‖)
      ≤ 6656 * (1 + Real.log (2 + ‖z‖)) + 21000 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not J
      (fun j => |(α * F^[j] z).im| ≤ gateDelta) (fun j => ‖tauC σ α (F^[j] z) - σ‖)
    have hsplit' : (∑ j ∈ J, ‖tauC σ α (F^[j] z) - σ‖)
        = (∑ j ∈ Jm, ‖tauC σ α (F^[j] z) - σ‖)
          + (∑ j ∈ J \ Jm, ‖tauC σ α (F^[j] z) - σ‖) := by
      rw [← hsplit]
      have h1 : J.filter (fun j => |(α * F^[j] z).im| ≤ gateDelta) = Jm := by rw [hJmdef]
      have h2 : J.filter (fun j => ¬ (|(α * F^[j] z).im| ≤ gateDelta)) = J \ Jm := by
        rw [Finset.filter_not, hJmdef]
      rw [h1, h2]
    rw [hsplit']
    linarith only [hmid_sum, houter_sum]
  -- ## 9.  assembly and final arithmetic
  have hsum_le : (∑ j ∈ J, ‖F (F^[j] z) - (F^[j] z + 1) - D‖)
      ≤ 2 ^ 11 * (1 + 1 / rr) * (6656 * (1 + Real.log (2 + ‖z‖)) + 21000) := by
    calc (∑ j ∈ J, ‖F (F^[j] z) - (F^[j] z + 1) - D‖)
        ≤ ∑ j ∈ J, 2 ^ 11 * (1 + 1 / rr) * ‖tauC σ α (F^[j] z) - σ‖ :=
          Finset.sum_le_sum hdefect
      _ = 2 ^ 11 * (1 + 1 / rr) * (∑ j ∈ J, ‖tauC σ α (F^[j] z) - σ‖) := by
          rw [Finset.mul_sum]
      _ ≤ 2 ^ 11 * (1 + 1 / rr) * (6656 * (1 + Real.log (2 + ‖z‖)) + 21000) :=
          mul_le_mul_of_nonneg_left hτsum (by positivity)
  have hM2 : (0 : ℝ) ≤ Real.log (2 + M) := Real.log_nonneg (by linarith only [hM1024])
  have hz2 : (0 : ℝ) ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith only [norm_nonneg z])
  have hL0 : (0 : ℝ) ≤ 1 + Real.log (2 + M) + Real.log (2 + ‖z‖) := by
    linarith only [hM2, hz2]
  have hLz : 1 + Real.log (2 + ‖z‖) ≤ 1 + Real.log (2 + M) + Real.log (2 + ‖z‖) := by
    linarith only [hM2]
  have hR : (0 : ℝ) < 1 + Ξ + 1 / Ξ + 1 / rr := by
    have h1 : 0 < 1 / Ξ := by positivity
    have h2 : 0 < 1 / rr := by positivity
    linarith only [h1, h2, hΞ]
  have hcoef : (1 : ℝ) + 1 / rr ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
    have h1 : 0 ≤ 1 / Ξ := by positivity
    have h2 : 0 ≤ Ξ := le_of_lt hΞ
    linarith only [h1, h2]
  have hc0 : (0 : ℝ) ≤ 2 ^ 11 * (6656 * (1 + Real.log (2 + ‖z‖)) + 21000) := by
    nlinarith only [hz2]
  have hkey : 2 ^ 11 * (6656 * (1 + Real.log (2 + ‖z‖)) + 21000)
      ≤ 2 ^ 30 * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
    have e1 : (2 : ℝ) ^ 11 * (6656 * (1 + Real.log (2 + ‖z‖)) + 21000)
        = (2 : ℝ) ^ 11 * 6656 * (1 + Real.log (2 + ‖z‖)) + (2 : ℝ) ^ 11 * 21000 := by ring
    have c1 : (2 : ℝ) ^ 11 * 6656 * (1 + Real.log (2 + ‖z‖))
        ≤ (2 : ℝ) ^ 11 * 6656 * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) :=
      mul_le_mul_of_nonneg_left hLz (by norm_num)
    have c2 : (2 : ℝ) ^ 11 * 6656 * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖))
        ≤ (2 : ℝ) ^ 30 * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) :=
      mul_le_mul_of_nonneg_right (by norm_num) hL0
    have c3 : (2 : ℝ) ^ 11 * 21000 ≤ (2 : ℝ) ^ 30 := by norm_num
    have c4 : (2 : ℝ) ^ 30 ≤ (2 : ℝ) ^ 30 * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
      have h1 : (1 : ℝ) ≤ 1 + Real.log (2 + M) + Real.log (2 + ‖z‖) := by
        linarith only [hM2, hz2]
      calc (2 : ℝ) ^ 30 = (2 : ℝ) ^ 30 * 1 := by ring
        _ ≤ (2 : ℝ) ^ 30 * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
    rw [e1]
    linarith only [c1, c2, c3, c4]
  have hfin : 2 ^ 11 * (1 + 1 / rr) * (6656 * (1 + Real.log (2 + ‖z‖)) + 21000)
      ≤ 2 ^ 30 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by
    calc 2 ^ 11 * (1 + 1 / rr) * (6656 * (1 + Real.log (2 + ‖z‖)) + 21000)
        = (1 + 1 / rr) * (2 ^ 11 * (6656 * (1 + Real.log (2 + ‖z‖)) + 21000)) := by ring
      _ ≤ (1 + Ξ + 1 / Ξ + 1 / rr)
            * (2 ^ 30 * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖))) :=
          mul_le_mul hcoef hkey hc0 (le_of_lt hR)
      _ = 2 ^ 30 * (1 + Ξ + 1 / Ξ + 1 / rr)
            * (1 + Real.log (2 + M) + Real.log (2 + ‖z‖)) := by ring
  linarith only [hsum_le, hfin]

end

end Work.Pert.GateDriftRate
