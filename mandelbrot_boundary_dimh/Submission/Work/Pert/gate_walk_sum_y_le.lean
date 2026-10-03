import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.liftF_defect_le_tau_explicit
import Submission.Work.Pert.walk_sum_tauC_sub_sigma_le
import Submission.Work.Pert.Qm_slice
import Submission.Work.Pert.walk_gate_mono
import Submission.Work.Pert.tauC_norm_le_gate_five
import Submission.Work.Pert.sigma_le_norm_alpha
import Submission.Work.Pert.norm_one_sub_exp_two_pi_I_mul_ge
import Submission.Work.Pert.sum_inv_dist_gate_walk
import Submission.Work.Pert.iInf_dist_eq_norm_sub_round
import Submission.Work.Pert.card_band_lattice_le
import Submission.Work.Pert.sum_inv_max_le_count_finset

/-
# PERT · `Work.Pert.gate_walk_sum_y_le`

The value-comparison sum of Shishikura §4.2 along a legal walk in the lower gate: with
`w_j = F_f^[j] z` the iterates of the lift `F_f = liftF u σ α` of a perturbed parabolic map,
`τ_j = tauC σ α w_j` the perturbed coordinate and `σ` the second fixed point,

  `∑_{j<n} ‖τ_j - σ‖ ≤ 2^18 (1 + log (2 + n + ‖z‖) + n ‖α‖)` .

The three ingredients are:

* the **pointwise value bound** `τ - σ = σ E/(1 - E)` with `E = exp (-2πi α w)`, combined with the
  lattice bound `‖1 - E‖ ≥ (3/4) min 1 (dist (α w, ℤ))` (`norm_one_sub_gateE_ge`);
* the **splitting into two end bands** (`E` large / small, where `‖τ - σ‖ ≤ 2‖σ‖`, resp. `≤ ‖σ‖`)
  and a **middle band** `|Im (α w)| ≤ δ = log 2 / 2π` (`E` inside `[1/2, 2]`), on which the term is
  at most `(256/3)‖α‖ / max (15‖α‖) Δ`;
* the **geometry of the gate**: inside the middle band the walk can spend at most `O(1/‖α‖)` steps
  (either the `Im (α w)`-drift moves it out of the band, or the gate's upper cone bounds `|Im w|`),
  so the phases are separated and confined to a window of length at most `9`; the counting lemma
  `card_band_lattice_le` and the layer-cake lemma `sum_inv_max_le_count_finset` then turn the
  lattice-close indices into a `log`-bound.

The main ingredients are `Work.Pert.tauC_norm_le_gate_five` (the cap `‖τ‖ ≤ 5` forcing
`‖1 - E‖ ≥ ‖σ‖/5`), `Work.Pert.walk_gate_mono` (the room bound), and the two sibling files
`Work.Pert.card_band_lattice_le` and `Work.Pert.sum_inv_max_le_count_finset`.
-/

namespace Work.Pert

open scoped Classical
open MandelDim Complex

noncomputable section

set_option maxHeartbeats 4000000

/-! ## Elementary facts about `α` -/

theorem InF1_alpha_ne_zero' {α : ℂ} (h : MandelDim.InF1 α) : α ≠ 0 := by
  intro h0
  have h1 : |α.im| < α.re := h
  rw [h0] at h1
  simp at h1

theorem InF1_norm_pos' {α : ℂ} (h : MandelDim.InF1 α) : 0 < ‖α‖ :=
  norm_pos_iff.mpr (InF1_alpha_ne_zero' h)

theorem InF1_re_pos' {α : ℂ} (h : MandelDim.InF1 α) : 0 < α.re := by
  have h1 : |α.im| < α.re := h
  linarith [abs_nonneg α.im]

/-- `(1 : ℂ)/α` has norm `1/‖α‖`. -/
theorem norm_one_div_alpha (α : ℂ) : ‖(1 : ℂ) / α‖ = 1 / ‖α‖ := by
  rw [norm_div, norm_one]

/-- The mid-band threshold `δ = log 2 / (2π)`. -/
def gateDelta : ℝ := Real.log 2 / (2 * Real.pi)

theorem gateDelta_pos : 0 < gateDelta := by
  rw [gateDelta]
  have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem gateDelta_le_one_eighth : gateDelta ≤ 1 / 8 := by
  rw [gateDelta, div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
  have h1 : Real.log 2 < (0.6932 : ℝ) := by linarith [Real.log_two_lt_d9]
  nlinarith [Real.pi_gt_three]

theorem gateDelta_le_one : gateDelta ≤ 1 := by
  have := gateDelta_le_one_eighth
  linarith

theorem gateDelta_nonneg : 0 ≤ gateDelta := le_of_lt gateDelta_pos

/-- `exp (2π δ) = 2`. -/
theorem exp_two_pi_gateDelta : Real.exp (2 * Real.pi * gateDelta) = 2 := by
  rw [gateDelta]
  rw [show 2 * Real.pi * (Real.log 2 / (2 * Real.pi)) = Real.log 2 from by field_simp]
  exact Real.exp_log (by norm_num)

/-- `exp (2π y) ≤ 2` for `y ≤ δ`. -/
theorem exp_two_pi_le_two {y : ℝ} (hy : y ≤ gateDelta) : Real.exp (2 * Real.pi * y) ≤ 2 := by
  have h : Real.exp (2 * Real.pi * y) ≤ Real.exp (2 * Real.pi * gateDelta) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  rwa [exp_two_pi_gateDelta] at h

/-- `1/2 ≤ exp (2π y)` for `-δ ≤ y`. -/
theorem half_le_exp_two_pi {y : ℝ} (hy : -gateDelta ≤ y) : 1 / 2 ≤ Real.exp (2 * Real.pi * y) := by
  have h : Real.exp (2 * Real.pi * (-gateDelta)) ≤ Real.exp (2 * Real.pi * y) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h2 : Real.exp (2 * Real.pi * (-gateDelta)) = 1 / 2 := by
    rw [show 2 * Real.pi * (-gateDelta) = -(2 * Real.pi * gateDelta) from by ring, Real.exp_neg,
      exp_two_pi_gateDelta]
    norm_num
  rwa [h2] at h

/-! ## The `E`-factor `E w = exp (-(2πi α w))` -/

def gateE (α w : ℂ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * α * w))

theorem gateE_re_arg (α w : ℂ) :
    (-(2 * Real.pi * Complex.I * α * w)).re = 2 * Real.pi * (α * w).im := by
  have key : (-(2 * Real.pi * Complex.I * α * w))
      = -((2 * (Real.pi : ℂ) * Complex.I) * (α * w)) := by ring
  rw [key, Complex.neg_re, Complex.mul_re]
  have h1 : (2 * (Real.pi : ℂ) * Complex.I).re = 0 := by simp
  have h2 : (2 * (Real.pi : ℂ) * Complex.I).im = 2 * Real.pi := by simp
  rw [h1, h2]
  ring

theorem norm_gateE (α w : ℂ) : ‖gateE α w‖ = Real.exp (2 * Real.pi * (α * w).im) := by
  rw [gateE, Complex.norm_exp, gateE_re_arg]

/-- The per-term identity `τ_f w - σ = σ E w / (1 - E w)` for `σ ≠ 0` and `E w ≠ 1`. -/
theorem tauC_sub_sigma_div {σ α w : ℂ} (hσ : σ ≠ 0) (hE : gateE α w ≠ 1) :
    Work.Pert.tauC σ α w - σ = σ * gateE α w / (1 - gateE α w) := by
  have h1 : (1 : ℂ) - gateE α w ≠ 0 := sub_ne_zero.mpr (Ne.symm hE)
  simp only [Work.Pert.tauC, gateE] at h1 ⊢
  rw [eq_div_iff h1]
  field_simp; try ring

/-- The lattice distance controls `‖1 - E‖`: `(3/4) min 1 Δ ≤ ‖1 - E w‖`. -/
theorem norm_one_sub_gateE_ge (α w : ℂ) :
    (3 / 4) * min 1 (⨅ k : ℤ, dist (α * w) (k : ℂ)) ≤ ‖1 - gateE α w‖ := by
  by_cases hpos : (0 : ℝ) < ⨅ k : ℤ, dist (α * w) (k : ℂ)
  · have hhyp : ∀ k : ℤ, (⨅ k : ℤ, dist (α * w) (k : ℂ)) ≤ ‖-(α * w) + (k : ℂ)‖ := by
      intro k
      have hk : (⨅ j : ℤ, dist (α * w) (j : ℂ)) ≤ dist (α * w) (k : ℂ) :=
        ciInf_le ⟨0, by rintro x ⟨j, rfl⟩; exact dist_nonneg⟩ k
      have h2 : ‖-(α * w) + (k : ℂ)‖ = dist (α * w) (k : ℂ) := by
        rw [dist_eq_norm, show -(α * w) + (k : ℂ) = -(α * w - (k : ℂ)) by ring, norm_neg]
      rwa [h2]
    have h := Work.Pert.norm_one_sub_exp_two_pi_I_mul_ge (-(α * w))
      (⨅ k : ℤ, dist (α * w) (k : ℂ)) hpos hhyp
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (-(α * w))) = gateE α w := by
      rw [gateE]; congr 1; ring
    rwa [hexp] at h
  · have hD0 : (⨅ k : ℤ, dist (α * w) (k : ℂ)) = 0 :=
      le_antisymm (le_of_not_gt hpos) (le_ciInf (fun k => dist_nonneg))
    have hzero : (3 / 4 : ℝ) * min (1:ℝ) (⨅ k : ℤ, dist (α * w) (k : ℂ)) = 0 := by
      rw [hD0]; norm_num
    rw [hzero]
    exact norm_nonneg _

/-- Reverse triangle in the form used for the two end bands: `|1 - ‖E‖| ≤ ‖1 - E‖`. -/
theorem abs_one_sub_norm_le (E : ℂ) : |1 - ‖E‖| ≤ ‖1 - E‖ := by
  have h := abs_norm_sub_norm_le (1 : ℂ) E
  simpa using h

/-! ## Gate geometry and the walk -/

/-- The gate lower cone: `-Re z < |Im z| + 2‖1/α‖`. -/
theorem Qm_neg_re_lt {Ξ : ℝ} {α z : ℂ} (hΞ : 0 < Ξ) (hz : z ∈ Work.Pert.Qm Ξ α) :
    -(z.re) < |z.im| + 2 * ‖(1 : ℂ) / α‖ := by
  rw [Work.Pert.Qm_mem_iff] at hz
  obtain ⟨hA, hB⟩ := hz
  have hR : (1 / α).re ≤ ‖(1 : ℂ) / α‖ := le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
  have hI : |(1 / α).im| ≤ ‖(1 : ℂ) / α‖ := Complex.abs_im_le_norm _
  have h1 : |z.im + (1 / α).im| ≤ |z.im| + |(1 / α).im| := abs_add_le _ _
  linarith

/-- The gate upper cone, pure form: `Re z < |Im z|`. -/
theorem Qm_re_lt_abs_im {Ξ : ℝ} {α z : ℂ} (hΞ : 0 < Ξ) (hz : z ∈ Work.Pert.Qm Ξ α) :
    z.re < |z.im| := by
  rw [Work.Pert.Qm_mem_iff] at hz
  linarith [hz.2]

/-- The gate upper cone: `Re z < |Im z| + 2‖1/α‖`. -/
theorem Qm_re_lt {Ξ : ℝ} {α z : ℂ} (hΞ : 0 < Ξ) (hz : z ∈ Work.Pert.Qm Ξ α) :
    z.re < |z.im| + 2 * ‖(1 : ℂ) / α‖ := by
  rw [Work.Pert.Qm_mem_iff] at hz
  obtain ⟨hA, hB⟩ := hz
  have hnn : (0:ℝ) ≤ ‖(1 : ℂ) / α‖ := norm_nonneg _
  have habs : |z.im| - Ξ < |z.im| + 2 * ‖(1 : ℂ) / α‖ := by linarith
  linarith

theorem Qm_abs_re_le {Ξ : ℝ} {α z : ℂ} (hΞ : 0 < Ξ) (hz : z ∈ Work.Pert.Qm Ξ α) :
    |z.re| ≤ |z.im| + 2 * ‖(1 : ℂ) / α‖ := by
  have h1 := Qm_neg_re_lt hΞ hz
  have h2 := Qm_re_lt hΞ hz
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Telescoping lemma for walks with one-sided step bounds. -/
theorem telescope_step {u : ℕ → ℝ} {n : ℕ} {c d : ℝ}
    (h : ∀ j < n, u j + c ≤ u (j + 1) ∧ u (j + 1) ≤ u j + d) :
    ∀ j j' : ℕ, j < j' → j' ≤ n →
      u j + c * ((j' - j : ℕ) : ℝ) ≤ u j' ∧ u j' ≤ u j + d * ((j' - j : ℕ) : ℝ) := by
  intro j j' hlt hj'
  have key : ∀ k : ℕ, j + k ≤ n →
      u j + c * ((k : ℕ) : ℝ) ≤ u (j + k) ∧ u (j + k) ≤ u j + d * ((k : ℕ) : ℝ) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ m ih =>
        intro hk
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        obtain ⟨h1, h2⟩ := h (j + m) (by omega)
        have heq : j + (m + 1) = j + m + 1 := by omega
        constructor
        · rw [heq]
          have hc : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
          rw [hc]; nlinarith [ih1, h1]
        · rw [heq]
          have hc : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
          rw [hc]; nlinarith [ih2, h2]
  have hjk : j + (j' - j) = j' := Nat.add_sub_cancel' (le_of_lt hlt)
  have := key (j' - j) (by omega)
  rwa [hjk] at this

/-- The real part of `α * w ·` is a walk with steps in `[(2/3)‖α‖, (33/32)‖α‖]`. -/
theorem gate_walk_re_sep {α : ℂ} (hInF1 : MandelDim.InF1 α) {w : ℕ → ℂ} {n : ℕ}
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32) :
    ∀ j j' : ℕ, j < j' → j' ≤ n →
      (α * w j).re + (2 / 3) * ‖α‖ * ((j' - j : ℕ) : ℝ) ≤ (α * w j').re ∧
      (α * w j').re ≤ (α * w j).re + (33 / 32) * ‖α‖ * ((j' - j : ℕ) : ℝ) := by
  have hs := Work.Pert.re_alpha_step (α := α) hInF1 (w := w) (n := n) hstep
  refine telescope_step (u := fun j => (α * w j).re) (n := n) (c := (2/3) * ‖α‖)
    (d := (33/32) * ‖α‖) (fun j hj => ?_)
  obtain ⟨h1, h2⟩ := hs j hj
  exact ⟨by linarith, by linarith⟩

/-- The imaginary part of `α * w ·`: the one-step drift is `α.im` up to `‖α‖/32`. -/
theorem gate_walk_im_step {α : ℂ} {w : ℕ → ℂ} {n j : ℕ}
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32) (hj : j < n) :
    |(α * w (j + 1)).im - (α * w j).im - α.im| ≤ ‖α‖ / 32 := by
  set ε : ℂ := w (j + 1) - (w j + 1) with hε
  have hεle : ‖ε‖ ≤ 1 / 32 := by rw [hε]; exact hstep j hj
  have hdiff : (α * w (j + 1)).im - (α * w j).im = α.im + (α * ε).im := by
    have h2 : α * w (j + 1) - α * w j = α * ε + α := by rw [hε]; ring
    have h3 : (α * w (j + 1) - α * w j).im = α.im + (α * ε).im := by
      rw [h2]; simp only [Complex.add_im]; ring
    rw [Complex.sub_im] at h3
    exact h3
  rw [hdiff]
  have hb : |(α * ε).im| ≤ ‖α‖ * ‖ε‖ := by
    calc |(α * ε).im| ≤ ‖α * ε‖ := Complex.abs_im_le_norm _
      _ = ‖α‖ * ‖ε‖ := norm_mul α ε
  have hb2 : ‖α‖ * ‖ε‖ ≤ ‖α‖ / 32 := by
    have := mul_le_mul_of_nonneg_left hεle (norm_nonneg α)
    linarith
  rw [add_sub_cancel_left]
  linarith [hb, hb2]

/-- Two-sided telescoped drift bounds along the walk. -/
theorem gate_walk_im_sep {α : ℂ} {w : ℕ → ℂ} {n : ℕ}
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32) :
    ∀ j j' : ℕ, j < j' → j' ≤ n →
      (α * w j).im + (α.im - ‖α‖ / 32) * ((j' - j : ℕ) : ℝ) ≤ (α * w j').im ∧
      (α * w j').im ≤ (α * w j).im + (α.im + ‖α‖ / 32) * ((j' - j : ℕ) : ℝ) := by
  refine telescope_step (u := fun j => (α * w j).im) (n := n) (c := α.im - ‖α‖ / 32)
    (d := α.im + ‖α‖ / 32) (fun j hj => ?_)
  have h := gate_walk_im_step (α := α) (w := w) (n := n) hstep hj
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

/-- Room bound: the walk index is controlled by the height and `‖α‖`. -/
private theorem gate_walk_room {Ξ : ℝ} {α : ℂ} {w : ℕ → ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, w j ∈ Work.Pert.Qm Ξ α) :
    ∀ j ≤ n, (j : ℝ) ≤ (32 / 15) * (|(w j).im| + ‖(1 : ℂ) / α‖) := by
  intro j hj
  have hmono := Work.Pert.walk_gate_mono (Ξ := Ξ) (w := w) (n := n) hstep
  have hre := hmono.2.2.2.2.1
  have him := hmono.2.2.2.2.2
  have hrej : (w 0).re + 31 * (j : ℝ) / 32 ≤ (w j).re := hre j hj
  have himj : |(w j).im - (w 0).im| ≤ (j : ℝ) / 32 := him j hj
  have hlow0 : -(w 0).re < |(w 0).im| + 2 * ‖(1 : ℂ) / α‖ :=
    Qm_neg_re_lt hΞ (hgate 0 (Nat.zero_le _))
  have hupj : (w j).re < |(w j).im| := Qm_re_lt_abs_im hΞ (hgate j hj)
  have h0j : |(w 0).im| ≤ |(w j).im| + (j : ℝ) / 32 := by
    have h1 : |(w 0).im| ≤ |(w j).im| + |(w 0).im - (w j).im| := by
      have := abs_add_le ((w j).im) ((w 0).im - (w j).im)
      have he : (w j).im + ((w 0).im - (w j).im) = (w 0).im := by ring
      rwa [he] at this
    rw [abs_sub_comm] at h1
    linarith
  have hnn : (0:ℝ) ≤ ‖(1 : ℂ) / α‖ := norm_nonneg _
  have hfin : 31 * (j : ℝ) / 32 ≤ 2 * |(w j).im| + (j : ℝ) / 32 + 2 * ‖(1 : ℂ) / α‖ := by
    linarith
  linarith

/-- Band location when `|α.im| < ‖α‖/16`: the band index is at most `5/‖α‖`. -/
theorem band_loc_of_small_im {Ξ : ℝ} {α : ℂ} {W : ℕ → ℂ} {n j : ℕ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α)
    (hstep : ∀ i < n, ‖W (i + 1) - (W i + 1)‖ ≤ 1 / 32)
    (hgate : ∀ i ≤ n, W i ∈ Work.Pert.Qm Ξ α) (hj : j ≤ n)
    (him : |α.im| < ‖α‖ / 16) (hband : |(α * W j).im| ≤ gateDelta) :
    (j : ℝ) ≤ 5 / ‖α‖ := by
  have ha_pos : 0 < ‖α‖ := InF1_norm_pos' hInF1
  have hR : ‖(1 : ℂ) / α‖ = 1 / ‖α‖ := norm_one_div_alpha α
  have hdec : (α * W j).im = α.re * (W j).im + α.im * (W j).re := by simp [Complex.mul_im]
  have habil : |α.re * (W j).im| ≤ |(α * W j).im| + |α.im * (W j).re| := by
    have h1 : |α.re * (W j).im|
        = |(α.re * (W j).im + α.im * (W j).re) + (-(α.im * (W j).re))| := by ring_nf
    rw [h1]
    have h2 : |α.re * (W j).im + α.im * (W j).re| = |(α * W j).im| := by rw [hdec]
    have h3 := abs_add_le (α.re * (W j).im + α.im * (W j).re) (-(α.im * (W j).re))
    rw [abs_neg, h2] at h3
    exact h3
  have habre : |α.re * (W j).im| = α.re * |(W j).im| := by
    rw [abs_mul, abs_of_pos (InF1_re_pos' hInF1)]
  have hre_le : |(W j).re| ≤ |(W j).im| + 2 * ‖(1 : ℂ) / α‖ := Qm_abs_re_le hΞ (hgate j hj)
  have him_le : |α.im| ≤ ‖α‖ / 16 := le_of_lt him
  have hkey : α.re * |(W j).im| ≤ gateDelta + (‖α‖ / 16) * (|(W j).im| + 2 * ‖(1 : ℂ) / α‖) := by
    have h2 : |α.im * (W j).re| ≤ (‖α‖ / 16) * (|(W j).im| + 2 * ‖(1 : ℂ) / α‖) := by
      rw [abs_mul]
      calc |α.im| * |(W j).re| ≤ (‖α‖ / 16) * |(W j).re| :=
            mul_le_mul_of_nonneg_right him_le (abs_nonneg _)
        _ ≤ (‖α‖ / 16) * (|(W j).im| + 2 * ‖(1 : ℂ) / α‖) :=
            mul_le_mul_of_nonneg_left hre_le (by positivity)
    have h3 : |(α * W j).im| ≤ gateDelta := hband
    rw [habre] at habil
    linarith [habil, h2, h3]
  have hcoef : (61 / 96) * ‖α‖ ≤ α.re - ‖α‖ / 16 := by
    have h := Work.Pert.InF1_re_ge hInF1
    linarith
  rw [hR] at hkey
  have hmain : (61 / 96) * ‖α‖ * |(W j).im| ≤ gateDelta + 1 / 8 := by
    have h := hkey
    have h2 : (‖α‖ / 16) * (|(W j).im| + 2 * (1 / ‖α‖)) = (‖α‖ / 16) * |(W j).im| + 1 / 8 := by
      field_simp; try ring
    rw [h2] at h
    have hnn : 0 ≤ |(W j).im| := abs_nonneg _
    nlinarith [h, hcoef, hnn, ha_pos]
  have hIm : |(W j).im| ≤ 1 / ‖α‖ := by
    have h1 : gateDelta + 1 / 8 ≤ 1 / 4 := by linarith [gateDelta_le_one_eighth]
    have h2 : (61 / 96 : ℝ) * ‖α‖ * |(W j).im| ≤ 1 / 4 := le_trans hmain h1
    have h3 : (0:ℝ) < (61 / 96) * ‖α‖ := by positivity
    have h4 : |(W j).im| ≤ (1 / 4) / ((61 / 96) * ‖α‖) := by
      rw [le_div_iff₀ h3]
      linarith [h2]
    have h5 : (1 / 4) / ((61 / 96) * ‖α‖) ≤ 1 / ‖α‖ := by
      rw [show (1:ℝ) / 4 / ((61 / 96) * ‖α‖) = 1 / (4 * ((61 / 96) * ‖α‖)) by
            rw [div_div],
          show (1:ℝ) / ‖α‖ = 1 / (1 * ‖α‖) by ring]
      exact one_div_le_one_div_of_le (by nlinarith [ha_pos]) (by nlinarith [ha_pos])
    exact le_trans h4 h5
  have hroom := gate_walk_room hΞ hstep hgate j hj
  rw [hR] at hroom
  have hstep2 : (j : ℝ) ≤ (32 / 15) * (1 / ‖α‖ + 1 / ‖α‖) := by
    have h2 : (32 / 15) * (|(W j).im| + 1 / ‖α‖) ≤ (32 / 15) * (1 / ‖α‖ + 1 / ‖α‖) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith [hIm]
    linarith [hroom, h2]
  have h3 : (32 / 15) * (1 / ‖α‖ + 1 / ‖α‖) = (64 / 15) / ‖α‖ := by ring
  have h4b : (64 / 15 : ℝ) / ‖α‖ ≤ 5 / ‖α‖ := by
    apply div_le_div_of_nonneg_right _ (le_of_lt ha_pos)
    norm_num
  calc (j : ℝ) ≤ (32 / 15) * (1 / ‖α‖ + 1 / ‖α‖) := hstep2
    _ = (64 / 15) / ‖α‖ := h3
    _ ≤ 5 / ‖α‖ := h4b


/-- The real lattice distance is at most the complex one. -/
theorem iInf_re_le_iInf (x : ℂ) :
    (⨅ k : ℤ, dist x.re (k : ℝ)) ≤ (⨅ k : ℤ, dist x (k : ℂ)) := by
  apply le_ciInf
  intro k
  have h1 : dist x.re (k : ℝ) ≤ dist x (k : ℂ) := by
    rw [Real.dist_eq, Complex.dist_eq]
    calc |x.re - (k : ℝ)| = |(x - (k : ℂ)).re| := by simp
      _ ≤ ‖x - (k : ℂ)‖ := Complex.abs_re_le_norm _
  exact le_trans (ciInf_le (f := fun k' : ℤ => dist x.re (k' : ℝ))
    ⟨0, by rintro y ⟨j, rfl⟩; exact dist_nonneg⟩ k) h1

/-- Mid-band per-term bound: in the band `|Im (α w)| ≤ δ ≤ 1`, a single term is at most
`(256/3)‖α‖ / max (15‖α‖) Δ`. -/
theorem band_term_le {α σ : ℂ} {W : ℕ → ℂ} {j : ℕ}
    (hσ : σ ≠ 0) (hσb : ‖σ‖ ≤ 32 * ‖α‖) (ha64 : ‖α‖ ≤ 1 / 64) (ha_pos : 0 < ‖α‖)
    (hcap : ‖Work.Pert.tauC σ α (W j)‖ ≤ 5)
    (hband : |(α * W j).im| ≤ gateDelta)
    (hΔ1 : (⨅ k : ℤ, dist (α * W j) (k : ℂ)) ≤ 1) :
    ‖Work.Pert.tauC σ α (W j) - σ‖
      ≤ (256 / 3) * ‖α‖ / max (15 * ‖α‖) (⨅ k : ℤ, dist (α * W j) (k : ℂ)) := by
  set D : ℝ := ⨅ k : ℤ, dist (α * W j) (k : ℂ) with hD
  have hD1 : D ≤ 1 := by rw [hD]; exact hΔ1
  by_cases hDLE : D ≤ 15 * ‖α‖
  · rw [max_eq_left hDLE]
    have h1 : ‖Work.Pert.tauC σ α (W j) - σ‖ ≤ 5 + 32 * ‖α‖ := by
      have := norm_sub_le (Work.Pert.tauC σ α (W j)) σ
      linarith [hcap, hσb]
    have h2 : 5 + 32 * ‖α‖ ≤ (256 / 3 : ℝ) * ‖α‖ / (15 * ‖α‖) := by
      have h3 : (256 / 3 : ℝ) * ‖α‖ / (15 * ‖α‖) = 256 / 45 := by
        field_simp; try ring
      rw [h3]
      nlinarith [ha64]
    linarith [h1, h2]
  · rw [max_eq_right (le_of_not_ge hDLE)]
    have hDpos : 0 < D := lt_of_lt_of_le (by positivity) (le_of_not_ge hDLE)
    by_cases hE : gateE α (W j) = 1
    · have hτ0 : Work.Pert.tauC σ α (W j) = 0 := by
        simp only [Work.Pert.tauC, gateE] at hE ⊢
        rw [hE, sub_self, div_zero]
      rw [hτ0, zero_sub, norm_neg]
      have h1 : (256 / 3 : ℝ) * ‖α‖ / 1 ≤ (256 / 3) * ‖α‖ / D :=
        div_le_div_of_nonneg_left (by positivity) hDpos hD1
      have h2 : ‖σ‖ ≤ (256 / 3) * ‖α‖ / 1 := by
        have h := hσb
        nlinarith [norm_nonneg α]
      linarith [h1, h2]
    · have hid := tauC_sub_sigma_div (σ := σ) (α := α) (w := W j) hσ hE
      have h1E : (3 / 4) * D ≤ ‖1 - gateE α (W j)‖ := by
        have h := norm_one_sub_gateE_ge α (W j)
        rw [← hD, min_eq_right hD1] at h
        exact h
      have hEnorm : ‖gateE α (W j)‖ ≤ 2 := by
        rw [norm_gateE]
        exact exp_two_pi_le_two (le_trans (le_abs_self _) hband)
      have hnormeq : ‖Work.Pert.tauC σ α (W j) - σ‖
          = ‖σ‖ * ‖gateE α (W j)‖ / ‖1 - gateE α (W j)‖ := by
        rw [hid, norm_div, norm_mul]
      rw [hnormeq]
      have h1Epos : 0 < (3 / 4) * D := by linarith
      have hA : ‖σ‖ * ‖gateE α (W j)‖ ≤ ‖σ‖ * 2 :=
        mul_le_mul_of_nonneg_left hEnorm (norm_nonneg σ)
      have hB : (1 : ℝ) / ‖1 - gateE α (W j)‖ ≤ 1 / ((3 / 4) * D) :=
        one_div_le_one_div_of_le h1Epos h1E
      calc ‖σ‖ * ‖gateE α (W j)‖ / ‖1 - gateE α (W j)‖
          = (‖σ‖ * ‖gateE α (W j)‖) * (1 / ‖1 - gateE α (W j)‖) := by rw [mul_one_div]
        _ ≤ (‖σ‖ * 2) * (1 / ((3 / 4) * D)) := by
            apply mul_le_mul hA hB (by positivity) (by positivity)
        _ = ‖σ‖ * 2 / ((3 / 4) * D) := by rw [mul_one_div]
        _ = (8 / 3) * ‖σ‖ / D := by ring
        _ ≤ (8 / 3) * (32 * ‖α‖) / D :=
            div_le_div_of_nonneg_right (by linarith [hσb]) (le_of_lt hDpos)
        _ = (256 / 3) * ‖α‖ / D := by ring

/-- High-band per-term bound: `Im (α w) ≥ δ` gives `‖E‖ ≥ 2` and a term `≤ 2‖σ‖`. -/
theorem high_term_le {α σ : ℂ} {W : ℕ → ℂ} {j : ℕ} (hσ : σ ≠ 0)
    (hhigh : gateDelta ≤ (α * W j).im) :
    ‖Work.Pert.tauC σ α (W j) - σ‖ ≤ 2 * ‖σ‖ := by
  have hρ : 2 ≤ ‖gateE α (W j)‖ := by
    rw [norm_gateE]
    have h : Real.exp (2 * Real.pi * gateDelta) ≤ Real.exp (2 * Real.pi * (α * W j).im) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    rwa [exp_two_pi_gateDelta] at h
  have hE : gateE α (W j) ≠ 1 := by
    intro h; rw [h, norm_one] at hρ; linarith
  have hid := tauC_sub_sigma_div (σ := σ) (α := α) (w := W j) hσ hE
  have hnormeq : ‖Work.Pert.tauC σ α (W j) - σ‖
      = ‖σ‖ * ‖gateE α (W j)‖ / ‖1 - gateE α (W j)‖ := by rw [hid, norm_div, norm_mul]
  rw [hnormeq]
  have hρpos : 0 < ‖gateE α (W j)‖ := by linarith
  have h1E : ‖gateE α (W j)‖ / 2 ≤ ‖1 - gateE α (W j)‖ := by
    have h := abs_one_sub_norm_le (gateE α (W j))
    rw [abs_le] at h
    linarith [h.1]
  have h2 : ‖σ‖ * ‖gateE α (W j)‖ / ‖1 - gateE α (W j)‖
      ≤ ‖σ‖ * ‖gateE α (W j)‖ / (‖gateE α (W j)‖ / 2) := by
    apply div_le_div_of_nonneg_left (by positivity) (by linarith) h1E
  have h3 : ‖σ‖ * ‖gateE α (W j)‖ / (‖gateE α (W j)‖ / 2) = 2 * ‖σ‖ := by
    field_simp
  linarith [h2, h3]

/-- Low-band per-term bound: `Im (α w) ≤ -δ` gives `‖E‖ ≤ 1/2` and a term `≤ ‖σ‖`. -/
theorem low_term_le {α σ : ℂ} {W : ℕ → ℂ} {j : ℕ} (hσ : σ ≠ 0)
    (hlow : (α * W j).im ≤ -gateDelta) :
    ‖Work.Pert.tauC σ α (W j) - σ‖ ≤ ‖σ‖ := by
  have hρ : ‖gateE α (W j)‖ ≤ 1 / 2 := by
    rw [norm_gateE]
    have h : Real.exp (2 * Real.pi * (α * W j).im) ≤ Real.exp (2 * Real.pi * (-gateDelta)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have h2 : Real.exp (2 * Real.pi * (-gateDelta)) = 1 / 2 := by
      rw [show 2 * Real.pi * (-gateDelta) = -(2 * Real.pi * gateDelta) from by ring, Real.exp_neg,
        exp_two_pi_gateDelta]
      norm_num
    rwa [h2] at h
  have hE : gateE α (W j) ≠ 1 := by
    intro h; rw [h, norm_one] at hρ; linarith
  have hid := tauC_sub_sigma_div (σ := σ) (α := α) (w := W j) hσ hE
  have hnormeq : ‖Work.Pert.tauC σ α (W j) - σ‖
      = ‖σ‖ * ‖gateE α (W j)‖ / ‖1 - gateE α (W j)‖ := by rw [hid, norm_div, norm_mul]
  rw [hnormeq]
  have h1E : 1 - ‖gateE α (W j)‖ ≤ ‖1 - gateE α (W j)‖ := by
    have h := abs_one_sub_norm_le (gateE α (W j))
    rw [abs_le] at h
    linarith [h.2]
  have h1Epos : 0 < 1 - ‖gateE α (W j)‖ := by linarith
  have h2 : ‖σ‖ * ‖gateE α (W j)‖ / ‖1 - gateE α (W j)‖
      ≤ ‖σ‖ * ‖gateE α (W j)‖ / (1 - ‖gateE α (W j)‖) :=
    div_le_div_of_nonneg_left (by positivity) h1Epos h1E
  have h3 : ‖σ‖ * ‖gateE α (W j)‖ / (1 - ‖gateE α (W j)‖) ≤ ‖σ‖ := by
    rw [div_le_iff₀ h1Epos]
    nlinarith [norm_nonneg (gateE α (W j)), norm_nonneg σ]
  linarith [h2, h3]

/-- When `|α.im| ≥ ‖α‖/16` the imaginary part of `α * w ·` grows at rate at least `‖α‖/32`
between any two (ordered) walk indices. -/
theorem im_sep_of_large_im {α : ℂ} {w : ℕ → ℂ} {n : ℕ}
    (hstep : ∀ j < n, ‖w (j + 1) - (w j + 1)‖ ≤ 1 / 32)
    (him : ‖α‖ / 16 ≤ |α.im|) :
    ∀ j j' : ℕ, j < j' → j' ≤ n →
      (‖α‖ / 32) * ((j' - j : ℕ) : ℝ) ≤ |(α * w j').im - (α * w j).im| := by
  intro j j' hlt hj'
  have hsep := gate_walk_im_sep (α := α) (w := w) (n := n) hstep j j' hlt hj'
  rcases le_total 0 α.im with hpos | hneg
  · -- `α.im ≥ 0`
    have h1 : (α * w j').im - (α * w j).im
        ≥ ((j' - j : ℕ) : ℝ) * (α.im - ‖α‖ / 32) := by linarith [hsep.1]
    have h2 : ((j' - j : ℕ) : ℝ) * (α.im - ‖α‖ / 32) ≥ (‖α‖ / 32) * ((j' - j : ℕ) : ℝ) := by
      have h3 : (0:ℝ) ≤ ((j' - j : ℕ) : ℝ) := Nat.cast_nonneg _
      have h4 : α.im - ‖α‖ / 32 ≥ ‖α‖ / 32 := by
        have := him
        rw [abs_of_nonneg hpos] at this
        linarith
      nlinarith [h3, h4]
    rw [abs_of_nonneg (by linarith : 0 ≤ (α * w j').im - (α * w j).im)]
    linarith [h1, h2]
  · -- `α.im ≤ 0`
    have h1 : (α * w j').im - (α * w j).im
        ≤ ((j' - j : ℕ) : ℝ) * (α.im + ‖α‖ / 32) := by
      have h := hsep.2
      rw [mul_comm (α.im + ‖α‖ / 32) ((j' - j : ℕ) : ℝ)] at h
      linarith
    have h2 : ((j' - j : ℕ) : ℝ) * (α.im + ‖α‖ / 32) ≤ -((‖α‖ / 32) * ((j' - j : ℕ) : ℝ)) := by
      have h3 : (0:ℝ) ≤ ((j' - j : ℕ) : ℝ) := Nat.cast_nonneg _
      have h4 : α.im + ‖α‖ / 32 ≤ -(‖α‖ / 32) := by
        have := him
        rw [abs_of_nonpos hneg] at this
        linarith
      nlinarith [h3, h4]
    have h5 : (α * w j').im - (α * w j).im ≤ 0 := by linarith [h1, h2]
    rw [abs_of_nonpos h5]
    linarith [h2, h1]


/-- In the case `|α.im| < ‖α‖/16` the band is contained in `[0, 5/‖α‖]`, whence span and
cardinality bounds. -/
theorem band_facts_small {Ξ : ℝ} {α : ℂ} {W : ℕ → ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (ha64 : ‖α‖ ≤ 1 / 64)
    (hstep : ∀ j < n, ‖W (j + 1) - (W j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, W j ∈ Work.Pert.Qm Ξ α)
    (him : |α.im| < ‖α‖ / 16) :
    (∀ j < n, |(α * W j).im| ≤ gateDelta → ∀ j' < n, |(α * W j').im| ≤ gateDelta →
        |(α * W j).re - (α * W j').re| ≤ 9) ∧
      (((Finset.range n).filter (fun j => |(α * W j).im| ≤ gateDelta)).card : ℝ) * ‖α‖ ≤ 10 := by
  have ha_pos : 0 < ‖α‖ := InF1_norm_pos' hInF1
  set B : Finset ℕ := (Finset.range n).filter (fun j => |(α * W j).im| ≤ gateDelta) with hB
  have hmem : ∀ j, j ∈ B ↔ j < n ∧ |(α * W j).im| ≤ gateDelta := by
    intro j; rw [hB]; simp [Finset.mem_range]
  have hloc : ∀ j < n, |(α * W j).im| ≤ gateDelta → (j : ℝ) ≤ 5 / ‖α‖ :=
    fun j hj hb => band_loc_of_small_im hΞ hInF1 hstep hgate (le_of_lt hj) him hb
  have hone : ∀ j j' : ℕ, j ∈ B → j' ∈ B → j < j' → (α * W j').re - (α * W j).re ≤ 9 := by
    intro j j' hj hj' hlt
    obtain ⟨hjn, hjb⟩ := (hmem j).mp hj
    obtain ⟨hj'n, hj'b⟩ := (hmem j').mp hj'
    have h1 : (j' : ℝ) ≤ 5 / ‖α‖ := hloc j' hj'n hj'b
    have h2 : (j : ℝ) ≤ 5 / ‖α‖ := hloc j hjn hjb
    have h3 : ((j' - j : ℕ) : ℝ) = (j' : ℝ) - (j : ℝ) := by
      rw [Nat.cast_sub (le_of_lt hlt)]
    have h4 : (j' : ℝ) - (j : ℝ) ≤ 5 / ‖α‖ := by linarith
    have h5 := (gate_walk_re_sep (α := α) hInF1 (w := W) (n := n) hstep j j' hlt
      (le_of_lt hj'n)).2
    rw [h3] at h5
    have h6 : (33 / 32) * ‖α‖ * ((j' : ℝ) - (j : ℝ)) ≤ (33 / 32) * ‖α‖ * (5 / ‖α‖) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h7 : (33 / 32 : ℝ) * ‖α‖ * (5 / ‖α‖) = 165 / 32 := by
      field_simp; try ring
    linarith [h5, h6, h7]
  have hlow : ∀ j j' : ℕ, j ∈ B → j' ∈ B → j < j' → 0 ≤ (α * W j').re - (α * W j).re := by
    intro j j' hj hj' hlt
    obtain ⟨hjn, hjb⟩ := (hmem j).mp hj
    obtain ⟨hj'n, hj'b⟩ := (hmem j').mp hj'
    have h5 := (gate_walk_re_sep (α := α) hInF1 (w := W) (n := n) hstep j j' hlt
      (le_of_lt hj'n)).1
    have h6 : 0 ≤ (2 / 3 : ℝ) * ‖α‖ * ((j' - j : ℕ) : ℝ) := by positivity
    linarith [h5, h6]
  constructor
  · intro j hj hb j' hj' hb'
    have hjB : j ∈ B := (hmem j).mpr ⟨hj, hb⟩
    have hj'B : j' ∈ B := (hmem j').mpr ⟨hj', hb'⟩
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · rw [abs_sub_comm, abs_of_nonneg (hlow j j' hjB hj'B hlt)]
      exact hone j j' hjB hj'B hlt
    · rw [heq]; simp
    · rw [abs_of_nonneg (hlow j' j hj'B hjB hgt)]
      exact hone j' j hj'B hjB hgt
  · have hbound : ∀ j ∈ B, (j : ℝ) ≤ 5 / ‖α‖ := by
      intro j hj; obtain ⟨h1, h2⟩ := (hmem j).mp hj; exact hloc j h1 h2
    have hsub : B ⊆ Finset.Icc 0 ⌊5 / ‖α‖⌋₊ := by
      intro j hj
      rw [Finset.mem_Icc]
      refine ⟨Nat.zero_le _, ?_⟩
      rw [Nat.le_floor_iff (by positivity)]
      exact hbound j hj
    have hcard : B.card ≤ ⌊5 / ‖α‖⌋₊ + 1 := by
      calc B.card ≤ (Finset.Icc 0 ⌊5 / ‖α‖⌋₊).card := Finset.card_le_card hsub
        _ = ⌊5 / ‖α‖⌋₊ + 1 := Nat.card_Icc 0 ⌊5 / ‖α‖⌋₊
    have hfloor : ((⌊5 / ‖α‖⌋₊ : ℕ) : ℝ) ≤ 5 / ‖α‖ := Nat.floor_le (by positivity)
    have h2 : (B.card : ℝ) ≤ 5 / ‖α‖ + 1 := by
      have : (B.card : ℝ) ≤ (⌊5 / ‖α‖⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
      linarith
    have h3 : (5 / ‖α‖ + 1) * ‖α‖ ≤ 10 := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt ha_pos), one_mul]
      nlinarith [ha64]
    calc (B.card : ℝ) * ‖α‖ ≤ (5 / ‖α‖ + 1) * ‖α‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg α)
      _ ≤ 10 := h3

/-- In the case `|α.im| ≥ ‖α‖/16` the band is short (length at most `8/‖α‖`), whence span and
cardinality bounds. -/
theorem band_facts_large {Ξ : ℝ} {α : ℂ} {W : ℕ → ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hInF1 : MandelDim.InF1 α) (ha64 : ‖α‖ ≤ 1 / 64)
    (hstep : ∀ j < n, ‖W (j + 1) - (W j + 1)‖ ≤ 1 / 32)
    (hgate : ∀ j ≤ n, W j ∈ Work.Pert.Qm Ξ α)
    (him : ‖α‖ / 16 ≤ |α.im|) :
    (∀ j < n, |(α * W j).im| ≤ gateDelta → ∀ j' < n, |(α * W j').im| ≤ gateDelta →
        |(α * W j).re - (α * W j').re| ≤ 9) ∧
      (((Finset.range n).filter (fun j => |(α * W j).im| ≤ gateDelta)).card : ℝ) * ‖α‖ ≤ 10 := by
  have ha_pos : 0 < ‖α‖ := InF1_norm_pos' hInF1
  set B : Finset ℕ := (Finset.range n).filter (fun j => |(α * W j).im| ≤ gateDelta) with hB
  have hmem : ∀ j, j ∈ B ↔ j < n ∧ |(α * W j).im| ≤ gateDelta := by
    intro j; rw [hB]; simp [Finset.mem_range]
  have hlen : ∀ j ∈ B, ∀ j' ∈ B, j < j' → ((j' - j : ℕ) : ℝ) ≤ 8 / ‖α‖ := by
    intro j hj j' hj' hlt
    obtain ⟨hjn, hjb⟩ := (hmem j).mp hj
    obtain ⟨hj'n, hj'b⟩ := (hmem j').mp hj'
    have h1 : (‖α‖ / 32) * ((j' - j : ℕ) : ℝ) ≤ |(α * W j').im - (α * W j).im| :=
      im_sep_of_large_im (α := α) (w := W) (n := n) hstep him j j' hlt (le_of_lt hj'n)
    have h2 : |(α * W j').im - (α * W j).im| ≤ gateDelta + gateDelta := by
      rw [abs_le]
      constructor <;> linarith [abs_le.mp hjb, abs_le.mp hj'b]
    have h4 : ((j' - j : ℕ) : ℝ) * (‖α‖ / 32) ≤ 1 / 4 := by
      have h5 : gateDelta + gateDelta ≤ 1 / 4 := by
        have := gateDelta_le_one_eighth; linarith
      have h6 : (‖α‖ / 32) * ((j' - j : ℕ) : ℝ) ≤ gateDelta + gateDelta := le_trans h1 h2
      linarith [h6, h5]
    rw [mul_comm] at h4
    rw [le_div_iff₀ (by positivity : (0:ℝ) < ‖α‖)]
    nlinarith [h4, ha_pos]
  have hone : ∀ j j' : ℕ, j ∈ B → j' ∈ B → j < j' → (α * W j').re - (α * W j).re ≤ 9 := by
    intro j j' hj hj' hlt
    obtain ⟨hjn, hjb⟩ := (hmem j).mp hj
    obtain ⟨hj'n, hj'b⟩ := (hmem j').mp hj'
    have hlen' : ((j' - j : ℕ) : ℝ) ≤ 8 / ‖α‖ := hlen j hj j' hj' hlt
    have h5 := (gate_walk_re_sep (α := α) hInF1 (w := W) (n := n) hstep j j' hlt
      (le_of_lt hj'n)).2
    have h6 : (33 / 32) * ‖α‖ * ((j' - j : ℕ) : ℝ) ≤ (33 / 32) * ‖α‖ * (8 / ‖α‖) :=
      mul_le_mul_of_nonneg_left hlen' (by positivity)
    have h7 : (33 / 32 : ℝ) * ‖α‖ * (8 / ‖α‖) = 33 / 4 := by
      field_simp; try ring
    linarith [h5, h6, h7]
  have hlow : ∀ j j' : ℕ, j ∈ B → j' ∈ B → j < j' → 0 ≤ (α * W j').re - (α * W j).re := by
    intro j j' hj hj' hlt
    obtain ⟨hjn, hjb⟩ := (hmem j).mp hj
    obtain ⟨hj'n, hj'b⟩ := (hmem j').mp hj'
    have h5 := (gate_walk_re_sep (α := α) hInF1 (w := W) (n := n) hstep j j' hlt
      (le_of_lt hj'n)).1
    have h6 : 0 ≤ (2 / 3 : ℝ) * ‖α‖ * ((j' - j : ℕ) : ℝ) := by positivity
    linarith [h5, h6]
  constructor
  · intro j hj hb j' hj' hb'
    have hjB : j ∈ B := (hmem j).mpr ⟨hj, hb⟩
    have hj'B : j' ∈ B := (hmem j').mpr ⟨hj', hb'⟩
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · rw [abs_sub_comm, abs_of_nonneg (hlow j j' hjB hj'B hlt)]
      exact hone j j' hjB hj'B hlt
    · rw [heq]; simp
    · rw [abs_of_nonneg (hlow j' j hj'B hjB hgt)]
      exact hone j' j hj'B hjB hgt
  · by_cases hne : B.Nonempty
    · have hj0 : B.min' hne ∈ B := Finset.min'_mem _ _
      have hj1 : B.max' hne ∈ B := Finset.max'_mem _ _
      have hsub : B ⊆ Finset.Icc (B.min' hne) (B.max' hne) := by
        intro j hj
        exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hj, Finset.le_max' _ _ hj⟩
      have hml : B.min' hne ≤ B.max' hne := Finset.min'_le _ _ hj1
      have hcard : B.card ≤ B.max' hne - B.min' hne + 1 := by
        calc B.card ≤ (Finset.Icc (B.min' hne) (B.max' hne)).card := Finset.card_le_card hsub
          _ = B.max' hne + 1 - B.min' hne := Nat.card_Icc (B.min' hne) (B.max' hne)
          _ = B.max' hne - B.min' hne + 1 := by omega
      have hdiff : ((B.max' hne - B.min' hne : ℕ) : ℝ) ≤ 8 / ‖α‖ := by
        rcases eq_or_lt_of_le hml with heq | hlt
        · rw [heq]; simp; positivity
        · exact hlen (B.min' hne) hj0 (B.max' hne) hj1 hlt
      have h2 : (B.card : ℝ) ≤ 8 / ‖α‖ + 1 := by
        have h3 : (B.card : ℝ) ≤ ((B.max' hne - B.min' hne : ℕ) : ℝ) + 1 := by
          exact_mod_cast hcard
        linarith
      have h3 : (8 / ‖α‖ + 1) * ‖α‖ ≤ 10 := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt ha_pos), one_mul]
        nlinarith [ha64]
      calc (B.card : ℝ) * ‖α‖ ≤ (8 / ‖α‖ + 1) * ‖α‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg α)
        _ ≤ 10 := h3
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp

/-- **Core summation.**  Given the two band facts (span bound `9` and `card·‖α‖ ≤ 10`) plus the
`Δ ≤ 1` fact inside the band, the walk sum is bounded by `2^18 (1 + log(2+n+‖z‖) + n‖α‖)`. -/
theorem gate_sum_le_of_band {α σ : ℂ} {W : ℕ → ℂ} {n : ℕ} {z : ℂ}
    (hW0 : W 0 = z) (hInF1 : MandelDim.InF1 α) (hσ : σ ≠ 0)
    (hσb : ‖σ‖ ≤ 32 * ‖α‖) (ha64 : ‖α‖ ≤ 1 / 64)
    (hcap : ∀ j ≤ n, ‖Work.Pert.tauC σ α (W j)‖ ≤ 5)
    (hstep : ∀ j < n, ‖W (j + 1) - (W j + 1)‖ ≤ 1 / 32)
    (hspan : ∀ j < n, |(α * W j).im| ≤ gateDelta → ∀ j' < n, |(α * W j').im| ≤ gateDelta →
        |(α * W j).re - (α * W j').re| ≤ 9)
    (hcard : (((Finset.range n).filter (fun j => |(α * W j).im| ≤ gateDelta)).card : ℝ) * ‖α‖ ≤ 10)
    (hΔ1 : ∀ j < n, |(α * W j).im| ≤ gateDelta → (⨅ k : ℤ, dist (α * W j) (k : ℂ)) ≤ 1) :
    (∑ j ∈ Finset.range n, ‖Work.Pert.tauC σ α (W j) - σ‖)
      ≤ 2 ^ 18 * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * ‖α‖) := by
  classical
  have ha_pos : 0 < ‖α‖ := InF1_norm_pos' hInF1
  set a : ℝ := ‖α‖ with ha
  have ha_p : 0 < a := by rw [ha]; exact ha_pos
  set B : Finset ℕ := (Finset.range n).filter (fun j => |(α * W j).im| ≤ gateDelta) with hB
  set D : ℕ → ℝ := fun j => (⨅ k : ℤ, dist (α * W j) (k : ℂ)) with hD
  have hmem : ∀ j, j ∈ B ↔ j < n ∧ |(α * W j).im| ≤ gateDelta := by
    intro j; rw [hB]; simp [Finset.mem_range]
  -- per-term bound on the band
  have hterm : ∀ j ∈ B, ‖Work.Pert.tauC σ α (W j) - σ‖
      ≤ (256 / 3) * a / max (15 * a) (D j) := by
    intro j hj
    obtain ⟨hjn, hjb⟩ := (hmem j).mp hj
    have h := band_term_le (σ := σ) (W := W) (j := j) hσ hσb ha64 ha_pos
      (hcap j (le_of_lt hjn)) hjb (hΔ1 j hjn hjb)
    simpa [ha, hD] using h
  -- counting bound
  have hcount : ∀ t : ℝ, 0 < t → ((B.filter (fun j => D j ≤ t)).card : ℝ) ≤ 26 * (3 / a * t + 1) := by
    intro t ht
    have hsepB : ∀ j ∈ B, ∀ j' ∈ B, j < j' →
        (α * W j).re + (2 / 3) * a * ((j' - j : ℕ) : ℝ) ≤ (α * W j').re := by
      intro j hj j' hj' hlt
      obtain ⟨hjn, _⟩ := (hmem j).mp hj
      obtain ⟨hj'n, _⟩ := (hmem j').mp hj'
      have hs := (gate_walk_re_sep (α := α) hInF1 (w := W) (n := n) hstep j j' hlt
        (le_of_lt hj'n)).1
      rw [← ha] at hs
      linarith
    have hspanB : ∀ j ∈ B, ∀ j' ∈ B, |(α * W j).re - (α * W j').re| ≤ 9 := by
      intro j hj j' hj'
      obtain ⟨hjn, hjb⟩ := (hmem j).mp hj
      obtain ⟨hj'n, hj'b⟩ := (hmem j').mp hj'
      exact hspan j hjn hjb j' hj'n hj'b
    have hcl := card_band_lattice_le (B := B) (t := fun j => (α * W j).re) (γ := (2 / 3) * a)
      (P := 9) (s := t) (by positivity) (by norm_num) (le_of_lt ht) hspanB hsepB
    by_cases ht1 : t ≤ 1
    · have hsub : B.filter (fun j => D j ≤ t)
          ⊆ B.filter (fun j => (⨅ k : ℤ, dist ((α * W j).re) (k : ℝ)) ≤ t) := by
        intro j hj
        rw [Finset.mem_filter] at hj ⊢
        refine ⟨hj.1, ?_⟩
        have h1 : (⨅ k : ℤ, dist ((α * W j).re) (k : ℝ)) ≤ D j := by
          rw [hD]; exact iInf_re_le_iInf (α * W j)
        linarith [h1, hj.2]
      have h1 : ((B.filter (fun j => D j ≤ t)).card : ℝ)
          ≤ ((B.filter (fun j => (⨅ k : ℤ, dist ((α * W j).re) (k : ℝ)) ≤ t)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have h2 : ((B.filter (fun j => (⨅ k : ℤ, dist ((α * W j).re) (k : ℝ)) ≤ t)).card : ℝ)
          ≤ (9 + 2 * t + 2) * (2 * t / ((2 / 3) * a) + 2) := hcl
      have h3 : (9 + 2 * t + 2) * (2 * t / ((2 / 3) * a) + 2) ≤ 26 * (3 / a * t + 1) := by
        have h4 : 2 * t / ((2 / 3) * a) = 3 / a * t := by
          field_simp; try ring
        rw [h4]
        have h5 : 9 + 2 * t + 2 ≤ 13 := by linarith
        have h6 : 0 ≤ 3 / a * t + 2 := by positivity
        have h7 : 3 / a * t + 2 ≤ 2 * (3 / a * t + 1) := by
          have h8 : 0 ≤ 3 / a * t := by positivity
          linarith
        calc (9 + 2 * t + 2) * (3 / a * t + 2) ≤ 13 * (3 / a * t + 2) :=
              mul_le_mul_of_nonneg_right h5 h6
          _ ≤ 13 * (2 * (3 / a * t + 1)) := mul_le_mul_of_nonneg_left h7 (by norm_num)
          _ = 26 * (3 / a * t + 1) := by ring
      linarith [h1, h2, h3]
    · push_neg at ht1
      have h1 : ((B.filter (fun j => D j ≤ t)).card : ℝ) ≤ (B.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      have h2 : (B.card : ℝ) ≤ 10 / a := by
        rw [le_div_iff₀ ha_p]
        linarith [hcard, ha]
      have h3 : 10 / a ≤ 26 * (3 / a * t + 1) := by
        have h4 : (0:ℝ) < 3 / a := by positivity
        have h5 : 3 / a ≤ 3 / a * t := by
          have h5' := mul_le_mul_of_nonneg_left (le_of_lt ht1) (le_of_lt h4)
          simpa using h5'
        have h6 : 10 / a ≤ 26 * (3 / a) := by
          have h7 : 26 * (3 / a) = 78 / a := by ring
          rw [h7]
          exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt ha_p)
        nlinarith [h5, h6, h4]
      linarith [h1, h2, h3]
  -- the band sum
  have hSB : (∑ j ∈ B, ‖Work.Pert.tauC σ α (W j) - σ‖)
      ≤ 13500 * (1 + Real.log (1 + (B.card : ℝ))) := by
    by_cases hbig : 26 * ((3 / a) * (15 * a) + 1) ≤ (B.card : ℝ)
    · have hlayer := sum_inv_max_le_count_finset (B := B) (d := D) (A := 26) (C := 3 / a)
        (H := 15 * a) (by norm_num) (by positivity) (by positivity)
        (fun i _ => by rw [hD]; exact le_ciInf (fun k => dist_nonneg)) hcount hbig
      have h1 : (∑ j ∈ B, ‖Work.Pert.tauC σ α (W j) - σ‖)
          ≤ (256 / 3) * a * (∑ j ∈ B, 1 / max (15 * a) (D j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        calc ‖Work.Pert.tauC σ α (W j) - σ‖ ≤ (256 / 3) * a / max (15 * a) (D j) := hterm j hj
          _ = (256 / 3) * a * (1 / max (15 * a) (D j)) := by rw [mul_one_div]
      have h2 : (256 / 3) * a * (∑ j ∈ B, 1 / max (15 * a) (D j))
          ≤ (256 / 3) * a * (26 * (3 / a) * (1 + Real.log (1 + (B.card : ℝ) / (26 * (3 / a) * (15 * a))))
              + 26 / (15 * a) + 26 * (3 / a)) :=
        mul_le_mul_of_nonneg_left hlayer (by positivity)
      have h3 : (256 / 3) * a * (26 * (3 / a) * (1 + Real.log (1 + (B.card : ℝ) / (26 * (3 / a) * (15 * a))))
            + 26 / (15 * a) + 26 * (3 / a))
          ≤ 13500 * (1 + Real.log (1 + (B.card : ℝ))) := by
        have ha_ne : a ≠ 0 := ne_of_gt ha_p
        have h4 : 26 * (3 / a) * (15 * a) = 1170 := by field_simp; ring
        rw [h4]
        have h5 : Real.log (1 + (B.card : ℝ) / 1170) ≤ Real.log (1 + (B.card : ℝ)) := by
          apply Real.log_le_log
          · have h7 : (0:ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
            linarith
          · have h7 : (0:ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
            linarith
        have h6 : 0 ≤ Real.log (1 + (B.card : ℝ)) := by
          apply Real.log_nonneg
          have h7 : (0:ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
          linarith
        have hexp : (256 / 3) * a * (26 * (3 / a) * (1 + Real.log (1 + (B.card : ℝ) / 1170))
              + 26 / (15 * a) + 26 * (3 / a))
            = 6656 * (1 + Real.log (1 + (B.card : ℝ) / 1170)) + 6656 / 45 + 6656 := by
          field_simp; try ring
        rw [hexp]
        nlinarith [h5, h6]
      linarith [h1, h2, h3]
    · have h1 : ∀ j ∈ B, ‖Work.Pert.tauC σ α (W j) - σ‖ ≤ 256 / 45 := by
        intro j hj
        have h := hterm j hj
        have h2 : (256 / 3) * a / max (15 * a) (D j) ≤ (256 / 3) * a / (15 * a) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (le_max_left _ _)
        have h3 : (256 / 3) * a / (15 * a) = 256 / 45 := by
          field_simp; try ring
        linarith [h, h2, h3]
      have h2 : (∑ j ∈ B, ‖Work.Pert.tauC σ α (W j) - σ‖) ≤ 256 / 45 * (B.card : ℝ) := by
        calc (∑ j ∈ B, ‖Work.Pert.tauC σ α (W j) - σ‖) ≤ ∑ _j ∈ B, (256 / 45 : ℝ) :=
              Finset.sum_le_sum h1
          _ = 256 / 45 * (B.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      have h3 : (B.card : ℝ) ≤ 1196 := by
        have h4 : (26:ℝ) * ((3 / a) * (15 * a) + 1) = 1196 := by field_simp; ring
        have h5 := not_le.mp hbig
        linarith [h4 ▸ h5]
      have h4 : 256 / 45 * (B.card : ℝ) ≤ 13500 * (1 + Real.log (1 + (B.card : ℝ))) := by
        have h5 : (256 / 45 : ℝ) * 1196 ≤ 13500 := by norm_num
        have h6 : 1 ≤ 1 + Real.log (1 + (B.card : ℝ)) := by
          have h7 : 0 ≤ Real.log (1 + (B.card : ℝ)) := by
            apply Real.log_nonneg
            have h8 : (0:ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
            linarith
          linarith
        nlinarith [h3, h5, h6]
      linarith [h2, h4]
  -- the two end bands
  have hrest : (∑ j ∈ (Finset.range n).filter (fun j => ¬ |(α * W j).im| ≤ gateDelta),
        ‖Work.Pert.tauC σ α (W j) - σ‖) ≤ 96 * (n : ℝ) * a := by
    have hpt : ∀ j ∈ (Finset.range n).filter (fun j => ¬ |(α * W j).im| ≤ gateDelta),
        ‖Work.Pert.tauC σ α (W j) - σ‖ ≤ 2 * ‖σ‖ + ‖σ‖ := by
      intro j hj
      rw [Finset.mem_filter] at hj
      obtain ⟨hjn, hjnb⟩ := hj
      have hcase : gateDelta < (α * W j).im ∨ (α * W j).im < -gateDelta := by
        rw [abs_le] at hjnb
        push_neg at hjnb
        by_cases h : -gateDelta ≤ (α * W j).im
        · exact Or.inl (hjnb h)
        · exact Or.inr (not_le.mp h)
      rcases hcase with hcase | hcase
      · have := high_term_le (α := α) (σ := σ) (W := W) (j := j) hσ (le_of_lt hcase)
        linarith [this, norm_nonneg σ]
      · have := low_term_le (α := α) (σ := σ) (W := W) (j := j) hσ (le_of_lt hcase)
        linarith [this, norm_nonneg σ]
    calc (∑ j ∈ (Finset.range n).filter (fun j => ¬ |(α * W j).im| ≤ gateDelta),
          ‖Work.Pert.tauC σ α (W j) - σ‖)
        ≤ ∑ _j ∈ (Finset.range n).filter (fun j => ¬ |(α * W j).im| ≤ gateDelta),
            (2 * ‖σ‖ + ‖σ‖) := Finset.sum_le_sum hpt
      _ = (2 * ‖σ‖ + ‖σ‖) * (((Finset.range n).filter
            (fun j => ¬ |(α * W j).im| ≤ gateDelta)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ (2 * ‖σ‖ + ‖σ‖) * (n : ℝ) := by
          have h1 : (((Finset.range n).filter (fun j => ¬ |(α * W j).im| ≤ gateDelta)).card : ℕ) ≤ n := by
            have := Finset.card_filter_le (Finset.range n) (fun j => ¬ |(α * W j).im| ≤ gateDelta)
            rwa [Finset.card_range] at this
          have h2 : ((((Finset.range n).filter
              (fun j => ¬ |(α * W j).im| ≤ gateDelta)).card : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast h1
          nlinarith [norm_nonneg σ]
      _ ≤ 96 * (n : ℝ) * a := by
          have h1 : 2 * ‖σ‖ + ‖σ‖ ≤ 96 * a := by linarith [hσb, norm_nonneg σ]
          have h2 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
          have h3 : (2 * ‖σ‖ + ‖σ‖) * (n : ℝ) ≤ (96 * a) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right h1 h2
          linarith [h3]
  -- assembly
  have hlog : Real.log (1 + (B.card : ℝ)) ≤ Real.log (2 + (n : ℝ) + ‖z‖) := by
    apply Real.log_le_log (by positivity)
    have h1 : ((B.card : ℕ) : ℝ) ≤ (n : ℝ) := by
      have h2 : B.card ≤ n := by
        have h3 : B ⊆ Finset.range n := by
          intro j hj
          rw [hB] at hj
          exact (Finset.mem_filter.mp hj).1
        calc B.card ≤ (Finset.range n).card := Finset.card_le_card h3
          _ = n := Finset.card_range n
      exact_mod_cast h2
    have h2 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
    linarith
  have hlog0 : 0 ≤ Real.log (1 + (B.card : ℝ)) := by
    apply Real.log_nonneg
    have h : (0:ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hlog2 : 0 ≤ Real.log (2 + (n : ℝ) + ‖z‖) := by
    apply Real.log_nonneg
    have h : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have h2 : (0:ℝ) ≤ ‖z‖ := norm_nonneg _
    linarith
  have hsplit : (∑ j ∈ Finset.range n, ‖Work.Pert.tauC σ α (W j) - σ‖)
      = (∑ j ∈ B, ‖Work.Pert.tauC σ α (W j) - σ‖)
        + (∑ j ∈ (Finset.range n).filter (fun j => ¬ |(α * W j).im| ≤ gateDelta),
            ‖Work.Pert.tauC σ α (W j) - σ‖) := by
    rw [hB, Finset.sum_filter_add_sum_filter_not]
  rw [hsplit]
  have hfinal : 13500 * (1 + Real.log (1 + (B.card : ℝ)))
      + 96 * (n : ℝ) * a ≤ 2 ^ 18 * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * a) := by
    have h1 : 13500 * (1 + Real.log (1 + (B.card : ℝ)))
        ≤ 2 ^ 18 * (1 + Real.log (2 + (n : ℝ) + ‖z‖)) := by nlinarith [hlog, hlog0, hlog2]
    have h2 : (0:ℝ) ≤ 96 * (n : ℝ) * a := by positivity
    have h3 : (0:ℝ) ≤ (n : ℝ) * a := by positivity
    nlinarith [h1, h2, h3]
  linarith [hSB, hrest, hfinal]

/-- **Main theorem.**  Along a legal walk in the lower gate of a perturbed map, the sum of the
values `‖τ_f w_j - σ‖` is bounded by `2^18 (1 + log(2+n+‖z‖) + n‖α‖)`. -/
theorem gate_walk_sum_y_le {Ξ rr M : ℝ} {α σ : ℂ} {u : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ w ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u w‖ ∧ ‖u w‖ ≤ 2)
    (hτQ : ∀ w ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α w ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ w ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α w - (w + 1)‖ ≤ 1 / 32)
    (hz : z ∈ Work.Pert.Qm Ξ α)
    (hwalk : ∀ j : ℕ, j ≤ n → (Work.Pert.liftF u σ α)^[j] z ∈ Work.Pert.Qm Ξ α) :
    (∑ j ∈ Finset.range n,
        ‖Work.Pert.tauC σ α ((Work.Pert.liftF u σ α)^[j] z) - σ‖)
      ≤ 2 ^ 18 * (1 + Real.log (2 + (n : ℝ) + ‖z‖) + (n : ℝ) * ‖α‖) := by
  classical
  set W : ℕ → ℂ := fun j => (Work.Pert.liftF u σ α)^[j] z with hW
  have hW0 : W 0 = z := by rw [hW]; rfl
  have hstep : ∀ j < n, ‖W (j + 1) - (W j + 1)‖ ≤ 1 / 32 := by
    intro j hj
    have h1 : W (j + 1) = Work.Pert.liftF u σ α (W j) := by
      rw [hW]
      exact Function.iterate_succ_apply' _ _ _
    rw [h1]
    exact hNT (W j) (hwalk j (le_of_lt hj))
  have hgate : ∀ j ≤ n, W j ∈ Work.Pert.Qm Ξ α := by
    intro j hj; rw [hW]; exact hwalk j hj
  have hM1024 : (1024 : ℝ) ≤ M := by
    have h := hM
    norm_num at h ⊢
    exact h
  have ha64 : ‖α‖ ≤ 1 / 64 := by
    have h32 : (64 : ℝ) ≤ 32 * (M + 2 + Ξ) := by nlinarith [hM1024, hΞ]
    exact le_trans hα (one_div_le_one_div_of_le (by norm_num) h32)
  have hσb : ‖σ‖ ≤ 32 * ‖α‖ :=
    Work.Pert.sigma_le_norm_alpha ha64 (hu2 0 (Metric.mem_ball_self hrr)).1 hnorm
  have hcap : ∀ j ≤ n, ‖Work.Pert.tauC σ α (W j)‖ ≤ 5 := fun j hj =>
    Work.Pert.tauC_norm_le_gate_five hΞ ha64 hσ hnorm hu2 hτQ hNT (W j) (hgate j hj)
  have hΔ1 : ∀ j < n, |(α * W j).im| ≤ gateDelta →
      (⨅ k : ℤ, dist (α * W j) (k : ℂ)) ≤ 1 := by
    intro j hj hb
    obtain ⟨m, hm1, hm2⟩ := iInf_dist_eq_norm_sub_round (α * W j)
    rw [hm2]
    have him : |(α * W j - (m : ℂ)).im| ≤ 1 / 8 := by
      rw [Complex.sub_im, Complex.intCast_im, sub_zero]
      exact le_trans hb gateDelta_le_one_eighth
    have hsq : ‖α * W j - (m : ℂ)‖ ^ 2 ≤ 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have h1 : (α * W j - (m : ℂ)).re ^ 2 ≤ 1 / 4 := by
        nlinarith [abs_le.mp hm1]
      have h2 : (α * W j - (m : ℂ)).im ^ 2 ≤ 1 / 64 := by
        nlinarith [abs_le.mp him]
      linarith
    have hnn : 0 ≤ ‖α * W j - (m : ℂ)‖ := norm_nonneg _
    nlinarith [hsq, hnn, sq_nonneg (‖α * W j - (m : ℂ)‖ - 1)]
  by_cases him : |α.im| < ‖α‖ / 16
  · obtain ⟨hspan, hcard⟩ := band_facts_small hΞ hInF1 ha64 hstep hgate him
    exact gate_sum_le_of_band hW0 hInF1 hσ hσb ha64 hcap hstep hspan hcard hΔ1
  · push_neg at him
    obtain ⟨hspan, hcard⟩ := band_facts_large hΞ hInF1 ha64 hstep hgate him
    exact gate_sum_le_of_band hW0 hInF1 hσ hσb ha64 hcap hstep hspan hcard hΔ1

end

end Work.Pert
