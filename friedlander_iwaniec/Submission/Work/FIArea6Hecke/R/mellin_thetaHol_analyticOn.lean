import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.R.thetaHol_meas_li
import Submission.Work.FIArea6Hecke.R.thetaHol_zero_basic

namespace Work.FIArea6Hecke.R

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open Work.FIArea5.S16Hecke

noncomputable section

/-- **`thetaOdd χ 0` is `O(u ^ (-b))` at `0⁺` for every `b`**, as a consequence of the
`O(e^{-δ/u})` decay near `0` (`hci_thetaOdd_decay_small`). -/
lemma thetaOdd_zero_isBigO_rpow (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) (h0 : gaussSum d chi 0 = 0) (b : ℝ) :
    thetaOdd chi 0 =O[𝓝[>] (0:ℝ)] (fun u : ℝ => u ^ (-b)) := by
  obtain ⟨C, δ, hCpos, hδpos, hdec⟩ :=
    hci_thetaOdd_decay_small d hd chi 0 hchi (Or.inl h0)
  have h1 : thetaOdd chi 0 =O[𝓝[>] (0:ℝ)] (fun u : ℝ => Real.exp (-δ / u)) := by
    refine IsBigO.of_bound (max C 1) ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by positivity : (0:ℝ) < 1 / ((4 * (d:ℝ)) ^ 2)))]
      with u hu hu2
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (hdec u hu (le_of_lt hu2)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))
  have h2 : (fun u : ℝ => Real.exp (-δ / u)) =O[𝓝[>] (0:ℝ)] (fun u : ℝ => u ^ (-b)) :=
    hci_exp_neg_div_isBigO_rpow_neg δ hδpos b
  exact h1.trans h2

/-- Pointwise splitting `thetaHol χ 0 = (unitSum χ 0)⁻¹ · thetaOdd χ 0` (`m = 0` case of
`hci_thetaHol_eq_inv_unitSum_mul`). -/
lemma thetaHol_zero_eq_const_mul_thetaOdd (d : ℕ) (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) (hU : unitSum chi 0 ≠ 0) :
    thetaHol chi 0 = fun u : ℝ => (unitSum chi 0)⁻¹ * thetaOdd chi 0 u := by
  funext u
  exact hci_thetaHol_eq_inv_unitSum_mul chi 0 hchi.1.2.1 hU u

/-- `thetaHol χ 0` is `O(e^{-π u})` at `+∞`. -/
lemma thetaHol_zero_isBigO_atTop (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict d chi) :
    thetaHol chi 0 =O[atTop] (fun u : ℝ => Real.exp (-Real.pi * u)) := by
  obtain ⟨-, C, u₀, hu₀, hbnd⟩ := thetaHol_zero_basic (d := d) hd hchi
  refine IsBigO.of_bound (max C 1) ?_
  filter_upwards [eventually_ge_atTop u₀] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (hbnd u hu).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))

/-- **`z ↦ mellin (thetaHol χ 0) z` is entire.**  For a strict character `χ` modulo `4d`
(`IsCharMod4dStrict d χ`) with non-zero unit sum and vanishing `0`-th Gauss sum, the Mellin
transform of the holomorphic theta series `thetaHol χ 0` is an entire function of `z`.

The three inputs to Mathlib's `mellin_differentiableAt_of_isBigO_rpow_exp` (at each `s`, with
`b = s.re - 1`) are: local integrability on `(0,∞)` (`thetaHol_meas_li`), exponential decay at
`+∞` (`thetaHol_zero_basic`), and `O(u^{-b})` at `0⁺`, which is reduced to the `e^{-δ/u}` decay of
`thetaOdd` via the pointwise identity `thetaHol χ 0 = (unitSum χ 0)⁻¹ · thetaOdd χ 0` and
`hci_exp_neg_div_isBigO_rpow_neg`. -/
theorem mellin_thetaHol_analyticOn (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hU : Work.FIArea5.S16Hecke.unitSum chi 0 ≠ 0)
    (h0 : Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0) :
    AnalyticOn ℂ (fun z : ℂ => mellin (Work.FIArea5.S16Hecke.thetaHol chi 0) z) Set.univ := by
  have hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have hli : LocallyIntegrableOn (thetaHol chi 0) (Set.Ioi 0) :=
    (thetaHol_meas_li (chi := chi) (m := 0) hb).2
  have htop : thetaHol chi 0 =O[atTop] (fun u : ℝ => Real.exp (-Real.pi * u)) :=
    thetaHol_zero_isBigO_atTop d hd chi hchi
  have hbot : ∀ b : ℝ, thetaHol chi 0 =O[𝓝[>] (0:ℝ)] (fun u : ℝ => u ^ (-b)) := by
    intro b
    rw [thetaHol_zero_eq_const_mul_thetaOdd d chi hchi hU]
    exact (thetaOdd_zero_isBigO_rpow d hd chi hchi h0 b).const_mul_left _
  rw [Complex.analyticOn_univ_iff_differentiable]
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp (a := Real.pi) Real.pi_pos hli htop
    (hbot (s.re - 1)) (by linarith)

end

end Work.FIArea6Hecke.R
