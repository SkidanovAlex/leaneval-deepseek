import Mathlib
import Submission.Work.TMComp.MAnalytic.strip_diffContOnCl
import Submission.Work.TMComp.MAnalytic.strip_boundary
import Submission.Work.TMComp.MAnalytic.exp_rpow_interp_le

namespace Work.TMComp.MAnalytic

/-- **Annulus step** (Hadamard three-circles type).  If `g` is analytic on a neighbourhood of the
closed ball `B(a, 2R)`, bounded by `1` on `B(a, 2R)` and by `exp(-δ)` on `B(a, R)`, then it is
bounded by `exp(-δ/2)` on the ball `B(a, R√2)`.

The proof transports the statement to the vertical strip `log R ≤ re ≤ log(2R)` via the
exponential map `w ↦ a + exp w` and applies Hadamard's three-lines theorem there. -/
theorem annulus_step {W : Set ℂ} {a : ℂ} {R δ : ℝ} (hR : 0 < R) (hδ : 0 ≤ δ)
    {g : ℂ → ℂ} (han : AnalyticOnNhd ℂ g W) (hball : Metric.closedBall a (2 * R) ⊆ W)
    (hbd : ∀ z ∈ Metric.closedBall a (2 * R), ‖g z‖ ≤ 1)
    (hsm : ∀ z ∈ Metric.closedBall a R, ‖g z‖ ≤ Real.exp (-δ)) :
    ∀ z ∈ Metric.closedBall a (R * Real.sqrt 2), ‖g z‖ ≤ Real.exp (-(δ / 2)) := by
  intro z hz
  by_cases hle : ‖z - a‖ ≤ R
  · -- `z` is already in the small ball
    have hzR : z ∈ Metric.closedBall a R := by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hle
    exact (hsm z hzR).trans (Real.exp_le_exp.mpr (by linarith))
  · -- `R < ‖z - a‖ ≤ R√2`: work on the strip through the exponential map
    push_neg at hle
    have hzle : ‖z - a‖ ≤ R * Real.sqrt 2 := by
      have h := hz; rw [Metric.mem_closedBall, dist_eq_norm] at h; exact h
    have hρpos : 0 < ‖z - a‖ := lt_trans hR hle
    have hzm : z - a ≠ 0 := by
      intro h; rw [h, norm_zero] at hρpos; exact (lt_irrefl 0) hρpos
    set w : ℂ := Complex.log (z - a) with hwdef
    have hexpw : Complex.exp w = z - a := by rw [hwdef]; exact Complex.exp_log hzm
    have hwre : w.re = Real.log ‖z - a‖ := by rw [hwdef, Complex.log_re]
    have hmem : w ∈ Complex.HadamardThreeLines.verticalClosedStrip
        (Real.log R) (Real.log (2 * R)) := by
      rw [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc, hwre]
      constructor
      · exact le_of_lt (Real.log_lt_log hR hle)
      · apply Real.log_le_log hρpos
        calc ‖z - a‖ ≤ R * Real.sqrt 2 := hzle
          _ ≤ 2 * R := by
              have h2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
              nlinarith [h2, hR]
    have hd : DiffContOnCl ℂ (fun w : ℂ => g (a + Complex.exp w))
        (Complex.HadamardThreeLines.verticalStrip (Real.log R) (Real.log (2 * R))) :=
      strip_diffContOnCl hR han hball
    obtain ⟨hB, ha, hb⟩ :=
      strip_boundary (W := Set.univ) (g := g) (a := a) (R := R) (δ := δ) hR hbd hsm
    have h3 := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
      (f := fun w : ℂ => g (a + Complex.exp w)) (z := w) (a := Real.exp (-δ)) (b := 1)
      (Real.log_lt_log hR (by linarith)) hmem hd hB ha hb
    have hsz : a + Complex.exp w = z := by rw [hexpw]; ring
    rw [hsz] at h3
    have hsimp : (Real.exp (-δ)) ^ (1 - (w.re - Real.log R) / (Real.log (2 * R) - Real.log R))
          * (1 : ℝ) ^ ((w.re - Real.log R) / (Real.log (2 * R) - Real.log R))
        = (Real.exp (-δ)) ^
            (1 - (Real.log ‖z - a‖ - Real.log R) / (Real.log (2 * R) - Real.log R)) := by
      rw [Real.one_rpow, mul_one, hwre]
    rw [hsimp] at h3
    exact h3.trans (exp_rpow_interp_le hR hρpos hzle hδ)

end Work.TMComp.MAnalytic
