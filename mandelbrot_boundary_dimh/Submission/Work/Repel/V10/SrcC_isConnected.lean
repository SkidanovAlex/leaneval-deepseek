import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.lift_dist_half

/-!
# `Work.Repel.SrcC_isConnected` : the source region of a §6 cell is a topological disc

Shishikura §6, Step 3 attaches to each cell `(j, k, n)` (chain level `j`, integer `Re`-translate
`k`, level-0 period index `n`) a *source region* in the level-0 Fatou plane,

  `SrcC j k n = Raw j k ∩ Metric.ball (w_c + n) (1/2)`,

where `Raw j k = {w | s·π w ∈ φ₁ '' (W j + k)}` is the total preimage of the level-1 fibre image
under `π w = e^{2πiw}` and the round box `ball (w_c + n) (1/2)` selects one period.  This file
proves that `SrcC j k n` is **connected** — it is the step that lets the transfer argument run on a
connected island rather than on a possibly split half-open box.

The proof is a bijection

  `V.lift j k n : V.fib j k → V.SrcC j k n`,

with `V.lift j k n u = w_c + n + log (φ₁ u / φ₁ (u_c + k)) / (2πi)`:

* `π (lift u) = φ₁ u / s`, so `lift u ∈ Raw j k`, and `lift u` lies in the round box
  (`Work.Repel.lift_dist_half`: the fibre `W j + k` has diameter `< 1/2` and `‖1/φ₁ + w‖ ≤ η₁/40`
  on `Sm1`, so the ratio `φ₁ u / φ₁ (u_c + k)` is within `1/2` of `1` and its logarithm has modulus
  `< π`);
* conversely, if `w ∈ Raw j k` then `π w = φ₁ u / s = π (lift u)` for some `u ∈ fib j k`, whence
  `w - lift u ∈ ℤ`; as both points lie in the open ball of radius `1/2`, their distance is `< 1`, so
  the integer is `0`.

Since `W j` is connected (`Work.L62.IsChain.open_conn`) and `lift` is continuous on the fibre
(`Complex.log` is continuous where the ratio lives, i.e. in `Metric.ball 1 1 ⊆ slitPlane`), `SrcC`
is the continuous image of a connected set.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

namespace V10

variable (V : V10)

/-- The fibre `V.fib j k = W j + k` is connected: a translate of the connected disc `W j`. -/
theorem fib_isConnected (j : ℕ) (k : ℤ) : IsConnected (V.fib j k) :=
  (V.hIsChain.open_conn j).2.image (fun x : ℂ => x + ((k : ℤ) : ℂ))
    (continuous_id.add continuous_const).continuousOn

/-- The explicit lift is continuous on the fibre: the ratio `φ₁ u / φ₁ (u_c + k)` is continuous
and takes its values in the slit plane (where `Complex.log` is continuous). -/
theorem lift_continuousOn_fib {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1) :
    ContinuousOn (V.lift j k n) (V.fib j k) := by
  have hratio : ContinuousOn
      (fun u => V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) (V.fib j k) :=
    (V.P₁.φ_holo.continuousOn.mono fun u hu => V.Sm1_sub_Dφ (hSm hu)).div_const _
  have hslit : ∀ u ∈ V.fib j k, V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) ∈ slitPlane := by
    intro u hu
    refine ball_one_subset_slitPlane ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have h := V.phi_div_sub_one_le hSm hu (V.uc_fib j k)
    linarith
  have hlog : ContinuousOn
      (fun u => Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))) (V.fib j k) :=
    hratio.clog hslit
  rw [show V.lift j k n = fun u => V.wc j k + ((n : ℤ) : ℂ) +
      Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) / (2 * Real.pi * Complex.I)
      from by funext u; rw [V10.lift]]
  exact continuousOn_const.add (hlog.div_const _)

/-- **The source region of a cell is the image of its fibre under the explicit lift.** -/
theorem SrcC_eq_image_lift {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1) :
    V.SrcC j k n = V.lift j k n '' V.fib j k := by
  ext w
  constructor
  · intro hw
    obtain ⟨hwRaw, hwball⟩ := hw
    obtain ⟨u, hu, hφ⟩ := hwRaw
    refine ⟨u, hu, ?_⟩
    have hpi : MandelDim.piExp (V.lift j k n u) = MandelDim.piExp w := by
      rw [V.lift_piExp (n := n) hSm hu, hφ, mul_div_cancel_left₀ _ V.hs]
    obtain ⟨m, hm⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hpi
    have hwdb : dist w (V.wc j k + ((n : ℤ) : ℂ)) < 1 / 2 := by
      rwa [Metric.mem_ball] at hwball
    have hlfb : dist (V.lift j k n u) (V.wc j k + ((n : ℤ) : ℂ)) < 1 / 2 := by
      rw [dist_eq_norm]
      exact lift_dist_half V (n := n) hSm hu
    have hdist : dist w (V.lift j k n u) < 1 := by
      calc dist w (V.lift j k n u)
          ≤ dist w (V.wc j k + ((n : ℤ) : ℂ)) +
              dist (V.wc j k + ((n : ℤ) : ℂ)) (V.lift j k n u) := dist_triangle _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add hwdb (by rw [dist_comm]; exact hlfb)
        _ = 1 := by norm_num
    have hm_lt : |((m : ℤ) : ℝ)| < 1 := by
      have h : ‖w - V.lift j k n u‖ < 1 := by rwa [dist_eq_norm] at hdist
      rw [show w - V.lift j k n u = -(((m : ℤ)) : ℂ) from by rw [hm]; ring, norm_neg,
        Complex.norm_intCast] at h
      exact h
    have hm0 : m = 0 := by
      have h' : |m| < 1 := by
        rw [← Int.cast_lt (R := ℝ), Int.cast_abs, Int.cast_one]
        simpa using hm_lt
      exact Int.abs_lt_one_iff.mp h'
    simpa [hm0] using hm
  · rintro ⟨u, hu, rfl⟩
    refine ⟨V.lift_mem_Raw (n := n) hSm hu, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    exact lift_dist_half V (n := n) hSm hu

end V10

theorem SrcC_isConnected (V : Work.Repel.V10) {j : ℕ} {k n : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) : IsConnected (V.SrcC j k n) := by
  rw [V10.SrcC_eq_image_lift V hSm]
  exact (V10.fib_isConnected V j k).image (V.lift j k n) (V10.lift_continuousOn_fib V hSm)

end

end Work.Repel
