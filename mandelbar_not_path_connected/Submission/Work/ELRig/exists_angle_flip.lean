/-
# ELRig — the external angle flips across a transversal crossing of the lift

The lemma `Work.ELRig.exists_angle_flip` (requested by the ELRig parity route):

at a point `p = γ₁ s₀` of the lift in the far-left half plane `{Re < -L.R}` at which the real part
of `γ₁` is differentiable with nonvanishing derivative (so that the lift crosses the vertical line
`Re = x₀` transversally at `p` and nowhere else near `p`), the external angle
`θ w = extAngle (dynPhi c d.φ) (Ψ w)` takes values strictly on opposite sides of `α₁` at the two
points `p + iδ` and `p - iδ`, for all small `δ` for which those points are off the two lifts.

The proof is a local argument on the straightening chart `h = sideFlipChart c d fl L s₀` of
`sideFlip_at_ray.lean`:

* `h` is continuous, injective and open on a small ball `ball p ρ`;
* on that ball the zero set of `Im h` is exactly the piece of the lift through `p`
  (`exists_chart_zero_neighbourhood`), which is a single crosscut of the ball
  (`local_data_all`), so that `ball p ρ \ {Im h = 0}` has exactly two components, and the vertical
  rays above and below `p` meet the lift only at `p` (the crossing hypothesis);
* the two rays lie in different components (`crossing_separation`, the pure plane-topology
  crosscut lemma), and since `Im h` is continuous, zero-free off the lift and `h '' ball` is open
  while `h p` is real, the two components are mapped to opposite sides of the real axis
  (`sign_flip_of_two_components`);
* finally `h w = (‖dynPhi (Ψ w)‖ / τ s₀) · exp (2πi (θ w - α₁))`
  (`sideFlipChart_eq_exp`), so the sign of `Im h` is the sign of `sin (2π (θ w - α₁))`, which for
  small `δ` is the sign of `θ w - α₁` (the angles stay within `1/2` of `α₁` by continuity of the
  external angle).
-/
import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.TailBand
import Submission.Work.ELRig.sideFlip_at_ray
import Submission.Work.ELRig.chart_sphere_crossings
import Submission.Work.ELRig.sideFlipChart_open_on_ball
import Submission.Work.ELRig.crossing_separation
import Submission.Work.ELRig.cover_of_crosscut
import Submission.Work.ELRig.local_data_all
import Submission.Work.ELRig.sign_flip_of_two_components
import Submission.Work.ELRig.crosscut_pair_separation
import Submission.Work.Top.extAngle_close_of_Phi_close
import Submission.Work.Top.mem_paramRay_extAngle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
variable {L : RayCylLift d fl}

/-- Multiplying by a positive real preserves negativity. -/
private theorem mul_neg_iff_of_pos_left' {a b : ℝ} (ha : 0 < a) : (a * b < 0 ↔ b < 0) :=
  ⟨fun h => by nlinarith [mul_pos ha (neg_pos.mpr h)], fun h => mul_neg_of_pos_of_neg ha h⟩

/-- **The sign of the imaginary part of the chart is the sign of `extAngle (Ψ ·) - α₁`.**
Off the filled Julia set the chart is `(‖·‖/τ s₀) exp (2πi (θ - α₁))` with a *positive* real
factor, and `sin (2π x)` has the sign of `x` for `|x| < 1/2`. -/
theorem im_sideFlipChart_sign {s₀ : ℝ} {w : ℂ} (hwK : fl.Ψ w ∉ Work.EL.K c)
    (hclose : |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w) - Work.EL.alpha1|
      < 1 / 2) :
    (0 < (Work.ELRig.sideFlipChart c d fl L s₀ w).im ↔
        Work.EL.alpha1 < Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w)) ∧
      ((Work.ELRig.sideFlipChart c d fl L s₀ w).im < 0 ↔
        Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w) < Work.EL.alpha1) := by
  have hnorm : (0 : ℝ) < ‖Work.EL.dynPhi c d.φ (fl.Ψ w)‖ / L.τ s₀ :=
    div_pos (norm_pos_iff.mpr (d.hN.Phi_ne_zero hwK)) (lt_trans zero_lt_one (L.hτ1 s₀))
  have h := sideFlipChart_eq_exp (c := c) (d := d) (fl := fl) (L := L) s₀ w hwK
  have him : (Work.ELRig.sideFlipChart c d fl L s₀ w).im =
      (‖Work.EL.dynPhi c d.φ (fl.Ψ w)‖ / L.τ s₀) *
        Real.sin (2 * Real.pi *
          (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ w) - Work.EL.alpha1)) := by
    rw [h, mul_im_exp_two_pi]
  refine ⟨?_, ?_⟩
  · rw [him, mul_pos_iff_of_pos_left hnorm,
      sin_two_pi_pos _ hclose, sub_pos]
  · rw [him, mul_neg_iff_of_pos_left' hnorm,
      sin_two_pi_neg _ hclose, sub_lt_iff_lt_add, zero_add]

/-- **The external angle is close to `α₁` near the lift**, and `Ψ` misses the filled Julia set
there. -/
theorem exists_extAngle_close {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R) :
    ∃ ε > 0, ∀ q : ℂ, ‖q - L.γ₁ s₀‖ < ε →
      fl.Ψ q ∉ Work.EL.K c ∧
      |Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (fl.Ψ q) - Work.EL.alpha1| < 1 / 2 := by
  have hθ₀ : (0 : ℝ) < Work.EL.alpha1 := by rw [Work.EL.alpha1]; norm_num
  have hθ₁ : Work.EL.alpha1 < 1 := alpha1_mem_Ico.2
  have hR : (1 : ℝ) < L.τ s₀ := L.hτ1 s₀
  obtain ⟨δ, hδpos, hδ⟩ :=
    Work.Top.extAngle_close_of_Phi_close d.hN hθ₀ hθ₁ hR (by norm_num : (0:ℝ) < 1/2)
  have hKp : fl.Ψ (L.γ₁ s₀) ∉ Work.EL.K c := by
    rw [L.hΨ₁ s₀]; exact Work.EL.rayPt_notMem_K d.hN (L.hτ1 s₀)
  have hΦp : Work.EL.dynPhi c d.φ (fl.Ψ (L.γ₁ s₀)) =
      Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀) := by
    rw [L.hΨ₁ s₀]
    exact Work.Top.NakaneData.Phi_rayPt d.hN (L.hτ1 s₀)
  have hcontΦ : ContinuousAt (fun q : ℂ => Work.EL.dynPhi c d.φ (fl.Ψ q)) (L.γ₁ s₀) :=
    ((continuousOn_dynPhi (c := c) (d := d)).continuousAt
      ((Work.ParamRays.isClosed_filledJulia c).isOpen_compl.mem_nhds hKp)).comp
      fl.Ψ_diff.continuous.continuousAt
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.continuousAt_iff.mp hcontΦ δ hδpos
  -- `Ψ` misses `K c` near `p`
  obtain ⟨δ', hδ'pos, hδ'⟩ :=
    Metric.isOpen_iff.mp ((Work.ParamRays.isClosed_filledJulia c).isOpen_compl)
      (fl.Ψ (L.γ₁ s₀)) hKp
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.continuousAt_iff.mp fl.Ψ_diff.continuous.continuousAt δ' hδ'pos
  refine ⟨min ε₁ ε₂, lt_min hε₁pos hε₂pos, fun q hq => ?_⟩
  have hq₁ : dist q (L.γ₁ s₀) < ε₁ :=
    lt_of_lt_of_le (by rwa [dist_eq_norm]) (min_le_left _ _)
  have hq₂ : dist q (L.γ₁ s₀) < ε₂ :=
    lt_of_lt_of_le (by rwa [dist_eq_norm]) (min_le_right _ _)
  have hΨdist : dist (fl.Ψ q) (fl.Ψ (L.γ₁ s₀)) < δ' := hε₂ hq₂
  have hqK : fl.Ψ q ∉ Work.EL.K c := hδ' (Metric.mem_ball.mpr hΨdist)
  refine ⟨hqK, hδ _ hqK ?_⟩
  rw [← hΦp]
  have h := hε₁ hq₁
  rwa [dist_eq_norm] at h

/-- **The external angle flips across a transversal crossing of the lift.** -/
theorem exists_angle_flip (hJ : Work.Top.JordanForm) {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {x₀ : ℝ} (hx : x₀ < -L.R) {s₀ : ℝ} (hs : (L.γ₁ s₀).re = x₀)
    (hcross : deriv (fun t : ℝ => (L.γ₁ t).re) s₀ ≠ 0) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      ((x₀ : ℂ) + ((L.γ₁ s₀).im + δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((x₀ : ℂ) + ((L.γ₁ s₀).im - δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ)
          (fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s₀).im + δ) * Complex.I)) - Work.EL.alpha1) *
        (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ)
          (fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s₀).im - δ) * Complex.I)) - Work.EL.alpha1) < 0 := by
  have hreR : (L.γ₁ s₀).re < -L.R := by rw [hs]; exact hx
  -- **the local data of the lift**
  obtain ⟨ρ₀, hρ₀pos, η, hηpos, hsignw, hmain⟩ := local_data_all (c := c) d fl L hx hs hcross
  -- **the charts' smallness data**
  obtain ⟨εU, hεUpos, hU⟩ := exists_chart_zero_neighbourhood (d := d) (fl := fl) (L := L) hreR
  obtain ⟨εA, hεApos, hA⟩ := exists_extAngle_close (c := c) (d := d) (fl := fl) (L := L) hreR
  obtain ⟨D, hDopen, hpD, hDsub, hDK, -⟩ := exists_local_angle_ray d fl L hreR
  obtain ⟨εD, hεDpos, hεD⟩ := Metric.isOpen_iff.mp hDopen (L.γ₁ s₀) hpD
  -- **the radius `ρ`**
  set ρ : ℝ := min ρ₀ (min εU (min εA εD)) / 2 with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    have h := lt_min hρ₀pos (lt_min hεUpos (lt_min hεApos hεDpos)); linarith
  have hρρ₀ : ρ ≤ ρ₀ := by
    rw [hρdef]; have h := min_le_left ρ₀ (min εU (min εA εD)); linarith
  have hρU : ρ ≤ εU := by
    rw [hρdef]
    have h := min_le_right ρ₀ (min εU (min εA εD))
    have h2 := min_le_left εU (min εA εD); linarith
  have hρA : ρ ≤ εA := by
    rw [hρdef]
    have h := min_le_right ρ₀ (min εU (min εA εD))
    have h2 := min_le_right εU (min εA εD)
    have h3 := min_le_left εA εD; linarith
  have hρD : 2 * ρ ≤ εD := by
    rw [hρdef]
    have h := min_le_right ρ₀ (min εU (min εA εD))
    have h2 := min_le_right εU (min εA εD)
    have h3 := min_le_right εA εD; linarith
  have hmemD : ∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ ρ → w ∈ D :=
    fun w hw => hεD (by rw [Metric.mem_ball, dist_eq_norm]; linarith)
  have hballD : ∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ ρ → fl.Ψ w ∉ Work.EL.K c :=
    fun w hw => hDK w (hmemD w hw)
  have hballDre : ∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ ρ → w.re < -L.R :=
    fun w hw => hDsub (hmemD w hw)
  -- **the arc data**
  obtain ⟨s₁, s₂, hs₁, hs₂, harc_in, hsph₁, hsph₂, harc_out, harc_win⟩ := hmain ρ hρpos hρρ₀
  have hdist_le : ∀ s ∈ Set.Icc s₁ s₂, dist (L.γ₁ s) (L.γ₁ s₀) ≤ ρ := by
    intro s hsmem
    rcases eq_or_lt_of_le hsmem.1 with h | h
    · rw [← h]; exact le_of_eq hsph₁
    rcases eq_or_lt_of_le hsmem.2 with h2 | h2
    · rw [h2]; exact le_of_eq hsph₂
    · exact le_of_lt (harc_in s hsmem (ne_of_gt h) (ne_of_lt h2))
  have hwin : ∀ s ∈ Set.Icc s₁ s₂, |s - s₀| < η := fun s hsmem => harc_win s (hdist_le s hsmem)
  have hsig : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₀ → 0 < ((L.γ₁ s).re - x₀) * (s - s₀) *
      deriv (fun t : ℝ => (L.γ₁ t).re) s₀ :=
    fun s hsmem hsne =>
      hsignw s (abs_pos.mpr (sub_ne_zero.mpr hsne)) (hwin s hsmem)
  have hax : ∀ s ∈ Set.Icc s₁ s₂, s ≠ s₀ → (L.γ₁ s).re ≠ (L.γ₁ s₀).re := by
    intro s hsmem hsne hcon
    have h := hsig s hsmem hsne
    rw [hcon, hs, sub_self, zero_mul, zero_mul] at h
    exact lt_irrefl 0 h
  -- **the sides of the crossing**
  have hside : ((L.γ₁ s₁).re < (L.γ₁ s₀).re ∧ (L.γ₁ s₀).re < (L.γ₁ s₂).re) ∨
      ((L.γ₁ s₀).re < (L.γ₁ s₁).re ∧ (L.γ₁ s₂).re < (L.γ₁ s₀).re) := by
    have hm₁ : s₁ ∈ Set.Icc s₁ s₂ := ⟨le_refl s₁, le_of_lt (lt_trans hs₁ hs₂)⟩
    have hm₂ : s₂ ∈ Set.Icc s₁ s₂ := ⟨le_of_lt (lt_trans hs₁ hs₂), le_refl s₂⟩
    have h1 := hsig s₁ hm₁ (ne_of_lt hs₁)
    have h2 := hsig s₂ hm₂ (ne_of_gt hs₂)
    have hs1s : s₁ - s₀ < 0 := by linarith
    have hs2s : 0 < s₂ - s₀ := by linarith
    rcases lt_or_gt_of_ne hcross with hDneg | hDpos
    · have ha : x₀ < (L.γ₁ s₁).re := by
        by_contra hcon
        have hcon' : (L.γ₁ s₁).re ≤ x₀ := not_lt.mp hcon
        have hAB : 0 ≤ ((L.γ₁ s₁).re - x₀) * (s₁ - s₀) :=
          mul_nonneg_of_nonpos_of_nonpos (by linarith) (le_of_lt hs1s)
        have hpr : ((L.γ₁ s₁).re - x₀) * (s₁ - s₀) * deriv (fun t : ℝ => (L.γ₁ t).re) s₀ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hAB (le_of_lt hDneg)
        exact absurd h1 (not_lt.mpr hpr)
      have hb : (L.γ₁ s₂).re < x₀ := by
        by_contra hcon
        have hcon' : x₀ ≤ (L.γ₁ s₂).re := not_lt.mp hcon
        have hAB : 0 ≤ ((L.γ₁ s₂).re - x₀) * (s₂ - s₀) :=
          mul_nonneg (by linarith) (le_of_lt hs2s)
        have hpr : ((L.γ₁ s₂).re - x₀) * (s₂ - s₀) * deriv (fun t : ℝ => (L.γ₁ t).re) s₀ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hAB (le_of_lt hDneg)
        exact absurd h2 (not_lt.mpr hpr)
      exact Or.inr ⟨by rw [hs]; exact ha, by rw [hs]; exact hb⟩
    · have ha : (L.γ₁ s₁).re < x₀ := by
        by_contra hcon
        have hcon' : x₀ ≤ (L.γ₁ s₁).re := not_lt.mp hcon
        have hAB : ((L.γ₁ s₁).re - x₀) * (s₁ - s₀) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_lt hs1s)
        have hpr : ((L.γ₁ s₁).re - x₀) * (s₁ - s₀) * deriv (fun t : ℝ => (L.γ₁ t).re) s₀ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hAB (le_of_lt hDpos)
        exact absurd h1 (not_lt.mpr hpr)
      have hb : x₀ < (L.γ₁ s₂).re := by
        by_contra hcon
        have hcon' : (L.γ₁ s₂).re ≤ x₀ := not_lt.mp hcon
        have hAB : ((L.γ₁ s₂).re - x₀) * (s₂ - s₀) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hs2s)
        have hpr : ((L.γ₁ s₂).re - x₀) * (s₂ - s₀) * deriv (fun t : ℝ => (L.γ₁ t).re) s₀ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hAB (le_of_lt hDpos)
        exact absurd h2 (not_lt.mpr hpr)
      exact Or.inl ⟨by rw [hs]; exact ha, by rw [hs]; exact hb⟩
  -- **the plane-topology input**
  have hpair := crosscut_pair_separation (p := L.γ₁ s₀) (ρ := ρ) hρpos hs₁ hs₂ L.cont₁
    (fun a _ b _ hab => rayCylLift_injective L hab) rfl harc_in hsph₁ hsph₂ hax hside
  obtain ⟨hsepR, hcovR⟩ := hpair
  -- **the zero set of the chart**
  set Z : Set ℂ := {w : ℂ | w ∈ Metric.ball (L.γ₁ s₀) ρ ∧
    (Work.ELRig.sideFlipChart c d fl L s₀ w).im = 0} with hZdef
  have harc_Z : ∀ w ∈ L.γ₁ '' Set.Icc s₁ s₂,
      (Work.ELRig.sideFlipChart c d fl L s₀ w).im = 0 := by
    rintro _ ⟨s, -, rfl⟩
    rw [sideFlipChart_eq_ofReal]
    exact Complex.ofReal_im _
  have hZarc : Z ⊆ L.γ₁ '' Set.Icc s₁ s₂ := by
    intro w hw
    obtain ⟨hwball, hwim⟩ := hw
    have h1 : ‖w - L.γ₁ s₀‖ < εU := by
      have hb : dist w (L.γ₁ s₀) < ρ := hwball
      rw [dist_eq_norm] at hb
      linarith [hρU]
    obtain ⟨s, hse⟩ := (hU w h1).mp hwim
    have hds : dist (L.γ₁ s) (L.γ₁ s₀) < ρ := by
      rw [hse]
      simpa [Metric.mem_ball] using hwball
    exact ⟨s, ⟨le_of_lt (harc_out s hds).1, le_of_lt (harc_out s hds).2⟩, hse⟩
  have hZsub : Z ⊆ Metric.ball (L.γ₁ s₀) ρ := fun w hw => hw.1
  have hhalf : (0 : ℝ) < ρ / 2 := by linarith
  have hhalfρ : ρ / 2 < ρ := by linarith
  -- **the two poles are off the arc**
  have hpole : ∀ t : ℝ, 0 < t → t ≤ ρ / 2 →
      L.γ₁ s₀ + t * Complex.I ∉ L.γ₁ '' Set.Icc s₁ s₂ ∧
      L.γ₁ s₀ - t * Complex.I ∉ L.γ₁ '' Set.Icc s₁ s₂ := by
    intro t ht htp
    have hltρ : t < ρ := by linarith
    constructor
    · rintro ⟨s, hsmem, hse⟩
      have hd : dist (L.γ₁ s) (L.γ₁ s₀) = t := by
        rw [hse, dist_eq_norm]
        have hzero : (L.γ₁ s₀ + (t : ℂ) * Complex.I) - L.γ₁ s₀ = (t : ℂ) * Complex.I := by ring
        rw [hzero, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos ht]
      have hlt : dist (L.γ₁ s) (L.γ₁ s₀) < ρ := by rw [hd]; exact hltρ
      have hηs : |s - s₀| < η := harc_win s (le_of_lt hlt)
      have hsne : s ≠ s₀ := by
        intro h
        rw [h, dist_self] at hd
        exact absurd hd (ne_of_lt ht)
      have hsg := hsignw s (abs_pos.mpr (sub_ne_zero.mpr hsne)) hηs
      have hre : (L.γ₁ s).re = x₀ := by rw [hse]; simp [hs]
      have hz : ((L.γ₁ s).re - x₀) = 0 := by rw [hre]; ring
      rw [hz, zero_mul, zero_mul] at hsg
      exact absurd hsg (lt_irrefl 0)
    · rintro ⟨s, hsmem, hse⟩
      have hd : dist (L.γ₁ s) (L.γ₁ s₀) = t := by
        rw [hse, dist_eq_norm]
        have hzero : (L.γ₁ s₀ - (t : ℂ) * Complex.I) - L.γ₁ s₀ = -((t : ℂ) * Complex.I) := by ring
        rw [hzero, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos ht]
      have hlt : dist (L.γ₁ s) (L.γ₁ s₀) < ρ := by rw [hd]; exact hltρ
      have hηs : |s - s₀| < η := harc_win s (le_of_lt hlt)
      have hsne : s ≠ s₀ := by
        intro h
        rw [h, dist_self] at hd
        exact absurd hd (ne_of_lt ht)
      have hsg := hsignw s (abs_pos.mpr (sub_ne_zero.mpr hsne)) hηs
      have hre : (L.γ₁ s).re = x₀ := by rw [hse]; simp [hs]
      have hz : ((L.γ₁ s).re - x₀) = 0 := by rw [hre]; ring
      rw [hz, zero_mul, zero_mul] at hsg
      exact absurd hsg (lt_irrefl 0)
  -- **the hypotheses of the sign-flip lemma**
  have hcontOn : ContinuousOn (Work.ELRig.sideFlipChart c d fl L s₀)
      (Metric.ball (L.γ₁ s₀) ρ) := by
    change ContinuousOn (fun w : ℂ => Work.EL.dynPhi c d.φ (fl.Ψ w) /
      Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)) (Metric.ball (L.γ₁ s₀) ρ)
    have h1 : ContinuousOn (fun w : ℂ => Work.EL.dynPhi c d.φ (fl.Ψ w))
        (Metric.ball (L.γ₁ s₀) ρ) :=
      (continuousOn_dynPhi (c := c) (d := d)).comp fl.Ψ_diff.continuous.continuousOn
        (fun w hw => hballD w (le_of_lt (by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw)))
    exact h1.div_const (Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀))
  have hopen : ∀ s : Set ℂ, IsOpen s → s ⊆ Metric.ball (L.γ₁ s₀) ρ →
      IsOpen ((Work.ELRig.sideFlipChart c d fl L s₀) '' s) :=
    sideFlipChart_open_on_ball d fl L hreR hρpos hballDre hballD
  have hpZ : L.γ₁ s₀ ∈ Z := by
    refine ⟨Metric.mem_ball_self hρpos, ?_⟩
    rw [sideFlipChart_at_p]; simp
  have hZero : ∀ w ∈ Metric.ball (L.γ₁ s₀) ρ,
      ((Work.ELRig.sideFlipChart c d fl L s₀ w).im = 0 ↔ w ∈ Z) := by
    intro w hw
    simp only [hZdef, Set.mem_setOf_eq]
    exact ⟨fun h => ⟨hw, h⟩, fun h => h.2⟩
  have hvray : ∀ t : ℝ, 0 < t → t ≤ ρ / 2 →
      L.γ₁ s₀ + t * Complex.I ∉ Z ∧ L.γ₁ s₀ - t * Complex.I ∉ Z := by
    intro t ht htp
    obtain ⟨ha, hb⟩ := hpole t ht htp
    exact ⟨fun h => ha (hZarc h), fun h => hb (hZarc h)⟩
  have hsepZ : ¬ JoinedIn (Metric.ball (L.γ₁ s₀) ρ \ Z) (L.γ₁ s₀ + (ρ / 2) * Complex.I)
      (L.γ₁ s₀ - (ρ / 2) * Complex.I) := by
    rintro ⟨γp, hγp⟩
    apply hsepR
    refine ⟨γp, fun t => ⟨(hγp t).1, fun harc => (hγp t).2 ?_⟩⟩
    exact ⟨(hγp t).1, harc_Z (γp t) harc⟩
  have hcoverZ : ∀ w ∈ Metric.ball (L.γ₁ s₀) ρ \ Z,
      JoinedIn (Metric.ball (L.γ₁ s₀) ρ \ Z) w (L.γ₁ s₀ + (ρ / 2) * Complex.I) ∨
      JoinedIn (Metric.ball (L.γ₁ s₀) ρ \ Z) w (L.γ₁ s₀ - (ρ / 2) * Complex.I) := by
    intro w hw
    have hw' : w ∈ Metric.ball (L.γ₁ s₀) ρ \ (L.γ₁ '' Set.Icc s₁ s₂) :=
      ⟨hw.1, fun harc => hw.2 ⟨hw.1, harc_Z w harc⟩⟩
    rcases hcovR w hw' with h | h
    · rcases h with ⟨γp, hγp⟩
      exact Or.inl ⟨γp, fun t => ⟨(hγp t).1, fun htZ => (hγp t).2 (hZarc htZ)⟩⟩
    · rcases h with ⟨γp, hγp⟩
      exact Or.inr ⟨γp, fun t => ⟨(hγp t).1, fun htZ => (hγp t).2 (hZarc htZ)⟩⟩
  -- rewrite the two special points into the `↑(ρ/2)` normal form
  have hsepZ' : ¬ JoinedIn (Metric.ball (L.γ₁ s₀) ρ \ Z)
      (L.γ₁ s₀ + (((ρ / 2 : ℝ)) : ℂ) * Complex.I)
      (L.γ₁ s₀ - (((ρ / 2 : ℝ)) : ℂ) * Complex.I) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hsepZ
  have hcoverZ' : ∀ w ∈ Metric.ball (L.γ₁ s₀) ρ \ Z,
      JoinedIn (Metric.ball (L.γ₁ s₀) ρ \ Z) w
        (L.γ₁ s₀ + (((ρ / 2 : ℝ)) : ℂ) * Complex.I) ∨
      JoinedIn (Metric.ball (L.γ₁ s₀) ρ \ Z) w
        (L.γ₁ s₀ - (((ρ / 2 : ℝ)) : ℂ) * Complex.I) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hcoverZ
  -- **the sign flip**
  have hflip := sign_flip_of_two_components (p := L.γ₁ s₀) (ρ := ρ) (δ₀ := ρ / 2)
    hρpos hhalf hhalfρ hpZ hZsub hcontOn hopen hZero hvray hcoverZ' hsepZ'
  -- **assembly**
  refine ⟨min (ρ / 2) εA, lt_min hhalf hεApos, fun δ hδ0 hδε hq₁ hq₂ => ?_⟩
  have hδρ : δ < ρ / 2 := lt_of_lt_of_le hδε (min_le_left _ _)
  have hδεA : δ < εA := lt_of_lt_of_le hδε (min_le_right _ _)
  have hqp₁ : (x₀ : ℂ) + ((L.γ₁ s₀).im + δ) * Complex.I = L.γ₁ s₀ + δ * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hs] <;> ring
  have hqp₂ : (x₀ : ℂ) + ((L.γ₁ s₀).im - δ) * Complex.I = L.γ₁ s₀ - δ * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hs] <;> ring
  have him := hflip δ hδ0 hδρ
  have hnorm₁ : ‖(L.γ₁ s₀ + δ * Complex.I) - L.γ₁ s₀‖ < εA := by
    have hz : (L.γ₁ s₀ + δ * Complex.I) - L.γ₁ s₀ = (δ : ℂ) * Complex.I := by ring
    rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ0]
    exact hδεA
  have hnorm₂ : ‖(L.γ₁ s₀ - δ * Complex.I) - L.γ₁ s₀‖ < εA := by
    have hz : (L.γ₁ s₀ - δ * Complex.I) - L.γ₁ s₀ = -((δ : ℂ) * Complex.I) := by ring
    rw [hz, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ0]
    exact hδεA
  obtain ⟨hK₁, hA₁⟩ := hA (L.γ₁ s₀ + δ * Complex.I) hnorm₁
  obtain ⟨hK₂, hA₂⟩ := hA (L.γ₁ s₀ - δ * Complex.I) hnorm₂
  rw [mul_neg_iff] at him
  rcases him with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : 0 < Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ)
        (fl.Ψ (L.γ₁ s₀ + δ * Complex.I)) - Work.EL.alpha1 :=
      sub_pos.mpr ((im_sideFlipChart_sign (s₀ := s₀) hK₁ hA₁).1.mp h1)
    have e2 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ)
        (fl.Ψ (L.γ₁ s₀ - δ * Complex.I)) - Work.EL.alpha1 < 0 :=
      sub_neg.mpr ((im_sideFlipChart_sign (s₀ := s₀) hK₂ hA₂).2.mp h2)
    rw [hqp₁, hqp₂]
    exact mul_neg_of_pos_of_neg e1 e2
  · have e1 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ)
        (fl.Ψ (L.γ₁ s₀ + δ * Complex.I)) - Work.EL.alpha1 < 0 :=
      sub_neg.mpr ((im_sideFlipChart_sign (s₀ := s₀) hK₁ hA₁).2.mp h1)
    have e2 : 0 < Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ)
        (fl.Ψ (L.γ₁ s₀ - δ * Complex.I)) - Work.EL.alpha1 :=
      sub_pos.mpr ((im_sideFlipChart_sign (s₀ := s₀) hK₂ hA₂).1.mp h2)
    rw [hqp₁, hqp₂]
    exact mul_neg_of_neg_of_pos e1 e2

end Work.ELRig
