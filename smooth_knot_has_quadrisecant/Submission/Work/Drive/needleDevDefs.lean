import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.cInfKnot

/-!
# The deviation of the retained arcs, and its Green representation

For the chord sweep `Work.Drive.sweepArc'` / `Work.Drive.sweepChord'` of a band arc `D` at sweep
parameter `σ`, the **deviation** of the retained arc from its chord at fraction `ξ` is

  `dev r D σ ξ = r (taR D σ + ξ * sweepW' D σ) - ((1 - ξ) • r (taR D σ) + ξ • r (tbR D σ))`.

Its primitive `devPrim r D σ` is `s ↦ r (taR D σ + s * sweepW' D σ) - r (taR D σ) - s • (w • v)`
(the deviation of the chord from its tangent at the base), and the key identity of this module is
the **Green representation** of `dev`: with `G(ξ,u) = (ξ - u)⁺ - ξ(1 - u) ≤ 0`,

  `dev r D σ ξ = ∫ u in 0..1, G(ξ,u) • (W² • accel r (a + u W))`.

The kernel is nonpositive on the unit square, and strictly negative on `(0,1)²`; hence an
`n`-component of the acceleration of one sign along the whole retained arc gives an `n`-component
of the deviation of the opposite sign (same `n`), with the accompanying `dev_inner_neg` below.
This is the mechanism by which the *needle* (the σ-average of these arcs) is made one-sided: see
`Submission/Work/Drive/NOTES_needleStarShaped_data.md`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology

/-- **The deviation** of the retained arc at sweep parameter `σ` from its chord, at fraction `ξ`. -/
def dev (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (σ ξ : ℝ) : Space :=
  sweepArc' r D σ ξ - sweepChord' r D σ ξ

@[simp] lemma dev_apply (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (σ ξ : ℝ) :
    dev r D σ ξ = r (taR D σ + ξ * sweepW' D σ)
      - ((1 - ξ) • r (taR D σ) + ξ • r (tbR D σ)) := rfl

/-- The primitive of the deviation: `s ↦ r (a + s w) - r a - s • (w • velocity r a)`.  Its
`ξ`-difference against `ξ • devPrim 1` is `dev`. -/
def devPrim (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (σ : ℝ) : ℝ → Space :=
  (fun y : ℝ => r (taR D σ + y * sweepW' D σ)) - (fun _ : ℝ => r (taR D σ))
    - (fun y : ℝ => y • (sweepW' D σ • velocity r (taR D σ)))

@[simp] lemma devPrim_zero (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (σ : ℝ) :
    devPrim r D σ 0 = 0 := by
  simp [devPrim]

/-- The deviation is the difference of the primitive against its value at `1`. -/
lemma dev_eq_devPrim (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (σ ξ : ℝ) :
    dev r D σ ξ = devPrim r D σ ξ - ξ • devPrim r D σ 1 := by
  have h1 : taR D σ + 1 * sweepW' D σ = tbR D σ := by rw [sweepW']; ring
  rw [dev, sweepArc', sweepChord', devPrim]
  simp only [Pi.sub_apply]
  rw [h1]
  module

lemma hasDerivAt_devPrim {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (σ s : ℝ) :
    HasDerivAt (devPrim r D σ)
      (sweepW' D σ • velocity r (taR D σ + s * sweepW' D σ)
        - sweepW' D σ • velocity r (taR D σ)) s := by
  have hlin : HasDerivAt (fun s : ℝ => taR D σ + s * sweepW' D σ) (sweepW' D σ) s := by
    have h := ((hasDerivAt_id s).mul_const (sweepW' D σ)).const_add (taR D σ)
    simpa using h
  have hdiffr : DifferentiableAt ℝ r (taR D σ + s * sweepW' D σ) :=
    (hr.smooth.differentiable (by simp)).differentiableAt
  have hcomp : HasDerivAt (fun y : ℝ => r (taR D σ + y * sweepW' D σ))
      (sweepW' D σ • velocity r (taR D σ + s * sweepW' D σ)) s :=
    (hdiffr.hasDerivAt).scomp s hlin
  have hc : HasDerivAt (fun _ : ℝ => r (taR D σ)) (0 : Space) s := hasDerivAt_const s _
  have hsm : HasDerivAt (fun y : ℝ => y • (sweepW' D σ • velocity r (taR D σ)))
      ((1:ℝ) • (sweepW' D σ • velocity r (taR D σ))) s :=
    (hasDerivAt_id s).smul_const (sweepW' D σ • velocity r (taR D σ))
  have h2 := (hcomp.sub hc).sub hsm
  simpa [one_smul, devPrim] using h2

lemma deriv_devPrim {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (σ : ℝ) :
    deriv (devPrim r D σ) =
      fun u : ℝ => sweepW' D σ • velocity r (taR D σ + u * sweepW' D σ)
        - sweepW' D σ • velocity r (taR D σ) := by
  funext u; exact (hasDerivAt_devPrim hr D σ u).deriv

lemma hasDerivAt_deriv_devPrim {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (σ s : ℝ) :
    HasDerivAt (deriv (devPrim r D σ))
      ((sweepW' D σ)^2 • deriv (velocity r) (taR D σ + s * sweepW' D σ)) s := by
  rw [deriv_devPrim hr D σ]
  have hlin : HasDerivAt (fun s : ℝ => taR D σ + s * sweepW' D σ) (sweepW' D σ) s := by
    have h := ((hasDerivAt_id s).mul_const (sweepW' D σ)).const_add (taR D σ)
    simpa using h
  have hderivCin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    exact ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := r)).mp hs).2
  have hdiffv : DifferentiableAt ℝ (velocity r) (taR D σ + s * sweepW' D σ) :=
    (hderivCin.differentiable (by simp)).differentiableAt
  have hcomp : HasDerivAt (fun u : ℝ => velocity r (taR D σ + u * sweepW' D σ))
      (sweepW' D σ • deriv (velocity r) (taR D σ + s * sweepW' D σ)) s :=
    (hdiffv.hasDerivAt).scomp s hlin
  have h1 := hcomp.const_smul (sweepW' D σ)
  have h2 := h1.sub_const (sweepW' D σ • velocity r (taR D σ))
  have h3 : (sweepW' D σ • (sweepW' D σ • deriv (velocity r) (taR D σ + s * sweepW' D σ)))
      = (sweepW' D σ)^2 • deriv (velocity r) (taR D σ + s * sweepW' D σ) := by
    rw [smul_smul]; ring_nf
  rw [h3] at h2
  simpa using h2

/-- **The Green representation of the deviation.**  The deviation equals the integral of the
second-order Green kernel `(ξ - u)⁺ - ξ(1 - u) ≤ 0` against `W²` times the acceleration along the
retained arc. -/
theorem dev_green {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {σ ξ : ℝ} (hξ : ξ ∈ Set.Icc (0:ℝ) 1) :
    dev r D σ ξ =
      ∫ u in (0:ℝ)..1, (max (ξ - u) 0 - ξ * (1 - u)) •
        ((sweepW' D σ)^2 • deriv (velocity r) (taR D σ + u * sweepW' D σ)) := by
  rw [dev_eq_devPrim]
  set w : ℝ := sweepW' D σ with hw
  set G : ℝ → Space := fun u => w^2 • deriv (velocity r) (taR D σ + u * w) with hG
  have hacc : Continuous (fun u : ℝ => deriv (velocity r) (taR D σ + u * w)) := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    have hderivCin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) :=
      ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := r)).mp hs).2
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv r)) :=
      ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := deriv r)).mp hderivCin).2
    exact h2.continuous.comp (by fun_prop)
  have hGcont : Continuous G := by rw [hG]; exact hacc.const_smul (w^2)
  have hGi : ∀ s, IntervalIntegrable G volume (0:ℝ) s := fun s => hGcont.intervalIntegrable 0 s
  have huG : Continuous (fun u : ℝ => u • G u) := continuous_id.smul hGcont
  have huGi : ∀ s, IntervalIntegrable (fun u => u • G u) volume (0:ℝ) s :=
    fun s => huG.intervalIntegrable 0 s
  have hA : ∀ s, HasDerivAt (fun t : ℝ => ∫ u in (0:ℝ)..t, G u) (G s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right (hGi s)
      (hGcont.stronglyMeasurableAtFilter volume (nhds s)) hGcont.continuousAt
  have hB : ∀ s, HasDerivAt (fun t : ℝ => ∫ u in (0:ℝ)..t, u • G u) (s • G s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right (huGi s)
      (huG.stronglyMeasurableAtFilter volume (nhds s)) huG.continuousAt
  have hHrep : ∀ s, (∫ u in (0:ℝ)..s, (s - u) • G u)
      = s • (∫ u in (0:ℝ)..s, G u) - ∫ u in (0:ℝ)..s, u • G u := by
    intro s
    have hsc : Continuous (fun u : ℝ => s • G u) :=
      (continuous_const : Continuous fun _ : ℝ => s).smul hGcont
    have h1 : (∫ u in (0:ℝ)..s, (s - u) • G u)
        = ∫ u in (0:ℝ)..s, (s • G u - u • G u) := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [sub_smul]
    rw [h1, intervalIntegral.integral_sub (f := fun u : ℝ => s • G u)
      (g := fun u : ℝ => u • G u) (hsc.intervalIntegrable 0 s) (huGi s),
      intervalIntegral.integral_smul]
  have hHderiv : ∀ s, HasDerivAt (fun t : ℝ => ∫ u in (0:ℝ)..t, (t - u) • G u)
      (∫ u in (0:ℝ)..s, G u) s := by
    intro s
    have hprod : HasDerivAt (fun t : ℝ => t • (∫ u in (0:ℝ)..t, G u))
        (s • G s + (1:ℝ) • (∫ u in (0:ℝ)..s, G u)) s :=
      (hasDerivAt_id s).smul (hA s)
    have hsub := hprod.sub (hB s)
    have hfun : (fun t : ℝ => ∫ u in (0:ℝ)..t, (t - u) • G u)
        = (fun t : ℝ => t • (∫ u in (0:ℝ)..t, G u))
          - (fun t : ℝ => ∫ u in (0:ℝ)..t, u • G u) := by
      funext t; exact hHrep t
    rw [hfun]
    have hd : (∫ u in (0:ℝ)..s, G u) = s • G s + (1:ℝ) • (∫ u in (0:ℝ)..s, G u) - s • G s := by
      rw [one_smul]; abel
    rw [hd]
    exact hsub
  have hFTC : ∀ s, deriv (devPrim r D σ) s = ∫ u in (0:ℝ)..s, G u := by
    intro s
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0:ℝ)) (b := s) (f := deriv (devPrim r D σ)) (f' := G)
      (fun x hx => by rw [hG]; exact hasDerivAt_deriv_devPrim hr D σ x) (hGi s)
    have h0 : deriv (devPrim r D σ) 0 = 0 := by
      rw [(hasDerivAt_devPrim hr D σ 0).deriv]
      simp
    rw [h0, sub_zero] at h
    exact h.symm
  have hHeq : ∀ s, (∫ u in (0:ℝ)..s, (s - u) • G u) = devPrim r D σ s := by
    intro s
    have hdiff : Differentiable ℝ (fun t : ℝ =>
        (∫ u in (0:ℝ)..t, (t - u) • G u) - devPrim r D σ t) :=
      fun t => ((hHderiv t).differentiableAt).sub ((hasDerivAt_devPrim hr D σ t).differentiableAt)
    have hzero : ∀ t : ℝ, deriv (fun t : ℝ =>
        (∫ u in (0:ℝ)..t, (t - u) • G u) - devPrim r D σ t) t = 0 := by
      intro t
      rw [show (fun t : ℝ => (∫ u in (0:ℝ)..t, (t - u) • G u) - devPrim r D σ t)
          = (fun t : ℝ => ∫ u in (0:ℝ)..t, (t - u) • G u) - devPrim r D σ from rfl,
        deriv_sub ((hHderiv t).differentiableAt) ((hasDerivAt_devPrim hr D σ t).differentiableAt),
        (hHderiv t).deriv, hFTC t, sub_self]
    have hc := is_const_of_deriv_eq_zero hdiff hzero s 0
    have h0 : devPrim r D σ 0 = 0 := by simp [devPrim]
    simp only [h0, sub_zero, intervalIntegral.integral_same] at hc
    exact sub_eq_zero.mp hc
  rw [← hHeq ξ, ← hHeq 1]
  have hmaxc : Continuous (fun u : ℝ => max (ξ - u) 0) :=
    (continuous_const.sub continuous_id).max continuous_const
  have hKc : Continuous (fun u : ℝ => max (ξ - u) 0 • G u) := hmaxc.smul hGcont
  have hmax : (∫ u in (0:ℝ)..1, max (ξ - u) 0 • G u)
      = ∫ u in (0:ℝ)..ξ, (ξ - u) • G u := by
    have h1 : (∫ u in (0:ℝ)..ξ, max (ξ - u) 0 • G u)
          + ∫ u in ξ..1, max (ξ - u) 0 • G u
        = (∫ u in (0:ℝ)..1, max (ξ - u) 0 • G u) :=
      intervalIntegral.integral_add_adjacent_intervals (hKc.intervalIntegrable 0 ξ)
        (hKc.intervalIntegrable ξ 1)
    have h2 : (∫ u in (0:ℝ)..ξ, max (ξ - u) 0 • G u)
        = ∫ u in (0:ℝ)..ξ, (ξ - u) • G u := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le hξ.1] at hu
      rw [max_eq_left (by linarith [hu.2])]
    have h3 : (∫ u in ξ..1, max (ξ - u) 0 • G u) = 0 := by
      have hz : (∫ u in ξ..1, max (ξ - u) 0 • G u) = ∫ u in ξ..1, (0 : Space) := by
        refine intervalIntegral.integral_congr (fun u hu => ?_)
        rw [Set.uIcc_of_le hξ.2] at hu
        rw [max_eq_right (by linarith [hu.1]), zero_smul]
      rw [hz, intervalIntegral.integral_zero]
    rw [← h1, h2, h3, add_zero]
  have hLc : Continuous (fun u : ℝ => (1 - u) • G u) :=
    (continuous_const.sub continuous_id).smul hGcont
  have hkey : ∀ (x : Space) (u : ℝ),
      (max (ξ - u) 0 - ξ * (1 - u)) • x = max (ξ - u) 0 • x - ξ • ((1 - u) • x) := by
    intro x u
    conv_lhs => rw [sub_smul, mul_smul]
  have hsplit : (∫ u in (0:ℝ)..1, (max (ξ - u) 0 - ξ * (1 - u)) • G u)
      = (∫ u in (0:ℝ)..1, max (ξ - u) 0 • G u)
        - ξ • (∫ u in (0:ℝ)..1, (1 - u) • G u) := by
    have hEq : (∫ u in (0:ℝ)..1, (max (ξ - u) 0 - ξ * (1 - u)) • G u)
        = ∫ u in (0:ℝ)..1, (max (ξ - u) 0 • G u - ξ • ((1 - u) • G u)) := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      exact hkey (G u) u
    rw [hEq, intervalIntegral.integral_sub (f := fun u : ℝ => max (ξ - u) 0 • G u)
      (g := fun u : ℝ => ξ • ((1 - u) • G u)) (hKc.intervalIntegrable 0 1)
      ((hLc.const_smul ξ).intervalIntegrable 0 1), intervalIntegral.integral_smul]
  rw [hsplit, hmax]



/-! ## The sign of the deviation

The Green kernel of `dev_green` is nonpositive on the unit square and strictly negative on
`(0,1)²`.  Hence an `n`-component of the acceleration of one sign along the whole retained arc
gives an `n`-component of the deviation of the opposite sign, with the strictness supplied by a
single interior point of strict sign. -/

/-- **The deviation is one-sided against a definite acceleration.**  If the `n`-component of the
acceleration is `≤ 0` along the whole retained arc (and `< 0` somewhere inside), then the
`n`-component of the deviation is `> 0` at every interior fraction. -/
theorem needleDev_inner_pos {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {σ : ℝ} {n : Space} (hW : 0 < sweepW' D σ)
    (hle : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      inner ℝ n (deriv (velocity r) (taR D σ + u * sweepW' D σ)) ≤ 0)
    (hlt : ∃ u ∈ Set.Ioo (0 : ℝ) 1,
      inner ℝ n (deriv (velocity r) (taR D σ + u * sweepW' D σ)) < 0)
    {ξ : ℝ} (hξ : ξ ∈ Set.Ioo (0 : ℝ) 1) :
    0 < inner ℝ n (dev r D σ ξ) := by
  have hξI : ξ ∈ Set.Icc (0 : ℝ) 1 := ⟨hξ.1.le, hξ.2.le⟩
  have hWsq : (0 : ℝ) < (sweepW' D σ)^2 := by positivity
  have hacc : Continuous (fun u : ℝ => deriv (velocity r) (taR D σ + u * sweepW' D σ)) := by
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
    have hd1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) :=
      ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := r)).mp hs).2
    have hd2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (deriv r)) :=
      ((contDiff_infty_iff_deriv (𝕜 := ℝ) (f := deriv r)).mp hd1).2
    exact hd2.continuous.comp (by fun_prop)
  have hinn : Continuous
      (fun u : ℝ => inner ℝ n (deriv (velocity r) (taR D σ + u * sweepW' D σ))) :=
    (innerSL ℝ n).continuous.comp hacc
  have hkerC : Continuous (fun u : ℝ => max (ξ - u) 0 - ξ * (1 - u)) := by
    have h1 : Continuous (fun u : ℝ => max (ξ - u) 0) :=
      (continuous_const.sub continuous_id).max continuous_const
    have h2 : Continuous (fun u : ℝ => ξ * (1 - u)) :=
      (continuous_const : Continuous fun _ : ℝ => ξ).mul
        ((continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).sub continuous_id)
    exact h1.sub h2
  have hbigC : Continuous (fun u : ℝ =>
      (sweepW' D σ)^2 * inner ℝ n (deriv (velocity r) (taR D σ + u * sweepW' D σ))) :=
    (continuous_const : Continuous fun _ : ℝ => (sweepW' D σ)^2).mul hinn
  have hgc : Continuous (fun u : ℝ =>
      (max (ξ - u) 0 - ξ * (1 - u)) *
        ((sweepW' D σ)^2 * inner ℝ n (deriv (velocity r) (taR D σ + u * sweepW' D σ)))) :=
    hkerC.mul hbigC
  have hint : IntervalIntegrable
      (fun u : ℝ => (max (ξ - u) 0 - ξ * (1 - u)) •
        ((sweepW' D σ)^2 • deriv (velocity r) (taR D σ + u * sweepW' D σ))) volume (0 : ℝ) 1 :=
    (hkerC.smul ((continuous_const : Continuous fun _ : ℝ => (sweepW' D σ)^2).smul hacc)).intervalIntegrable 0 1
  have hInt : inner ℝ n (dev r D σ ξ)
      = ∫ u in (0 : ℝ)..1,
          (max (ξ - u) 0 - ξ * (1 - u)) * ((sweepW' D σ)^2 *
            inner ℝ n (deriv (velocity r) (taR D σ + u * sweepW' D σ))) := by
    rw [dev_green hr D hξI]
    conv_lhs => rw [← innerSL_apply_apply]
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ n) hint]
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    simp only [innerSL_apply_apply, inner_smul_right, RCLike.conj_to_real, smul_eq_mul]
  rw [hInt]
  refine intervalIntegral.integral_pos zero_lt_one hgc.continuousOn ?_ ?_
  · intro u hu
    have huI : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
    have hk : max (ξ - u) 0 - ξ * (1 - u) ≤ 0 := by
      by_cases h : u ≤ ξ
      · rw [max_eq_left (by linarith)]
        nlinarith [hξ.1, hξ.2, hu.1, h]
      · rw [max_eq_right (by linarith)]
        nlinarith [hξ.1, hξ.2, hu.1, hu.2, h]
    have ha : inner ℝ n (deriv (velocity r) (taR D σ + u * sweepW' D σ)) ≤ 0 := hle u huI
    exact mul_nonneg_of_nonpos_of_nonpos hk (mul_nonpos_of_nonneg_of_nonpos hWsq.le ha)
  · obtain ⟨u₀, hu₀, hu₀lt⟩ := hlt
    refine ⟨u₀, ⟨hu₀.1.le, hu₀.2.le⟩, ?_⟩
    have hk : max (ξ - u₀) 0 - ξ * (1 - u₀) < 0 := by
      by_cases h : u₀ ≤ ξ
      · rw [max_eq_left (by linarith)]
        nlinarith [hξ.1, hξ.2, hu₀.1, h]
      · rw [max_eq_right (by linarith)]
        nlinarith [hξ.1, hξ.2, hu₀.1, hu₀.2, h]
    exact mul_pos_of_neg_of_neg hk (mul_neg_of_pos_of_neg hWsq hu₀lt)

end Work.Drive
