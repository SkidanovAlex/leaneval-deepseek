import Mathlib
import Submission.Work.Drive.Generic.nclmChart
import Submission.Work.Generic.angVelNum_le_margin_of_chordConcave

/-!
# The branch margins of the needle's chart

The margin of `Work.Drive.Generic.needleChartLoop_margin` is the bilinear expression `nclmMarg Γ V`
below, which is *linear* in `Γ`.  The chamfered loop has four pieces; on each of them the pair
`(Γ, V)` has an explicit form, and this module proves the lower bound of the margin on each piece:

* `nclm_arc_margin` — the arc piece (the angular-velocity margin of a chord-concave profile);
* `nclm_chord_margin` — the chord piece;
* `nclm_chamfer_fwd_margin` / `nclm_chamfer_bwd_margin` — the two endpoint forms of a chamfer;
* `nclm_marg_seg` — the linearity that turns endpoint bounds into a bound on the whole segment.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- **The chart margin** of `Work.Drive.Generic.needleChartLoop_margin`, with the loop point `Γ` and
the loop velocity `V` as separate arguments. -/
noncomputable def nclmMarg (r : ℝ → Space) {d : BandArcData} (D : Work.Drive.SweepData d)
    (lam δ₁ δ₂ ε : ℝ) (v Γ V : Space) : ℝ :=
  inner ℝ (Γ - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
      (Work.Drive.chartE r D lam δ₁ δ₂ ε v) * inner ℝ V v
    - inner ℝ (Γ - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v
      * inner ℝ V (Work.Drive.chartE r D lam δ₁ δ₂ ε v)

lemma nclmAbs_le (x t : ℝ) (h : |x| ≤ t) : -t ≤ x ∧ x ≤ t := abs_le.mp h

lemma nclmPos_period : (0 : ℝ) < period := period_pos

/-- **The linearity of the margin in the loop point.** -/
theorem nclm_marg_seg {r : ℝ → Space} {d : BandArcData} (D : Work.Drive.SweepData d)
    {lam δ₁ δ₂ ε : ℝ} {v P Q V : Space} {t kap : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hP : kap ≤ nclmMarg r D lam δ₁ δ₂ ε v P V)
    (hQ : kap ≤ nclmMarg r D lam δ₁ δ₂ ε v Q V) :
    kap ≤ nclmMarg r D lam δ₁ δ₂ ε v ((1 - t) • P + t • Q) V := by
  have hsplit : ∀ y : Space,
      inner ℝ ((1 - t) • P + t • Q - Work.Drive.chartC r D lam δ₁ δ₂ ε v) y
        = (1 - t) * inner ℝ (P - Work.Drive.chartC r D lam δ₁ δ₂ ε v) y
          + t * inner ℝ (Q - Work.Drive.chartC r D lam δ₁ δ₂ ε v) y := by
    intro y
    have hres : (1 - t) • P + t • Q - Work.Drive.chartC r D lam δ₁ δ₂ ε v
        = (1 - t) • (P - Work.Drive.chartC r D lam δ₁ δ₂ ε v)
          + t • (Q - Work.Drive.chartC r D lam δ₁ δ₂ ε v) := by
      rw [smul_sub, smul_sub]; module
    rw [hres, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have haff : nclmMarg r D lam δ₁ δ₂ ε v ((1 - t) • P + t • Q) V
      = (1 - t) * nclmMarg r D lam δ₁ δ₂ ε v P V
        + t * nclmMarg r D lam δ₁ δ₂ ε v Q V := by
    simp only [nclmMarg, hsplit]
    ring
  rw [haff]
  nlinarith [hP, hQ, ht0, ht1]

/-- **The arc piece.** -/
theorem nclm_arc_margin {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : Work.Drive.SweepData d) {lam δ₁ δ₂ ε σ : ℝ} {v : Space} {w m kap : ℝ}
    (hlam0 : 0 < lam) (hlam4 : lam ≤ 1 / 4) (hw : 0 < w) (hm : 0 < m) (hkap : 0 < kap)
    (hwdef : Work.Drive.sweepW' D σ = w)
    (hmono : StrictMonoOn (nclmAX r D lam δ₁ δ₂ ε σ v) (Set.Icc (0 : ℝ) 1))
    (hxpos : ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, m * w / 8 ≤ deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ)
    (hdiff : ∀ ξ ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ (nclmAH r D lam δ₁ δ₂ ε σ v) ξ)
    (hchord : ∀ ξ₁ ∈ Set.Icc (0 : ℝ) 1, ∀ ξ₂ ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
        nclmAX r D lam δ₁ δ₂ ε σ v ξ
            = t * nclmAX r D lam δ₁ δ₂ ε σ v ξ₁
              + (1 - t) * nclmAX r D lam δ₁ δ₂ ε σ v ξ₂ →
        t * nclmAH r D lam δ₁ δ₂ ε σ v ξ₁
            + (1 - t) * nclmAH r D lam δ₁ δ₂ ε σ v ξ₂ ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ)
    (hξ₀ : ∃ ξ₀ ∈ Set.Ioo lam (1 - lam),
      nclmAX r D lam δ₁ δ₂ ε σ v ξ₀ = 0
        ∧ kap * w ^ 2 / 2 ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ₀)
    {ξ : ℝ} (hξ : ξ ∈ Set.Ioo lam (1 - lam)) :
    kap * m * w ^ 3 / (16 * period)
      ≤ nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepArc' r D σ ξ)
          (((1 - 2 * lam) * (2 / period) * w) •
            velocity r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ)) := by
  obtain ⟨ξ₀, hξ₀mem, hX0, hH0⟩ := hξ₀
  have hξ01 : ξ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  have hsub : Set.Icc lam (1 - lam) ⊆ Set.Icc (0 : ℝ) 1 :=
    Set.Icc_subset_Icc (by linarith) (by linarith)
  have hmono' : StrictMonoOn (nclmAX r D lam δ₁ δ₂ ε σ v) (Set.Icc lam (1 - lam)) :=
    hmono.mono hsub
  have hxpos' : ∀ ξ ∈ Set.Ioo lam (1 - lam), 0 < deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ := by
    intro ξ hξ
    have h1 := hxpos ξ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
    have h2 : 0 < m * w / 8 := by positivity
    linarith
  have hdiff' : ∀ ξ ∈ Set.Ioo lam (1 - lam),
      DifferentiableAt ℝ (nclmAH r D lam δ₁ δ₂ ε σ v) ξ :=
    fun ξ hξ => hdiff ξ ⟨by linarith [hξ.1], by linarith [hξ.2]⟩
  have hchord' : ∀ ξ₁ ∈ Set.Icc lam (1 - lam), ∀ ξ₂ ∈ Set.Icc lam (1 - lam),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ξ ∈ Set.Icc lam (1 - lam),
        nclmAX r D lam δ₁ δ₂ ε σ v ξ
            = t * nclmAX r D lam δ₁ δ₂ ε σ v ξ₁
              + (1 - t) * nclmAX r D lam δ₁ δ₂ ε σ v ξ₂ →
        t * nclmAH r D lam δ₁ δ₂ ε σ v ξ₁
            + (1 - t) * nclmAH r D lam δ₁ δ₂ ε σ v ξ₂ ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ :=
    fun ξ₁ h₁ ξ₂ h₂ t ht ξ hξ => hchord ξ₁ (hsub h₁) ξ₂ (hsub h₂) t ht ξ (hsub hξ)
  have hHpos : 0 < nclmAH r D lam δ₁ δ₂ ε σ v ξ₀ := by
    have h : 0 < kap * w ^ 2 / 2 := by positivity
    linarith
  have hkey := (Work.Generic.angVelNum_le_margin_of_chordConcave
    (H := nclmAH r D lam δ₁ δ₂ ε σ v) (X := nclmAX r D lam δ₁ δ₂ ε σ v)
    (a := lam) (b := 1 - lam) (xc := 0) (yc := 0) (ξ₀ := ξ₀)
    (by linarith) hmono' hxpos' hdiff' hchord' hξ₀mem hHpos (by rw [hX0])) ξ hξ
  simp only [sub_zero] at hkey
  have hbracket : kap * m * w ^ 3 / 16 ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ
      * deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ
      - nclmAX r D lam δ₁ δ₂ ε σ v ξ * deriv (nclmAH r D lam δ₁ δ₂ ε σ v) ξ := by
    have hx := hxpos ξ hξ01
    have h1 : kap * w ^ 2 / 2 * (m * w / 8) ≤ nclmAH r D lam δ₁ δ₂ ε σ v ξ₀
        * deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ :=
      mul_le_mul hH0 hx (by positivity) (by positivity)
    have h2 : kap * m * w ^ 3 / 16 ≤ kap * w ^ 2 / 2 * (m * w / 8) := by
      nlinarith [hw, hm, hkap]
    linarith [hkey, h1, h2]
  have hid : nclmMarg r D lam δ₁ δ₂ ε v (Work.Drive.sweepArc' r D σ ξ)
      (((1 - 2 * lam) * (2 / period) * w) •
        velocity r (Work.Drive.taR D σ + ξ * Work.Drive.sweepW' D σ))
      = ((1 - 2 * lam) * (2 / period)) * (nclmAH r D lam δ₁ δ₂ ε σ v ξ
          * deriv (nclmAX r D lam δ₁ δ₂ ε σ v) ξ
          - nclmAX r D lam δ₁ δ₂ ε σ v ξ * deriv (nclmAH r D lam δ₁ δ₂ ε σ v) ξ) := by
    have h1 : inner ℝ (Work.Drive.sweepArc' r D σ ξ
        - Work.Drive.chartC r D lam δ₁ δ₂ ε v) (Work.Drive.chartE r D lam δ₁ δ₂ ε v)
        = nclmAH r D lam δ₁ δ₂ ε σ v ξ := rfl
    have h2 : inner ℝ (Work.Drive.sweepArc' r D σ ξ
        - Work.Drive.chartC r D lam δ₁ δ₂ ε v) v = nclmAX r D lam δ₁ δ₂ ε σ v ξ := rfl
    rw [nclmMarg, h1, h2, real_inner_smul_left, real_inner_smul_left,
      nclm_deriv_nclmAX hr, nclm_deriv_nclmAH hr, hwdef]
    have hwne : w ≠ 0 := ne_of_gt hw
    field_simp
    try ring
  rw [hid]
  have hcoef : period⁻¹ ≤ (1 - 2 * lam) * (2 / period) := by
    have hp : (0 : ℝ) < 2 / period := div_pos two_pos nclmPos_period
    have h3 : period⁻¹ = (1 / 2) * (2 / period) := by
      rw [div_eq_mul_inv]; ring
    rw [h3]
    exact mul_le_mul_of_nonneg_right (by linarith : (1:ℝ)/2 ≤ 1 - 2 * lam) hp.le
  have hb0 : (0:ℝ) ≤ kap * m * w ^ 3 / 16 := by positivity
  have ha : (0:ℝ) ≤ (1 - 2 * lam) * (2 / period) := by
    have hp : (0 : ℝ) < 2 / period := div_pos two_pos nclmPos_period
    nlinarith [hp, hlam4]
  have hstep1 : kap * m * w ^ 3 / (16 * period)
      ≤ (kap * m * w ^ 3 / 16) * ((1 - 2 * lam) * (2 / period)) := by
    rw [show kap * m * w ^ 3 / (16 * period) = (kap * m * w ^ 3 / 16) * period⁻¹ from by ring]
    exact mul_le_mul_of_nonneg_left hcoef hb0
  refine le_trans hstep1 ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left hbracket ha

end Work.Drive.Generic
