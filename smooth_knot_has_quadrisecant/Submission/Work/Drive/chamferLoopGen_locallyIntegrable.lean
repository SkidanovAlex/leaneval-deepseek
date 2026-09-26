import Mathlib
import Submission.Work.Drive.chamferSchedule
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable
import Submission.Work.Drive.chamferLoopGenLipAux

/-!
# Local integrability of the σ-scheduled chamfer loop

`Work.Drive.chamferLoopGen r D lay α β` is the generalised chamfer loop of the lead's
uniform-`ρ₀` design (`NOTES_LEAD_endgameUniform.md` §3): a chord-sweep loop whose arc-depth
fraction `α σ` and chord-target fraction `β σ` depend on the sweep parameter `σ` through the
schedules `schedAlpha`, `schedBeta` of `chamferSchedule.lean`.

Here we prove that the *fully scheduled* loop

`(s, t) ↦ chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D) s t`

is locally integrable for the Lebesgue measure on `ℝ × ℝ`, for any `lay > 0` and `δs > 0`.

The two ingredients are exactly as for the constant-fraction loop
(`Work.Drive.sweepLoopChamfer_locallyIntegrable`):

* **measurability**: the loop is the piecewise (in the profile `u = sweepParam t`) composition of
  `r`, the lifts `taR`, `tbR`, `sweepW'` and the schedules, which are all measurable;
* **a global bound**: the three quantities that can degenerate are controlled by the schedules
  themselves —

  - the *depth* `dep σ = α σ * W_σ` is bounded by `max (lay · period) |ρ₀|` (the ramp `φ` is
    clamped to `[0,1]`), so the arc-side evaluations of `r` stay in a fixed compact interval;
  - the *width* `W_σ = sweepW' D σ` is bounded by `period`, and `r` is globally Lipschitz on the
    knot (`Work.Drive.exists_knot_lipschitz`), so the chord vector `V_σ = r (tb σ) - r (ta σ)`
    obeys `‖V_σ‖ ≤ M · period`;
  - the *target fraction* `β σ` may blow up when the chord degenerates, but the product
    `β σ • V_σ` does not: `Work.Drive.schedBeta_smul_bound` bounds it by
    `lay · M · period + |cQ| · max (lay · period) |ρ₀|` (this is what the `min lay (…)` clamp of
    `schedBeta` buys; the same fact is used for the Lipschitz constant in `t` of the profile in
    `chamferLoopGenLipschitzT.lean`).

  With those, every branch of the loop is bounded by `R + M · period + 2 · B` where `R` bounds
  `‖r x‖` on the compact interval that the arc-side evaluations live in.

Local integrability then follows from `LocallyIntegrable.mono` against the constant function.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory

/-! ## Measurability of the schedules

The schedules are built from the continuous data `sweepW'`, `schedC` and the continuous ramp
`φ` by division, so they are Borel measurable even though they are not continuous (the division
by `sweepW'` and by the chord length `‖r (tbR) - r (taR)‖` may degenerate). -/

lemma measurable_schedC {d : BandArcData} (D : SweepData d) : Measurable (schedC D) :=
  (continuous_schedC D).measurable

lemma measurable_schedPsi {d : BandArcData} (D : SweepData d) (δs : ℝ) :
    Measurable (schedPsi D δs) := by
  unfold schedPsi
  exact schedPhi_continuous.measurable.comp
    ((measurable_const.mul (measurable_schedC D)).div measurable_const)

lemma measurable_schedDep {d : BandArcData} (D : SweepData d) (lay ρ δs : ℝ) :
    Measurable (fun σ : ℝ => schedDep lay ρ δs D σ) := by
  unfold schedDep
  exact (measurable_const.mul (sweepLoopChamfer_sweepW'_continuous D).measurable).max
    (measurable_const.mul (schedPhi_continuous.measurable.comp
      ((measurable_schedC D).div_const δs)))

lemma measurable_schedAlpha {d : BandArcData} (D : SweepData d) (lay ρ δs : ℝ) :
    Measurable (schedAlpha lay ρ δs D) := by
  unfold schedAlpha
  exact (measurable_schedDep D lay ρ δs).div (sweepLoopChamfer_sweepW'_continuous D).measurable

lemma measurable_schedBeta {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) (lay ρ δs cQ : ℝ) :
    Measurable (schedBeta r lay ρ δs cQ D) := by
  unfold schedBeta
  refine Measurable.add (Measurable.mul ?_ measurable_const) (Measurable.mul ?_ ?_)
  · exact measurable_const.sub (measurable_schedPsi D δs)
  · exact measurable_schedPsi D δs
  · refine Measurable.min measurable_const ?_
    refine Measurable.div ?_ ?_
    · exact measurable_const.mul (measurable_schedDep D lay ρ δs)
    · exact (((hr.comp (sweepLoopChamfer_tbR_continuous D)).sub
        (hr.comp (sweepLoopChamfer_taR_continuous D))).norm).measurable

/-- **The scheduled chamfer loop is measurable in the pair `(s, t)`.** -/
lemma chamferLoopGen_measurable {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) (lay : ℝ) {α β : ℝ → ℝ} (hα : Measurable α) (hβ : Measurable β) :
    Measurable (fun p : ℝ × ℝ => chamferLoopGen r D lay α β p.1 p.2) := by
  have hta : Measurable (fun i : unitInterval => D.ta i) := D.cont_ta.measurable
  have htb : Measurable (fun i : unitInterval => D.tb i) := D.cont_tb.measurable
  have hcl : Measurable (clampI : ℝ → unitInterval) := sweepLoopChamfer_clampI_continuous.measurable
  have hr' : Measurable r := hr.measurable
  have hsp : Measurable (fun p : ℝ × ℝ => sweepParam p.2) :=
    sweepLoopChamfer_sweepParam_measurable.comp measurable_snd
  have hαc : Measurable (fun p : ℝ × ℝ => α p.1) := hα.comp measurable_fst
  have hβc : Measurable (fun p : ℝ × ℝ => β p.1) := hβ.comp measurable_fst
  simp only [chamferLoopGen]
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le hsp measurable_const
  · unfold sweepArc' sweepW' taR tbR; fun_prop
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le hsp measurable_const
  · unfold sweepArc' sweepChord' sweepW' taR tbR; fun_prop
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le hsp measurable_const
  · unfold sweepChord' taR tbR; fun_prop
  · unfold sweepArc' sweepChord' sweepW' taR tbR; fun_prop

/-! ## The pointwise bound for the profile of the loop -/

/-- The chord point at fraction `ξ` is the `a`-endpoint plus `ξ` times the chord vector. -/
lemma sweepChord'_eq_add_smul {r : ℝ → Space} {d : BandArcData} (D : SweepData d) (s ξ : ℝ) :
    sweepChord' r D s ξ = r (taR D s) + ξ • (r (tbR D s) - r (taR D s)) := by
  rw [sweepChord']
  module

/-- **The profile of the scheduled chamfer loop is bounded.**  The hypotheses are exactly the
quantitative facts that the schedules provide at a fixed sweep parameter `s`:

* `|taR D s| ≤ A`, `|tbR D s| ≤ A` — the two branch lifts are bounded;
* `0 ≤ W = sweepW' D s ≤ period` — the width of the retained arc;
* `|a · W| ≤ Dz` — the *depth* (the product of the arc fraction and the width) is bounded;
* `‖V‖ ≤ Lb` and `‖b • V‖ ≤ B` with `V = r (tbR D s) - r (taR D s)` — the chord vector and the
  chord *target vector* are bounded (the second one although `b` itself need not be);
* `‖r x‖ ≤ Rr` on `|x| ≤ A + Dz + period` — the arc-side evaluations live in that interval.

The conclusion is `‖Φ‖ ≤ Rr + Lb + 2 · B` for every profile value `u ∈ [0, 1)`. -/
lemma chamferLoopProf_bound {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay a b s u A Dz Lb B Rr : ℝ} (hlay : 0 < lay)
    (hA : |taR D s| ≤ A) (hA' : |tbR D s| ≤ A)
    (hW0 : 0 ≤ sweepW' D s) (hWp : sweepW' D s ≤ period)
    (hDz0 : 0 ≤ Dz) (hdep : |a * sweepW' D s| ≤ Dz)
    (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hV : ‖r (tbR D s) - r (taR D s)‖ ≤ Lb)
    (hβV : ‖b • (r (tbR D s) - r (taR D s))‖ ≤ B)
    (hR : ∀ x : ℝ, |x| ≤ A + Dz + period → ‖r x‖ ≤ Rr)
    (hLb0 : 0 ≤ Lb) (hB0 : 0 ≤ B) (_hRr0 : 0 ≤ Rr) :
    ‖chamferLoopProf r D lay a b s u‖ ≤ Rr + Lb + 2 * B := by
  have hper : 0 < period := period_pos
  -- the two endpoints of the chord, and the interval that the arc evaluations live in
  have hP : ‖r (taR D s)‖ ≤ Rr := by
    refine hR _ ?_
    have hle : |taR D s| ≤ A + Dz + period := by linarith [abs_le.mp hA]
    exact hle
  have hQ : ‖r (tbR D s)‖ ≤ Rr := by
    refine hR _ ?_
    have hle : |tbR D s| ≤ A + Dz + period := by linarith [abs_le.mp hA']
    exact hle
  have hWabs : |sweepW' D s| ≤ period := abs_le.mpr ⟨by linarith, hWp⟩
  have htarget : Rr ≤ Rr + Lb + 2 * B := by linarith [hLb0, hB0]
  have hC1 : Rr + B ≤ Rr + Lb + 2 * B := by linarith
  have hC2 : Rr + Lb + B ≤ Rr + Lb + 2 * B := by linarith
  -- the chord identity and its `ξ = 1 - b` and `ξ = b` forms
  have hchord1 : sweepChord' r D s (1 - b) = r (tbR D s) - b • (r (tbR D s) - r (taR D s)) := by
    rw [sweepChord'_eq_add_smul]
    module
  have hchord2 : sweepChord' r D s b = r (taR D s) + b • (r (tbR D s) - r (taR D s)) :=
    sweepChord'_eq_add_smul D s b
  have harcA : ‖sweepArc' r D s a‖ ≤ Rr := by
    rw [sweepArc']
    refine hR _ ?_
    calc |taR D s + a * sweepW' D s| ≤ |taR D s| + |a * sweepW' D s| := abs_add_le _ _
      _ ≤ A + Dz := add_le_add hA hdep
      _ ≤ A + Dz + period := by linarith
  have harcB : ‖sweepArc' r D s (1 - a)‖ ≤ Rr := by
    rw [sweepArc']
    refine hR _ ?_
    have hrew : taR D s + (1 - a) * sweepW' D s
        = taR D s + sweepW' D s - a * sweepW' D s := by ring
    rw [hrew]
    calc |taR D s + sweepW' D s - a * sweepW' D s|
        ≤ |taR D s + sweepW' D s| + |a * sweepW' D s| := by
          rw [sub_eq_add_neg]
          have h := abs_add_le (taR D s + sweepW' D s) (-(a * sweepW' D s))
          rwa [abs_neg] at h
      _ ≤ |taR D s| + |sweepW' D s| + |a * sweepW' D s| :=
          add_le_add (abs_add_le _ _) le_rfl
      _ ≤ A + period + Dz := by linarith [hA, hWabs, hdep]
      _ ≤ A + Dz + period := by linarith
  have hchordA : ‖sweepChord' r D s (1 - b)‖ ≤ Rr + B := by
    rw [hchord1]
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hchordB : ‖sweepChord' r D s b‖ ≤ Rr + B := by
    rw [hchord2]
    exact (norm_add_le _ _).trans (by linarith)
  -- the four branches
  simp only [chamferLoopProf]
  split_ifs with h1 h2 h3
  · -- branch 1: the retained arc
    rw [sweepArc']
    rw [show taR D s + (a + (1 - 2 * a) * (2 * u)) * sweepW' D s
        = taR D s + ((1 - 4 * u) * (a * sweepW' D s) + (2 * u) * sweepW' D s) from by ring]
    refine (hR _ ?_).trans htarget
    have h14 : |1 - 4 * u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2u : |2 * u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hsplit : |(1 - 4 * u) * (a * sweepW' D s) + (2 * u) * sweepW' D s|
        ≤ |1 - 4 * u| * |a * sweepW' D s| + |2 * u| * |sweepW' D s| := by
      refine (abs_add_le _ _).trans ?_
      have h1 : |(1 - 4 * u) * (a * sweepW' D s)| = |1 - 4 * u| * |a * sweepW' D s| :=
        abs_mul _ _
      have h2 : |(2 * u) * sweepW' D s| = |2 * u| * |sweepW' D s| := abs_mul _ _
      rw [h1, h2]
    calc |taR D s + ((1 - 4 * u) * (a * sweepW' D s) + (2 * u) * sweepW' D s)|
        ≤ |taR D s| + |(1 - 4 * u) * (a * sweepW' D s) + (2 * u) * sweepW' D s| :=
          abs_add_le _ _
      _ ≤ |taR D s| + (|1 - 4 * u| * |a * sweepW' D s| + |2 * u| * |sweepW' D s|) :=
          add_le_add le_rfl hsplit
      _ ≤ A + (1 * Dz + 1 * period) := by
          refine add_le_add hA ?_
          refine add_le_add ?_ ?_
          · calc |1 - 4 * u| * |a * sweepW' D s| ≤ 1 * Dz :=
                mul_le_mul h14 hdep (abs_nonneg _) (by norm_num)
              _ = 1 * Dz := rfl
          · calc |2 * u| * |sweepW' D s| ≤ 1 * period :=
                mul_le_mul h2u hWabs (abs_nonneg _) (by norm_num)
              _ = 1 * period := rfl
      _ = A + Dz + period := by ring
  · -- branch 2: the head connector
    set c : ℝ := (2 * u - 1) / lay with hcdef
    have hc0 : 0 ≤ c := by
      rw [hcdef]; exact div_nonneg (by linarith [lt_of_not_ge h1]) hlay.le
    have hc1 : c ≤ 1 := by
      rw [hcdef, div_le_one hlay]; linarith
    calc ‖(1 - c) • sweepArc' r D s (1 - a) + c • sweepChord' r D s (1 - b)‖
        ≤ max ‖sweepArc' r D s (1 - a)‖ ‖sweepChord' r D s (1 - b)‖ :=
          sweepLoopChamfer_norm_smul_combo_le hc0 hc1 _ _
      _ ≤ Rr + Lb + 2 * B :=
          max_le (le_trans harcB htarget) (le_trans hchordA hC1)
  · -- branch 3: the chord side
    set c : ℝ := (u - (1 / 2 + lay / 2)) / (1 / 2 - lay) with hcdef
    have hl12 : lay < 1 / 2 := by linarith [lt_of_not_ge h2, h3]
    have hden : 0 < 1 / 2 - lay := by linarith
    have hc0 : 0 ≤ c := by
      rw [hcdef]; exact div_nonneg (by linarith [lt_of_not_ge h2]) hden.le
    have hc1 : c ≤ 1 := by
      rw [hcdef, div_le_one hden]; linarith
    have hzeta : (1 - b) - c * (1 - 2 * b) = (1 - c) + b * (2 * c - 1) := by ring
    rw [hzeta, sweepChord'_eq_add_smul]
    have hsmul : ((1 - c) + b * (2 * c - 1)) • (r (tbR D s) - r (taR D s))
        = (1 - c) • (r (tbR D s) - r (taR D s))
          + (2 * c - 1) • (b • (r (tbR D s) - r (taR D s))) := by
      rw [add_smul, mul_smul, smul_smul, smul_smul, mul_comm]
    rw [hsmul]
    have h1c : ‖(1 - c) • (r (tbR D s) - r (taR D s))‖ ≤ Lb := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      calc (1 - c) * ‖r (tbR D s) - r (taR D s)‖ ≤ 1 * Lb :=
            mul_le_mul (by linarith) hV (norm_nonneg _) (by norm_num)
        _ = Lb := one_mul _
    have h2c1 : ‖(2 * c - 1) • (b • (r (tbR D s) - r (taR D s)))‖ ≤ B := by
      rw [norm_smul, Real.norm_eq_abs]
      calc |2 * c - 1| * ‖b • (r (tbR D s) - r (taR D s))‖ ≤ 1 * B :=
            mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩) hβV (norm_nonneg _) (by norm_num)
        _ = B := one_mul _
    calc ‖r (taR D s) + ((1 - c) • (r (tbR D s) - r (taR D s))
          + (2 * c - 1) • (b • (r (tbR D s) - r (taR D s))))‖
        ≤ ‖r (taR D s)‖ + (‖(1 - c) • (r (tbR D s) - r (taR D s))‖
            + ‖(2 * c - 1) • (b • (r (tbR D s) - r (taR D s)))‖) :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ Rr + Lb + 2 * B := by linarith
  · -- branch 4: the tail connector
    set c : ℝ := (u - (1 - lay / 2)) / (lay / 2) with hcdef
    have hden : 0 < lay / 2 := by linarith
    have hc0 : 0 ≤ c := by
      rw [hcdef]; exact div_nonneg (by linarith [lt_of_not_ge h3]) hden.le
    have hc1 : c ≤ 1 := by
      rw [hcdef, div_le_one hden]; linarith
    calc ‖(1 - c) • sweepChord' r D s b + c • sweepArc' r D s a‖
        ≤ max ‖sweepChord' r D s b‖ ‖sweepArc' r D s a‖ :=
          sweepLoopChamfer_norm_smul_combo_le hc0 hc1 _ _
      _ ≤ Rr + Lb + 2 * B :=
          max_le (le_trans hchordB hC1) (le_trans harcA htarget)

/-! ## The global bound for the scheduled loop -/

theorem chamferLoopGen_locallyIntegrable {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    {lay ρ₀ δs cQ : ℝ} (hlay : 0 < lay) (hδs : 0 < δs) :
    MeasureTheory.LocallyIntegrable (fun p : ℝ × ℝ =>
      Work.Drive.chamferLoopGen r D lay (Work.Drive.schedAlpha lay ρ₀ δs D)
        (Work.Drive.schedBeta r lay ρ₀ δs cQ D) p.1 p.2) MeasureTheory.volume := by
  -- a global Lipschitz constant for the knot
  obtain ⟨Mr, hMrpos, hMr⟩ := exists_knot_lipschitz hr
  have hMr0 : 0 ≤ Mr := hMrpos.le
  -- a bound on the two branch lifts
  obtain ⟨A₀, hliftA⟩ :=
    (isCompact_univ (X := unitInterval)).exists_bound_of_continuousOn D.cont_ta.continuousOn
  obtain ⟨B₀, hliftB⟩ :=
    (isCompact_univ (X := unitInterval)).exists_bound_of_continuousOn D.cont_tb.continuousOn
  set A : ℝ := max A₀ B₀ with hAdef
  have hA : ∀ x : ℝ, |taR D x| ≤ A ∧ |tbR D x| ≤ A := by
    intro x
    constructor
    · exact le_trans (by simpa [taR, Real.norm_eq_abs] using hliftA (clampI x) (Set.mem_univ _))
        (le_max_left _ _)
    · exact le_trans (by simpa [tbR, Real.norm_eq_abs] using hliftB (clampI x) (Set.mem_univ _))
        (le_max_right _ _)
  -- the depth bound
  set Dz : ℝ := max (lay * period) |ρ₀| with hDzdef
  have hDz0 : 0 ≤ Dz := le_trans (abs_nonneg ρ₀) (le_max_right _ _)
  have hdep : ∀ s : ℝ, |schedAlpha lay ρ₀ δs D s * sweepW' D s| ≤ Dz := by
    intro s
    have h1 : schedAlpha lay ρ₀ δs D s * sweepW' D s = schedDep lay ρ₀ δs D s :=
      schedAlpha_mul_sweepW' D hlay hδs s
    rw [h1]
    have h2 : 0 ≤ schedDep lay ρ₀ δs D s := schedDep_nonneg D hlay s
    have h3 : schedDep lay ρ₀ δs D s ≤ Dz := schedDep_le D hlay s
    exact abs_le.mpr ⟨by linarith, h3⟩
  -- the chord vector is bounded by the Lipschitz constant times a period
  have hVb : ∀ s : ℝ, ‖r (tbR D s) - r (taR D s)‖ ≤ Mr * period := by
    intro s
    have h := hMr (tbR D s) (taR D s)
    rw [show tbR D s - taR D s = sweepW' D s from rfl,
      abs_of_nonneg (sweepW'_bounds D s).1] at h
    exact h.trans (mul_le_mul_of_nonneg_left (sweepW'_bounds D s).2 hMr0)
  -- the chord *target* vector is bounded
  set Bc : ℝ := lay * Mr * period + |cQ| * Dz with hBcdef
  have hBc0 : 0 ≤ Bc := by
    rw [hBcdef]
    exact add_nonneg (mul_nonneg (mul_nonneg hlay.le hMr0) period_pos.le)
      (mul_nonneg (abs_nonneg cQ) hDz0)
  have hβV : ∀ s : ℝ,
      ‖schedBeta r lay ρ₀ δs cQ D s • (r (tbR D s) - r (taR D s))‖ ≤ Bc :=
    fun s => schedBeta_smul_bound D hMr0 hMr hlay hδs s
  -- the bound on `r` on the interval that the arc-side evaluations live in
  have hA0 : 0 ≤ A := le_trans (abs_nonneg (taR D 0)) (hA 0).1
  set Bd : ℝ := A + Dz + period with hBddef
  have hBd0 : 0 ≤ Bd := by
    rw [hBddef]; have := period_pos; linarith
  have hrc : Continuous r := hr.smooth.continuous
  obtain ⟨Rr, hRr⟩ :=
    (isCompact_Icc (a := -|Bd|) (b := |Bd|)).exists_bound_of_continuousOn hrc.continuousOn
  have hR : ∀ x : ℝ, |x| ≤ A + Dz + period → ‖r x‖ ≤ Rr := by
    intro x hx
    refine hRr x ?_
    rw [Set.mem_Icc]
    have hx' : |x| ≤ |Bd| := by rw [abs_of_nonneg hBd0, hBddef]; exact hx
    exact ⟨by linarith [neg_abs_le x, hx'], by linarith [le_abs_self x, hx']⟩
  have hRr0 : 0 ≤ Rr := by
    refine le_trans (norm_nonneg _) (hRr 0 ?_)
    rw [Set.mem_Icc]
    exact ⟨neg_nonpos.mpr (abs_nonneg Bd), abs_nonneg Bd⟩
  -- the global bound
  have hbd : ∀ s t : ℝ,
      ‖chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D) s t‖
        ≤ Rr + Mr * period + 2 * Bc := by
    intro s t
    obtain ⟨hu0, hu1⟩ := sweepParam_mem t
    rw [chamferLoopGen_eq_prof']
    exact chamferLoopProf_bound D hlay (hA s).1 (hA s).2 (sweepW'_bounds D s).1
      (sweepW'_bounds D s).2 hDz0 (hdep s) hu0 hu1 (hVb s) (hβV s) hR
      (mul_nonneg hMr0 period_pos.le) hBc0 hRr0
  have hC0 : 0 ≤ Rr + Mr * period + 2 * Bc := by
    have h1 : 0 ≤ Mr * period := mul_nonneg hMr0 period_pos.le
    linarith [hRr0, h1, hBc0]
  refine (locallyIntegrable_const (Rr + Mr * period + 2 * Bc)).mono
    (chamferLoopGen_measurable hrc D lay
      (measurable_schedAlpha D lay ρ₀ δs) (measurable_schedBeta hrc D lay ρ₀ δs cQ)).aestronglyMeasurable
    ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg hC0]
  exact hbd p.1 p.2

end Work.Drive
