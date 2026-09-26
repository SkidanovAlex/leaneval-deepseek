import Mathlib
import Submission.Work.Drive.chamferSchedule
import Submission.Work.Drive.chamferLoopGenBlur
import Submission.Work.Drive.sweepFamFarSep

/-!
# Elementary estimates for the Lipschitz constant in `t` of the scheduled chamfer loop

This module collects the *quantitative* inputs of `Work.Drive.chamferLoopGenLipschitzT`,
i.e. of the Lipschitz continuity of `t ↦ chamferLoopGen r D lay α β σ t` with a constant
**uniform in** `σ`:

* `Work.Drive.sweepW'_bounds` — `0 ≤ sweepW' D s ≤ period`;
* `Work.Drive.schedDep_nonneg`, `Work.Drive.schedDep_le` — the cut depth is a non-negative
  quantity bounded by `max (lay * period) |ρ|` (the schedule's spatial part is clamped by the
  ramp `φ ∈ [0,1]`);
* `Work.Drive.schedAlpha_mul_sweepW'` — `α s * W_s = dep s` (the *spatial* depth, with the
  `W_s = 0` case covered by `schedDep = 0`);
* `Work.Drive.schedBeta_smul_bound` — `‖β s • (r (tbR s) - r (taR s))‖` is bounded by
  `lay * Mr * period + |cQ| * max (lay * period) |ρ|`, i.e. the *product* of the (possibly
  large, when the chord degenerates) target fraction with the (then small) chord vector is
  uniformly controlled — this is what the `min lay (...)` clamp of `schedBeta` buys;
* `Work.Drive.chamferProf_zero_eq_one` — the profile loop is *closed*, `Φ 1 = Φ 0`, the extra
  input needed to pass from the profile variable `u ∈ [0,1]` to the sawtooth `sweepParam`.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped unitInterval

/-! ### The width of the retained arc -/

/-- The width of the retained arc lies in `[0, period]` for every real sweep parameter. -/
lemma sweepW'_bounds {d : BandArcData} (D : SweepData d) (s : ℝ) :
    0 ≤ sweepW' D s ∧ sweepW' D s ≤ period := by
  have he : sweepW' D s = sweepW D (clampI s) := rfl
  rw [he]
  have hval : ((clampI s : unitInterval) : ℝ) = min 1 (max 0 s) := rfl
  have h0 : 0 ≤ ((clampI s : unitInterval) : ℝ) := by
    rw [hval]; exact le_min zero_le_one (le_max_left _ _)
  have h1 : ((clampI s : unitInterval) : ℝ) ≤ 1 := by
    rw [hval]; exact min_le_left _ _
  rcases eq_or_lt_of_le h0 with hz | hz
  · have hSi : clampI s = (0 : unitInterval) := Subtype.ext (by rw [← hz]; rfl)
    rw [hSi, sweepW_zero]
    exact ⟨le_rfl, period_pos.le⟩
  · rcases eq_or_lt_of_le h1 with ho | ho
    · have hSi : clampI s = (1 : unitInterval) := Subtype.ext (by rw [ho]; rfl)
      rw [hSi, sweepW_one]
      exact ⟨period_pos.le, le_rfl⟩
    · obtain ⟨hp, hl⟩ := sweepW_pos_lt D (clampI s) ⟨hz, ho⟩
      exact ⟨hp.le, hl.le⟩

/-! ### The depth schedule -/

/-- The cut depth is non-negative. -/
lemma schedDep_nonneg {d : BandArcData} (D : SweepData d) {lay ρ δs : ℝ} (hlay : 0 < lay)
    (s : ℝ) : 0 ≤ schedDep lay ρ δs D s := by
  rw [schedDep]
  exact le_trans (mul_nonneg hlay.le (sweepW'_bounds D s).1) (le_max_left _ _)

/-- The cut depth is at most `max (lay * period) |ρ|`: the first term by `sweepW' ≤ period`,
the second because the ramp `φ` takes values in `[0,1]`. -/
lemma schedDep_le {d : BandArcData} (D : SweepData d) {lay ρ δs : ℝ} (hlay : 0 < lay)
    (s : ℝ) : schedDep lay ρ δs D s ≤ max (lay * period) |ρ| := by
  rw [schedDep]
  refine max_le ?_ ?_
  · exact le_trans (mul_le_mul_of_nonneg_left (sweepW'_bounds D s).2 hlay.le) (le_max_left _ _)
  · rcases le_total (0 : ℝ) ρ with hρ | hρ
    · calc ρ * schedPhi (schedC D s / δs) ≤ ρ * 1 :=
            mul_le_mul_of_nonneg_left (schedPhi_le_one _) hρ
        _ = ρ := by ring
        _ ≤ |ρ| := le_abs_self ρ
        _ ≤ max (lay * period) |ρ| := le_max_right _ _
    · calc ρ * schedPhi (schedC D s / δs) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hρ (schedPhi_nonneg _)
        _ ≤ |ρ| := abs_nonneg ρ
        _ ≤ max (lay * period) |ρ| := le_max_right _ _

/-- **The arc-depth fraction times the width is the cut depth.**  (At `W = 0` both sides
vanish: the ramp argument is `c_s / δs = 0`, hence `schedDep = 0`.) -/
lemma schedAlpha_mul_sweepW' {d : BandArcData} (D : SweepData d) {lay ρ δs : ℝ}
    (hlay : 0 < lay) (hδs : 0 < δs) (s : ℝ) :
    schedAlpha lay ρ δs D s * sweepW' D s = schedDep lay ρ δs D s := by
  rw [schedAlpha]
  rcases eq_or_ne (sweepW' D s) 0 with hW | hW
  · have hc : schedC D s = 0 := by
      rw [schedC, hW, min_eq_left (by linarith [period_pos])]
    have hphi : schedPhi (0 / δs) = 0 := by
      rw [zero_div, schedPhi]; norm_num
    have hdep : schedDep lay ρ δs D s = 0 := by
      rw [schedDep, hc, hphi, mul_zero, hW, mul_zero, max_self]
    rw [hW, hdep, div_zero, zero_mul]
  · rw [div_mul_cancel₀ _ hW]

/-! ### The chord-target schedule -/

/-- **The target fraction times the chord vector is uniformly bounded.**  Writing
`β = (1-ψ) lay + ψ · min lay (cQ · dep / L)` with `L = ‖r (tbR) - r (taR)‖`, the first term
contributes at most `lay · L ≤ lay · Mr · period` and the second at most
`max (lay · Mr · period) (|cQ| · dep)`. -/
lemma schedBeta_smul_bound {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {Mr lay ρ δs cQ : ℝ} (hMr : 0 ≤ Mr)
    (hMrlip : ∀ x y : ℝ, ‖r x - r y‖ ≤ Mr * |x - y|)
    (hlay : 0 < lay) (hδs : 0 < δs) (s : ℝ) :
    ‖schedBeta r lay ρ δs cQ D s • (r (tbR D s) - r (taR D s))‖
      ≤ lay * Mr * period + |cQ| * max (lay * period) |ρ| := by
  have hlay0 : 0 ≤ lay := hlay.le
  set dep := schedDep lay ρ δs D s with hdepdef
  have hdep0 : 0 ≤ dep := schedDep_nonneg D hlay s
  have hdeple : dep ≤ max (lay * period) |ρ| := schedDep_le D hlay s
  have hDz0 : 0 ≤ max (lay * period) |ρ| := le_trans (abs_nonneg ρ) (le_max_right _ _)
  set ψ := schedPsi D δs s with hψdef
  have hψ0 : 0 ≤ ψ := schedPhi_nonneg _
  have hψ1 : ψ ≤ 1 := schedPhi_le_one _
  set L := ‖r (tbR D s) - r (taR D s)‖ with hLdef
  have hL0 : 0 ≤ L := norm_nonneg _
  set V := r (tbR D s) - r (taR D s) with hVdef
  have hVL : ‖V‖ = L := rfl
  have hchord : L ≤ Mr * period := by
    have h1 := hMrlip (tbR D s) (taR D s)
    have h2 : tbR D s - taR D s = sweepW' D s := rfl
    rw [h2, abs_of_nonneg (sweepW'_bounds D s).1] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (sweepW'_bounds D s).2 hMr)
  have hm : ‖min lay (cQ * dep / L) • V‖
      ≤ max (lay * Mr * period) (|cQ| * max (lay * period) |ρ|) := by
    rcases le_total lay (cQ * dep / L) with hle | hle
    · have h : ‖min lay (cQ * dep / L) • V‖ = lay * L := by
        rw [min_eq_left hle, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlay0, hVL]
      rw [h]
      calc lay * L ≤ lay * (Mr * period) := mul_le_mul_of_nonneg_left hchord hlay0
        _ = lay * Mr * period := by ring
        _ ≤ _ := le_max_left _ _
    · have hmem : ‖min lay (cQ * dep / L) • V‖ ≤ |cQ| * dep := by
        rw [min_eq_right hle]
        rcases eq_or_ne L 0 with hLz | hLz
        · have hV0 : V = 0 := by
            have hzero : ‖V‖ = 0 := by rw [hVL, hLz]
            exact norm_eq_zero.mp hzero
          rw [hV0, smul_zero, norm_zero]
          exact mul_nonneg (abs_nonneg cQ) hdep0
        · have hcQ : |cQ * dep / L| = |cQ| * dep / L := by
            rw [abs_div, abs_mul, abs_of_nonneg hdep0, abs_of_nonneg hL0]
          have h : ‖(cQ * dep / L) • V‖ = |cQ| * dep := by
            rw [norm_smul, Real.norm_eq_abs, hcQ, hVL, div_mul_cancel₀ _ hLz]
          rw [h]
      calc ‖min lay (cQ * dep / L) • V‖ ≤ |cQ| * dep := hmem
        _ ≤ |cQ| * max (lay * period) |ρ| :=
            mul_le_mul_of_nonneg_left hdeple (abs_nonneg cQ)
        _ ≤ _ := le_max_right _ _
  have hb : schedBeta r lay ρ δs cQ D s
      = (1 - ψ) * lay + ψ * min lay (cQ * dep / L) := rfl
  rw [hb, add_smul]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖((1 - ψ) * lay) • V‖ ≤ (1 - ψ) * (lay * Mr * period) := by
    have h : ‖((1 - ψ) * lay) • V‖ = (1 - ψ) * lay * L := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) hlay0), hVL]
    rw [h]
    calc (1 - ψ) * lay * L ≤ (1 - ψ) * lay * (Mr * period) :=
          mul_le_mul_of_nonneg_left hchord (mul_nonneg (by linarith) hlay0)
      _ = (1 - ψ) * (lay * Mr * period) := by ring
  have h2 : ‖(ψ * min lay (cQ * dep / L)) • V‖
      ≤ ψ * max (lay * Mr * period) (|cQ| * max (lay * period) |ρ|) := by
    have h : (ψ * min lay (cQ * dep / L)) • V = ψ • (min lay (cQ * dep / L) • V) := by
      rw [smul_smul]
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg hψ0]
    exact mul_le_mul_of_nonneg_left hm hψ0
  have hBz : lay * Mr * period ≤ lay * Mr * period + |cQ| * max (lay * period) |ρ| :=
    le_add_of_nonneg_right (mul_nonneg (abs_nonneg cQ) hDz0)
  have hmax : max (lay * Mr * period) (|cQ| * max (lay * period) |ρ|)
      ≤ lay * Mr * period + |cQ| * max (lay * period) |ρ| :=
    max_le hBz (le_add_of_nonneg_left (mul_nonneg (mul_nonneg hlay0 hMr) period_pos.le))
  calc ‖((1 - ψ) * lay) • V‖ + ‖(ψ * min lay (cQ * dep / L)) • V‖
      ≤ (1 - ψ) * (lay * Mr * period)
          + ψ * max (lay * Mr * period) (|cQ| * max (lay * period) |ρ|) := add_le_add h1 h2
    _ ≤ (1 - ψ) * (lay * Mr * period + |cQ| * max (lay * period) |ρ|)
          + ψ * (lay * Mr * period + |cQ| * max (lay * period) |ρ|) := by
        refine add_le_add ?_ (mul_le_mul_of_nonneg_left hmax hψ0)
        exact mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) hmax) (by linarith)
    _ = lay * Mr * period + |cQ| * max (lay * period) |ρ| := by ring

/-! ### Closedness of the profile loop -/

/-- **The profile loop is closed**: `Φ 1 = Φ 0` (both are the arc point at fraction `α s`). -/
lemma chamferProf_zero_eq_one {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay a b : ℝ} (hlay : 0 < lay) (hlay1 : lay < 1 / 2) (s : ℝ) :
    chamferLoopProf r D lay a b s 1 = chamferLoopProf r D lay a b s 0 := by
  have h0 : chamferLoopProf r D lay a b s 0 = sweepArc' r D s a := by
    rw [chamferLoopProf, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  have h1 : chamferLoopProf r D lay a b s 1 = sweepArc' r D s a := by
    rw [chamferLoopProf, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2),
      if_neg (by linarith : ¬ (1 : ℝ) ≤ 1 / 2 + lay / 2),
      if_neg (by linarith : ¬ (1 : ℝ) ≤ 1 - lay / 2)]
    have hd : lay / 2 ≠ 0 := by positivity
    rw [show (1 : ℝ) - (1 - lay / 2) = lay / 2 by ring, div_self hd, sub_self, zero_smul,
      zero_add, one_smul]
  rw [h0, h1]

/-! ### From the profile variable to the loop parameter -/

/-- **The sawtooth reduction.**  If `Φ` is `K`-Lipschitz on the line *and* closed
(`Φ 1 = Φ 0`), then the composed loop `x ↦ Φ (sweepParam x)` is Lipschitz with constant
`K / period`: on a single cell this is the Lipschitz property of `Φ`, and across the
discontinuity of the sawtooth the two pieces are glued by `Φ 1 = Φ 0`. -/
lemma sweepParam_lipschitz_of_closed {Φ : ℝ → Space} {K : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ u v : ℝ, ‖Φ u - Φ v‖ ≤ K * |u - v|) (hper : Φ 1 = Φ 0) :
    ∀ x y : ℝ, ‖Φ (sweepParam x) - Φ (sweepParam y)‖ ≤ (K / period) * |x - y| := by
  have key : ∀ x y : ℝ, x ≤ y →
      ‖Φ (sweepParam x) - Φ (sweepParam y)‖ ≤ (K / period) * (y - x) := by
    intro x y hxy
    have hux := sweepParam_mem x
    have huy := sweepParam_mem y
    have hkx : x / period = sweepParam x + ((⌊x / period⌋ : ℤ) : ℝ) :=
      (Int.fract_add_floor (x / period)).symm.trans (by rw [sweepParam_eq_fract])
    have hky : y / period = sweepParam y + ((⌊y / period⌋ : ℤ) : ℝ) :=
      (Int.fract_add_floor (y / period)).symm.trans (by rw [sweepParam_eq_fract])
    have hx : x = (sweepParam x + ((⌊x / period⌋ : ℤ) : ℝ)) * period := by
      rw [← hkx, div_mul_cancel₀ x period_ne_zero]
    have hy : y = (sweepParam y + ((⌊y / period⌋ : ℤ) : ℝ)) * period := by
      rw [← hky, div_mul_cancel₀ y period_ne_zero]
    have hdiff : y - x = (sweepParam y - sweepParam x
        + (((⌊y / period⌋ : ℤ) - ⌊x / period⌋ : ℤ) : ℝ)) * period := by
      push_cast
      linarith [hx, hy]
    have hfloor : (⌊x / period⌋ : ℤ) ≤ ⌊y / period⌋ :=
      Int.floor_mono (div_le_div_of_nonneg_right hxy period_pos.le)
    have hqp : (y - x) / period = (sweepParam y - sweepParam x)
        + (((⌊y / period⌋ : ℤ) - ⌊x / period⌋ : ℤ) : ℝ) := by
      rw [hdiff, mul_div_cancel_right₀ _ period_ne_zero]
    rcases lt_or_ge (sweepParam x) (sweepParam y) with huv | huv
    · have h1 : sweepParam y - sweepParam x ≤ (y - x) / period := by
        rw [hqp]
        have : (0 : ℝ) ≤ (((⌊y / period⌋ : ℤ) - ⌊x / period⌋ : ℤ) : ℝ) := by
          have h : (0 : ℤ) ≤ ⌊y / period⌋ - ⌊x / period⌋ := by omega
          exact_mod_cast h
        linarith
      have h2 := hlip (sweepParam x) (sweepParam y)
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ sweepParam y - sweepParam x)]
        at h2
      calc ‖Φ (sweepParam x) - Φ (sweepParam y)‖ ≤ K * (sweepParam y - sweepParam x) := h2
        _ ≤ K * ((y - x) / period) := mul_le_mul_of_nonneg_left h1 hK
        _ = (K / period) * (y - x) := by ring
    · rcases eq_or_lt_of_le huv with heq | hlt
      · rw [heq, sub_self, norm_zero]
        exact mul_nonneg (div_nonneg hK period_pos.le) (by linarith)
      · have hkpos : (0 : ℝ) < (((⌊y / period⌋ : ℤ) - ⌊x / period⌋ : ℤ) : ℝ) := by
          have h1 : 0 ≤ (y - x) / period := div_nonneg (by linarith) period_pos.le
          rw [hqp] at h1
          linarith
        have hk1 : (1 : ℝ) ≤ (((⌊y / period⌋ : ℤ) - ⌊x / period⌋ : ℤ) : ℝ) := by
          have hZ : (0 : ℤ) < ⌊y / period⌋ - ⌊x / period⌋ := by exact_mod_cast hkpos
          have : (1 : ℤ) ≤ ⌊y / period⌋ - ⌊x / period⌋ := Int.lt_iff_add_one_le.mp hZ
          exact_mod_cast this
        have h1 : (1 - sweepParam x) + sweepParam y ≤ (y - x) / period := by
          rw [hqp]; linarith
        have he : Φ (sweepParam x) - Φ (sweepParam y)
            = (Φ (sweepParam x) - Φ 1) + (Φ 0 - Φ (sweepParam y)) := by
          rw [← hper]; abel
        have h2 : ‖Φ (sweepParam x) - Φ 1‖ ≤ K * (1 - sweepParam x) := by
          have h := hlip (sweepParam x) 1
          rw [abs_of_nonpos (by linarith [hux.2] : sweepParam x - 1 ≤ 0)] at h
          linarith [h]
        have h3 : ‖Φ 0 - Φ (sweepParam y)‖ ≤ K * sweepParam y := by
          have h := hlip 0 (sweepParam y)
          rw [zero_sub, abs_neg, abs_of_nonneg huy.1] at h
          exact h
        rw [he]
        calc ‖(Φ (sweepParam x) - Φ 1) + (Φ 0 - Φ (sweepParam y))‖
            ≤ ‖Φ (sweepParam x) - Φ 1‖ + ‖Φ 0 - Φ (sweepParam y)‖ := norm_add_le _ _
          _ ≤ K * (1 - sweepParam x) + K * sweepParam y := add_le_add h2 h3
          _ = K * ((1 - sweepParam x) + sweepParam y) := by ring
          _ ≤ K * ((y - x) / period) := mul_le_mul_of_nonneg_left h1 hK
          _ = (K / period) * (y - x) := by ring
  intro x y
  rcases le_total x y with hxy | hxy
  · rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - x)]
    exact key x y hxy
  · rw [norm_sub_rev, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
    exact key y x hxy

end Work.Drive
