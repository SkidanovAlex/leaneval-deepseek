import Mathlib
import Submission.Work.Drive.sweepFamOfSlicesOfCone
import Submission.Work.Drive.schedContinuity
import Submission.Work.Drive.chamferLoopGenBlur
import Submission.Work.Drive.chamferLoopGenLipschitzT
import Submission.Work.Drive.chamferChordNoPiCorner

/-!
# The slices clause of the *scheduled* loop, from the blur package (the clamped assembly)

`NOTES_LEAD_scheduledBlur.md` §3 asks for the final statement of the blur layer: the slices clause of
the double blur of the scheduled loop `Γ = chamferLoopGen r D lay (schedAlpha …) (schedBeta …)` on a
compact window `[a,b] ⊂ (0,1)`, with the width budget `L ≤ a/2`, `L ≤ (1-b)/2` (so that the `σ`-blur
window of a slice `σ ∈ [a,b]` stays inside the clamped window on which the schedules are regular).

This module performs the whole **analytic** part of that assembly, leaving the two *geometric* inputs
as explicit hypotheses:

* `hloc` — the pointwise local secant cone of the scheduled loop on the clamped window
  `[a/2, (1+b)/2]`.  Its producer is `chamferLoopGen_localCone` (the note's §2), whose content is
  `Work.Drive.ChamferJunctionOK`;
* `hinj` — the injectivity on one period of the **raw** scheduled loop on the clamped window.

Everything else is supplied here from proved pieces:

* `Work.Drive.sweepFamOf_slices_of_localCone_window` (the blur package of this lane);
* `Work.Drive.continuous_schedAlpha_comp_clamp` / `continuous_schedBeta_comp_clamp`
  (`schedContinuity.lean`, this lane) for the joint continuity of the clamped loop;
* `Work.Drive.chamferLoopGenLipschitzT` (the Lipschitz constant in the loop parameter);
* `Work.Drive.sweepFamOf_congr_window` (the transfer from the clamped loop back to `Γ`, which is what
  makes the width budget `L ≤ a/2`, `L ≤ (1-b)/2` necessary).

The conclusion is exactly the blurred-slices clause (`InjOn` on one period and non-vanishing velocity)
for `Work.Drive.sweepFamOf Γ δ₁ δ₂ σ`, i.e. the shape the top end
(`Work.Drive.sweepToNeedleStrictNT_gen`'s `hcomb`) consumes.
-/

noncomputable section

set_option maxHeartbeats 4000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- The *scheduled loop*, named: `chamferLoopGen r D lay (schedAlpha …) (schedBeta …)`.  Naming it
keeps the statements of this file cheap to elaborate (the schedules are heavy terms). -/
def schedLoop (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lay ρ₀ δs cQ : ℝ) :
    ℝ → ℝ → Space :=
  chamferLoopGen r D lay (schedAlpha lay ρ₀ δs D) (schedBeta r lay ρ₀ δs cQ D)

/-- **Change of schedule at a fixed sweep parameter.**  Two pairs of schedules that agree *at* the
sweep parameter `s` give the same loop slice at `s`.  (Used to compare the clamped loop
`s ↦ Γ (cl s)` with the loop of the clamped schedules.) -/
lemma chamferLoopGen_sched_congr {r : ℝ → Space} {d : BandArcData} (D : SweepData d) (lay : ℝ)
    {α α' β β' : ℝ → ℝ} {s : ℝ} (hα : α' s = α s) (hβ : β' s = β s) :
    chamferLoopGen r D lay α' β' s = chamferLoopGen r D lay α β s := by
  funext t
  simp only [chamferLoopGen]
  rw [hα, hβ]

/-- **The clamped assembly, for an abstract pair of schedules `(α, β)`.**  If the clamped loop
`s ↦ chamferLoopGen r D lay α β (cl s)` (with `cl = schedClamp a b`) is `M`-Lipschitz in the loop
parameter, the clamped schedules are continuous, there is a pointwise local cone on the clamped
window for the *unclamped* loop and the unclamped raw loop is injective on one period there, then
the blurred slices of the unclamped scheduled loop are injective with non-vanishing velocity for all
small widths, with the width budget `L ≤ a/2`, `L ≤ (1-b)/2`. -/
private theorem schedCore {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d)
    {lay : ℝ} (hlay0 : 0 < lay) (hlay1 : lay < 1 / 2) {α β : ℝ → ℝ}
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) {M : ℝ} (hMnn : 0 ≤ M)
    (hMc : ∀ s t₁ t₂ : ℝ,
      ‖chamferLoopGen r D lay α β (schedClamp a b s) t₁
        - chamferLoopGen r D lay α β (schedClamp a b s) t₂‖ ≤ M * |t₂ - t₁|)
    (hαcl : Continuous (fun s : ℝ => α (schedClamp a b s)))
    (hβcl : Continuous (fun s : ℝ => β (schedClamp a b s)))
    (hloc : ∀ σ₀ ∈ Set.Icc (a / 2) ((1 + b) / 2), ∀ t₀ ∈ Set.Icc (0 : ℝ) period,
      ∃ (n : Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
        ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
          c * (t₂ - t₁) ≤ inner ℝ n
            (chamferLoopGen r D lay α β s t₂ - chamferLoopGen r D lay α β s t₁))
    (hinj : ∀ s ∈ Set.Icc (a / 2) ((1 + b) / 2),
      Set.InjOn (chamferLoopGen r D lay α β s) (Set.Ico (0 : ℝ) period)) :
    ∃ L : ℝ, 0 < L ∧ L ≤ a / 2 ∧ L ≤ (1 - b) / 2 ∧
      ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L → ∀ σ ∈ Set.Icc a b,
        Set.InjOn (fun t : ℝ => sweepFamOf (chamferLoopGen r D lay α β) δ₁ δ₂ σ t)
          (Set.Ico (0 : ℝ) period) ∧
        ∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf (chamferLoopGen r D lay α β) δ₁ δ₂ σ t) t ≠ 0 := by
  have hab' : a / 2 ≤ (1 + b) / 2 := by linarith
  -- ## joint continuity of the clamped loop, from the composed schedules
  have hΓc : Continuous (fun p : ℝ × ℝ =>
      chamferLoopGen r D lay α β (schedClamp a b p.1) p.2) := by
    have h1 : Continuous (fun p : ℝ × ℝ => chamferLoopGen r D lay
        (fun s : ℝ => α (schedClamp a b s)) (fun s : ℝ => β (schedClamp a b s)) p.1 p.2) :=
      continuous_chamferLoopGen hr.continuous D hlay0 hlay1 hαcl hβcl
    have h2 : Continuous (fun p : ℝ × ℝ => ((schedClamp a b p.1, p.2) : ℝ × ℝ)) :=
      ((continuous_schedClamp a b).comp continuous_fst).prodMk continuous_snd
    have h3 : Continuous (fun p : ℝ × ℝ => chamferLoopGen r D lay
        (fun s : ℝ => α (schedClamp a b s)) (fun s : ℝ => β (schedClamp a b s))
        (schedClamp a b p.1) p.2) := h1.comp h2
    have hFG : (fun p : ℝ × ℝ => chamferLoopGen r D lay
          (fun s : ℝ => α (schedClamp a b s)) (fun s : ℝ => β (schedClamp a b s))
          (schedClamp a b p.1) p.2)
        = (fun p : ℝ × ℝ => chamferLoopGen r D lay α β (schedClamp a b p.1) p.2) := by
      funext p
      exact congrFun (chamferLoopGen_sched_congr (r := r) (d := d) D lay
        (α := α) (α' := fun s : ℝ => α (schedClamp a b s))
        (β := β) (β' := fun s : ℝ => β (schedClamp a b s)) (s := schedClamp a b p.1)
        (by show α (schedClamp a b (schedClamp a b p.1)) = α (schedClamp a b p.1)
            rw [schedClamp_idem hab'])
        (by show β (schedClamp a b (schedClamp a b p.1)) = β (schedClamp a b p.1)
            rw [schedClamp_idem hab'])) p.2
    rw [← hFG]
    exact h3
  -- ## the clamped loop agrees with `Γ` on `[a,b]`
  have hcl_eq : ∀ s ∈ Set.Icc a b, schedClamp a b s = s := fun s hs =>
    schedClamp_eq_self hab' ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hper' : ∀ s t : ℝ, chamferLoopGen r D lay α β (schedClamp a b s) (t + period)
      = chamferLoopGen r D lay α β (schedClamp a b s) t :=
    fun s t => chamferLoopGen_periodic_t D lay α β (schedClamp a b s) t
  have hinjc : ∀ s ∈ Set.Icc a b,
      Set.InjOn (chamferLoopGen r D lay α β (schedClamp a b s)) (Set.Ico (0 : ℝ) period) := by
    intro s hs
    rw [hcl_eq s hs]
    exact hinj s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hlocc : ∀ σ₀ ∈ Set.Icc a b, ∀ t₀ ∈ Set.Icc (0 : ℝ) period,
      ∃ (n : Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
        ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
          c * (t₂ - t₁) ≤ inner ℝ n
            (chamferLoopGen r D lay α β (schedClamp a b s) t₂
              - chamferLoopGen r D lay α β (schedClamp a b s) t₁) := by
    intro σ₀ hσ₀ t₀ ht₀
    have hm0 : (0 : ℝ) < min (a / 2) ((1 - b) / 2) := lt_min (by linarith) (by linarith)
    obtain ⟨n, ε₀, c, hε₀, hc, hcone⟩ := hloc σ₀
      ⟨by linarith [hσ₀.1], by linarith [hσ₀.2]⟩ t₀ ht₀
    refine ⟨n, min ε₀ (min (a / 2) ((1 - b) / 2) / 2), c, lt_min hε₀ (by linarith), hc, ?_⟩
    intro s hs t₁ t₂ h1 h2 h3
    have hεle : min ε₀ (min (a / 2) ((1 - b) / 2) / 2) ≤ ε₀ := min_le_left _ _
    have hmle : min ε₀ (min (a / 2) ((1 - b) / 2) / 2) ≤ min (a / 2) ((1 - b) / 2) :=
      (min_le_right _ _).trans (by linarith : min (a / 2) ((1 - b) / 2) / 2
        ≤ min (a / 2) ((1 - b) / 2))
    have hslo : a / 2 ≤ s := by
      have h1' : σ₀ - min (a / 2) ((1 - b) / 2) ≤ s := by linarith [hs.1, hmle]
      have h2' : min (a / 2) ((1 - b) / 2) ≤ σ₀ - a / 2 := by
        have := min_le_left (a / 2) ((1 - b) / 2); linarith [hσ₀.1]
      linarith
    have hshi : s ≤ (1 + b) / 2 := by
      have h1' : s ≤ σ₀ + min (a / 2) ((1 - b) / 2) := by linarith [hs.2, hmle]
      have h2' : min (a / 2) ((1 - b) / 2) ≤ (1 + b) / 2 - σ₀ := by
        have := min_le_right (a / 2) ((1 - b) / 2); linarith [hσ₀.2]
      linarith
    have hcl : schedClamp a b s = s := by
      rw [schedClamp, min_eq_left hshi, max_eq_right hslo]
    rw [hcl]
    exact hcone s (Set.mem_Icc.mpr ⟨by linarith [hs.1, hεle], by linarith [hs.2, hεle]⟩)
      t₁ t₂ (by linarith [h1, hεle]) h2 (by linarith [h3, hεle])
  -- ## the package on the clamped loop
  obtain ⟨L, hL, hLa, hLb, hmain⟩ :=
    sweepFamOf_slices_of_localCone_window
      (Γ := fun s t => chamferLoopGen r D lay α β (schedClamp a b s) t)
      hΓc hper' hMnn hMc ha hab hb hinjc hlocc
  refine ⟨L, hL, hLa, hLb, ?_⟩
  intro δ₁ δ₂ h1 h2 h3 h4 σ hσ
  have hδ₂' : δ₂ ≤ a / 2 := le_trans h4 hLa
  have hδ₂'' : δ₂ ≤ (1 - b) / 2 := le_trans h4 hLb
  have hcongr : sweepFamOf (fun s t => chamferLoopGen r D lay α β (schedClamp a b s) t) δ₁ δ₂ σ
      = sweepFamOf (chamferLoopGen r D lay α β) δ₁ δ₂ σ := by
    refine sweepFamOf_congr_window δ₁ δ₂ σ (fun v hv t => ?_)
    have hle1 : δ₂ * v ≤ δ₂ * 1 := mul_le_mul_of_nonneg_left hv.2 (le_of_lt h3)
    have hle2 : -(δ₂ * 1) ≤ δ₂ * v := by
      have := mul_le_mul_of_nonneg_left hv.1 (le_of_lt h3)
      linarith
    have hmem : σ - δ₂ * v ∈ Set.Icc (a / 2) ((1 + b) / 2) :=
      ⟨by linarith [hσ.1, hle1, hδ₂'], by linarith [hσ.2, hle2, hδ₂'']⟩
    rw [schedClamp_eq_self hab' hmem]
  obtain ⟨hinjσ, hvelσ⟩ := hmain δ₁ δ₂ h1 h2 h3 h4 σ hσ
  refine ⟨?_, ?_⟩
  · rw [← hcongr]; exact hinjσ
  · intro t
    rw [← hcongr]; exact hvelσ t

/-! ## The trough zone: the schedules are constant, so the scheduled blur is the standard one

On the *trough* zone (the note's zone 0) both schedules are at their floor `lay`: the depth is
`lay · sweepW'` and the chord target is `lay`.  There the scheduled loop *is* the standard chamfer
loop and the blurred family is the standard `Work.Drive.sweepFam`, which is the junction at which the
needle end (`Work.Drive.sweepNeedleFam = Work.Drive.sweepFam · ε`) attaches to the top end. -/

/-- **The depth fraction is at its floor on the trough zone**: if `2 · schedC D σ ≤ δs` (and the
retained width is positive, `lay ≥ 0`), then `schedAlpha = lay`. -/
lemma schedAlpha_eq_lay_of_schedC {d : BandArcData} (D : SweepData d) {lay ρ δs : ℝ}
    (hδs : 0 < δs) (hlay : 0 ≤ lay) {σ : ℝ} (hW : 0 < sweepW' D σ)
    (hc : 2 * schedC D σ ≤ δs) : schedAlpha lay ρ δs D σ = lay := by
  have hphi : schedPhi (schedC D σ / δs) = 0 := by
    rw [schedPhi_eq_zero_iff, div_le_iff₀ hδs]; linarith
  have hdep : schedDep lay ρ δs D σ = lay * sweepW' D σ := by
    rw [schedDep, hphi, mul_zero, max_eq_left (mul_nonneg hlay hW.le)]
  rw [schedAlpha, hdep, mul_div_cancel_right₀ lay (ne_of_gt hW)]

/-- **The chord target is at its floor on the trough zone**: if `4 · schedC D σ ≤ δs` then
`schedBeta = lay`.  (Note the factor `4`: `schedC` enters `schedPsi` with a factor `2`, and
`schedPhi` halves again.) -/
lemma schedBeta_eq_lay_of_schedC {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay ρ δs cQ : ℝ} (hδs : 0 < δs) {σ : ℝ} (hc : 4 * schedC D σ ≤ δs) :
    schedBeta r lay ρ δs cQ D σ = lay := by
  have hpsi : schedPsi D δs σ = 0 := by
    rw [schedPsi, schedPhi_eq_zero_iff, div_le_iff₀ hδs]; linarith
  rw [schedBeta, hpsi]
  ring

/-- **The junction with the needle end.**  If both schedules are at their floor `lay` on the whole
`δ₂`-blur window of the slice `ε`, then the blurred slice of the *scheduled* loop at `ε` is the
standard blurred slice, i.e. the needle `Work.Drive.sweepNeedleFam r D lay δ₁ δ₂ ε` of the top end's
statement.  (This is `Work.Drive.sweepFamOf_chamferLoopGen_eq_sweepFam` plus the definitional identity
`sweepNeedleFam = sweepFam · ε`.) -/
theorem sweepFamOf_schedLoop_eq_needle {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay ρ₀ δs cQ δ₁ δ₂ ε : ℝ}
    (hwin : ∀ v ∈ Set.Icc (-1 : ℝ) 1, schedAlpha lay ρ₀ δs D (ε - δ₂ * v) = lay ∧
      schedBeta r lay ρ₀ δs cQ D (ε - δ₂ * v) = lay) :
    sweepFamOf (schedLoop r D lay ρ₀ δs cQ) δ₁ δ₂ ε = sweepNeedleFam r D lay δ₁ δ₂ ε :=
  sweepFamOf_chamferLoopGen_eq_sweepFam (r := r) D (lay := lay)
    (α := schedAlpha lay ρ₀ δs D) (β := schedBeta r lay ρ₀ δs cQ D) (σ := ε)
    (δ₁ := δ₁) (δ₂ := δ₂) hwin

/-- **The slices clause of the scheduled blur, with the geometric inputs exposed.**  With
`Γ := schedLoop r D lay ρ₀ δs cQ`, if

* `hloc` is a pointwise local cone for `Γ` on the clamped window `[a/2, (1+b)/2]` (producer:
  `chamferLoopGen_localCone`, from `ChamferJunctionOK`), and
* `hinj` is the injectivity on one period of the raw loop `Γ s` on the clamped window,

then there is a positive width budget `L ≤ a/2`, `L ≤ (1-b)/2` such that for all `0 < δ₁, δ₂ ≤ L` and
all `σ ∈ [a,b]` the blurred slice `sweepFamOf Γ δ₁ δ₂ σ` is injective on one period and has
nowhere-vanishing velocity. -/
theorem chamferLoopGen_blurSlices_of_localCone {r : ℝ → Space} (hr : IsSmoothKnot r)
    {d : BandArcData} (D : SweepData d) {lay ρ₀ δs cQ : ℝ}
    (hlay0 : 0 < lay) (hlay : lay ≤ 1 / 4) (hδs : 0 < δs)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hcL : ∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2), ‖r (tbR D σ) - r (taR D σ)‖ ≠ 0)
    (hloc : ∀ σ₀ ∈ Set.Icc (a / 2) ((1 + b) / 2), ∀ t₀ ∈ Set.Icc (0 : ℝ) period,
      ∃ (n : Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
        ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
          c * (t₂ - t₁) ≤ inner ℝ n
            (schedLoop r D lay ρ₀ δs cQ s t₂ - schedLoop r D lay ρ₀ δs cQ s t₁))
    (hinj : ∀ s ∈ Set.Icc (a / 2) ((1 + b) / 2),
      Set.InjOn (schedLoop r D lay ρ₀ δs cQ s) (Set.Ico (0 : ℝ) period)) :
    ∃ L : ℝ, 0 < L ∧ L ≤ a / 2 ∧ L ≤ (1 - b) / 2 ∧
      ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L → ∀ σ ∈ Set.Icc a b,
        Set.InjOn (fun t : ℝ => sweepFamOf (schedLoop r D lay ρ₀ δs cQ) δ₁ δ₂ σ t)
          (Set.Ico (0 : ℝ) period) ∧
        ∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf (schedLoop r D lay ρ₀ δs cQ) δ₁ δ₂ σ t)
          t ≠ 0 := by
  have hlay1 : lay < 1 / 2 := by linarith
  have hb2 : (1 + b) / 2 < 1 := by linarith
  have hWne : ∀ σ ∈ Set.Icc (a / 2) ((1 + b) / 2), sweepW' D σ ≠ 0 := fun σ hσ =>
    ne_of_gt (sweepW'_pos_lt D (by linarith [ha, hσ.1]) (lt_of_le_of_lt hσ.2 hb2)).1
  obtain ⟨M, hMnn, hM⟩ := chamferLoopGenLipschitzT hr D (ρ₀ := ρ₀) (δs := δs) (cQ := cQ)
    hlay0 hlay1 hδs
  exact schedCore hr D hlay0 hlay1 ha hab hb hMnn
    (fun s t₁ t₂ => hM (schedClamp a b s) t₁ t₂)
    (continuous_schedAlpha_comp_clamp D (by linarith : a / 2 ≤ (1 + b) / 2) hWne)
    (continuous_schedBeta_comp_clamp D hr.continuous
      (by linarith : a / 2 ≤ (1 + b) / 2) hcL)
    hloc hinj

/-- **The same, with the chord non-degeneracy discharged.**  On the clamped window
`[a/2, (1+b)/2] ⊂ (0,1)` the chord `r (tbR D σ) - r (taR D σ)` is bounded away from `0`
(`Work.Drive.sweepFamChord_lower_bound`), so the hypothesis `hcL` of
`Work.Drive.chamferLoopGen_blurSlices_of_localCone` is free.  This is the form in which the
geometric inputs reduce to *exactly* the pair (`hcone`, `hinj`). -/
theorem chamferLoopGen_blurSlices_of_localCone' {r : ℝ → Space} (hr : IsSmoothKnot r)
    {d : BandArcData} (D : SweepData d) {lay ρ₀ δs cQ : ℝ}
    (hlay0 : 0 < lay) (hlay : lay ≤ 1 / 4) (hδs : 0 < δs)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hloc : ∀ σ₀ ∈ Set.Icc (a / 2) ((1 + b) / 2), ∀ t₀ ∈ Set.Icc (0 : ℝ) period,
      ∃ (n : Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
        ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
          c * (t₂ - t₁) ≤ inner ℝ n
            (schedLoop r D lay ρ₀ δs cQ s t₂ - schedLoop r D lay ρ₀ δs cQ s t₁))
    (hinj : ∀ s ∈ Set.Icc (a / 2) ((1 + b) / 2),
      Set.InjOn (schedLoop r D lay ρ₀ δs cQ s) (Set.Ico (0 : ℝ) period)) :
    ∃ L : ℝ, 0 < L ∧ L ≤ a / 2 ∧ L ≤ (1 - b) / 2 ∧
      ∀ δ₁ δ₂ : ℝ, 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L → ∀ σ ∈ Set.Icc a b,
        Set.InjOn (fun t : ℝ => sweepFamOf (schedLoop r D lay ρ₀ δs cQ) δ₁ δ₂ σ t)
          (Set.Ico (0 : ℝ) period) ∧
        ∀ t : ℝ, velocity (fun t : ℝ => sweepFamOf (schedLoop r D lay ρ₀ δs cQ) δ₁ δ₂ σ t)
          t ≠ 0 := by
  obtain ⟨δ, hδpos, hδ⟩ := sweepFamChord_lower_bound hr D (a := a / 2) (b := (1 + b) / 2)
    (by linarith) (by linarith) (by linarith)
  exact chamferLoopGen_blurSlices_of_localCone hr D hlay0 hlay hδs ha hab hb
    (fun σ hσ => ne_of_gt (lt_of_lt_of_le hδpos (hδ σ hσ))) hloc hinj

end Work.Drive
