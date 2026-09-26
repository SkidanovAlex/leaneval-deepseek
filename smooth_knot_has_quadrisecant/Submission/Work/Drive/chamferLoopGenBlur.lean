import Mathlib
import Submission.Work.Drive.chamferLoopGenDefs
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.sweepFamOf_contDiff_periodic
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable
import Submission.Work.Drive.thinLoopSeparation

/-!
# The blur of the scheduled chamfer loop: joint continuity and the zone coincidences

The uniform-`ρ₀` design (`NOTES_LEAD_endgameUniform.md` §3, §5) runs the *scheduled* loop

`Γ := Work.Drive.chamferLoopGen r D lay α β`

through the same double bump-blur `Work.Drive.sweepFamOf` that the old design applied to the standard
chamfer loop.  This module supplies the two *vocabulary-level* inputs the blur layer needs:

* **joint continuity** of `Γ` (`Work.Drive.continuous_chamferLoopGen`): the loop is the composition
  of the *profile* `Work.Drive.chamferLoopProf` (piecewise in the profile variable `u`, globally
  continuous by `Continuous.if_le`) with the sawtooth `sweepParam`, which is handled by the
  factorisation through `Int.fract` (`Work.Drive.sweepParam_eq_fract`,
  `ContinuousOn.comp_fract'`).  This is what `Work.Drive.farSep_window_of_injOn` and the local
  injectivity layer consume.
* the **zone coincidences**: at a slice where the schedule is constant (`α s = β s = lay`) the loop
  *is* the standard chamfer loop, and — because the blur only sees a neighbourhood of the slice —
  the blurred family coincides with `Work.Drive.sweepFam r D lay δ₁ δ₂` there.  These are the
  coincidences by which the needle end (`sweepNeedleFam r D lay δ₁ δ₂ ε`) and the wide-end estimate
  (`Work.Drive.wideEnd_prescribed`, stated for `sweepFam`) apply to the scheduled family.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The profile of the scheduled chamfer loop**: the piecewise formula of
`Work.Drive.chamferLoopGen` with the profile variable `u` explicit and the two cut fractions
`a = α s`, `b = β s` as parameters. -/
def chamferLoopProf (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lay a b s u : ℝ) : Space :=
  if u ≤ 1 / 2 then sweepArc' r D s (a + (1 - 2 * a) * (2 * u))
  else if u ≤ 1 / 2 + lay / 2 then
    (1 - (2 * u - 1) / lay) • sweepArc' r D s (1 - a)
      + ((2 * u - 1) / lay) • sweepChord' r D s (1 - b)
  else if u ≤ 1 - lay / 2 then
    sweepChord' r D s ((1 - b) - ((u - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b))
  else (1 - (u - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D s b
      + ((u - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D s a

/-- The scheduled loop is its profile at the loop fraction. -/
lemma chamferLoopGen_eq_prof' (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lay : ℝ)
    (α β : ℝ → ℝ) (s t : ℝ) :
    chamferLoopGen r D lay α β s t
      = chamferLoopProf r D lay (α s) (β s) s (sweepParam t) := rfl

/-! ## Joint continuity of the profile -/

/-- **The profile is jointly continuous.**  The four branches are continuous in `(s, u)` (the data
`taR`, `tbR`, `sweepW'` and the schedules `α`, `β` are continuous), and they agree at the three
junctions `u = 1/2`, `u = 1/2 + lay/2`, `u = 1 - lay/2`. -/
theorem continuous_chamferLoopProf {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lay : ℝ} (hlay0 : 0 < lay) (hlay1 : lay < 1 / 2)
    {α β : ℝ → ℝ} (hα : Continuous α) (hβ : Continuous β) :
    Continuous (fun p : ℝ × ℝ => chamferLoopProf r D lay (α p.1) (β p.1) p.1 p.2) := by
  have hta : Continuous (fun p : ℝ × ℝ => taR D p.1) :=
    (sweepLoopChamfer_taR_continuous D).comp continuous_fst
  have htb : Continuous (fun p : ℝ × ℝ => tbR D p.1) :=
    (sweepLoopChamfer_tbR_continuous D).comp continuous_fst
  have hW : Continuous (fun p : ℝ × ℝ => sweepW' D p.1) :=
    (sweepLoopChamfer_sweepW'_continuous D).comp continuous_fst
  have hαc : Continuous (fun p : ℝ × ℝ => α p.1) := hα.comp continuous_fst
  have hβc : Continuous (fun p : ℝ × ℝ => β p.1) := hβ.comp continuous_fst
  have hrc : Continuous (fun p : ℝ × ℝ => r (taR D p.1)) := hr.comp hta
  have hrb : Continuous (fun p : ℝ × ℝ => r (tbR D p.1)) := hr.comp htb
  have hsA : Continuous (fun p : ℝ × ℝ => sweepArc' r D p.1 (α p.1)) :=
    hr.comp (show Continuous (fun p : ℝ × ℝ => taR D p.1 + α p.1 * sweepW' D p.1) from
      hta.add (hαc.mul hW))
  have hsB : Continuous (fun p : ℝ × ℝ => sweepArc' r D p.1 (1 - α p.1)) :=
    hr.comp (show Continuous (fun p : ℝ × ℝ => taR D p.1 + (1 - α p.1) * sweepW' D p.1) from
      hta.add ((continuous_const.sub hαc).mul hW))
  have hcB : Continuous (fun p : ℝ × ℝ => sweepChord' r D p.1 (1 - β p.1)) := by
    have h : Continuous (fun p : ℝ × ℝ =>
        (1 - (1 - β p.1)) • r (taR D p.1) + (1 - β p.1) • r (tbR D p.1)) :=
      ((continuous_const.sub (continuous_const.sub hβc)).smul hrc).add
        ((continuous_const.sub hβc).smul hrb)
    simpa only [sweepChord'] using h
  have hcD : Continuous (fun p : ℝ × ℝ => sweepChord' r D p.1 (β p.1)) := by
    have h : Continuous (fun p : ℝ × ℝ =>
        (1 - β p.1) • r (taR D p.1) + β p.1 • r (tbR D p.1)) :=
      ((continuous_const.sub hβc).smul hrc).add (hβc.smul hrb)
    simpa only [sweepChord'] using h
  -- the four branch values
  have hA : Continuous (fun p : ℝ × ℝ => sweepArc' r D p.1 (α p.1 + (1 - 2 * α p.1) * (2 * p.2))) :=
    hr.comp (show Continuous (fun p : ℝ × ℝ =>
        taR D p.1 + (α p.1 + (1 - 2 * α p.1) * (2 * p.2)) * sweepW' D p.1) from by fun_prop)
  have hB : Continuous (fun p : ℝ × ℝ =>
      (1 - (2 * p.2 - 1) / lay) • sweepArc' r D p.1 (1 - α p.1)
        + ((2 * p.2 - 1) / lay) • sweepChord' r D p.1 (1 - β p.1)) := by
    have hc : Continuous (fun p : ℝ × ℝ => (2 * p.2 - 1) / lay) := by fun_prop
    exact ((continuous_const.sub hc).smul hsB).add (hc.smul hcB)
  have hC : Continuous (fun p : ℝ × ℝ =>
      sweepChord' r D p.1 ((1 - β p.1)
        - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β p.1))) := by
    have hξ : Continuous (fun p : ℝ × ℝ => (1 - β p.1)
        - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β p.1)) := by fun_prop
    have h : Continuous (fun p : ℝ × ℝ =>
        (1 - ((1 - β p.1) - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β p.1)))
          • r (taR D p.1)
        + ((1 - β p.1) - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β p.1))
          • r (tbR D p.1)) :=
      ((continuous_const.sub hξ).smul hrc).add (hξ.smul hrb)
    simpa only [sweepChord'] using h
  have hD : Continuous (fun p : ℝ × ℝ =>
      (1 - (p.2 - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D p.1 (β p.1)
        + ((p.2 - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D p.1 (α p.1)) := by
    have hc : Continuous (fun p : ℝ × ℝ => (p.2 - (1 - lay / 2)) / (lay / 2)) := by fun_prop
    exact ((continuous_const.sub hc).smul hcD).add (hc.smul hsA)
  -- the nested `if`s
  have hCD : Continuous (fun p : ℝ × ℝ =>
      if p.2 ≤ 1 - lay / 2 then
        sweepChord' r D p.1 ((1 - β p.1)
          - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β p.1))
      else
        (1 - (p.2 - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D p.1 (β p.1)
          + ((p.2 - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D p.1 (α p.1)) := by
    refine Continuous.if_le (f := fun p : ℝ × ℝ => p.2) (g := fun _ : ℝ × ℝ => 1 - lay / 2)
      hC hD continuous_snd continuous_const ?_
    intro p hp
    have hden : 1 / 2 - lay ≠ 0 := by linarith
    have hquot : (p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay) = 1 := by
      rw [hp, show (1 : ℝ) - lay / 2 - (1 / 2 + lay / 2) = 1 / 2 - lay by ring, div_self hden]
    have hξ : (1 - β p.1)
        - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β p.1) = β p.1 := by
      rw [hquot]; ring
    have hc : (p.2 - (1 - lay / 2)) / (lay / 2) = 0 := by
      rw [hp, sub_self, zero_div]
    rw [hξ, hc]
    simp
  have hBCD : Continuous (fun p : ℝ × ℝ =>
      if p.2 ≤ 1 / 2 + lay / 2 then
        (1 - (2 * p.2 - 1) / lay) • sweepArc' r D p.1 (1 - α p.1)
          + ((2 * p.2 - 1) / lay) • sweepChord' r D p.1 (1 - β p.1)
      else
        if p.2 ≤ 1 - lay / 2 then
          sweepChord' r D p.1 ((1 - β p.1)
            - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β p.1))
        else
          (1 - (p.2 - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D p.1 (β p.1)
            + ((p.2 - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D p.1 (α p.1)) := by
    refine Continuous.if_le (f := fun p : ℝ × ℝ => p.2) (g := fun _ : ℝ × ℝ => 1 / 2 + lay / 2)
      hB hCD continuous_snd continuous_const ?_
    intro p hp
    rw [if_pos (by rw [hp]; linarith)]
    have h1 : 2 * p.2 - 1 = lay := by rw [hp]; ring
    have h2 : p.2 - (1 / 2 + lay / 2) = 0 := by rw [hp]; ring
    have hl : lay / lay = 1 := div_self (ne_of_gt hlay0)
    rw [h1, h2, hl]
    simp
  have hmain : Continuous (fun p : ℝ × ℝ =>
      if p.2 ≤ 1 / 2 then sweepArc' r D p.1 (α p.1 + (1 - 2 * α p.1) * (2 * p.2))
      else
        if p.2 ≤ 1 / 2 + lay / 2 then
          (1 - (2 * p.2 - 1) / lay) • sweepArc' r D p.1 (1 - α p.1)
            + ((2 * p.2 - 1) / lay) • sweepChord' r D p.1 (1 - β p.1)
        else
          if p.2 ≤ 1 - lay / 2 then
            sweepChord' r D p.1 ((1 - β p.1)
              - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * β p.1))
          else
            (1 - (p.2 - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D p.1 (β p.1)
              + ((p.2 - (1 - lay / 2)) / (lay / 2)) • sweepArc' r D p.1 (α p.1)) := by
    refine Continuous.if_le (f := fun p : ℝ × ℝ => p.2) (g := fun _ : ℝ × ℝ => 1 / 2)
      hA hBCD continuous_snd continuous_const ?_
    intro p hp
    rw [if_pos (by rw [hp]; linarith)]
    have h1 : α p.1 + (1 - 2 * α p.1) * (2 * p.2) = 1 - α p.1 := by rw [hp]; ring
    have h2 : 2 * p.2 - 1 = 0 := by rw [hp]; ring
    rw [h1, h2]
    simp
  exact hmain

/-! ## Joint continuity of the loop -/

/-- **The scheduled chamfer loop is jointly continuous.** -/
theorem continuous_chamferLoopGen {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lay : ℝ} (hlay0 : 0 < lay) (hlay1 : lay < 1 / 2)
    {α β : ℝ → ℝ} (hα : Continuous α) (hβ : Continuous β) :
    Continuous (fun p : ℝ × ℝ => chamferLoopGen r D lay α β p.1 p.2) := by
  have hprof := continuous_chamferLoopProf hr D hlay0 hlay1 hα hβ
  have hper : ∀ s : ℝ, chamferLoopProf r D lay (α s) (β s) s 0
      = chamferLoopProf r D lay (α s) (β s) s 1 := by
    intro s
    have h0 : chamferLoopProf r D lay (α s) (β s) s 0 = sweepArc' r D s (α s) := by
      rw [chamferLoopProf, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 2
      ring
    have h1 : chamferLoopProf r D lay (α s) (β s) s 1 = sweepArc' r D s (α s) := by
      rw [chamferLoopProf, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2),
        if_neg (by linarith : ¬ (1 : ℝ) ≤ 1 / 2 + lay / 2),
        if_neg (by linarith : ¬ (1 : ℝ) ≤ 1 - lay / 2)]
      have hd2 : lay / 2 ≠ 0 := by positivity
      have hquot : (1 - (1 - lay / 2)) / (lay / 2) = 1 := by
        rw [show (1 : ℝ) - (1 - lay / 2) = lay / 2 by ring, div_self hd2]
      rw [show (1 : ℝ) - (1 - (1 - lay / 2)) / (lay / 2) = 1 - 1 by rw [hquot], hquot,
        sub_self, zero_smul, zero_add, one_smul]
    rw [h0, h1]
  have hf : Continuous (fun u : ℝ × ℝ => chamferLoopProf r D lay (α u.1) (β u.1) u.1 (Int.fract u.2)) :=
    ContinuousOn.comp_fract' (β := ℝ) hprof.continuousOn hper
  have heq : (fun p : ℝ × ℝ => chamferLoopGen r D lay α β p.1 p.2)
      = (fun u : ℝ × ℝ => chamferLoopProf r D lay (α u.1) (β u.1) u.1 (Int.fract u.2))
        ∘ (fun p : ℝ × ℝ => (p.1, p.2 / period)) := by
    funext p
    show chamferLoopGen r D lay α β p.1 p.2
      = chamferLoopProf r D lay (α p.1) (β p.1) p.1 (Int.fract (p.2 / period))
    rw [chamferLoopGen_eq_prof', sweepParam_eq_fract]
  rw [heq]
  exact hf.comp (continuous_fst.prodMk (continuous_snd.div_const period))

/-- **The scheduled loop is `period`-periodic in the loop parameter.** -/
theorem chamferLoopGen_periodic_t {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (lay : ℝ) (α β : ℝ → ℝ) (s t : ℝ) :
    chamferLoopGen r D lay α β s (t + period) = chamferLoopGen r D lay α β s t := by
  simp only [chamferLoopGen, sweepParam_add_period]

/-- **The scheduled loop is the standard chamfer loop at a slice where the schedule is constant.** -/
theorem chamferLoopGen_eq_chamfer_of_eq {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay : ℝ} {α β : ℝ → ℝ} {σ : ℝ} (hα : α σ = lay) (hβ : β σ = lay) :
    chamferLoopGen r D lay α β σ = sweepLoopChamfer r D lay σ := by
  funext t
  simp only [chamferLoopGen, sweepLoopChamfer, hα, hβ]

/-- **The double blur only sees the sweep parameters in the blur window.**  If two families agree
on `[σ - δ₂, σ + δ₂]` (pointwise in the loop parameter) then their blurred `σ`-slices coincide. -/
theorem sweepFamOf_congr_window {Γ Γ' : ℝ → ℝ → Space} (δ₁ δ₂ σ : ℝ)
    (h : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ t : ℝ, Γ (σ - δ₂ * v) t = Γ' (σ - δ₂ * v) t) :
    sweepFamOf Γ δ₁ δ₂ σ = sweepFamOf Γ' δ₁ δ₂ σ := by
  funext t
  simp only [sweepFamOf]
  apply intervalIntegral.integral_congr
  intro v hv
  dsimp only
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hv
  rw [h v hv (t - δ₁ * u)]

/-- **The blur of the scheduled loop is the blur of the standard chamfer loop at a slice where the
schedule is constant on the whole blur window.** -/
theorem sweepFamOf_chamferLoopGen_eq_sweepFam {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay : ℝ} {α β : ℝ → ℝ} {σ δ₁ δ₂ : ℝ}
    (hwin : ∀ v ∈ Set.Icc (-1 : ℝ) 1, α (σ - δ₂ * v) = lay ∧ β (σ - δ₂ * v) = lay) :
    sweepFamOf (chamferLoopGen r D lay α β) δ₁ δ₂ σ = sweepFam r D lay δ₁ δ₂ σ := by
  rw [sweepFam_eq_sweepFamOf]
  refine sweepFamOf_congr_window δ₁ δ₂ σ (fun v hv t => ?_)
  rw [chamferLoopGen_eq_chamfer_of_eq D (hwin v hv).1 (hwin v hv).2]

/-- **The structural clauses of the blurred scheduled loop.**  If the schedules `α, β` are
continuous, then `sweepFamOf Γ δ₁ δ₂` is jointly `C¹`, `period`-periodic in the loop parameter, and
has `C^∞` slices.  This is the `hsm` input of the top end (`Work.Drive.sweepToNeedleStrictNT`). -/
theorem sweepFamOf_chamferLoopGen_contDiff_periodic {r : ℝ → Space} (hr : Continuous r)
    {d : BandArcData} (D : SweepData d) {lay : ℝ} (hlay0 : 0 < lay) (hlay1 : lay < 1 / 2)
    {α β : ℝ → ℝ} (hα : Continuous α) (hβ : Continuous β)
    {δ₁ δ₂ : ℝ} (hδ₁ : δ₁ ≠ 0) (hδ₂ : δ₂ ≠ 0) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => sweepFamOf (chamferLoopGen r D lay α β) δ₁ δ₂ p.1 p.2) ∧
    (∀ s t : ℝ, sweepFamOf (chamferLoopGen r D lay α β) δ₁ δ₂ s (t + period)
      = sweepFamOf (chamferLoopGen r D lay α β) δ₁ δ₂ s t) ∧
    (∀ s : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => sweepFamOf (chamferLoopGen r D lay α β) δ₁ δ₂ s t)) :=
  sweepFamOf_contDiff_periodic _ (continuous_chamferLoopGen hr D hlay0 hlay1 hα hβ)
    (fun s t => chamferLoopGen_periodic_t D lay α β s t) δ₁ δ₂ hδ₁ hδ₂

end Work.Drive
