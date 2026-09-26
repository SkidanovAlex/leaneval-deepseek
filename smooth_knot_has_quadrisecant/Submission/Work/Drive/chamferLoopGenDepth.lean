import Mathlib
import Submission.Work.Drive.chamferLoopGenDefs
import Submission.Work.Drive.chamferLoopGenBlur

/-!
# The depth-parametrised chamfer loop: global continuity of the scheduled loop

`Work.Drive.chamferLoopGen r D lay α β` takes its cut fraction `α` as a function of the sweep
parameter `s`, and the design's schedule `Work.Drive.schedAlpha` is
`dep s / sweepW' D s` — **discontinuous at `s = 0`**, where both numerator and denominator vanish
(Lean gives `0 / 0 = 0`, whereas the one-sided limit is `lay`).  The scheduled loop
`Γ := chamferLoopGen r D lay schedAlpha schedBeta` is therefore not globally continuous, and every
compactness statement of the blur layer (`Work.Drive.farSep_window_of_injOn`,
`Work.Drive.sweepFamOf_close_uc`, `Work.Drive.sweepFamOf_contDiff_periodic_li`) needs either a
`ContinuousOn` variant or a globally continuous loop.

This module removes the obstruction *without touching the existing schedule definitions*: it
introduces the loop written in terms of the **absolute cut depth** `dep s` instead of the fraction
`α s` (the arc just runs from `ta + dep` to `tb - dep`), which depends on the schedule only through
`Work.Drive.schedDep` (globally continuous) and the chord target `β`:

* `Work.Drive.chamferLoopProfD`, `Work.Drive.chamferLoopGenD` — the depth-parametrised loop;
* `Work.Drive.chamferLoopProfD_eq_chamferLoopProf` / `Work.Drive.chamferLoopGenD_eq_chamferLoopGen`
  — it *is* the old loop as soon as `α s * sweepW' D s = dep s` (which holds wherever the chord is
  non-degenerate);
* `Work.Drive.continuous_chamferLoopProfD` / `Work.Drive.continuous_chamferLoopGenD` — joint
  continuity whenever `dep` and `β` are continuous.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- **The profile of the depth-parametrised chamfer loop**: `u` is the profile variable, `dep` the
absolute cut depth (a length) and `b` the chord target fraction. -/
def chamferLoopProfD (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lay dep b s u : ℝ) :
    Space :=
  if u ≤ 1 / 2 then r (taR D s + dep + (sweepW' D s - 2 * dep) * (2 * u))
  else if u ≤ 1 / 2 + lay / 2 then
    (1 - (2 * u - 1) / lay) • r (tbR D s - dep)
      + ((2 * u - 1) / lay) • sweepChord' r D s (1 - b)
  else if u ≤ 1 - lay / 2 then
    sweepChord' r D s ((1 - b) - ((u - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b))
  else (1 - (u - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D s b
      + ((u - (1 - lay / 2)) / (lay / 2)) • r (taR D s + dep)

/-- **The depth-parametrised chamfer loop.** -/
def chamferLoopGenD (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (lay : ℝ)
    (dep b : ℝ → ℝ) (s t : ℝ) : Space :=
  chamferLoopProfD r D lay (dep s) (b s) s (sweepParam t)

/-- **The depth-parametrised loop is the design's loop** as soon as the absolute depth is
`α s * sweepW' D s`; this holds wherever the chord is non-degenerate. -/
theorem chamferLoopProfD_eq_chamferLoopProf {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay dep a b : ℝ} {s u : ℝ} (hdep : a * sweepW' D s = dep) :
    chamferLoopProfD r D lay dep b s u = chamferLoopProf r D lay a b s u := by
  have hW : sweepW' D s = tbR D s - taR D s := rfl
  rw [chamferLoopProfD, chamferLoopProf]
  split_ifs with h1 h2 h3
  · -- arc branch
    rw [sweepArc']
    have h2' : taR D s + dep + (sweepW' D s - 2 * dep) * (2 * u)
        = taR D s + (a + (1 - 2 * a) * (2 * u)) * sweepW' D s := by
      rw [← hdep]; ring
    rw [h2']
  · -- first connector: the arc endpoint `1 - a` is `tb - dep`
    rw [sweepArc']
    have h2' : taR D s + (1 - a) * sweepW' D s = tbR D s - dep := by
      rw [← hdep, hW]; ring
    rw [h2']
  · rfl
  · -- second connector: the arc endpoint `a` is `ta + dep`
    rw [sweepArc']
    have h2' : taR D s + a * sweepW' D s = taR D s + dep := by
      rw [← hdep]
    rw [h2']

/-- **The depth-parametrised loop is the design's loop** with `α s = dep s / sweepW' D s`. -/
theorem chamferLoopGenD_eq_chamferLoopGen {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lay : ℝ} {dep b : ℝ → ℝ} {a b' : ℝ → ℝ}
    (hdep : ∀ s : ℝ, a s * sweepW' D s = dep s) (hb : ∀ s : ℝ, b' s = b s) :
    chamferLoopGenD r D lay dep b = chamferLoopGen r D lay a b' := by
  have hbf : b' = b := funext hb
  rw [hbf]
  funext s t
  exact chamferLoopProfD_eq_chamferLoopProf D (hdep s)

/-! ## Joint continuity -/

/-- **The profile is jointly continuous** in `(s, u)` when `dep` and `b` are continuous functions of
`s`.  The proof is the one of `Work.Drive.continuous_chamferLoopProf`, with `ta + dep` and
`tb - dep` in place of `sweepArc' (·) (a s)` and `sweepArc' (·) (1 - a s)`. -/
theorem continuous_chamferLoopProfD {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lay : ℝ} (hlay0 : 0 < lay) (hlay1 : lay < 1 / 2)
    {dep b : ℝ → ℝ} (hdep : Continuous dep) (hb : Continuous b) :
    Continuous (fun p : ℝ × ℝ => chamferLoopProfD r D lay (dep p.1) (b p.1) p.1 p.2) := by
  have hta : Continuous (fun p : ℝ × ℝ => taR D p.1) :=
    (sweepLoopChamfer_taR_continuous D).comp continuous_fst
  have htb : Continuous (fun p : ℝ × ℝ => tbR D p.1) :=
    (sweepLoopChamfer_tbR_continuous D).comp continuous_fst
  have hW : Continuous (fun p : ℝ × ℝ => sweepW' D p.1) :=
    (sweepLoopChamfer_sweepW'_continuous D).comp continuous_fst
  have hdc : Continuous (fun p : ℝ × ℝ => dep p.1) := hdep.comp continuous_fst
  have hbc : Continuous (fun p : ℝ × ℝ => b p.1) := hb.comp continuous_fst
  have hrc : Continuous (fun p : ℝ × ℝ => r (taR D p.1)) := hr.comp hta
  have hrb : Continuous (fun p : ℝ × ℝ => r (tbR D p.1)) := hr.comp htb
  have hsA : Continuous (fun p : ℝ × ℝ => r (taR D p.1 + dep p.1)) :=
    hr.comp (hta.add hdc)
  have hsB : Continuous (fun p : ℝ × ℝ => r (tbR D p.1 - dep p.1)) :=
    hr.comp (htb.sub hdc)
  have hcB : Continuous (fun p : ℝ × ℝ => sweepChord' r D p.1 (1 - b p.1)) := by
    have h : Continuous (fun p : ℝ × ℝ =>
        (1 - (1 - b p.1)) • r (taR D p.1) + (1 - b p.1) • r (tbR D p.1)) :=
      ((continuous_const.sub (continuous_const.sub hbc)).smul hrc).add
        ((continuous_const.sub hbc).smul hrb)
    simpa only [sweepChord'] using h
  have hcD : Continuous (fun p : ℝ × ℝ => sweepChord' r D p.1 (b p.1)) := by
    have h : Continuous (fun p : ℝ × ℝ =>
        (1 - b p.1) • r (taR D p.1) + b p.1 • r (tbR D p.1)) :=
      ((continuous_const.sub hbc).smul hrc).add (hbc.smul hrb)
    simpa only [sweepChord'] using h
  -- the four branch values
  have hA : Continuous (fun p : ℝ × ℝ =>
      r (taR D p.1 + dep p.1 + (sweepW' D p.1 - 2 * dep p.1) * (2 * p.2))) :=
    hr.comp (hta.add hdc |>.add ((hW.sub (hdc.const_mul 2)).mul
      (continuous_const.mul continuous_snd)))
  have hB : Continuous (fun p : ℝ × ℝ =>
      (1 - (2 * p.2 - 1) / lay) • r (tbR D p.1 - dep p.1)
        + ((2 * p.2 - 1) / lay) • sweepChord' r D p.1 (1 - b p.1)) := by
    have hc : Continuous (fun p : ℝ × ℝ => (2 * p.2 - 1) / lay) := by fun_prop
    exact ((continuous_const.sub hc).smul hsB).add (hc.smul hcB)
  have hC : Continuous (fun p : ℝ × ℝ =>
      sweepChord' r D p.1 ((1 - b p.1)
        - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b p.1))) := by
    have hξ : Continuous (fun p : ℝ × ℝ => (1 - b p.1)
        - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b p.1)) := by fun_prop
    have h : Continuous (fun p : ℝ × ℝ =>
        (1 - ((1 - b p.1) - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b p.1)))
          • r (taR D p.1)
        + ((1 - b p.1) - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b p.1))
          • r (tbR D p.1)) :=
      ((continuous_const.sub hξ).smul hrc).add (hξ.smul hrb)
    simpa only [sweepChord'] using h
  have hD : Continuous (fun p : ℝ × ℝ =>
      (1 - (p.2 - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D p.1 (b p.1)
        + ((p.2 - (1 - lay / 2)) / (lay / 2)) • r (taR D p.1 + dep p.1)) := by
    have hc : Continuous (fun p : ℝ × ℝ => (p.2 - (1 - lay / 2)) / (lay / 2)) := by fun_prop
    exact ((continuous_const.sub hc).smul hcD).add (hc.smul hsA)
  -- the nested `if`s
  have hCD : Continuous (fun p : ℝ × ℝ =>
      if p.2 ≤ 1 - lay / 2 then
        sweepChord' r D p.1 ((1 - b p.1)
          - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b p.1))
      else
        (1 - (p.2 - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D p.1 (b p.1)
          + ((p.2 - (1 - lay / 2)) / (lay / 2)) • r (taR D p.1 + dep p.1)) := by
    refine Continuous.if_le (f := fun p : ℝ × ℝ => p.2) (g := fun _ : ℝ × ℝ => 1 - lay / 2)
      hC hD continuous_snd continuous_const ?_
    intro p hp
    have hden : 1 / 2 - lay ≠ 0 := by linarith
    have hquot : (p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay) = 1 := by
      rw [hp, show (1 : ℝ) - lay / 2 - (1 / 2 + lay / 2) = 1 / 2 - lay by ring, div_self hden]
    have hξ : (1 - b p.1)
        - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b p.1) = b p.1 := by
      rw [hquot]; ring
    have hc : (p.2 - (1 - lay / 2)) / (lay / 2) = 0 := by
      rw [hp, sub_self, zero_div]
    rw [hξ, hc]
    simp
  have hBCD : Continuous (fun p : ℝ × ℝ =>
      if p.2 ≤ 1 / 2 + lay / 2 then
        (1 - (2 * p.2 - 1) / lay) • r (tbR D p.1 - dep p.1)
          + ((2 * p.2 - 1) / lay) • sweepChord' r D p.1 (1 - b p.1)
      else
        if p.2 ≤ 1 - lay / 2 then
          sweepChord' r D p.1 ((1 - b p.1)
            - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b p.1))
        else
          (1 - (p.2 - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D p.1 (b p.1)
            + ((p.2 - (1 - lay / 2)) / (lay / 2)) • r (taR D p.1 + dep p.1)) := by
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
      if p.2 ≤ 1 / 2 then
        r (taR D p.1 + dep p.1 + (sweepW' D p.1 - 2 * dep p.1) * (2 * p.2))
      else
        if p.2 ≤ 1 / 2 + lay / 2 then
          (1 - (2 * p.2 - 1) / lay) • r (tbR D p.1 - dep p.1)
            + ((2 * p.2 - 1) / lay) • sweepChord' r D p.1 (1 - b p.1)
        else
          if p.2 ≤ 1 - lay / 2 then
            sweepChord' r D p.1 ((1 - b p.1)
              - ((p.2 - (1 / 2 + lay / 2)) / (1 / 2 - lay)) * (1 - 2 * b p.1))
          else
            (1 - (p.2 - (1 - lay / 2)) / (lay / 2)) • sweepChord' r D p.1 (b p.1)
              + ((p.2 - (1 - lay / 2)) / (lay / 2)) • r (taR D p.1 + dep p.1)) := by
    refine Continuous.if_le (f := fun p : ℝ × ℝ => p.2) (g := fun _ : ℝ × ℝ => 1 / 2)
      hA hBCD continuous_snd continuous_const ?_
    intro p hp
    rw [if_pos (by rw [hp]; linarith)]
    have h2 : 2 * p.2 = 1 := by rw [hp]; ring
    have h1 : 2 * p.2 - 1 = 0 := by rw [hp]; ring
    have h3 : taR D p.1 + dep p.1 + (sweepW' D p.1 - 2 * dep p.1) * (2 * p.2)
        = tbR D p.1 - dep p.1 := by
      rw [h2]
      have hW : sweepW' D p.1 = tbR D p.1 - taR D p.1 := rfl
      rw [hW]; ring
    rw [h3, h1]
    simp
  exact hmain

/-- **The depth-parametrised loop is jointly continuous.** -/
theorem continuous_chamferLoopGenD {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : SweepData d) {lay : ℝ} (hlay0 : 0 < lay) (hlay1 : lay < 1 / 2)
    {dep b : ℝ → ℝ} (hdep : Continuous dep) (hb : Continuous b) :
    Continuous (fun p : ℝ × ℝ => chamferLoopGenD r D lay dep b p.1 p.2) := by
  have hprof := continuous_chamferLoopProfD hr D hlay0 hlay1 hdep hb
  have hper : ∀ s : ℝ, chamferLoopProfD r D lay (dep s) (b s) s 0
      = chamferLoopProfD r D lay (dep s) (b s) s 1 := by
    intro s
    have h0 : chamferLoopProfD r D lay (dep s) (b s) s 0 = r (taR D s + dep s) := by
      simp only [chamferLoopProfD, if_pos (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_zero, add_zero]
    have h1 : chamferLoopProfD r D lay (dep s) (b s) s 1 = r (taR D s + dep s) := by
      rw [chamferLoopProfD, if_neg (by norm_num : ¬ (1 : ℝ) ≤ 1 / 2),
        if_neg (by linarith : ¬ (1 : ℝ) ≤ 1 / 2 + lay / 2),
        if_neg (by linarith : ¬ (1 : ℝ) ≤ 1 - lay / 2)]
      have hd2 : lay / 2 ≠ 0 := by positivity
      have hquot : (1 - (1 - lay / 2)) / (lay / 2) = 1 := by
        rw [show (1 : ℝ) - (1 - lay / 2) = lay / 2 by ring, div_self hd2]
      rw [show (1 : ℝ) - (1 - (1 - lay / 2)) / (lay / 2) = 1 - 1 by rw [hquot], hquot,
        sub_self, zero_smul, zero_add, one_smul]
    rw [h0, h1]
  have hf : Continuous (fun u : ℝ × ℝ =>
      chamferLoopProfD r D lay (dep u.1) (b u.1) u.1 (Int.fract u.2)) :=
    ContinuousOn.comp_fract' (β := ℝ) hprof.continuousOn hper
  have heq : (fun p : ℝ × ℝ => chamferLoopGenD r D lay dep b p.1 p.2)
      = (fun u : ℝ × ℝ => chamferLoopProfD r D lay (dep u.1) (b u.1) u.1 (Int.fract u.2))
        ∘ (fun p : ℝ × ℝ => (p.1, p.2 / period)) := by
    funext p
    show chamferLoopGenD r D lay dep b p.1 p.2
      = chamferLoopProfD r D lay (dep p.1) (b p.1) p.1 (Int.fract (p.2 / period))
    rw [chamferLoopGenD, sweepParam_eq_fract]
  rw [heq]
  exact hf.comp (continuous_fst.prodMk (continuous_snd.div_const period))

/-- The depth-parametrised loop is `period`-periodic in the loop parameter. -/
theorem chamferLoopGenD_periodic_t {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (lay : ℝ) (dep b : ℝ → ℝ) (s t : ℝ) :
    chamferLoopGenD r D lay dep b s (t + period) = chamferLoopGenD r D lay dep b s t := by
  simp only [chamferLoopGenD, sweepParam_add_period]

end Work.Drive
