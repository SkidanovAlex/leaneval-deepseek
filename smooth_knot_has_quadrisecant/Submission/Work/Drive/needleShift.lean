import Mathlib
import Submission.Work.Drive.needleStarShapedAux
import Submission.Work.Drive.sweepFam_contDiff_periodic
import Submission.Work.Drive.needleLowEnd
import Submission.Work.Drive.reparam_slice_knot
import Submission.Work.Drive.sweepGlue_clauses
import Submission.Work.Drive.cInfKnot
import Submission.Work.Drive.needleFlatteningDefs

/-!
# The needle pin at a SHIFTED parametrisation

The needle's flattening pin `Work.Drive.NeedleFlatteningData r D lam δ₁ δ₂ ε` asks for a frame
`(u, v)`, a centre `c'` and the clauses

* `polarDir (projectAlong w c N) c' u v 0 = (1, 0)` (`h0`), and
* `Set.InjOn (polarDir (projectAlong w c N) c' u v) (Set.Ico 0 period)` (`hdir`),

where `N = needleFam r D lam δ₁ δ₂ ε`.  The clause `h0` *anchors the base point to the parameter
`t = 0`*, and `t = 0` is the loop fraction `0` of the chamfered loop, i.e. the **collapsed end** of
the retained arc (`taR D 0`): in the picture of `NOTES_lowEnd_ANGLE_ROUTE.md` §3 (base the ray
condition at the cell boundary `sweepParam = 0`, i.e. the *left* end `A` of the lens), the ray from
`c'` through `N 0` in the direction `u` is the "vertical" through the `A`-end of the lens, and the
arc side of the needle passes through the same chord coordinate *again*, strictly higher (both
coordinates of the comparison, `x₀` and the arc side's chord coordinate, are `O(ε²)` — of
indefinite order).  So the single-ray condition of
`Work.Drive.polarDir_injOn_of_singleRay` is at best delicate at `t = 0`.

**This module removes the anchoring: it shifts the parametrisation.**  With

    N' t := N (t + period / 4)

the base point `N' 0` is the loop fraction `1/4`, i.e. (on the arc branch) the arc fraction
`arcFrac = lam + (1 - 2 lam) * 2 * (1/4) = 1/2`, the **middle of the retained arc**.  There the
comparison is *robust*: the ray condition at the middle of the arc is `X t = X 0` only for `t ≡ 0`
(arc side: strict monotonicity, `Work.Drive.needleArcZoneMono`), the chord side meets the ray only
*below* the centre (`NeedleFlatteningData`'s `H < 0` clause, `Work.Drive.needleFam_chordZone_inner`),
and every point of the two chamfer zones and of the wrap zone is a *definite* distance
`~ (1/2 - lam) * ℓ` away in the chord coordinate (`ℓ = ‖chordEndB - chordEndA‖ ~ ε`), against the
`O(ε²)` blur corrections.  See `Submission/Work/Drive/NOTES_lowEnd_SHIFT.md`.

`N'` is the same *curve* as `N` with the parameter rotated, so the two are joined by the elementary
family `(t, s) ↦ N (t + s * period / 4)` of `C^∞` knots (`Work.Drive.shiftFamily_of_cInfKnot`), and
the low end of `NOTES_lowEnd_ANGLE_ROUTE.md` applied to `N'` gives, after gluing
(`Work.Drive.sweepGlue_clauses`), the needle end.

## Main statements

* `Work.Drive.FlatteningData N` — the pin's conjunction for an arbitrary curve `N` (so that it can be
  applied to a shifted needle); `Work.Drive.needleFlatteningData_iff_FlatteningData` identifies it
  with `NeedleFlatteningData` on the needle itself.
* `Work.Drive.shiftFamily_of_cInfKnot` — the parameter rotation as a family of `C^∞` knots.
* `Work.Drive.shifted_needle_family` — the polar datum of the *shifted* needle gives the family from
  the needle to the round circle.
* `Work.Drive.NeedleShiftedFlatteningData` / `Work.Drive.needleEnd_of_shiftedPin` — the pin in the
  shifted form, and the needle end from it (same conclusion as `Work.Drive.needleEnd_of_flattening`).
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology

/-- **The flattening/polar datum of an arbitrary curve.**  This is the conjunction of
`Work.Drive.NeedleFlatteningData` with the needle replaced by the curve `N`; on the needle the two
are definitionally equal (`Work.Drive.needleFlatteningData_iff_FlatteningData`). -/
def FlatteningData (N : ℝ → Space) : Prop :=
  ∃ w c c' u v : Space,
    ‖w‖ = 1 ∧
    Set.InjOn (projectAlong w c N) (Set.Ico (0 : ℝ) period) ∧
    (∀ t : ℝ, velocity (projectAlong w c N) t ≠ 0) ∧
    ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ u v = 0 ∧
    (∀ t : ℝ, projectAlong w c N t - c' =
      inner ℝ (projectAlong w c N t - c') u • u +
      inner ℝ (projectAlong w c N t - c') v • v) ∧
    (∀ t : ℝ, projectAlong w c N t ≠ c') ∧
    polarDir (projectAlong w c N) c' u v 0 = (1, 0) ∧
    Set.InjOn (polarDir (projectAlong w c N) c' u v) (Set.Ico (0 : ℝ) period) ∧
    (∀ t : ℝ, 0 < polarCoord (projectAlong w c N) c' u t *
        deriv (polarCoord (projectAlong w c N) c' v) t -
      polarCoord (projectAlong w c N) c' v t *
        deriv (polarCoord (projectAlong w c N) c' u) t)

/-- The pin on the needle itself is the general datum at the needle. -/
lemma needleFlatteningData_iff_FlatteningData {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    (lam δ₁ δ₂ ε : ℝ) :
    NeedleFlatteningData r D lam δ₁ δ₂ ε ↔ FlatteningData (needleFam r D lam δ₁ δ₂ ε) :=
  Iff.rfl

/-- **Shifting a `C^∞` knot.**  `t ↦ N (t + c)` is again a `C^∞` knot with the same period. -/
theorem isCInfKnot_comp_add_const {N : ℝ → Space} (hN : IsCInfKnot N) (c : ℝ) :
    IsCInfKnot (fun t : ℝ => N (t + c)) := by
  obtain ⟨hsm, hper, hinj, hreg⟩ := hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hsm.comp (contDiff_id.add contDiff_const)
  · intro t
    show N (t + period + c) = N (t + c)
    rw [show t + period + c = (t + c) + period by ring, hper]
  · intro t₁ h₁ t₂ h₂ h
    have hinjc := injOn_Ico_add_period (r := N) (P := period) (a := c) period_pos hper hinj
    have h₁' : t₁ + c ∈ Set.Ico c (c + period) :=
      ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
    have h₂' : t₂ + c ∈ Set.Ico c (c + period) :=
      ⟨by linarith [h₂.1], by linarith [h₂.2]⟩
    have heq : N (t₁ + c) = N (t₂ + c) := h
    have := hinjc h₁' h₂' heq
    linarith
  · intro t
    have hd : HasDerivAt N (deriv N (t + c)) (t + c) :=
      ((hsm.differentiable cInfT_ne_zero) (t + c)).hasDerivAt
    have hd2 : HasDerivAt (fun y : ℝ => y + c) 1 t := (hasDerivAt_id t).add_const c
    have hvel : velocity (fun t : ℝ => N (t + c)) t = deriv N (t + c) := by
      change deriv (fun y : ℝ => N (y + c)) t = deriv N (t + c)
      have hcomp := (hd.scomp t hd2).deriv
      rw [one_smul] at hcomp
      exact hcomp
    rw [hvel]
    exact hreg (t + c)

/-- The converse: a shift of a curve is a `C^∞` knot only if the curve is. -/
theorem isCInfKnot_of_comp_add_const {N : ℝ → Space} {c : ℝ}
    (h : IsCInfKnot (fun t : ℝ => N (t + c))) : IsCInfKnot N := by
  have hfun : (fun t : ℝ => (fun s : ℝ => N (s + c)) (t + (-c))) = N := by
    funext t
    show N (t + (-c) + c) = N t
    rw [show t + (-c) + c = t by ring]
  have h' := isCInfKnot_comp_add_const h (-c)
  rwa [hfun] at h'

/-- **The parameter rotation of a `C^∞` knot, as a family of `C^∞` knots.**  For any shift `t₀`, the
family `(t, s) ↦ N (t + s * t₀)` is jointly `C¹`, `period`-periodic in `t`, has `C^∞` knot slices,
starts at `N` and ends at `t ↦ N (t + t₀)`. -/
theorem shiftFamily_of_cInfKnot {N : ℝ → Space} (hN : IsCInfKnot N) (t₀ : ℝ) :
    ∃ F : ℝ → ℝ → Space,
      ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
      (∀ s t : ℝ, F (t + period) s = F t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
      (∀ t : ℝ, F t 0 = N t) ∧
      (∀ t : ℝ, F t 1 = N (t + t₀)) := by
  refine ⟨fun t s => N (t + s * t₀), ?_, ?_, ?_, ?_, ?_⟩
  · show ContDiff ℝ 1 (fun p : ℝ × ℝ => N (p.1 + p.2 * t₀))
    have hφ : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 + p.2 * t₀) :=
      contDiff_fst.add (contDiff_snd.mul contDiff_const)
    exact (hN.1.of_le one_le_cInfT).comp hφ
  · intro s t
    show N (t + period + s * t₀) = N (t + s * t₀)
    rw [show t + period + s * t₀ = (t + s * t₀) + period by ring, hN.2.1]
  · intro s hs
    exact isCInfKnot_comp_add_const hN (s * t₀)
  · intro t; simp
  · intro t; simp

/-- **The needle is a `C^∞` knot as soon as its flattening datum is available**: the `C^∞` and
periodicity clauses come from the smoothing, the injectivity from the injectivity of the projection
(the shear map), and the regularity from the regularity of the projection.  (This is the extraction
performed inline in `Work.Drive.needleStarShapedDataProved`, in the form needed for the shifted
needle.) -/
theorem isCInfKnot_of_flatteningData {N : ℝ → Space} (hNsm : ContDiff ℝ cInfT N)
    (hNper : Function.Periodic N period) (hdata : FlatteningData N) : IsCInfKnot N := by
  obtain ⟨w, c, c', u, v, hw, hinj, hvel, hu, hv, huv, hplane, hne, h0, hdir, hang⟩ := hdata
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ N t :=
    fun t => (hNsm.differentiable cInfT_ne_zero).differentiableAt
  refine ⟨hNsm, hNper, ?_, ?_⟩
  · intro t₁ h₁ t₂ h₂ heq
    exact hinj h₁ h₂ (congrArg (fun p : Space => p - inner ℝ (p - c) w • w) heq)
  · intro t hzero
    refine hvel t ?_
    rw [velocity_projectAlong (w := w) (c := c) (hdiff t), hzero]
    simp

/-- **The low end at a shifted parameter.**  If the flattening/polar datum holds for the needle
*shifted by `period / 4`* — whose base point is the middle of the retained arc — then the needle is
joined to the round circle of the frame by a jointly `C¹`, `period`-periodic family of `C^∞` knots.

This is `Work.Drive.lowEnd_of_projection_starShaped` applied to the shifted needle, glued with the
parameter rotation `Work.Drive.shiftFamily_of_cInfKnot`. -/
theorem shifted_needle_family {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam δ₁ δ₂ ε : ℝ}
    (hδ₁0 : 0 < δ₁) (hδ₂0 : 0 < δ₂)
    (hdata : FlatteningData (fun t : ℝ => needleFam r D lam δ₁ δ₂ ε (t + period / 4))) :
    ∃ (c f1 f2 : Space) (R : ℝ) (F : ℝ → ℝ → Space),
      ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
      (∀ s t : ℝ, F (t + period) s = F t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
      (∀ t : ℝ, F t 0 = needleFam r D lam δ₁ δ₂ ε t) ∧
      (∀ t : ℝ, F t 1 = c + R • (Real.cos t • f1 + Real.sin t • f2)) ∧
      0 < R ∧ ‖f1‖ = 1 ∧ ‖f2‖ = 1 ∧ inner ℝ f1 f2 = 0 := by
  have hsm : ContDiff ℝ cInfT (needleFam r D lam δ₁ δ₂ ε) :=
    (sweepFam_contDiff_periodic hr.smooth.continuous D lam δ₁ δ₂
      (ne_of_gt hδ₁0) (ne_of_gt hδ₂0)).2.2 ε
  have hper : Function.Periodic (needleFam r D lam δ₁ δ₂ ε) period :=
    fun t => (sweepFam_contDiff_periodic hr.smooth.continuous D lam δ₁ δ₂
      (ne_of_gt hδ₁0) (ne_of_gt hδ₂0)).2.1 ε t
  -- the shifted needle
  have hsm' : ContDiff ℝ cInfT (fun t : ℝ => needleFam r D lam δ₁ δ₂ ε (t + period / 4)) :=
    hsm.comp (contDiff_id.add contDiff_const)
  have hper' : Function.Periodic (fun t : ℝ => needleFam r D lam δ₁ δ₂ ε (t + period / 4))
      period := by
    intro t
    show needleFam r D lam δ₁ δ₂ ε (t + period + period / 4)
      = needleFam r D lam δ₁ δ₂ ε (t + period / 4)
    rw [show t + period + period / 4 = (t + period / 4) + period by ring, hper]
  have hN'k : IsCInfKnot (fun t : ℝ => needleFam r D lam δ₁ δ₂ ε (t + period / 4)) :=
    isCInfKnot_of_flatteningData hsm' hper' hdata
  have hNk : IsCInfKnot (needleFam r D lam δ₁ δ₂ ε) := isCInfKnot_of_comp_add_const hN'k
  obtain ⟨w, c, c', u, v, hw, hinj, hvel, hu, hv, huv, hplane, hne, h0, hdir, hang⟩ := hdata
  obtain ⟨F2, hF2j, hF2per, hF2sl, hF20, hF21⟩ :=
    lowEnd_of_projection_starShaped hN'k (w := w) (c := c) (c' := c') (u := u) (v := v)
      hw hinj hvel hu hv huv hplane hne h0 hdir hang
  obtain ⟨F1, hF1j, hF1per, hF1sl, hF10, hF11⟩ := shiftFamily_of_cInfKnot hNk (period / 4)
  have hjun : ∀ t : ℝ, F1 t 1 = F2 t 0 := by intro t; rw [hF11 t, hF20 t]
  obtain ⟨hjoint, hglper, hslice, hzero, hone⟩ :=
    sweepGlue_clauses hF1j hF2j hjun hF1sl hF2sl hF1per hF2per
  refine ⟨0, u, v, 1, fun t s => sweepGlue F1 F2 s t, hjoint, hglper, hslice, ?_, ?_,
    by norm_num, hu, hv, huv⟩
  · intro t
    show sweepGlue F1 F2 0 t = needleFam r D lam δ₁ δ₂ ε t
    rw [hzero t, hF10 t]
  · intro t
    show sweepGlue F1 F2 1 t = 0 + 1 • (Real.cos t • u + Real.sin t • v)
    rw [hone t, hF21 t]
    simp

/-- **The needle pin, in the shifted form.**  The flattening/polar datum of the needle shifted by
`period / 4` (the base point is then the middle of the retained arc), uniformly in the parameter box
of `Work.Drive.NeedleFlatteningData`.  This is the form in which the single-ray condition is robust;
see `Submission/Work/Drive/NOTES_lowEnd_SHIFT.md`. -/
def NeedleShiftedFlatteningData (r : ℝ → Space) {d : BandArcData} (D : SweepData d) : Prop :=
  ∃ ε₀ L : ℝ, 0 < ε₀ ∧ 0 < L ∧
    ∀ (lam δ₁ δ₂ ε : ℝ), 0 < lam → lam ≤ L → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ L →
      0 < δ₂ → δ₂ ≤ L → 0 < ε → ε ≤ ε₀ → δ₂ ≤ ε / 2 →
      FlatteningData (fun t : ℝ => needleFam r D lam δ₁ δ₂ ε (t + period / 4))

/-- **The needle end, from the shifted pin.**  Same conclusion as
`Work.Drive.needleEnd_of_flattening`, with the shifted flattening pin in place of the pin at
`t = 0`. -/
theorem needleEnd_of_shiftedPin {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) (hpin : NeedleShiftedFlatteningData r D) :
    ∃ ε₀ L : ℝ, 0 < ε₀ ∧ 0 < L ∧
      ∀ (lam δ₁ δ₂ ε : ℝ), 0 < lam → lam ≤ L → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ L →
        0 < δ₂ → δ₂ ≤ L → 0 < ε → ε ≤ ε₀ → δ₂ ≤ ε / 2 →
        ∃ (c f1 f2 : Space) (R : ℝ) (F : ℝ → ℝ → Space),
          ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
          (∀ s t : ℝ, F (t + period) s = F t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
          (∀ t : ℝ, F t 0 = sweepNeedleFam r D lam δ₁ δ₂ ε t) ∧
          (∀ t : ℝ, F t 1 = c + R • (Real.cos t • f1 + Real.sin t • f2)) ∧
          0 < R ∧ ‖f1‖ = 1 ∧ ‖f2‖ = 1 ∧ inner ℝ f1 f2 = 0 := by
  obtain ⟨ε₀, L, hε₀, hL, hmain⟩ := hpin
  refine ⟨ε₀, L, hε₀, hL, ?_⟩
  intro lam δ₁ δ₂ ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨c, f1, f2, R, F, hF1, hF2, hF3, hF4, hF5, hF6, hF7, hF8, hF9⟩ :=
    shifted_needle_family hr D (hδ₁0 := h4) (hδ₂0 := h6)
      (hdata := hmain lam δ₁ δ₂ ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
  refine ⟨c, f1, f2, R, F, hF1, hF2, hF3, ?_, hF5, hF6, hF7, hF8, hF9⟩
  intro t
  rw [hF4 t]
  rfl

end Work.Drive
