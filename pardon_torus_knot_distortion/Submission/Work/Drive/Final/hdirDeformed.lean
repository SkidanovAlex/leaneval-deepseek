import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.hdir_of_htrans
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.Smooth.BoxGeneric.Defs

/-!
# The direction into the box at a box-sphere junction of the *deformed* wall

This is the hypothesis `hdir` of `Work.Drive.Final.boxSphereWallJunctionLocalModel`, proved for the
deformed wall `ℓ ∘ D.deform`: at a point `x` of the dent's annulus on the box sphere at which the
deformed wall passes, there is a direction into the box along which `ℓ` increases past `ℓ D.centre`.

The proof transcribes the two halves of `Work.Drive.Mono.hdir_of_htrans` (the same statement for the
undeformed wall `ℓ`), with the pulled-back deformed height `fun q ↦ ℓ (D.deform (par ψ q))` in the
role of the sweep height `sweepHeight ψ ℓ`:

* the two halves of the analytic input at the parameter `p` of `x` are supplied by `hΓ` (regularity
  of the box norm) and `hann` (independence of the two differentials), applied at `p`;
* differentiability of the deformed height comes from `hpar'`, which exhibits it as the sweep height
  of the diffeo `ψ'`;
* the only new point is that the point `w` found on the surface must be pushed forward by the dent,
  and that the result stays in the open box: `D.box_pres` if `w` is inside the dent's ball, and
  `dentDeform_eq_self_of_le` (the deformation is the identity outside the ball) if not.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-! ## The deformation is the identity outside its ball -/

/-- **The dent deformation is the identity outside its closed ball** (`χ` vanishes beyond radius
`1`).  A local copy of `Work.Drive.Final.dentDeform_eq_self_of_le`, stated for the field data of an
`AnyDentDatum`. -/
theorem dentDeform_eq_self_of_le_field {χ : ℝ → ℝ} {centre d : R3} {r a' : ℝ}
    (hr : 0 < r) (hχ : ∀ t : ℝ, 1 ≤ t → χ t = 0) {z : R3} (hz : r ≤ ‖z - centre‖) :
    dentDeform χ centre d r a' z = z := by
  rw [dentDeform]
  have h1 : 1 ≤ ‖z - centre‖ / r := (one_le_div hr).mpr hz
  rw [hχ _ h1, mul_zero, zero_smul, add_zero]

theorem hdirDeformed /-
**The direction into the box at a box-sphere junction of the *deformed* wall.**  Put this in
`namespace Work.Drive.Final`, in `Submission/Work/Drive/Final/hdirDeformed.lean` (`R3` and `Knot`
are written out fully because that file need not open `LeanEval.KnotTheory.PardonDistortion`).

PROOF PLAN: transcribe the two halves of `Work.Drive.Mono.hdir_of_htrans`, which proves the same
statement for the *undeformed* wall `ℓ - lam`; that file is the model to copy.

1. `p` is a parameter of `x` on the surface (`hp`), the box norm is regular there (`hΓ.1`), and the
pulled-back deformed height `G := fun q ↦ ℓ (D.deform (par ψ q))` is not a multiple of it
(`hann`'s third clause at `p`, whose hypotheses are `hxs`, `hρ1`, `hρ2`, `hxslab` and
`x ∈ closure (PBox s c σ)`, the last from `hxs` and `hs` by scaling toward `c`); `G` is
differentiable at `p` because `G = sweepHeight ψ' ℓ` by `hpar'` and the sweep height of a diffeo is
smooth (`Work.Drive.EpsForm.sweepHeight_contDiff_two`).  Applying
`Work.Drive.Mono.hdir_exists_neg_pos_of_indep` to `(fderiv (boxNorm ∘ par ψ) p)` and `(fderiv G p)`
gives a direction `vv` of the parameter plane with `dB_p vv < 0 < dG_p vv`; the one-sided Taylor
lemmas `Work.Drive.Mono.hdir_eventually_lt_of_hasFDerivAt` and
`Work.Drive.Mono.hdir_eventually_gt_of_hasFDerivAt` then give `t > 0` with
`boxNorm (par ψ (p + t • vv)) < s` and `G (p + t • vv) > ℓ D.centre` (using `hxg`).  Setting
`w := D.deform (par ψ (p + t • vv))` gives `ℓ w > ℓ D.centre`, and `w ∈ PBox s c σ`: if
`‖par ψ (p + t • vv) - D.centre‖ ≤ D.r` this is `D.box_pres`, otherwise `D.deform = id` there
(`Work.Drive.Final.dentDeform_eq_self_of_le`).

2. For `y` with `boxNorm c σ y = s`, `ℓ y = ℓ D.centre` and `ε > 0`, the convex combination
`θ • w + (1 - θ) • y` with `θ := min (1/2) (ε / (2 * (‖w - y‖ + 1)))` lies in `PBox s c σ`
(`Work.Drive.Mono.hdir_convex_combo_mem_PBox`, with `faceNorm_le_boxNorm` to bound the coordinates of
`y`), lies within `ε` of `y`, and has `ℓ`-value `≥ ℓ D.centre` by linearity of `ℓ`: this is the second
half of the proof of `Work.Drive.Mono.hdir_of_htrans` verbatim with `w` from part 1; `δ := 1` works. -/
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot}
    {s u h R : ℝ} {c v : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ}
    {U : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hs : 0 < s)
    {ψ' : Submission.Diffeo}
    (hpar' : ∀ q : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ' q = D.deform (Work.BoxShrink.Pinch.par ψ q))
    (hΓ : ∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p)
    (hann : ∀ q' : ℝ × ℝ,
      D.r / 2 ≤ ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ →
      ‖Work.BoxShrink.Pinch.par ψ q' - D.centre‖ ≤ D.r →
      Work.BoxShrink.Pinch.par ψ q' ∈ closure (Submission.PBox s c σ) →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| ≤ h →
      fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠ 0 ∧
      (|Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ q')| = h → ∀ t : ℝ,
        fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠
          t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) q') ∧
      (Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q') = s → ∀ t : ℝ,
        fderiv ℝ (fun q'' : ℝ × ℝ => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q''))) q' ≠
          t • fderiv ℝ (fun q'' : ℝ × ℝ =>
            Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q'')) q'))
    {x : LeanEval.KnotTheory.PardonDistortion.R3}
    (hxc : x ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hxs : Submission.boxNorm c σ x = s)
    (hxslab : |Work.Drive.Final.slabFn c u v x| < h)
    (hxg : ℓ (D.deform x) = ℓ D.centre)
    (hρ1 : D.r / 2 ≤ ‖x - D.centre‖) (hρ2 : ‖x - D.centre‖ ≤ D.r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : LeanEval.KnotTheory.PardonDistortion.R3, dist y (D.deform x) < δ →
      Submission.boxNorm c σ y = s → ℓ y = ℓ D.centre → ∀ ε : ℝ, 0 < ε →
      ∃ y' : LeanEval.KnotTheory.PardonDistortion.R3,
        dist y' y < ε ∧ Submission.boxNorm c σ y' < s ∧ ℓ D.centre ≤ ℓ y' := by
  -- ## Step 1: the parameter of `x` on the surface
  obtain ⟨p, hp⟩ : ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = x := by
    have h : x ∈ Set.range (Work.BoxShrink.Pinch.par ψ) := by
      rw [← Work.BoxShrink.Pinch.carrier_eq_range ψ]
      exact hxc
    exact h
  have hxs' : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s := by
    rw [hp]; exact hxs
  have hxslab' : |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h := by
    rw [hp]; exact le_of_lt hxslab
  have hxclos : x ∈ closure (Submission.PBox s c σ) := by
    have hfr : x ∈ frontier (Submission.PBox s c σ) := by
      rw [Work.Topology.SphereSlicing.frontier_PBox hs c σ,
        Work.Topology.SphereSlicing.mem_BoxSphere]
      exact hxs
    exact frontier_subset_closure hfr
  have hpclos : Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ) := by
    rw [hp]; exact hxclos
  -- ## Step 2: the two analytic inputs at `p`
  have hΓp := hΓ p hxs' hxslab'
  have hannp := hann p (by rw [hp]; exact hρ1) (by rw [hp]; exact hρ2) hpclos hxslab'
  set B : ℝ × ℝ → ℝ := fun q => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) with hB
  set G : ℝ × ℝ → ℝ := fun q => ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q)) with hG
  have hBne : fderiv ℝ B p ≠ 0 := by rw [hB]; exact hΓp.1
  have htrans : ∀ t : ℝ, fderiv ℝ G p ≠ t • fderiv ℝ B p := by
    intro t
    have hc := hannp.2.2 hxs' t
    simpa only [hG, hB] using hc
  have hG_eq : G = Work.Drive.EpsForm.sweepHeight ψ' ℓ := by
    funext q
    show ℓ (D.deform (Work.BoxShrink.Pinch.par ψ q)) = Work.Drive.EpsForm.sweepHeight ψ' ℓ q
    rw [← hpar' q]
    rfl
  have hfdB : HasFDerivAt B (fderiv ℝ B p) p := by
    by_cases hd : DifferentiableAt ℝ B p
    · exact hd.hasFDerivAt
    · exact absurd (fderiv_zero_of_not_differentiableAt hd) hBne
  have hGdiff : DifferentiableAt ℝ G p := by
    rw [hG_eq]
    exact ((Work.Drive.EpsForm.sweepHeight_contDiff_two ψ' ℓ).contDiffAt).differentiableAt
      (by norm_num)
  have hfdG : HasFDerivAt G (fderiv ℝ G p) p := hGdiff.hasFDerivAt
  -- ## Step 3: a direction of the parameter plane into the box and up the wall
  obtain ⟨vv, hvv1, hvv2⟩ :=
    Work.Drive.Mono.hdir_exists_neg_pos_of_indep (fderiv ℝ B p) (fderiv ℝ G p) hBne htrans
  have hBev : ∀ᶠ t in 𝓝[>] (0 : ℝ), B (p + t • vv) < B p :=
    Work.Drive.Mono.hdir_eventually_lt_of_hasFDerivAt hfdB hvv1
  have hGev : ∀ᶠ t in 𝓝[>] (0 : ℝ), G p < G (p + t • vv) :=
    Work.Drive.Mono.hdir_eventually_gt_of_hasFDerivAt hfdG hvv2
  have hBp : B p = s := hxs'
  have hGp : G p = ℓ D.centre := by
    rw [hG]
    show ℓ (D.deform (Work.BoxShrink.Pinch.par ψ p)) = ℓ D.centre
    rw [hp]
    exact hxg
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < t ∧ B (p + t • vv) < s ∧ ℓ D.centre < G (p + t • vv) := by
    filter_upwards [self_mem_nhdsWithin, hBev, hGev] with t htpos htB htG
    exact ⟨htpos, by rwa [hBp] at htB, by rwa [hGp] at htG⟩
  obtain ⟨t, htpos, htB, htG⟩ :=
    @Filter.Eventually.exists ℝ _ _ (nhdsGT_neBot (0 : ℝ)) hall
  -- ## Step 4: the point of the open box with `ℓ`-value above `ℓ D.centre`
  set w : R3 := D.deform (Work.BoxShrink.Pinch.par ψ (p + t • vv)) with hw
  have hzl : ℓ w = ℓ (D.deform (Work.BoxShrink.Pinch.par ψ (p + t • vv))) := rfl
  have hwl : ℓ D.centre < ℓ w := by
    have h := htG
    rw [hG] at h
    exact h
  have hzB : Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ (p + t • vv)) < s := by
    have h := htB
    rw [hB] at h
    exact h
  have hzPBox : Work.BoxShrink.Pinch.par ψ (p + t • vv) ∈ Submission.PBox s c σ :=
    (Submission.mem_PBox_iff s c σ _).mpr hzB
  have hwPBox : w ∈ Submission.PBox s c σ := by
    by_cases hle : ‖Work.BoxShrink.Pinch.par ψ (p + t • vv) - D.centre‖ ≤ D.r
    · have h := (D.box_pres _ hle).mp hzPBox
      show D.deform (Work.BoxShrink.Pinch.par ψ (p + t • vv)) ∈ Submission.PBox s c σ
      exact h
    · push Not at hle
      have hself : D.deform (Work.BoxShrink.Pinch.par ψ (p + t • vv))
          = Work.BoxShrink.Pinch.par ψ (p + t • vv) := by
        rw [AnyDentDatum.deform]
        exact dentDeform_eq_self_of_le_field D.r_pos D.χ_eq_zero (le_of_lt hle)
      show D.deform (Work.BoxShrink.Pinch.par ψ (p + t • vv)) ∈ Submission.PBox s c σ
      rw [hself]
      exact hzPBox
  -- ## Step 5: the convex combination with a point of the box sphere
  refine ⟨1, one_pos, ?_⟩
  intro y _hy1 hy2 hy3 ε hε
  have hybnd : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
    intro i
    have h1 : Work.Smooth.BoxGeneric.faceNorm c σ i y ≤ Submission.boxNorm c σ y :=
      Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i y
    rw [hy2] at h1
    rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_le_iff₀ (Submission.boxSide_pos i)] at h1
    linarith [h1]
  have hwy : 0 < ‖w - y‖ := by
    rw [norm_pos_iff]
    intro hzero
    have hwyeq : w = y := sub_eq_zero.mp hzero
    have hlt : Submission.boxNorm c σ y < s := by
      rw [← hwyeq]
      exact (Submission.mem_PBox_iff s c σ w).mp hwPBox
    rw [hy2] at hlt
    exact lt_irrefl s hlt
  set θ : ℝ := min (1 / 2) (ε / (2 * (‖w - y‖ + 1))) with hθ
  have hθpos : 0 < θ := by rw [hθ]; exact lt_min (by norm_num) (by positivity)
  have hθlt : θ < 1 := by
    rw [hθ]
    exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hθε : θ * ‖w - y‖ < ε := by
    rw [hθ]
    have hbound : ε / (2 * (‖w - y‖ + 1)) * ‖w - y‖ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖w - y‖ + 1))]
      nlinarith [norm_nonneg (w - y)]
    calc min (1 / 2) (ε / (2 * (‖w - y‖ + 1))) * ‖w - y‖
        ≤ (ε / (2 * (‖w - y‖ + 1))) * ‖w - y‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ < ε := hbound
  refine ⟨θ • w + (1 - θ) • y, ?_, ?_, ?_⟩
  · rw [dist_eq_norm]
    have hsub : θ • w + (1 - θ) • y - y = θ • (w - y) := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hθpos]
    exact hθε
  · exact (Submission.mem_PBox_iff s c σ _).mp
      (Work.Drive.Mono.hdir_convex_combo_mem_PBox hwPBox hybnd hθpos hθlt)
  · have hsplit : ℓ (θ • w + (1 - θ) • y) = θ * ℓ w + (1 - θ) * ℓ y := by
      simp [map_add, map_smul, smul_eq_mul]
    rw [hsplit, hy3]
    have h1 : θ * ℓ D.centre < θ * ℓ w := mul_lt_mul_of_pos_left hwl hθpos
    linarith

end

end Work.Drive.Final
