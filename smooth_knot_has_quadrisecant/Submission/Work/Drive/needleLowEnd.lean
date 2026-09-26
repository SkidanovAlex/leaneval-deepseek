import Mathlib
import Submission.Work.Drive.polarDataOfStarShaped
import Submission.Work.Drive.sweepGlue_clauses
import Submission.Work.Drive.sweepGlue_easy_clauses
import Submission.Work.Drive.isUnknotted_of_cInf_isotopy

/-!
# The low end of the chord sweep: flattening a thin needle

The needle at the low end of the chord sweep is a *space* curve, while the polar machinery
(`Work.Drive.needleToCircle_of_starShaped`) consumes a *planar* star-shaped curve.  This file
supplies the missing geometric operation: the **shear family** that flattens a knot into the plane
perpendicular to a direction `w`.

* `Work.Drive.projectAlong w c N` — the orthogonal projection of `N` onto the plane through `c`
  perpendicular to `w`;
* `Work.Drive.shearFamily_of_projection` — if that projection is injective on one period and
  regular, then the shear `(s, t) ↦ (1 - s) • N t + s • projectAlong w c N t` is a jointly `C¹`
  family of `C^∞` knots from `N` to its projection.  Both the injectivity and the vanishing of the
  velocity of a slice reduce to the two hypotheses on the projection; the only extra inputs are
  that `N` is a `C^∞` knot (so `N' ≠ 0` and `N` is injective on one period) and `‖w‖ = 1`.

The hypotheses that remain for the low end of the sweep are exactly the geometric ones a geometer
must check for the needle: that some direction `w` projects it injectively and regularly, and that
the flattened needle is star-shaped about a suitable centre with a positively oriented
parametrisation (`Work.Drive.polarData_of_starShaped`).
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- The orthogonal projection of the curve `N` onto the plane through `c` perpendicular to `w`. -/
def projectAlong (w c : Space) (N : ℝ → Space) : ℝ → Space :=
  fun t => N t - inner ℝ (N t - c) w • w

lemma projectAlong_smooth {N : ℝ → Space} (hN : ContDiff ℝ cInfT N) (w c : Space) :
    ContDiff ℝ cInfT (projectAlong w c N) := by
  have h1 : ContDiff ℝ cInfT (fun t : ℝ => inner ℝ (N t - c) w) :=
    ContDiff.inner ℝ (hN.sub (contDiff_const (c := c))) contDiff_const
  exact hN.sub (ContDiff.smul_const h1 w)

lemma projectAlong_periodic {N : ℝ → Space} (hNper : Function.Periodic N period) (w c : Space) :
    Function.Periodic (projectAlong w c N) period := by
  intro t
  show N (t + period) - inner ℝ (N (t + period) - c) w • w
      = N t - inner ℝ (N t - c) w • w
  rw [hNper t]

/-- The projection of a difference: the `c` drops out. -/
lemma projectAlong_sub (w c : Space) (N : ℝ → Space) (t t' : ℝ) :
    projectAlong w c N t - projectAlong w c N t'
      = (N t - N t') - inner ℝ (N t - N t') w • w := by
  have hc : inner ℝ (N t - c) w - inner ℝ (N t' - c) w = inner ℝ (N t - N t') w := by
    rw [← inner_sub_left]
    congr 1
    abel
  show N t - inner ℝ (N t - c) w • w - (N t' - inner ℝ (N t' - c) w • w)
      = (N t - N t') - inner ℝ (N t - N t') w • w
  rw [← hc, sub_smul]
  abel

/-- The velocity of the projection. -/
lemma velocity_projectAlong {N : ℝ → Space} {w c : Space} {t : ℝ}
    (hN : DifferentiableAt ℝ N t) :
    velocity (projectAlong w c N) t = velocity N t - inner ℝ (velocity N t) w • w := by
  have h1 : DifferentiableAt ℝ (fun u : ℝ => N u - c) t := hN.sub_const c
  have h2 : DifferentiableAt ℝ (fun u : ℝ => inner ℝ (N u - c) w) t :=
    DifferentiableAt.inner ℝ h1 (differentiableAt_const w)
  have hderiv : deriv (fun u : ℝ => inner ℝ (N u - c) w) t = inner ℝ (velocity N t) w := by
    have h := deriv_inner_apply ℝ (f := fun u : ℝ => N u - c) (g := fun _ : ℝ => w) h1
      (differentiableAt_const w)
    simpa [velocity, deriv_const] using h
  show deriv ((fun u : ℝ => N u) - fun y : ℝ => inner ℝ (N y - c) w • w) t
      = deriv N t - inner ℝ (deriv N t) w • w
  rw [deriv_sub hN (h2.smul_const w), deriv_smul_const h2 w, hderiv]
  rfl

/-- The shear identity: the convex combination of a curve and its projection. -/
lemma shear_eq (w c : Space) (N : ℝ → Space) (s t : ℝ) :
    N t - s • (inner ℝ (N t - c) w • w) = (1 - s) • N t + s • projectAlong w c N t := by
  have hcancel : (1 - s) • N t + s • N t = N t := by
    rw [← add_smul]; norm_num
  show N t - s • (inner ℝ (N t - c) w • w)
      = (1 - s) • N t + s • (N t - inner ℝ (N t - c) w • w)
  calc N t - s • (inner ℝ (N t - c) w • w)
      = ((1 - s) • N t + s • N t) - s • (inner ℝ (N t - c) w • w) := by rw [hcancel]
    _ = (1 - s) • N t + (s • N t - s • (inner ℝ (N t - c) w • w)) := by abel
    _ = (1 - s) • N t + s • (N t - inner ℝ (N t - c) w • w) := by rw [smul_sub]

/-- **The shear family flattening a knot into the plane perpendicular to `w`.**  If the projection
of the `C^∞` knot `N` along `w` is injective on one period and regular, then the shear
`s ↦ (fun t => N t - s • ⟪N t - c, w⟫ • w)` is a jointly `C¹` family of `C^∞` knots from `N` to
its projection. -/
theorem shearFamily_of_projection {N : ℝ → Space} (hN : IsCInfKnot N) {w c : Space}
    (hw : ‖w‖ = 1)
    (hinj : Set.InjOn (projectAlong w c N) (Set.Ico (0 : ℝ) period))
    (hreg : ∀ t : ℝ, velocity (projectAlong w c N) t ≠ 0) :
    ∃ F : ℝ → ℝ → Space,
      ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
      (∀ s t : ℝ, F (t + period) s = F t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
      (∀ t : ℝ, F t 0 = N t) ∧
      (∀ t : ℝ, F t 1 = projectAlong w c N t) := by
  have hNsm : ContDiff ℝ cInfT N := hN.1
  have hPsm : ContDiff ℝ cInfT (projectAlong w c N) := projectAlong_smooth hNsm w c
  have hPdiff : ∀ t : ℝ, DifferentiableAt ℝ (projectAlong w c N) t :=
    fun t => (hPsm.differentiable cInfT_ne_zero).differentiableAt
  have hNdiff : ∀ t : ℝ, DifferentiableAt ℝ N t :=
    fun t => (hNsm.differentiable cInfT_ne_zero).differentiableAt
  -- the inner-product difference is the difference of parameters
  have hinner_sub : ∀ t t' : ℝ,
      inner ℝ (N t - c) w - inner ℝ (N t' - c) w = inner ℝ (N t - N t') w := by
    intro t t'
    rw [← inner_sub_left]
    congr 1
    abel
  refine ⟨fun t s => N t - s • (inner ℝ (N t - c) w • w), ?_, ?_, ?_, ?_, ?_⟩
  · -- joint `C¹`
    show ContDiff ℝ 1 (fun p : ℝ × ℝ => N p.1 - p.2 • (inner ℝ (N p.1 - c) w • w))
    have hN1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => N p.1) :=
      (hNsm.of_le one_le_cInfT).comp contDiff_fst
    have hA : ContDiff ℝ 1 (fun p : ℝ × ℝ => inner ℝ (N p.1 - c) w) :=
      ContDiff.inner ℝ (hN1.sub contDiff_const) contDiff_const
    have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.2 * inner ℝ (N p.1 - c) w) • w) :=
      ContDiff.smul_const (contDiff_snd.mul hA) w
    rw [show (fun p : ℝ × ℝ => N p.1 - p.2 • (inner ℝ (N p.1 - c) w • w))
        = fun p : ℝ × ℝ => N p.1 - (p.2 * inner ℝ (N p.1 - c) w) • w from by
      funext p
      rw [smul_smul]]
    exact hN1.sub h2
  · -- periodicity
    intro s t
    show N (t + period) - s • (inner ℝ (N (t + period) - c) w • w)
        = N t - s • (inner ℝ (N t - c) w • w)
    rw [hN.2.1 t]
  · -- the slices are `C^∞` knots
    intro s hs
    have hslt : s ≤ 1 := hs.2
    have hsmooth : ContDiff ℝ cInfT (fun t : ℝ => N t - s • (inner ℝ (N t - c) w • w)) := by
      have hA : ContDiff ℝ cInfT (fun t : ℝ => inner ℝ (N t - c) w) :=
        ContDiff.inner ℝ (hNsm.sub contDiff_const) contDiff_const
      have h2 : ContDiff ℝ cInfT (fun t : ℝ => (s * inner ℝ (N t - c) w) • w) :=
        ContDiff.smul_const (contDiff_const.mul hA) w
      rw [show (fun t : ℝ => N t - s • (inner ℝ (N t - c) w • w))
          = fun t : ℝ => N t - (s * inner ℝ (N t - c) w) • w from by
        funext t
        rw [smul_smul]]
      exact hNsm.sub h2
    have hper : Function.Periodic (fun t : ℝ => N t - s • (inner ℝ (N t - c) w • w)) period := by
      intro t
      show N (t + period) - s • (inner ℝ (N (t + period) - c) w • w)
          = N t - s • (inner ℝ (N t - c) w • w)
      rw [hN.2.1 t]
    have hinjs : Set.InjOn (fun t : ℝ => N t - s • (inner ℝ (N t - c) w • w))
        (Set.Ico (0 : ℝ) period) := by
      intro t ht t' ht' heq
      have hdiff : N t - N t' = s • (inner ℝ (N t - N t') w • w) := by
        have h : N t - s • (inner ℝ (N t - c) w • w)
            - (N t' - s • (inner ℝ (N t' - c) w • w)) = 0 := sub_eq_zero.mpr heq
        rw [show N t - s • (inner ℝ (N t - c) w • w)
              - (N t' - s • (inner ℝ (N t' - c) w • w))
            = (N t - N t')
              - s • ((inner ℝ (N t - c) w - inner ℝ (N t' - c) w) • w) from by module] at h
        rw [hinner_sub t t'] at h
        exact sub_eq_zero.mp h
      have hinner : inner ℝ (N t - N t') w = s * inner ℝ (N t - N t') w := by
        have h := congrArg (fun p : Space => inner ℝ p w) hdiff
        rw [inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, hw] at h
        simp only [one_pow, mul_one, RCLike.conj_to_real] at h
        exact h
      rcases lt_or_eq_of_le hslt with hslt' | hseq
      · have hz' : (1 - s) * inner ℝ (N t - N t') w = 0 := by linarith [hinner]
        have hinner0 : inner ℝ (N t - N t') w = 0 := by
          rcases mul_eq_zero.mp hz' with h | h
          · linarith
          · exact h
        have hNtt' : N t = N t' := by
          refine sub_eq_zero.mp ?_
          rw [hdiff, hinner0]
          simp
        exact hN.2.2.1 ht ht' hNtt'
      · have hdiff' : N t - N t' = inner ℝ (N t - N t') w • w := by
          have h := hdiff
          rw [hseq, one_smul] at h
          exact h
        have hproj : projectAlong w c N t - projectAlong w c N t' = 0 := by
          rw [projectAlong_sub]
          exact sub_eq_zero.mpr hdiff'
        exact hinj ht ht' (sub_eq_zero.mp hproj)
    have hvel : ∀ t : ℝ, velocity (fun t : ℝ => N t - s • (inner ℝ (N t - c) w • w)) t ≠ 0 := by
      intro t
      have hderiv : velocity (fun u : ℝ => N u - s • (inner ℝ (N u - c) w • w)) t
          = velocity N t - s • (inner ℝ (velocity N t) w • w) := by
        have hAdiff : DifferentiableAt ℝ (fun u : ℝ => inner ℝ (N u - c) w) t :=
          DifferentiableAt.inner ℝ ((hNdiff t).sub_const c) (differentiableAt_const w)
        have hAderiv : deriv (fun u : ℝ => inner ℝ (N u - c) w) t = inner ℝ (velocity N t) w := by
          have h := deriv_inner_apply ℝ (f := fun u : ℝ => N u - c) (g := fun _ : ℝ => w)
            ((hNdiff t).sub_const c) (differentiableAt_const w)
          simpa [velocity, deriv_const] using h
        have h2diff : DifferentiableAt ℝ (fun u : ℝ => inner ℝ (N u - c) w • w) t :=
          hAdiff.smul_const w
        show deriv ((fun u : ℝ => N u)
              - s • (fun u : ℝ => inner ℝ (N u - c) w • w)) t
            = velocity N t - s • (inner ℝ (velocity N t) w • w)
        rw [deriv_sub (f := fun u : ℝ => N u)
            (g := s • (fun u : ℝ => inner ℝ (N u - c) w • w)) (hNdiff t)
            ((h2diff.const_smul s)),
          deriv_const_smul s h2diff, deriv_smul_const hAdiff w, hAderiv]
        rfl
      rw [hderiv]
      intro hzero
      have hdiff : velocity N t = s • (inner ℝ (velocity N t) w • w) :=
        sub_eq_zero.mp hzero
      have hinner : inner ℝ (velocity N t) w = s * inner ℝ (velocity N t) w := by
        have h := congrArg (fun p : Space => inner ℝ p w) hdiff
        rw [inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, hw] at h
        simp only [one_pow, mul_one, RCLike.conj_to_real] at h
        exact h
      rcases lt_or_eq_of_le hslt with hslt' | hseq
      · have hz' : (1 - s) * inner ℝ (velocity N t) w = 0 := by linarith [hinner]
        have hinner0 : inner ℝ (velocity N t) w = 0 := by
          rcases mul_eq_zero.mp hz' with h | h
          · linarith
          · exact h
        refine hN.2.2.2 t ?_
        rw [hdiff, hinner0]
        simp
      · refine hreg t ?_
        have hA : inner ℝ (velocity N t) w • w = velocity N t := by
          have h := hdiff
          rw [hseq, one_smul] at h
          exact h.symm
        rw [velocity_projectAlong (hNdiff t), hA]
        simp
    exact ⟨hsmooth, hper, hinjs, hvel⟩
  · intro t
    simp
  · intro t
    rw [show projectAlong w c N t = N t - inner ℝ (N t - c) w • w from rfl]
    simp


/-- **The low end of the chord sweep.**  Let `N` be a `C^∞` knot whose projection along a unit
direction `w` is injective on one period and regular, and suppose that the projected curve is a
planar star-shaped curve about `c'` of the orthonormal frame `(u, v)` (every ray from `c'` meets it
once, positively oriented).  Then `N` is joined to the round circle `t ↦ cos t • u + sin t • v` by
a jointly `C¹` family of `C^∞` knots.

The two ingredients are `Work.Drive.shearFamily_of_projection` (the flattening of `N` to its
projection) and `Work.Drive.needleToCircle_of_starShaped` (the polar interpolation of the flat
needle to the circle), glued by `Work.Drive.sweepGlue_clauses`. -/
theorem lowEnd_of_projection_starShaped {N : ℝ → Space} (hN : IsCInfKnot N)
    {w c c' u v : Space} (hw : ‖w‖ = 1)
    (hinj : Set.InjOn (projectAlong w c N) (Set.Ico (0 : ℝ) period))
    (hreg : ∀ t : ℝ, velocity (projectAlong w c N) t ≠ 0)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hplane : ∀ t : ℝ,
      projectAlong w c N t - c' = inner ℝ (projectAlong w c N t - c') u • u
        + inner ℝ (projectAlong w c N t - c') v • v)
    (hne : ∀ t : ℝ, projectAlong w c N t ≠ c')
    (h0 : polarDir (projectAlong w c N) c' u v 0 = (1, 0))
    (hdir : Set.InjOn (polarDir (projectAlong w c N) c' u v) (Set.Ico (0 : ℝ) period))
    (hang : ∀ t : ℝ,
      0 < polarCoord (projectAlong w c N) c' u t
            * deriv (polarCoord (projectAlong w c N) c' v) t
        - polarCoord (projectAlong w c N) c' v t
            * deriv (polarCoord (projectAlong w c N) c' u) t) :
    ∃ F : ℝ → ℝ → Space,
      ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
      (∀ s t : ℝ, F (t + period) s = F t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
      (∀ t : ℝ, F t 0 = N t) ∧
      (∀ t : ℝ, F t 1 = Real.cos t • u + Real.sin t • v) := by
  have hNsm : ContDiff ℝ cInfT N := hN.1
  set M : ℝ → Space := projectAlong w c N with hMdef
  have hMsm : ContDiff ℝ cInfT M := projectAlong_smooth hNsm w c
  have hMper : Function.Periodic M period := projectAlong_periodic hN.2.1 w c
  obtain ⟨F1, hF1joint, hF1per, hF1slice, hF1zero, hF1one⟩ :=
    shearFamily_of_projection hN hw hinj hreg
  obtain ⟨F2, hF2joint, hF2per, hF2slice, hF2zero, hF2one⟩ :=
    needleToCircle_of_starShaped hu hv huv hMsm hMper hplane hne h0 hdir hang
  have hjun : ∀ t : ℝ, F1 t 1 = F2 t 0 := by
    intro t
    rw [hF1one t, hF2zero t]
  obtain ⟨hjoint, hper, hslice, hzero, hone⟩ :=
    sweepGlue_clauses hF1joint hF2joint hjun hF1slice hF2slice hF1per hF2per
  refine ⟨fun t s => sweepGlue F1 F2 s t, hjoint, ?_, ?_, ?_, ?_⟩
  · intro s t
    exact hper s t
  · intro s hs
    exact hslice s hs
  · intro t
    show sweepGlue F1 F2 0 t = N t
    rw [hzero t]
    exact hF1zero t
  · intro t
    show sweepGlue F1 F2 1 t = Real.cos t • u + Real.sin t • v
    rw [hone t]
    exact hF2one t


/-- **The endgame assembly.**  A jointly `C¹` family of `C^∞` knots from `r` to a curve `N`, and a
jointly `C¹` family of `C^∞` knots from `N` to `standardCircle`, give `IsUnknotted r`.  This is the
shape in which the sweep route is completed: `N` is the needle, the first family is
`Work.Drive.sweepToNeedle` and the second is supplied by
`Work.Drive.lowEnd_of_projection_starShaped` (followed by the rotation of the frame `(u, v)` into
the standard frame, `Work.Drive.framePath`). -/
theorem isUnknotted_of_family_through {r : ℝ → Space} (hr : IsSmoothKnot r) {N : ℝ → Space}
    (h1 : ∃ F : ℝ → ℝ → Space, ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
      (∀ s t : ℝ, F (t + period) s = F t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
      (∀ t : ℝ, F t 0 = r t) ∧ (∀ t : ℝ, F t 1 = N t))
    (h2 : ∃ F : ℝ → ℝ → Space, ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) ∧
      (∀ s t : ℝ, F (t + period) s = F t s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) ∧
      (∀ t : ℝ, F t 0 = N t) ∧ (∀ t : ℝ, F t 1 = standardCircle t)) :
    IsUnknotted r := by
  obtain ⟨F1, hF1j, hF1per, hF1sl, hF10, hF11⟩ := h1
  obtain ⟨F2, hF2j, hF2per, hF2sl, hF20, hF21⟩ := h2
  have hjun : ∀ t : ℝ, F1 t 1 = F2 t 0 := by
    intro t
    rw [hF11 t, hF20 t]
  obtain ⟨hjoint, hper, hslice, hzero, hone⟩ :=
    sweepGlue_clauses hF1j hF2j hjun hF1sl hF2sl hF1per hF2per
  refine isUnknotted_of_cInf_isotopy hr hjoint hper ?_ ?_ hslice
  · intro t
    show sweepGlue F1 F2 0 t = r t
    rw [hzero t]
    exact hF10 t
  · intro t
    show sweepGlue F1 F2 1 t = standardCircle t
    rw [hone t]
    exact hF21 t

end Work.Drive
