import Mathlib
import Submission.Work.Drive.ZerosCircle.Defs
import Submission.Work.Drive.ZerosCircle.zc_exists_smul_fderiv
import Submission.Work.Drive.ZerosCircle.zc_exists_arc_param
import Submission.Work.Drive.exists_pos_hasDerivAt_ne
import Submission.Work.Drive.finite_of_isCompact_of_isolated

/-!
# The zeros of a `C¹` function on the unit circle are finite when the gradient is not radial

Let `h : ℝ² → ℝ` be `C¹` and suppose that at every zero of `h` on the unit circle the differential of
`h` is not parallel to the differential of `w ↦ ‖w‖ ^ 2`.  Then `h` has only finitely many zeros on
the unit circle.

Indeed, at such a zero `z` the differential of `h` does not vanish on the tangent vector
`zcTang z` (`Work.Drive.zc_fderiv_tang_ne_zero`), so `h` restricted to the arc of the unit circle
through `z` has a nonzero derivative there and is therefore locally nonzero away from `z`
(`Work.Drive.zc_local_isolated`).  The zero set is closed and contained in the compact unit sphere,
and a compact set all of whose points are isolated is finite
(`Work.Drive.finite_of_isCompact_of_isolated`).
-/

namespace Work.Drive

open scoped InnerProductSpace

noncomputable section

/-- The arc `s ↦ zcArcPt z v s` has derivative `v` at `0`. -/
theorem zc_arc_hasDerivAt (z v : EuclideanSpace ℝ (Fin 2)) :
    HasDerivAt (fun s : ℝ => zcArcPt z v s) v 0 := by
  have key : (fun s : ℝ => zcArcPt z v s) =
      ((fun y : ℝ => Real.cos y • z) + fun y : ℝ => Real.sin y • v) := rfl
  have h := ((Real.hasDerivAt_cos 0).smul_const z).add ((Real.hasDerivAt_sin 0).smul_const v)
  have hderiv : (-Real.sin 0 : ℝ) • z + Real.cos 0 • v = v := by simp
  rw [key]
  simpa only [hderiv] using h

/-- The function `s ↦ h (zcArcPt z v s)` is `C¹` when `h` is. -/
theorem zc_arc_contDiff (h : EuclideanSpace ℝ (Fin 2) → ℝ) (hh : ContDiff ℝ 1 h)
    (z v : EuclideanSpace ℝ (Fin 2)) : ContDiff ℝ 1 (fun s : ℝ => h (zcArcPt z v s)) := by
  have hg : ContDiff ℝ 1 (fun s : ℝ => zcArcPt z v s) := by
    rw [show (fun s : ℝ => zcArcPt z v s) =
      fun s : ℝ => Real.cos s • z + Real.sin s • v from rfl]
    fun_prop
  exact hh.comp hg

/-- The derivative at `0` of `s ↦ h (zcArcPt z v s)` is `fderiv ℝ h z v`. -/
theorem zc_arc_deriv (h : EuclideanSpace ℝ (Fin 2) → ℝ) (hh : ContDiff ℝ 1 h)
    (z v : EuclideanSpace ℝ (Fin 2)) :
    deriv (fun s : ℝ => h (zcArcPt z v s)) 0 = fderiv ℝ h z v := by
  have hf : HasFDerivAt h (fderiv ℝ h z) (zcArcPt z v 0) := by
    simpa [zcArcPt_zero] using (hh.differentiable_one (zcArcPt z v 0)).hasFDerivAt
  have h := (hf.comp_hasDerivAt 0 (zc_arc_hasDerivAt z v)).deriv
  simpa only [Function.comp_def] using h

/-- **The differential of `h` is nonzero on the tangent vector of the circle.**  If `h` is `C¹`, `z`
is a zero of `h` on the unit circle, and at `z` the differential of `h` is not a multiple of the
differential of `w ↦ ‖w‖ ^ 2`, then `fderiv ℝ h z` does not vanish on the tangent vector
`zcTang z`. -/
theorem zc_fderiv_tang_ne_zero (h : EuclideanSpace ℝ (Fin 2) → ℝ)
    (htrans : ∀ z : EuclideanSpace ℝ (Fin 2), h z = 0 → ‖z‖ = 1 →
      ¬ ∃ c : ℝ,
        fderiv ℝ h z = c • fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖ ^ 2) z)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : h z = 0) (hzn : ‖z‖ = 1) :
    fderiv ℝ h z (zcTang z) ≠ 0 := by
  intro hd
  have hv : ‖zcTang z‖ = 1 := by rw [zcTang_norm, hzn]
  have hzv : inner ℝ z (zcTang z) = 0 := by
    rw [real_inner_comm]
    exact zcTang_inner z
  exact htrans z hz hzn (ZerosCircle.zc_exists_smul_fderiv hzn hv hzv hd)

/-- **Isolation of a zero on the circle.**  Under the transversality hypothesis of the main theorem,
a zero `z` of `h` on the unit circle is isolated among the zeros of `h` on the circle. -/
theorem zc_local_isolated (h : EuclideanSpace ℝ (Fin 2) → ℝ) (hh : ContDiff ℝ 1 h)
    (htrans : ∀ z : EuclideanSpace ℝ (Fin 2), h z = 0 → ‖z‖ = 1 →
      ¬ ∃ c : ℝ,
        fderiv ℝ h z = c • fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖ ^ 2) z)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : h z = 0) (hzn : ‖z‖ = 1) :
    ∃ δ > 0, ∀ z' : EuclideanSpace ℝ (Fin 2), h z' = 0 → ‖z'‖ = 1 → ‖z' - z‖ < δ → z' = z := by
  have hv : ‖zcTang z‖ = 1 := by rw [zcTang_norm, hzn]
  have hzv : inner ℝ z (zcTang z) = 0 := by
    rw [real_inner_comm]
    exact zcTang_inner z
  have hd : fderiv ℝ h z (zcTang z) ≠ 0 := zc_fderiv_tang_ne_zero h htrans z hz hzn
  have hderiv := zc_arc_deriv h hh z (zcTang z)
  have hcont := zc_arc_contDiff h hh z (zcTang z)
  -- the restriction of `h` to the arc is a `C¹` function with a nonzero derivative at `0`
  have hg0 : (fun s : ℝ => h (zcArcPt z (zcTang z) s)) 0 = 0 := by
    simp [zcArcPt_zero, hz]
  have hhas : HasDerivAt (fun s : ℝ => h (zcArcPt z (zcTang z) s))
      (deriv (fun s : ℝ => h (zcArcPt z (zcTang z) s)) 0) 0 :=
    (hcont.differentiable_one 0).hasDerivAt
  have hgne : deriv (fun s : ℝ => h (zcArcPt z (zcTang z) s)) 0 ≠ 0 := by
    rw [hderiv]
    exact hd
  obtain ⟨η, hηpos, hη⟩ := exists_pos_hasDerivAt_ne hhas hgne
  have hη' : ∀ s : ℝ, |s| < η → s ≠ 0 → h (zcArcPt z (zcTang z) s) ≠ 0 := by
    intro s hs hs0
    have h1 : 0 < |s - 0| := by simpa using abs_pos.mpr hs0
    have h2 : |s - 0| < η := by simpa using hs
    have h3 := hη s h1 h2
    simpa [hz] using h3
  -- points of the circle close to `z` are reached by the arc at a small parameter
  obtain ⟨δ, hδpos, hδ⟩ := ZerosCircle.zc_exists_arc_param z (zcTang z) hzn hv hzv η hηpos
  refine ⟨δ, hδpos, ?_⟩
  intro z' hz' hzn' hdist
  obtain ⟨s, hslt, hsz⟩ := hδ z' hzn' hdist
  have hgs : h (zcArcPt z (zcTang z) s) = 0 := by
    rw [← hsz]
    exact hz'
  by_cases hs0 : s = 0
  · rw [hs0, zcArcPt_zero] at hsz
    exact hsz
  · exact absurd hgs (hη' s hslt hs0)

/-- **Zeros of a `C¹` function on the unit circle are finite**, provided the differential of `h` is
nowhere parallel to the differential of `w ↦ ‖w‖ ^ 2` at those zeros. -/
theorem zeros_finite_on_unitCircle (h : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hh : ContDiff ℝ 1 h)
    (htrans : ∀ z : EuclideanSpace ℝ (Fin 2), h z = 0 → ‖z‖ = 1 →
      ¬ ∃ c : ℝ,
        fderiv ℝ h z = c • fderiv ℝ (fun w : EuclideanSpace ℝ (Fin 2) => ‖w‖ ^ 2) z) :
    Set.Finite {z : EuclideanSpace ℝ (Fin 2) | h z = 0 ∧ ‖z‖ = 1} := by
  set S : Set (EuclideanSpace ℝ (Fin 2)) := {z | h z = 0 ∧ ‖z‖ = 1} with hSdef
  have hSclosed : IsClosed S := by
    have hset : S = {z : EuclideanSpace ℝ (Fin 2) | h z = 0} ∩
        {z : EuclideanSpace ℝ (Fin 2) | ‖z‖ = 1} := by
      rw [hSdef]
      ext z
      simp
    rw [hset]
    exact (isClosed_singleton.preimage hh.continuous).inter
      (isClosed_eq continuous_norm continuous_const)
  have hSsub : S ⊆ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    intro z hz
    rw [hSdef] at hz
    simpa [Metric.mem_sphere, dist_eq_norm] using hz.2
  have hScomp : IsCompact S :=
    IsCompact.of_isClosed_subset (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) hSclosed hSsub
  have hfin : S.Finite := by
    refine finite_of_isCompact_of_isolated hScomp ?_
    intro z hz
    rw [hSdef] at hz
    obtain ⟨hz0, hz1⟩ := hz
    obtain ⟨δ, hδpos, hiso⟩ := zc_local_isolated h hh htrans z hz0 hz1
    refine ⟨Metric.ball z δ, Metric.isOpen_ball, Metric.mem_ball_self hδpos, ?_⟩
    intro w hw
    obtain ⟨hwU, hwS⟩ := hw
    rw [hSdef] at hwS
    rw [Metric.mem_ball, dist_eq_norm] at hwU
    exact hiso w hwS.1 hwS.2 hwU
  rwa [hSdef] at hfin

end

end Work.Drive
