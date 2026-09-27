import Mathlib
import Submission.Work.Potential.removable_singularity_of_bounded_near
import Submission.Work.SimplyConnected.ABS.trace_of_finiteException

/-!
# Local removability: the brick that gates the isolated and polar fragments of the trace

Everything downstream of the isolated-complement case (and of the whole polar/finite-exception
branch) waits on one local statement:

    (local removability)  u harmonic and bounded on `D \ {ζ}` (`D` a chart ball around `ζ`)
                          ⇒  the limit of `u` at `ζ` along the relevant filter exists.

The workspace already has the global form, `Work.Potential.removable_singularity_of_bounded_near`
(harmonic off `univ \ {ζ}`, bounded near `ζ`), and the ℂ-side form
`Work.Potential.punctured_ball_harmonic_extension` (harmonic + bounded on `0 < ‖z - a‖ < ρ` extends
across the centre).  What is missing is the *chart transport* joining them, and that is what this
module builds, one brick at a time.

## Plan of the route (and the order in which the bricks are needed)

1. **Transport** (this file, proved): if `u` is harmonic on the punctured chart ball
   `D \ {ζ}` and the chart ball is inside the chart's target, then the pullback
   `z ↦ u ((chartAt ℂ ζ).symm z)` is harmonic at every `z` of the punctured Euclidean ball.
   This is `Submission.HarmonicOnXAt_iff_chart`, measured *in the chart at `ζ`* rather than in the
   preferred chart at the point — which is legitimate precisely because harmonicity is chart
   independent, and is the only transfer tool needed.
2. **ℂ-side extension**: apply `Work.Potential.punctured_ball_harmonic_extension` to the pullback.
3. **Push back and read off the limit**: the extension is harmonic on the whole ball, hence
   continuous, so it has a value at the centre; the pullback agrees with `u` off the centre.
4. **Finite exceptions**: iterate (3) over a `Finset`, using `exists_bound_of_finset_exception`
   (`trace_of_finiteException.lean`) at each removal to widen the bound to the remaining points.
5. **Polar sets**: replace the finite set by an arbitrary polar `K ∋ ζ`, using
   `Work.Mori.IsPolar.of_finite` for the finite case and (E4) removability for the general one.

Note on hypotheses: the transport brick carries the technical hypothesis
`Metric.ball ((chartAt ℂ ζ) ζ) ρ ⊆ (chartAt ℂ ζ).target`, which is what makes
`(chartAt ℂ ζ).symm z` lie in the chart's source (hence in the set on which `u` is harmonic).  It is
not needed for the *truth* of the limit statement — a chart ball is a neighbourhood of its centre, so
the statement can always be shrunk to a radius for which it holds — but it is needed for this proof.
-/

open Filter Set
open scoped Topology

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Chart transport of harmonicity on a punctured chart ball.**

If `u` is harmonic on the punctured chart ball
`{x ∈ (chartAt ℂ ζ).source : ‖(chartAt ℂ ζ) x - (chartAt ℂ ζ) ζ‖ < ρ} \ {ζ}`, and the Euclidean
ball of radius `ρ` about `(chartAt ℂ ζ) ζ` lies in the chart's target, then the pullback
`z ↦ u ((chartAt ℂ ζ).symm z)` is harmonic at every point `z` of the punctured Euclidean ball.

This is the first brick of local removability: it reduces the manifold statement to the ℂ-side
statement `Work.Potential.punctured_ball_harmonic_extension`. -/
theorem harmonicAt_chartSymm_of_punctured_chartBall {u : X → ℝ} {ζ : X} {ρ : ℝ}
    (hsub : Metric.ball ((chartAt ℂ ζ) ζ) ρ ⊆ (chartAt ℂ ζ).target)
    (hu : Submission.HarmonicOnX u
      (Submission.chartBall (chartAt ℂ ζ) ((chartAt ℂ ζ) ζ) ρ \ {ζ})) :
    ∀ z : ℂ, ‖z - (chartAt ℂ ζ) ζ‖ < ρ → z ≠ (chartAt ℂ ζ) ζ →
      InnerProductSpace.HarmonicAt (fun w : ℂ => u ((chartAt ℂ ζ).symm w)) z := by
  intro z hz hzne
  have hzball : z ∈ Metric.ball ((chartAt ℂ ζ) ζ) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hz
  have hsymm_mem : (chartAt ℂ ζ).symm z ∈
      Submission.chartBall (chartAt ℂ ζ) ((chartAt ℂ ζ) ζ) ρ \ {ζ} := by
    refine ⟨⟨(chartAt ℂ ζ).map_target (hsub hzball), ?_⟩, ?_⟩
    · show (chartAt ℂ ζ) ((chartAt ℂ ζ).symm z) ∈ Metric.ball ((chartAt ℂ ζ) ζ) ρ
      rw [(chartAt ℂ ζ).right_inv (hsub hzball)]
      exact hzball
    · intro h
      apply hzne
      have h' : (chartAt ℂ ζ) ((chartAt ℂ ζ).symm z) = (chartAt ℂ ζ) ζ := by rw [h]
      rwa [(chartAt ℂ ζ).right_inv (hsub hzball)] at h'
  have hAt : Submission.HarmonicOnXAt u ((chartAt ℂ ζ).symm z) := hu _ hsymm_mem
  have := (Submission.HarmonicOnXAt_iff_chart (u := u) (x := (chartAt ℂ ζ).symm z) (y := ζ)
    ((chartAt ℂ ζ).map_target (hsub hzball))).mp hAt
  rwa [(chartAt ℂ ζ).right_inv (hsub hzball)] at this


/-- **Step 2 of the local route: extend the pullback across the puncture.**

Applying `Work.Potential.punctured_ball_harmonic_extension` to the pullback of
`harmonicAt_chartSymm_of_punctured_chartBall`: a function harmonic on the punctured chart ball and
bounded there has a pullback that extends to a function harmonic on the whole Euclidean ball
`‖z - (chartAt ℂ ζ) ζ‖ < ρ`, agreeing with it off the centre. -/
theorem exists_extension_of_punctured_chartBall {u : X → ℝ} {ζ : X} {ρ M : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.ball ((chartAt ℂ ζ) ζ) ρ ⊆ (chartAt ℂ ζ).target)
    (hu : Submission.HarmonicOnX u
      (Submission.chartBall (chartAt ℂ ζ) ((chartAt ℂ ζ) ζ) ρ \ {ζ}))
    (hb : ∀ x ∈ Submission.chartBall (chartAt ℂ ζ) ((chartAt ℂ ζ) ζ) ρ, x ≠ ζ → |u x| ≤ M) :
    ∃ h : ℂ → ℝ,
      (∀ z : ℂ, ‖z - (chartAt ℂ ζ) ζ‖ < ρ → InnerProductSpace.HarmonicAt h z) ∧
      (∀ z : ℂ, ‖z - (chartAt ℂ ζ) ζ‖ < ρ → z ≠ (chartAt ℂ ζ) ζ →
        h z = u ((chartAt ℂ ζ).symm z)) := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ ζ with hc
  set a : ℂ := c ζ with ha
  have hwharm : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a →
      InnerProductSpace.HarmonicAt (fun w : ℂ => u (c.symm w)) z := by
    intro z hz hzne
    have hz' : ‖z - (chartAt ℂ ζ) ζ‖ < ρ := by simpa [ha, hc] using hz
    have hzne' : z ≠ (chartAt ℂ ζ) ζ := by simpa [ha, hc] using hzne
    exact harmonicAt_chartSymm_of_punctured_chartBall (ζ := ζ) (ρ := ρ) (u := u) hsub hu z hz' hzne'
  have hwbdd : ∀ z : ℂ, ‖z - a‖ < ρ → z ≠ a → |u (c.symm z)| ≤ M := by
    intro z hz hzne
    have hzball : z ∈ Metric.ball a ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hz
    have hzball' : z ∈ Metric.ball ((chartAt ℂ ζ) ζ) ρ := by simpa [ha, hc] using hzball
    have hztgt : z ∈ c.target := hsub hzball'
    have hmem : c.symm z ∈ Submission.chartBall c a ρ \ {ζ} := by
      refine ⟨⟨c.map_target hztgt, ?_⟩, ?_⟩
      · show c (c.symm z) ∈ Metric.ball a ρ
        rw [c.right_inv hztgt]
        exact hzball
      · intro h
        apply hzne
        have h2 : c (c.symm z) = z := c.right_inv hztgt
        have h3 : c (c.symm z) = a := by rw [h, ha]
        rw [h2] at h3
        exact h3
    exact hb _ (by simpa [ha, hc] using hmem.1) (by simpa [ha, hc] using hmem.2)
  obtain ⟨h, hharm, heq⟩ :=
    Work.Potential.punctured_ball_harmonic_extension (a := a) (ρ := ρ) (M := M) hρ
      (w := fun z : ℂ => u (c.symm z)) hwharm hwbdd
  refine ⟨h, ?_, ?_⟩
  · intro z hz
    have hz' : ‖z - a‖ < ρ := by simpa [ha, hc] using hz
    exact hharm z hz'
  · intro z hz hzne
    have hz' : ‖z - a‖ < ρ := by simpa [ha, hc] using hz
    have hzne' : z ≠ a := by simpa [ha, hc] using hzne
    simpa [hc] using heq z hz' hzne'


/-- **Step 3 of the local route: the limit at the puncture.**

With the extension `h` of brick 2 in hand the limit is read off: `h` is harmonic on the Euclidean
ball, hence continuous at its centre, and on `U` the pullback `h ∘ (chartAt ℂ ζ)` agrees with `u`
(the centre is *not* in `U`, so every point of `U` near `ζ` is off the puncture, where brick 2's
agreement applies).

This is the full local removability statement, modulo the technical hypothesis
`Metric.ball ((chartAt ℂ ζ) ζ) ρ ⊆ (chartAt ℂ ζ).target` discussed in the module docstring. -/
theorem tendsto_of_punctured_chartBall_of_chart_target {U : Set X} {u : X → ℝ} {ζ : X} {ρ M : ℝ}
    (hρ : 0 < ρ) (hζU : ζ ∉ U)
    (hsub : Metric.ball ((chartAt ℂ ζ) ζ) ρ ⊆ (chartAt ℂ ζ).target)
    (hu : Submission.HarmonicOnX u
      (Submission.chartBall (chartAt ℂ ζ) ((chartAt ℂ ζ) ζ) ρ \ {ζ}))
    (hb : ∀ x ∈ Submission.chartBall (chartAt ℂ ζ) ((chartAt ℂ ζ) ζ) ρ, x ≠ ζ → |u x| ≤ M) :
    ∃ l : ℝ, Filter.Tendsto u (nhdsWithin ζ U) (𝓝 l) := by
  classical
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ ζ with hc
  set a : ℂ := c ζ with ha
  have hζsrc : ζ ∈ c.source := mem_chart_source ℂ ζ
  have hopen : IsOpen (Submission.chartBall c a ρ) := by
    have h1 : IsOpen (c.source ∩ c ⁻¹' Metric.ball a ρ) :=
      c.continuousOn.isOpen_inter_preimage c.open_source Metric.isOpen_ball
    convert h1 using 1
    ext x
    simp [Submission.chartBall]
  have hζball : ζ ∈ Submission.chartBall c a ρ := by
    refine ⟨hζsrc, ?_⟩
    show c ζ ∈ Metric.ball a ρ
    rw [ha]
    exact Metric.mem_ball_self hρ
  obtain ⟨h, hharm, heq⟩ :=
    exists_extension_of_punctured_chartBall (ζ := ζ) (ρ := ρ) (M := M) hρ hsub hu hb
  refine ⟨h a, ?_⟩
  have houter : Filter.Tendsto (fun x : X => h (c x)) (nhdsWithin ζ U) (𝓝 (h a)) := by
    have h1 : Filter.Tendsto c (𝓝 ζ) (𝓝 a) := by
      simpa [ha] using (c.continuousAt hζsrc).tendsto
    have h2 : ContinuousAt h a :=
      (hharm a (by rw [sub_self, norm_zero]; exact hρ)).1.continuousAt
    exact (h2.tendsto.comp h1).mono_left nhdsWithin_le_nhds
  have hev : u =ᶠ[nhdsWithin ζ U] (fun x : X => h (c x)) := by
    have hball_nhds : Submission.chartBall c a ρ ∈ 𝓝[U] ζ :=
      nhdsWithin_le_nhds (hopen.mem_nhds hζball)
    filter_upwards [hball_nhds, self_mem_nhdsWithin] with x hxball hxU
    have hxne : x ≠ ζ := fun hx => hζU (hx ▸ hxU)
    have hxsrc : x ∈ c.source := hxball.1
    have hcne : c x ≠ a := by
      intro h
      apply hxne
      have h2 : c x = c ζ := by rw [ha] at h; exact h
      exact c.injOn hxsrc hζsrc h2
    have hz : ‖c x - (chartAt ℂ ζ) ζ‖ < ρ := by
      have hb'' : c x ∈ Metric.ball a ρ := hxball.2
      rw [Metric.mem_ball, dist_eq_norm] at hb''
      simpa [ha, hc] using hb''
    have hzne : c x ≠ (chartAt ℂ ζ) ζ := by simpa [ha, hc] using hcne
    rw [heq (c x) hz hzne, c.left_inv hxsrc]
  have hmap : Filter.map u (nhdsWithin ζ U) =
      Filter.map (fun x : X => h (c x)) (nhdsWithin ζ U) := by
    refine Filter.map_congr ?_
    filter_upwards [hev] with x hx
    exact hx
  show Filter.map u (nhdsWithin ζ U) ≤ 𝓝 (h a)
  rw [hmap]
  exact houter

end Work.SimplyConnected.ABS
