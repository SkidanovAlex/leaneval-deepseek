import ChallengeDeps
import Submission.RiemannSurface
import Submission.SuperharmonicX
import Submission.DirichletRegionOn
import Submission.DualPerron
import Submission.SubharmonicChartMVP
import Submission.Commons.Analysis.Complex.Harmonic.max_principle_subharmonic

/-!
# The sweep (balayage) of a subharmonic barrier

The Green function of a region `U` with a pole at `z₀` is classically obtained as the **sweep**
(balayage) of the logarithmic potential: the *least* superharmonic function on `U ∖ {z₀}` which
dominates the potential.  The dual Perron theorem (`Submission.IsPerronOnInf.lowerEnvelope_harmonic`)
turns this into a theorem: if the family

`Submission.sweepFamily G U = {v | v superharmonic on U, `G x ≤ v x` on `U`}`

is nonempty, then its lower envelope `E = inf (sweepFamily G U)` is harmonic on `U`, and it is the
least superharmonic majorant of `G`.

The technical heart is the *barrier min principle*: a harmonic replacement of a superharmonic
majorant of a subharmonic `G` is again a majorant of `G`.  On a chart disc this is the Euclidean
statement `Submission.subharmonic_barrier_le_harmonic`: a subharmonic (mean-value-inequality)
function on a disc which is dominated by the boundary values of the harmonic function is dominated
by that harmonic function on the whole disc.  The proof is the maximum principle applied to
`G - glued`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

/-! ## The Euclidean barrier min principle -/

/-- **Barrier min principle.**  Let `Gp` satisfy the circle sub-mean-value inequality on the disc
`ball a ρ` and be continuous on the closed disc, and let `u` be harmonic on the disc, with the glued
function `gluedBall u F a ρ` continuous.  If `Gp ≤ F` on the sphere, then `Gp ≤ u` on the disc.

(Equivalently: the harmonic replacement of the boundary data of a superharmonic function is again
a superharmonic majorant of `Gp`.) -/
theorem subharmonic_barrier_le_harmonic {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {Gp u F : ℂ → ℝ}
    (hGcont : ContinuousOn Gp (Metric.closedBall a ρ))
    (hGmvp : ∀ p : ℂ, ‖p - a‖ < ρ → ∀ r : ℝ, 0 < r → ‖p - a‖ + r < ρ →
      Gp p ≤ Real.circleAverage Gp p r)
    (hu : ∀ w : ℂ, ‖w - a‖ < ρ → InnerProductSpace.HarmonicAt u w)
    (hglue : ContinuousOn (gluedBall u F a ρ) (Metric.closedBall a ρ))
    (hle : ∀ ζ ∈ Metric.sphere a ρ, Gp ζ ≤ F ζ) :
    ∀ w : ℂ, ‖w - a‖ < ρ → Gp w ≤ u w := by
  set Φ : ℂ → ℝ := Gp - gluedBall u F a ρ with hΦdef
  have hcont : ContinuousOn Φ (Metric.closedBall a ρ) := hGcont.sub hglue
  have hbd : ∀ z : ℂ, ‖z - a‖ = ρ → Φ z ≤ 0 := by
    intro z hz
    have hz' : z ∈ Metric.sphere a ρ := by rwa [Metric.mem_sphere, dist_eq_norm]
    have hnot : z ∉ Metric.ball a ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [hz]; exact lt_irrefl ρ
    have hgl : gluedBall u F a ρ z = F z := gluedBall_of_not_mem hnot
    have h := hle z hz'
    simp only [hΦdef, Pi.sub_apply, hgl]
    linarith
  have hmvp : ∀ p : ℂ, ‖p - a‖ < ρ → ∀ r : ℝ, 0 < r → ‖p - a‖ + r < ρ →
      Φ p ≤ Real.circleAverage Φ p r := by
    intro p hp r hr hpr
    have hpr' : r + ‖p - a‖ < ρ := by linarith
    have hpball : p ∈ Metric.ball a ρ := by rwa [Metric.mem_ball, dist_eq_norm]
    have hglp : gluedBall u F a ρ p = u p := gluedBall_of_mem hpball
    have hclosed : Metric.closedBall p r ⊆ Metric.ball a ρ := by
      intro y hy
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      calc dist y a ≤ dist y p + dist p a := dist_triangle _ _ _
        _ ≤ r + dist p a := by linarith
        _ = r + ‖p - a‖ := by rw [dist_eq_norm]
        _ < ρ := hpr'
    have hcirc : Metric.sphere p r ⊆ Metric.ball a ρ := by
      intro y hy
      rw [Metric.mem_sphere, dist_eq_norm] at hy
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖y - a‖ = ‖(y - p) + (p - a)‖ := by ring_nf
        _ ≤ ‖y - p‖ + ‖p - a‖ := norm_add_le _ _
        _ = r + ‖p - a‖ := by rw [hy]
        _ < ρ := hpr'
    have hHar : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall p r) := by
      intro y hy
      have h2 := hclosed hy
      rw [Metric.mem_ball, dist_eq_norm] at h2
      exact hu y h2
    have hsphere : ContinuousOn Gp (Metric.sphere p |r|) := by
      rw [abs_of_pos hr]
      exact (hGcont.mono (hclosed.trans Metric.ball_subset_closedBall)).mono
        Metric.sphere_subset_closedBall
    have hsphere' : ContinuousOn (gluedBall u F a ρ) (Metric.sphere p |r|) := by
      rw [abs_of_pos hr]
      exact (hglue.mono (hclosed.trans Metric.ball_subset_closedBall)).mono
        Metric.sphere_subset_closedBall
    have hIntG : CircleIntegrable Gp p r := hsphere.circleIntegrable'
    have hIntG' : CircleIntegrable (gluedBall u F a ρ) p r := hsphere'.circleIntegrable'
    have heqOn : Set.EqOn (gluedBall u F a ρ) u (Metric.sphere p |r|) := by
      intro y hy
      have hy' : y ∈ Metric.sphere p r := by
        rw [Metric.mem_sphere, dist_eq_norm] at hy ⊢
        rwa [abs_of_pos hr] at hy
      exact gluedBall_of_mem (hcirc hy')
    have havg : Real.circleAverage Φ p r
        = Real.circleAverage Gp p r - Real.circleAverage u p r := by
      have h1 : Real.circleAverage Φ p r
          = Real.circleAverage Gp p r - Real.circleAverage (gluedBall u F a ρ) p r :=
        Real.circleAverage_sub hIntG hIntG'
      rw [h1, Real.circleAverage_congr_sphere heqOn]
    have hHar' : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall p |r|) := by
      rw [abs_of_pos hr]; exact hHar
    have hup : Real.circleAverage u p r = u p :=
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq hHar'
    have hΦp : Φ p = Gp p - u p := by simp only [hΦdef, Pi.sub_apply, hglp]
    rw [havg, hup, hΦp]
    exact sub_le_sub_right (hGmvp p hp r hr hpr) (u p)
  have hmain := Commons.Analysis.Complex.Harmonic.max_principle_subharmonic (c := a) (R := ρ) hρ
    hcont hmvp hbd
  intro w hw
  have hglw : gluedBall u F a ρ w = u w :=
    gluedBall_of_mem (by rwa [Metric.mem_ball, dist_eq_norm])
  have h := hmain w hw.le
  simp only [hΦdef, Pi.sub_apply, hglw] at h
  linarith

end Submission

namespace Submission

section Sweep

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The sweep family of a barrier `G` on an open set `U`**: the superharmonic functions on `U`
which dominate `G` pointwise.  The lower envelope of this family is the *sweep* (balayage) of `G`. -/
def sweepFamily (G : X → ℝ) (U : Set X) : Set (X → ℝ) :=
  {v | SuperharmonicOnX v U ∧ ∀ x ∈ U, G x ≤ v x}

theorem sweepFamily_superharmonic {G : X → ℝ} {U : Set X} {v : X → ℝ}
    (hv : v ∈ sweepFamily G U) : SuperharmonicOnX v U := hv.1

theorem sweepFamily_le {G : X → ℝ} {U : Set X} {v : X → ℝ}
    (hv : v ∈ sweepFamily G U) {x : X} (hx : x ∈ U) : G x ≤ v x := hv.2 x hx

theorem sweepFamily_min {G : X → ℝ} {U : Set X} {v w : X → ℝ}
    (hv : v ∈ sweepFamily G U) (hw : w ∈ sweepFamily G U) :
    min v w ∈ sweepFamily G U :=
  ⟨hv.1.min hw.1, fun x hx => le_min (hv.2 x hx) (hw.2 x hx)⟩


end Sweep

end Submission

/-! ## The sweep of a subharmonic barrier, continued

The sweep family `sweepFamily G U` of a barrier `G` on the open set `U` is closed under harmonic
replacement, *provided* the barrier `G` is itself subharmonic on `U`.  This is the hypothesis under
which the dual Perron theorem (`Submission.IsPerronOnInf.lowerEnvelope_harmonic`) applies to the
sweep: the sweep of a subharmonic barrier is harmonic, and it is the least superharmonic majorant
of the barrier.

The two ingredients are

* the Euclidean barrier minimum principle `subharmonic_barrier_le_harmonic` (the harmonic
  replacement of the boundary data of a subharmonic function dominates it on the disc), which
  gives the domination `G ≤ replaceOnDisc … u v` inside the replacement disc, and
* the negation bridge: `-v` is subharmonic and `-u` is harmonic, so
  `replaceOnDisc_subharmonicOn` identifies the replacement of `-v` with the negative of the
  replacement of `v`, whence the replaced function is again superharmonic.
-/

namespace Submission

section SweepReplacement

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The harmonic replacement of the pointwise negative is the negative of the harmonic
replacement. -/
theorem replaceOnDisc_neg (c : OpenPartialHomeomorph X ℂ) (a : ℂ) (ρ : ℝ) (u : ℂ → ℝ)
    (f : X → ℝ) :
    replaceOnDisc c a ρ (fun w => -u w) (fun y => -f y)
      = fun x => -(replaceOnDisc c a ρ u f x) := by
  funext x
  by_cases hx : x ∈ chartBall c a ρ
  · rw [replaceOnDisc_of_mem_chartBall hx, replaceOnDisc_of_mem_chartBall hx]
  · rw [replaceOnDisc_of_not_mem_chartBall hx, replaceOnDisc_of_not_mem_chartBall hx]

/-- The glued function of the negated data is the negative of the glued function. -/
theorem gluedBall_neg (u F : ℂ → ℝ) (a : ℂ) (ρ : ℝ) :
    gluedBall (fun w => -u w) (fun w => -F w) a ρ = fun w => -(gluedBall u F a ρ w) := by
  funext w
  rw [gluedBall_apply, gluedBall_apply]
  by_cases hw : w ∈ Metric.ball a ρ
  · rw [if_pos hw, if_pos hw]
  · rw [if_neg hw, if_neg hw]

/-- **The sweep family is closed under harmonic replacement** (for a subharmonic barrier `G`).
If `v` is superharmonic on `U` and `G ≤ v` on `U`, and `u` is a harmonic function on the disc
`Metric.ball a ρ` whose glued extension along `(chartAt ℂ z).symm` is continuous, then the
replacement `replaceOnDisc (chartAt ℂ z) a ρ u v` again dominates `G` and is superharmonic. -/
theorem replaceOnDisc_sweepFamily {G : X → ℝ} {U : Set X} (hU : IsOpen U)
    (hG : SubharmonicOnX G U) {v : X → ℝ} (hv : v ∈ sweepFamily G U)
    {z : X} {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall a ρ ⊆ (chartAt ℂ z).target)
    (hΔU : (chartAt ℂ z).symm '' Metric.closedBall a ρ ⊆ U)
    (hGcont : ContinuousOn (fun w : ℂ => G ((chartAt ℂ z).symm w)) (Metric.closedBall a ρ))
    (hGmvp : ∀ p : ℂ, ‖p - a‖ < ρ → ∀ r : ℝ, 0 < r → ‖p - a‖ + r < ρ →
      (G ∘ (chartAt ℂ z).symm) p ≤ Real.circleAverage (G ∘ (chartAt ℂ z).symm) p r)
    {u : ℂ → ℝ} (hu : ∀ w : ℂ, ‖w - a‖ < ρ → InnerProductSpace.HarmonicAt u w)
    (hglue : ContinuousOn (gluedBall u (fun w => v ((chartAt ℂ z).symm w)) a ρ)
      (Metric.closedBall a ρ)) :
    replaceOnDisc (chartAt ℂ z) a ρ u v ∈ sweepFamily G U := by
  constructor
  · -- superharmonicity, by negation
    have hvneg : SubharmonicOnX (fun y => -v y) U := hv.1.neg
    have hneg_u : ∀ w : ℂ, ‖w - a‖ < ρ → InnerProductSpace.HarmonicAt (fun w : ℂ => -u w) w :=
      fun w hw => (hu w hw).neg
    have hglue' : ContinuousOn
        (gluedBall (fun w : ℂ => -u w) (fun w => -(v ((chartAt ℂ z).symm w))) a ρ)
        (Metric.closedBall a ρ) := by
      rw [gluedBall_neg]
      exact hglue.neg
    have hsubst := replaceOnDisc_subharmonicOn (U := U) hU hρ hsub hΔU hvneg hneg_u hglue'
    rw [replaceOnDisc_neg] at hsubst
    have hneg := hsubst.neg
    have heq : (fun x : X => -(fun y : X => -(replaceOnDisc (chartAt ℂ z) a ρ u v y)) x)
        = replaceOnDisc (chartAt ℂ z) a ρ u v := by
      funext x; simp
    rwa [heq] at hneg
  · -- domination of the barrier
    intro x hx
    by_cases hxball : x ∈ chartBall (chartAt ℂ z) a ρ
    · rw [replaceOnDisc_of_mem_chartBall hxball]
      have hx' : (chartAt ℂ z).symm ((chartAt ℂ z) x) = x :=
        (chartAt ℂ z).left_inv (chartBall_subset_source _ _ _ hxball)
      have hxmem : (chartAt ℂ z) x ∈ Metric.ball a ρ := hxball.2
      have hle := subharmonic_barrier_le_harmonic (a := a) (ρ := ρ) hρ hGcont hGmvp hu hglue
        (fun ζ hζ => hv.2 _ (hΔU ⟨ζ, Metric.sphere_subset_closedBall hζ, rfl⟩))
      have h1 := hle ((chartAt ℂ z) x) (by simpa [Metric.mem_ball, dist_eq_norm] using hxmem)
      simpa [hx', Function.comp_def] using h1
    · rw [replaceOnDisc_of_not_mem_chartBall hxball]
      exact hv.2 x hx

end SweepReplacement

end Submission

/-! ## The dual Perron theorem for the sweep of a subharmonic barrier -/

namespace Submission

section SweepPerron

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

open Filter Set

variable {G : X → ℝ} {U : Set X}

/-- The negated sweep family is closed under maxima: the maximum of the negations is the negation
of the minimum. -/
theorem max_neg_neg_mem_sweepFamily {v w : X → ℝ} (hv : v ∈ sweepFamily G U)
    (hw : w ∈ sweepFamily G U) :
    (fun x => max (-v x) (-w x)) ∈ (fun f : X → ℝ => fun x => -f x) '' sweepFamily G U :=
  ⟨fun x => Min.min (v x) (w x), sweepFamily_min hv hw, by
    funext x
    show -(Min.min (v x) (w x)) = Max.max (-v x) (-w x)
    rcases le_total (v x) (w x) with h | h
    · rw [min_eq_left h, max_eq_left (neg_le_neg h)]
    · rw [min_eq_right h, max_eq_right (neg_le_neg h)]⟩

/-- **The sweep family of a subharmonic barrier satisfies the dual Perron conditions.** -/
theorem isPerronOnInf_sweepFamily (hU : IsOpen U) (hG : SubharmonicOnX G U)
    (hne : (sweepFamily G U).Nonempty) : IsPerronOnInf (sweepFamily G U) G U := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hne
    exact ⟨fun x => -v x, ⟨v, hv, rfl⟩⟩
  · rintro f ⟨v, hv, rfl⟩
    exact hv.1.neg
  · rintro f ⟨v, hv, rfl⟩ x hx
    show -v x ≤ -G x
    linarith [hv.2 x hx]
  · rintro f ⟨v, hv, rfl⟩ g ⟨w, hw, rfl⟩
    exact max_neg_neg_mem_sweepFamily hv hw
  · -- the replacement clause
    intro z hz
    have hsrc : z ∈ (chartAt ℂ z).source := mem_chart_source ℂ z
    have hzt : (chartAt ℂ z) z ∈ (chartAt ℂ z).target := (chartAt ℂ z).map_source hsrc
    -- a neighbourhood of `(chartAt ℂ z) z` which is mapped into `U`
    obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.mem_nhds_iff.mp (by
      have h2 : U ∈ 𝓝 ((chartAt ℂ z).symm ((chartAt ℂ z) z)) := by
        rw [(chartAt ℂ z).left_inv hsrc]
        exact hU.mem_nhds hz
      exact ((chartAt ℂ z).continuousAt_symm hzt).preimage_mem_nhds h2)
    -- a ball inside the chart target
    obtain ⟨ε₂, hε₂, hε₂sub⟩ :=
      Metric.mem_nhds_iff.mp ((chartAt ℂ z).open_target.mem_nhds hzt)
    -- the mean-value data of the barrier
    set ε₀ : ℝ := min ε₁ ε₂ with hε₀def
    have hε₀ : 0 < ε₀ := lt_min hε₁ hε₂
    have hε₀₁ : ε₀ ≤ ε₁ := min_le_left _ _
    have hε₀₂ : ε₀ ≤ ε₂ := min_le_right _ _
    have htgt₀ : Metric.ball ((chartAt ℂ z) z) ε₀ ⊆ (chartAt ℂ z).target :=
      (Metric.ball_subset_ball hε₀₂).trans hε₂sub
    have hU₀ : (chartAt ℂ z).symm '' Metric.ball ((chartAt ℂ z) z) ε₀ ⊆ U := by
      rintro y ⟨w, hw, rfl⟩
      exact hε₁sub ((Metric.ball_subset_ball hε₀₁) hw)
    have hmvp₀ := SubharmonicOnX.chart_mvp hU hG hε₀ htgt₀ hU₀
    refine ⟨ε₀ / 2, half_pos hε₀, ?_⟩
    intro f hf ρ hρ hρε hsub u hup hglue
    obtain ⟨v, hv, rfl⟩ := hf
    have hρε₀ : ρ < ε₀ := lt_of_le_of_lt hρε (by linarith)
    -- the data for `replaceOnDisc_sweepFamily` at radius `ρ`
    have hsubρ : Metric.closedBall ((chartAt ℂ z) z) ρ ⊆ (chartAt ℂ z).target :=
      (Metric.closedBall_subset_ball hρε₀).trans htgt₀
    have hΔUρ : (chartAt ℂ z).symm '' Metric.closedBall ((chartAt ℂ z) z) ρ ⊆ U :=
      fun y ⟨w, hw, hwy⟩ => hU₀ ⟨w, (Metric.closedBall_subset_ball hρε₀) hw, hwy⟩
    have hGcontρ : ContinuousOn (fun w : ℂ => G ((chartAt ℂ z).symm w))
        (Metric.closedBall ((chartAt ℂ z) z) ρ) :=
      hG.1.comp (((chartAt ℂ z).continuousOn_symm).mono (fun w hw => hsubρ hw))
        (fun w hw => hΔUρ ⟨w, hw, rfl⟩)
    have hGmvpρ : ∀ p : ℂ, ‖p - (chartAt ℂ z) z‖ < ρ → ∀ r : ℝ, 0 < r →
        ‖p - (chartAt ℂ z) z‖ + r < ρ →
        (G ∘ (chartAt ℂ z).symm) p ≤ Real.circleAverage (G ∘ (chartAt ℂ z).symm) p r := by
      intro p hp r hr hpr
      refine hmvp₀ p ?_ r hr ?_
      · rw [Metric.mem_ball, dist_eq_norm]; linarith
      · intro w hw
        rw [Metric.mem_closedBall, dist_eq_norm] at hw
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖w - (chartAt ℂ z) z‖ = dist w ((chartAt ℂ z) z) := by rw [dist_eq_norm]
          _ ≤ dist w p + dist p ((chartAt ℂ z) z) := dist_triangle w p _
          _ = ‖w - p‖ + ‖p - (chartAt ℂ z) z‖ := by rw [dist_eq_norm, dist_eq_norm]
          _ ≤ r + ‖p - (chartAt ℂ z) z‖ := by linarith
          _ < ε₀ := by linarith
    -- the harmonic replacement, in the negated form
    have hnegv : (fun x => -v x) ∈ (fun f : X → ℝ => fun x => -f x) '' sweepFamily G U :=
      ⟨v, hv, rfl⟩
    refine ⟨replaceOnDisc (chartAt ℂ z) ((chartAt ℂ z) z) ρ (fun w => -u w) v,
      replaceOnDisc_sweepFamily hU hG hv hρ hsubρ hΔUρ hGcontρ hGmvpρ
        (fun w hw => (hup w hw).neg) ?_, ?_⟩
    · refine hglue.neg.congr ?_
      intro w _
      simp only [gluedBall_apply, Pi.neg_apply]
      by_cases hw : w ∈ Metric.ball ((chartAt ℂ z) z) ρ <;> simp [hw]
    · -- the replacement of `-v` is the negation of the replacement of `v` with data `-u`
      funext x
      simp only [Pi.neg_apply]
      by_cases hx : x ∈ chartBall (chartAt ℂ z) ((chartAt ℂ z) z) ρ
      · rw [replaceOnDisc_of_mem_chartBall hx, replaceOnDisc_of_mem_chartBall hx]
        simp
      · rw [replaceOnDisc_of_not_mem_chartBall hx, replaceOnDisc_of_not_mem_chartBall hx]
        simp

/-- **The sweep of a subharmonic barrier is harmonic.**  The lower envelope of the sweep family of
a subharmonic barrier `G` on an open set `U` — the *least superharmonic majorant* of `G` — is
harmonic on `U`, by the dual Perron theorem. -/
theorem lowerEnvelope_sweepFamily_harmonic (hU : IsOpen U) (hG : SubharmonicOnX G U)
    (hne : (sweepFamily G U).Nonempty) : HarmonicOnX (lowerEnvelope (sweepFamily G U)) U :=
  IsPerronOnInf.lowerEnvelope_harmonic hU (isPerronOnInf_sweepFamily hU hG hne)

end SweepPerron

end Submission
