import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.Pullback
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.familyDataOfTwoDiscsInner
import Submission.Work.Smooth.SphereJordan.innerDiscSection2
import Submission.Work.Smooth.SphereJordan.pullbackSphereCurve_pairwiseDisjoint

/-!
# Pardon's first innermost step: an innermost intersection curve exists

`Work.Topology.Classical.InnermostCurveExists P` is Pardon's "innermost in the surface" step: every
embedded disc `D ⊆ ℝ³` whose boundary is a simple closed curve `α` of the torus `F = P.carrier` and
whose interior meets `F` only along a finite family of pairwise disjoint inessential simple closed
curves `curves i ⊆ D` has an intersection curve `curves j` which bounds a *sub-disc* `f` of `D`
whose interior misses `F` and which no other intersection curve meets.

The proof is the classical one, carried out on the model disc:

* pull the intersection curves of `D` back to the model disc `𝔻 ⊆ ℂ` along the parametrising
  embedding `D.e` (`Work.Smooth.SphereJordan.SliceDiscPullback`);
* apply the planar Jordan–Schoenflies theorem (`PlaneHypothesis`) to each pulled-back plane curve,
  obtaining two complementary discs of the Riemann sphere bounded by it
  (`Work.Smooth.SphereJordan.planeTwoDiscs`);
* put the family of pairwise disjoint curves in *standard position*
  (`Work.Smooth.SphereJordan.familyDataOfTwoDiscsInner`): each curve is given the disc not
  containing the base point `∞`, and the relation "the curve `j` meets the open disc of `i`" is a
  strict partial order, so a nesting rank exists;
* a curve `j` of minimal rank then has the property that **no** intersection curve meets the open
  part of its inner disc.  Its inner disc is (the Riemann-sphere image of) a continuous map
  `s : 𝔻 → 𝔻` into the closed unit disc (`Work.Smooth.SphereJordan.innerDiscSection2`, which also
  shows that `s` maps the open unit disc into the open unit disc);
* `f := D.e ∘ s` is then the required innermost sub-disc: it is embedded, spans `curves j`, its
  interior misses `F` (a point of `F` in the interior of `D` lies on one of the curves, which would
  meet the open part of the inner disc of `j`), and no other intersection curve meets its interior.

Nothing outside `Submission/Work/Smooth/SphereJordan/` is modified.
-/

open Set Filter
open scoped Topology
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **The open inner piece of the two-disc decomposition of a plane curve in the closed unit disc
lies in the *open* unit disc.**

`T.inner ∞` is the disc of `T` that does not contain `∞`; for a curve whose trace lies in the closed
unit disc, that disc is contained in the closed unit disc (`innerDiscSection2`).  Since its open
part is *open* in the sphere, it cannot meet the unit circle: a point of the open part of norm
exactly `1` would have a whole neighbourhood of norm-`1`-nearby points, including points of norm
`> 1`, inside the closed unit disc.
-/
theorem innerDisc_norm_lt_one {γ : ℝ → ℂ} (hball : ∀ t : ℝ, ‖γ t‖ ≤ 1)
    (T : TwoDiscs (fun t : ℝ => (γ t : RiemannSphere))) {x : ℂ}
    (hx : (x : RiemannSphere) ∈ T.inSide infty) : ‖x‖ < 1 := by
  classical
  obtain ⟨s, hs⟩ := innerDiscSection2 hball T
  -- the inner disc is contained in the closed unit disc
  have hclosed : ∀ y : ℂ, (y : RiemannSphere) ∈ T.inSide infty → ‖y‖ ≤ 1 := by
    intro y hy
    obtain ⟨z, -, hzy⟩ := hy
    have h1 : (y : RiemannSphere) = (((s z : Disc) : ℂ) : RiemannSphere) :=
      hzy.symm.trans (hs z).symm
    have h2 : y = ((s z : Disc) : ℂ) := OnePoint.coe_injective h1
    rw [h2]
    have h3 : dist (s z) (0 : Disc) ≤ 1 := Metric.mem_closedBall.mp (s z).2
    simpa [Subtype.dist_eq, dist_eq_norm, sub_zero] using h3
  by_contra hcon
  push_neg at hcon
  have hnorm : ‖x‖ = 1 := le_antisymm (hclosed x hx) hcon
  -- the open part is open in the sphere, hence in the plane
  have hopen : IsOpen ((↑) ⁻¹' T.inSide infty : Set ℂ) :=
    (TwoDiscs.isOpen_inSide T infty).preimage OnePoint.continuous_coe
  have hmem : ((↑) ⁻¹' T.inSide infty : Set ℂ) ∈ 𝓝 x := hopen.mem_nhds hx
  obtain ⟨ε, hε, hball'⟩ := Metric.mem_nhds_iff.mp hmem
  -- a point of norm `> 1` in that neighbourhood
  set y : ℂ := ((1 + ε / 2 : ℝ) : ℂ) * x with hy
  have hymem : (y : RiemannSphere) ∈ T.inSide infty := by
    refine hball' ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : y - x = ((ε / 2 : ℝ) : ℂ) * x := by rw [hy]; push_cast; ring
    rw [hsub, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hnorm, mul_one]
    linarith
  have hynorm : ‖y‖ = 1 + ε / 2 := by
    rw [hy, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hnorm, mul_one]
  have := hclosed y hymem
  rw [hynorm] at this
  linarith

/-- **Pardon's first innermost step ("innermost in the surface")**, proved from the planar
Jordan–Schoenflies theorem. -/
theorem innermostCurveExists2 (h : PlaneHypothesis) (P : Work.CoreTopology.ParamTorus) :
    Work.Topology.Classical.InnermostCurveExists P := by
  classical
  intro D hcard
  -- the two-disc decomposition of each pulled-back intersection curve
  have hT : ∀ i : D.ι, TwoDiscs (pullbackSphereCurve D i) := fun i =>
    (planeTwoDiscs h (pullbackPlaneCurve_continuous D i) (pullbackPlaneCurve_periodic D i)
      (pullbackPlaneCurve_injOn D i)).some
  -- standard position: a nesting rank for the family of pulled-back curves
  obtain ⟨F, hF⟩ := familyDataOfTwoDiscsInner (isSimpleClosedCurve_pullbackSphereCurve D)
    (pullbackSphereCurve_pairwiseDisjoint D) hT infty
    (fun i => by rintro ⟨t, ht⟩; exact pullbackSphereCurve_ne_infty D i t ht)
  -- a curve of minimal rank
  have hne : (Finset.univ : Finset D.ι).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ]
    exact hcard
  obtain ⟨j, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset D.ι) F.rank hne
  have hminj : ∀ k : D.ι, F.rank j ≤ F.rank k := fun k => hmin k (Finset.mem_univ k)
  -- the inner disc of `j`, as a map into the model disc
  obtain ⟨s, hs⟩ := innerDiscSection2 (pullbackPlaneCurve_norm_le_one D j) (hT j)
  have hFj : ∀ z : Disc, F.e j z = (hT j).inner infty z :=
    fun z => congrArg (fun g : C(Disc, RiemannSphere) => g z) (hF j)
  have hsF : ∀ z : Disc, (((s z : Disc) : ℂ) : RiemannSphere) = F.e j z :=
    fun z => (hs z).trans (hFj z).symm
  -- the open part of that inner disc lies in the open unit disc
  have hstrict : ∀ z : Disc, ‖(z : ℂ)‖ < 1 → ‖((s z : Disc) : ℂ)‖ < 1 := by
    intro z hz
    refine innerDisc_norm_lt_one (pullbackPlaneCurve_norm_le_one D j) (hT j) ?_
    rw [hs z]
    exact ⟨z, hz, rfl⟩
  -- the innermost sub-disc, transported to `ℝ³`
  let f : C(Disc, R3) := D.e.comp s
  have hf : ∀ z : Disc, f z = D.e (s z) := fun _ => rfl
  -- a point of the interior of `f` on an intersection curve would force that curve to meet the
  -- open part of the inner disc of `j`, contradicting the minimality of the rank of `j`
  have key : ∀ (i : D.ι) (z : Disc), ‖(z : ℂ)‖ < 1 → f z ∈ Set.range (D.curves i).γ →
      F.rank i < F.rank j := by
    intro i z hz hmem
    obtain ⟨t, ht⟩ := hmem
    have h1 : s z = SliceDiscPullback D i t := by
      apply D.inj
      rw [SliceDiscPullback_spec]
      exact ht.symm
    have h2 : F.e j z = pullbackSphereCurve D i t := by
      rw [← hsF z, h1]
      exact pullbackSphereCurve_eq_coe D i t
    exact F.nested j i ⟨z, hz, ⟨t, h2.symm⟩⟩
  refine ⟨j, f, ?_, ?_, ?_, ?_, ?_⟩
  · -- the sub-disc is embedded
    intro a b hab
    have h1 : s a = s b := D.inj hab
    have h2 : (((s a : Disc) : ℂ) : RiemannSphere) = (((s b : Disc) : ℂ) : RiemannSphere) :=
      congrArg (fun z : Disc => ((z : ℂ) : RiemannSphere)) h1
    rw [hsF a, hsF b] at h2
    exact F.inj j h2
  · -- its boundary is the intersection curve `j`
    intro θ
    have hb : F.e j (Work.CoreTopology.circlePoint θ) = pullbackSphereCurve D j θ :=
      F.boundary j θ
    have h1 : (((s (Work.CoreTopology.circlePoint θ) : Disc) : ℂ) : RiemannSphere) =
        ((pullbackPlaneCurve D j θ : ℂ) : RiemannSphere) := by
      rw [hsF (Work.CoreTopology.circlePoint θ), hb, pullbackSphereCurve_eq_coe]
    have h2 : s (Work.CoreTopology.circlePoint θ) = SliceDiscPullback D j θ :=
      Subtype.ext (OnePoint.coe_injective h1)
    rw [hf, h2, SliceDiscPullback_spec]
  · -- its interior misses the surface
    intro z hz hcarrier
    have hcar : D.e (s z) ∈ P.carrier := hf z ▸ hcarrier
    obtain ⟨i, hi⟩ := D.covers (s z) (hstrict z hz) hcar
    exact absurd (key i z hz ((hf z).symm ▸ hi)) (not_lt.mpr (hminj i))
  · -- it lies in the original disc
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨s z, rfl⟩
  · -- no other intersection curve meets its interior
    intro i _hi
    rw [Set.disjoint_left]
    rintro x hx1 hx2
    obtain ⟨t, ht⟩ := hx1
    obtain ⟨z, hz, hzf⟩ := hx2
    exact absurd (key i z hz ⟨t, ht.trans hzf.symm⟩) (not_lt.mpr (hminj i))

end

end Work.Smooth.SphereJordan
