import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.outerArcs
import Submission.Work.Smooth.SphereJordan.isOpen_slitAnnulus
import Submission.Work.Smooth.SphereJordan.DiscSpansAPI
import Submission.Work.Smooth.SphereJordan.disc_spans_schoenflies_clean
import Submission.Work.Smooth.Jordan.All

/-!
# `Work.Smooth.SphereJordan.exists_half_spans`

The two halves of the slit annulus of a two-disc datum are discs.

Let `c : ℝ → ℂ ∪ {∞}` be a simple closed curve on the Riemann sphere, `T : TwoDiscs c` a two-disc
datum for it, and `hball : ∀ z, InOpenDisc (T.e z)` — the hypothesis that the *inner* disc
`range T.e` lies in the open unit disc, so that the unit circle `Ω` and `range T.e` bound an
annulus `A = {‖z‖ < 1} ∖ range T.e`.  Fix two distinct boundary directions `w₁ ≠ w₂` whose radial
arcs in the outer disc leave the unit disc (`hne₁`, `hne₂`), and let `C₁`, `C₂` be the two
crosscuts of `A` so obtained.

The slit annulus

`slitAnnulus T w₁ w₂ = A ∖ (C₁ ∪ C₂)`

is then the disjoint union of exactly two non-empty open preconnected sets `P₁`, `P₂` (the two
halves of the annulus cut along the two crosscuts), and the closure of each is the image of an
injective continuous map of the model disc — i.e. each is a *disc*, by Jordan–Schoenflies.

This is the "two cuts" step of the classical proof of the planar annulus theorem: the region
between a Jordan curve inside the unit disc and the unit circle is an annulus, and cutting an
annulus along two disjoint crosscuts joining its two boundary components produces two discs.

## The route

Everything is carried out in the plane `ℂ`, in the chart `ℂ ⊆ ℂ ∪ {∞}`:

* the curve `c` is a plane curve `γc` because its trace lies in the open unit disc;
* the inner disc `range T.e` is the image of a plane disc map `ep : 𝔻 → ℂ`;
* the two cuts are the plane images of the radial arcs of the outer disc `T.e'`.

The two halves are described by the two four-arc Jordan curves

`J₁ = C₁ ∪ β₁ ∪ C₂ ∪ α₁`,   `J₂ = C₁ ∪ β₂ ∪ C₂ ∪ α₂`

where `α₁, α₂` are the two arcs of the unit circle `Ω` between the outer feet of the cuts and
`β₁, β₂` the two arcs of the inner curve `Γ = c.trace` between their inner feet.  Their bounded
sides, supplied by `h : PlaneHypothesis` (Jordan–Schoenflies for plane curves), are the two halves.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set Metric
open LeanEval.KnotTheory.PardonDistortion

theorem e_ne_infty {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) (z : Disc) : T.e z ≠ infty := by
  obtain ⟨u, -, hu⟩ := hball z
  rw [← hu]
  exact OnePoint.coe_ne_infty u


theorem c_mem_openDisc {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) (t : ℝ) : InOpenDisc (c t) := by
  have h1 : c t ∈ Set.range T.e := T.range_subset_left ⟨t, rfl⟩
  obtain ⟨z, hz⟩ := h1
  rw [← hz]
  exact hball z

theorem arcPt_one_mem_openDisc {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) (w : Metric.sphere (0 : ℂ) 1) :
    InOpenDisc (T.e' (arcPt w 1)) := by
  have hnorm : ‖((arcPt w 1 : Disc) : ℂ)‖ = 1 := by
    rw [arcPt_coe, show max 0 (min (1 : ℝ) 1) = 1 from by norm_num, Complex.ofReal_one,
      one_mul]
    simpa [dist_eq_norm] using w.2
  obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq (arcPt w 1) hnorm
  rw [← hθ, T.boundary' θ]
  exact c_mem_openDisc T hball θ

/-- **The inner disc as a plane disc map**: `T.e` read in the chart `ℂ ⊆ ℂ ∪ {∞}`. -/
def ep {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) : C(Disc, ℂ) :=
  ⟨fun z => Classical.choose (OnePoint.ne_infty_iff_exists.mp (e_ne_infty T hball z)),
    continuous_iff_continuousAt.mpr (fun z => by
      show Filter.Tendsto (fun z : Disc =>
        Classical.choose (OnePoint.ne_infty_iff_exists.mp (e_ne_infty T hball z))) (nhds z)
        (nhds (Classical.choose (OnePoint.ne_infty_iff_exists.mp (e_ne_infty T hball z))))
      rw [← OnePoint.comap_coe_nhds (Classical.choose
        (OnePoint.ne_infty_iff_exists.mp (e_ne_infty T hball z)))]
      rw [Filter.tendsto_comap_iff]
      have hcoe : (OnePoint.some ∘ fun z : Disc =>
          Classical.choose (OnePoint.ne_infty_iff_exists.mp (e_ne_infty T hball z))) = ⇑T.e :=
        funext (fun z => Classical.choose_spec
          (OnePoint.ne_infty_iff_exists.mp (e_ne_infty T hball z)))
      rw [hcoe, Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp (e_ne_infty T hball z))]
      exact T.e.continuous.continuousAt)⟩

theorem ep_coe {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) (z : Disc) :
    ((ep T hball z : ℂ) : RiemannSphere) = T.e z :=
  Classical.choose_spec (OnePoint.ne_infty_iff_exists.mp (e_ne_infty T hball z))

theorem ep_injective {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) : Function.Injective (ep T hball) := by
  intro a b hab
  apply T.inj
  have hab' : (ep T hball a : ℂ) = ep T hball b := hab
  rw [← ep_coe T hball a, ← ep_coe T hball b, hab']

/-! ## The plane picture of the two-disc datum

Throughout, `hball` puts the inner disc `range T.e` in the open unit disc, so that the unit circle
`Ω` and the inner curve `Γ = c.trace` bound an annulus in the plane.  The two crosscuts are the
images of the radial arcs of the outer disc `T.e'` through the two directions `w₁ ≠ w₂`. -/

/-- A point of the open unit disc of the Riemann sphere, as a complex number. -/
def toPlane (x : RiemannSphere) (hx : InOpenDisc x) : ℂ := Classical.choose hx

theorem toPlane_mem (x : RiemannSphere) (hx : InOpenDisc x) : ‖toPlane x hx‖ < 1 :=
  (Classical.choose_spec hx).1

theorem toPlane_coe (x : RiemannSphere) (hx : InOpenDisc x) :
    ((toPlane x hx : ℂ) : RiemannSphere) = x :=
  (Classical.choose_spec hx).2

/-- The plane avatar of the inner curve `c`: the inner disc of a two-disc datum lies in the open
unit disc, hence in the plane. -/
def cpl {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) (t : ℝ) : ℂ :=
  toPlane (c t) (c_mem_openDisc T hball t)

theorem cpl_coe {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) (t : ℝ) :
    ((cpl T hball t : ℂ) : RiemannSphere) = c t :=
  toPlane_coe _ _

theorem cpl_norm_lt_one {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) (t : ℝ) : ‖cpl T hball t‖ < 1 :=
  toPlane_mem _ _

/-- The two-disc datum of the unit circle is not used; what is used is that the *inner* boundary of
the annulus is the trace of the plane curve `cpl`. -/
theorem cpl_eq_ep_of_circlePoint {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) (θ : ℝ) :
    cpl T hball θ = ep T hball (circlePoint θ) := by
  apply OnePoint.coe_injective
  rw [cpl_coe, ep_coe, T.boundary]

/-- **The outer foot of a cut**: the point of the unit circle at which the radial arc of `T.e'`
through `w` last leaves the open unit disc. -/
def feets {c : ℝ → RiemannSphere} (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w : Metric.sphere (0 : ℂ) 1) (hne : (arcOutSet T w).Nonempty) : ℂ :=
  Classical.choose (crosscutTime_norm_eq_one T hne (arcPt_one_mem_openDisc T hball w))

theorem feets_norm {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w : Metric.sphere (0 : ℂ) 1) (hne : (arcOutSet T w).Nonempty) :
    ‖feets T hball w hne‖ = 1 :=
  (Classical.choose_spec
    (crosscutTime_norm_eq_one T hne (arcPt_one_mem_openDisc T hball w))).1

theorem feets_coe {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w : Metric.sphere (0 : ℂ) 1) (hne : (arcOutSet T w).Nonempty) :
    ((feets T hball w hne : ℂ) : RiemannSphere) =
      T.e' (arcPt w (crosscutTime T w)) :=
  (Classical.choose_spec
    (crosscutTime_norm_eq_one T hne (arcPt_one_mem_openDisc T hball w))).2

/-- **The cut through `w`**, as a set of points of the plane: the image of the radial arc of the
outer disc beyond the last exit from the open unit disc. -/
def plCut {c : ℝ → RiemannSphere} (T : TwoDiscs c) (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w : Metric.sphere (0 : ℂ) 1) : Set ℂ :=
  {z : ℂ | ((z : ℂ) : RiemannSphere) ∈ cutSet T w}

theorem plCut_mem_iff {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) (w : Metric.sphere (0 : ℂ) 1) (z : ℂ) :
    z ∈ plCut T hball w ↔ ((z : ℂ) : RiemannSphere) ∈ cutSet T w := Iff.rfl

/-- Every point of a cut lies in the open unit disc, hence is the image of a unique complex
number, and that complex number is in `plCut`. -/
theorem plCut_subset_ball {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z))
    (w : Metric.sphere (0 : ℂ) 1) (hne : (arcOutSet T w).Nonempty) :
    plCut T hball w ⊆ Metric.ball 0 1 := by
  intro z hz
  obtain ⟨⟨u, hu, hu'⟩, -⟩ := cutSet_subset_openAnnulus T hne hz
  have h1 : ((z : ℂ) : RiemannSphere) = ((u : ℂ) : RiemannSphere) := by rw [hu']
  have h2 : (z : ℂ) = u := OnePoint.coe_injective h1
  rw [h2]
  simpa [Metric.mem_ball, dist_eq_norm] using hu



/-! ## From the plane statement to the sphere statement

If the slit annulus is split into two half-discs in the plane, then the corresponding subsets of the
Riemann sphere (the images under the coercion `ℂ → ℂ ∪ {∞}`) satisfy the sphere-level statement:
the coercion is an open embedding, its image of a bounded closed set is closed, and it preserves
preconnectedness. -/

/-- The plane model of the slit annulus is the preimage of the slit annulus under the coercion. -/
theorem preimage_slitAnnulus {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hball : ∀ z : Disc, InOpenDisc (T.e z)) (w₁ w₂ : Metric.sphere (0 : ℂ) 1) :
    {z : ℂ | ‖z‖ < 1 ∧ z ∉ Set.range (ep T hball) ∧
        ((z : ℂ) : RiemannSphere) ∈ openAnnulus T ∧
        ((z : ℂ) : RiemannSphere) ∉ cutSet T w₁ ∧
        ((z : ℂ) : RiemannSphere) ∉ cutSet T w₂}
      = ((↑) : ℂ → RiemannSphere) ⁻¹' slitAnnulus T w₁ w₂ := by
  ext z
  constructor
  · rintro ⟨-, hz, hA, h1, h2⟩
    exact ⟨hA, by simp only [Set.mem_union, not_or]; exact ⟨h1, h2⟩⟩
  · rintro ⟨hA, hcut⟩
    have h1 : ((z : ℂ) : RiemannSphere) ∉ cutSet T w₁ := fun h => hcut (Or.inl h)
    have h2 : ((z : ℂ) : RiemannSphere) ∉ cutSet T w₂ := fun h => hcut (Or.inr h)
    have hmem : ((z : ℂ) : RiemannSphere) ∈ openAnnulus T := hA
    obtain ⟨hz1, hz2⟩ := hmem
    refine ⟨?_, ?_, hA, h1, h2⟩
    · obtain ⟨u, hu, hu'⟩ := hz1
      have : z = u := by
        apply OnePoint.coe_injective
        rw [hu']
      rw [this]; exact hu
    · intro hcon
      obtain ⟨z', hz'⟩ := hcon
      exact hz2 ⟨z', by rw [← hz']; exact (ep_coe T hball z').symm⟩

end

end Work.Smooth.SphereJordan
