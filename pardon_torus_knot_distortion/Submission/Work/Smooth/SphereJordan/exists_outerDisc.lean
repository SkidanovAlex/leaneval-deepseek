import Mathlib
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.Smooth.Schoenflies.Unconditional
import Submission.Work.Smooth.SphereJordan.outerDiscAux
import Submission.Work.Smooth.SphereJordan.range_coe_eq_inner

/-!
# The disc spanning the outer side of an embedded plane disc

`exists_outerDisc F` says that an injective continuous map `F : 𝔻 → ℂ` of the closed unit disc
extends to a continuous injection `e : 𝔻 → ℂ ∪ {∞}` of the Riemann sphere whose image is the
*outer* region bounded by the Jordan curve `F (S¹)`: the closure of the unbounded side of that
curve together with `∞`.  Concretely `e` agrees with `F` on the boundary circle, takes the value
`∞` at an interior point `w`, and

`range e = {∞} ∪ (range F)ᶜ ∪ range (F ∘ circlePoint)`,

the finite part being read in the plane `ℂ ⊆ ℂ ∪ {∞}`.

The curve `c = F ∘ circlePoint` is a simple closed plane curve, and the planar
Jordan–Schoenflies theorem supplies two complementary discs spanning it in `ℂ ∪ {∞}`
(`Work.Smooth.SphereJordan.planeTwoDiscs`).  The disc that does *not* contain `∞` spans the
*bounded* side: after deleting `∞` it is an injective disc map of the plane with the same boundary
as `F`, so it has the same range as `F` by uniqueness of the spanning disc
(`Work.Smooth.SphereJordan.range_eq_closure_of_boundary_eq`).  The other disc is therefore the
complement of the first one, together with the curve — which is exactly the outer region.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

variable {c : ℝ → RiemannSphere}

/-- **The two pieces of a two-disc datum are complementary.**  If `x₀` lies off the curve `c`,
then the disc containing `x₀` is the complement of the other one together with the curve; the
statement is the pure set theory of `cover` and `meet`. -/
theorem range_outer_eq (T : TwoDiscs c) (x₀ : RiemannSphere) :
    Set.range (T.outer x₀) = (Set.range (T.inner x₀))ᶜ ∪ Set.range c := by
  have key : ∀ A B K : Set RiemannSphere, A ∪ B = Set.univ → A ∩ B = K →
      B = Aᶜ ∪ K := by
    intro A B K huv hAB
    apply Set.Subset.antisymm
    · intro x hx
      rcases em (x ∈ A) with hxA | hxA
      · exact Or.inr (hAB ▸ ⟨hxA, hx⟩)
      · exact Or.inl hxA
    · rintro x (hx | hx)
      · rcases Set.eq_univ_iff_forall.mp huv x with hA | hB
        · exact absurd hA hx
        · exact hB
      · rw [← hAB] at hx
        exact hx.2
  by_cases h : x₀ ∈ Set.range T.e
  · rw [T.outer_eq_of_mem x₀ h, T.inner_eq_of_mem x₀ h]
    exact key (Set.range T.e') (Set.range T.e) (Set.range c)
      (by rw [Set.union_comm, T.cover]) (by rw [Set.inter_comm, T.meet])
  · rw [T.outer_eq_of_notMem x₀ h, T.inner_eq_of_notMem x₀ h]
    exact key (Set.range T.e) (Set.range T.e') (Set.range c) T.cover T.meet

/-- The image of the boundary circle of the model disc under a disc map, as the coercion of the
image of the boundary curve. -/
theorem range_circlePoint_coe (g : C(Disc, ℂ)) :
    Set.range (fun t : ℝ => ((g (circlePoint t) : ℂ) : RiemannSphere)) =
      (fun x : ℂ => (x : RiemannSphere)) '' Set.range (fun θ : ℝ => g (circlePoint θ)) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨g (circlePoint t), ⟨t, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨θ, rfl⟩, rfl⟩
    exact ⟨θ, rfl⟩

theorem exists_outerDisc (F : C(Metric.closedBall (0 : ℂ) 1, ℂ)) (hF : Function.Injective F) :
    ∃ (e : C(Metric.closedBall (0 : ℂ) 1, OnePoint ℂ)) (w : Metric.closedBall (0 : ℂ) 1),
      Function.Injective e ∧
      (∀ θ : ℝ, e (Work.Smooth.Jordan.circlePoint θ) =
        ((F (Work.Smooth.Jordan.circlePoint θ) : ℂ) : OnePoint ℂ)) ∧
      ‖(w : ℂ)‖ < 1 ∧ e w = OnePoint.infty ∧
      Set.range e = ({OnePoint.infty} : Set (OnePoint ℂ)) ∪
        ((fun x : ℂ => (x : OnePoint ℂ)) ''
          (Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => (F z : ℂ)))ᶜ) ∪
        ((fun x : ℂ => (x : OnePoint ℂ)) ''
          Set.range (fun θ : ℝ => F (Work.Smooth.Jordan.circlePoint θ))) := by
  have hcont : Continuous (fun θ : ℝ => F (Work.Smooth.Jordan.circlePoint θ)) :=
    F.continuous.comp continuous_circlePoint
  have hper : Function.Periodic (fun θ : ℝ => F (Work.Smooth.Jordan.circlePoint θ))
      (2 * Real.pi) :=
    fun t => congrArg F (Work.Smooth.SphereJordan.circlePoint_add_two_pi t)
  have hinj : Set.InjOn (fun θ : ℝ => F (Work.Smooth.Jordan.circlePoint θ))
      (Set.Ico 0 (2 * Real.pi)) := fun a ha b hb hab =>
    Work.Smooth.SphereJordan.injOn_circlePoint ha hb (hF hab)
  obtain ⟨T⟩ : Nonempty (TwoDiscs
      (fun t : ℝ => ((F (Work.Smooth.Jordan.circlePoint t) : ℂ) : OnePoint ℂ))) :=
    planeTwoDiscs Work.Smooth.Schoenflies.planeHypothesis hcont hper hinj
  have hc : OnePoint.infty ∉ Set.range
      (fun t : ℝ => ((F (Work.Smooth.Jordan.circlePoint t) : ℂ) : OnePoint ℂ)) := by
    rintro ⟨t, ht⟩
    exact OnePoint.coe_ne_infty (F (Work.Smooth.Jordan.circlePoint t)) ht
  have hboundary : ∀ θ : ℝ, T.outer OnePoint.infty (Work.Smooth.Jordan.circlePoint θ) =
      ((F (Work.Smooth.Jordan.circlePoint θ) : ℂ) : OnePoint ℂ) :=
    fun θ => T.outer_boundary OnePoint.infty θ
  obtain ⟨w, hw, hwe⟩ := exists_interior_preimage_infty T hc
  refine ⟨T.outer OnePoint.infty, w, T.outer_injective OnePoint.infty, hboundary, hw, hwe, ?_⟩
  have hrange : Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => ((F z : ℂ) : OnePoint ℂ)) =
      Set.range (T.inner OnePoint.infty) :=
    range_coe_eq_inner T hc hF (fun θ => rfl)
  have houter : Set.range (T.outer OnePoint.infty) =
      (Set.range (T.inner OnePoint.infty))ᶜ ∪
        Set.range (fun t : ℝ => ((F (Work.Smooth.Jordan.circlePoint t) : ℂ) : OnePoint ℂ)) :=
    range_outer_eq T OnePoint.infty
  rw [houter, ← hrange, image_coe_range F, compl_image_coe_eq (Set.range F),
    range_circlePoint_coe F]

end

end Work.Smooth.SphereJordan
