import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.annulusTheoremOfPlaneHypothesis

/-!
# The planar annulus theorem (strict form), from the plain annulus form of Schoenflies

`Work.Smooth.SphereJordan.annulus_of_planeHypothesis_strict`: for a simple closed plane curve `γ`
whose trace lies in the open unit disc and a Schoenflies datum `S` for it, there is a
homeomorphism `Θ` of the closed unit disc fixing the boundary circle pointwise, carrying the
bounded side `S.V` onto the open half-disc `{‖z‖ < 1/2}` and its closure onto the closed
half-disc `{‖z‖ ≤ 1/2}`.

The mathematical content is the two-dimensional **annulus theorem**: the region between a Jordan
curve inside the unit disc and the boundary circle of the disc is a standard annulus.

The auxiliary reduction `annulusStrict_of_plain` applies the *plain* (set-level) annulus form
`Work.Smooth.SphereJordan.PlainAnnulusSchoenflies` to the embedding `S.e` of the Schoenflies disc,
regarded as a map into the closed unit disc (legitimate because `hball` puts `closure S.V` inside
the *open* disc, hence inside the closed disc).  The plain form then gives a homeomorphism `Θ` of
`𝔻` fixing `∂𝔻` pointwise with `(∃ z, S.e z = x) ↔ ‖Θ x‖ ≤ 1/2` and
`‖z‖ < 1 ↔ ‖Θ (S.e z)‖ < 1/2`; translating along `Set.range S.e = closure S.V` and
`S.e '' {‖z‖ < 1} = S.V` (Jordan–Schoenflies) gives the two membership clauses.  The final theorem
is then obtained from the planar annulus theorem `annulusTheoremOfPlaneHypothesis`.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **The strict (open-disc) clause of the plain annulus form, for the Schoenflies embedding.**

Applying the plain annulus form of Schoenflies to the embedded disc `S.e` of a plane curve `γ`
whose trace lies in the open unit disc yields a homeomorphism `Θ` of `𝔻` fixing `∂𝔻` pointwise and
carrying the *open* disc bounded by `γ` onto the open half-disc and its closure onto the closed
half-disc. -/
theorem annulusStrict_of_plain (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (hP : Work.Smooth.SphereJordan.PlainAnnulusSchoenflies) :
    ∃ Θ : Work.Smooth.SphereJordan.Disc ≃ₜ Work.Smooth.SphereJordan.Disc,
      (∀ θ : ℝ, Θ (Work.Smooth.SphereJordan.circlePoint θ) =
        Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ x : Work.Smooth.SphereJordan.Disc,
        (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ S.V) ↔
        ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 / 2) ∧
      (∀ x : Work.Smooth.SphereJordan.Disc,
        (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ closure S.V) ↔
        ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) := by
  -- the image of the Schoenflies embedding lies in the closed unit disc
  have hVclosed : S.V ⊆ Metric.closedBall (0 : ℂ) 1 := fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Work.Smooth.SphereJordan.planeSeparation_V_subset_closedBall
      S.toPlaneSeparation hball x hx
  have hrange : closure S.V ⊆ Metric.closedBall (0 : ℂ) 1 :=
    closure_minimal hVclosed Metric.isClosed_closedBall
  have hmem1 : ∀ z : Work.Smooth.SphereJordan.Disc, S.e z ∈ closure S.V := fun z => by
    rw [← S.range_e]; exact ⟨z, rfl⟩
  have hbdd : ∀ z : Work.Smooth.SphereJordan.Disc,
      S.e z ∈ Metric.closedBall (0 : ℂ) 1 := fun z => hrange (hmem1 z)
  -- the Schoenflies embedding, as a map into the closed unit disc
  let f : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.Disc) :=
    ⟨fun z => ⟨S.e z, hbdd z⟩, Continuous.subtype_mk S.e.continuous hbdd⟩
  have hfval : ∀ z : Work.Smooth.SphereJordan.Disc, ((f z : Work.Smooth.SphereJordan.Disc) : ℂ)
      = S.e z := fun z => rfl
  have hfinj : Function.Injective f := fun a b hab =>
    S.inj (by rw [← hfval a, ← hfval b, congrArg Subtype.val hab])
  have hfbd : ∀ θ : ℝ,
      ‖((f (Work.Smooth.SphereJordan.circlePoint θ) : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 := by
    intro θ
    rw [hfval, S.boundary θ]
    exact hball θ
  obtain ⟨Θ, hfix, hmem, hopen⟩ := hP f hfinj hfbd
  -- `x` is in the closed disc bounded by `γ` iff it is in the range of `f`
  have hrange_f : ∀ x : Work.Smooth.SphereJordan.Disc,
      (∃ z : Work.Smooth.SphereJordan.Disc, f z = x) ↔
        (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ closure S.V) := by
    intro x
    constructor
    · rintro ⟨z, rfl⟩
      rw [hfval]
      exact hmem1 z
    · intro hx
      have hx' : ((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ Set.range S.e := by
        rwa [S.range_e]
      obtain ⟨z, hz⟩ := hx'
      exact ⟨z, Subtype.ext hz⟩
  refine ⟨Θ, hfix, ?_, ?_⟩
  · -- the open disc bounded by `γ` is carried onto the open half-disc
    intro x
    constructor
    · intro hxV
      have hxmem : ((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈
          S.e '' {z : Work.Smooth.SphereJordan.Disc |
            ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1} := by
        rw [Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
        exact hxV
      obtain ⟨z, hz1, hz2⟩ := hxmem
      have hfzx : f z = x := Subtype.ext (by rw [hfval]; exact hz2)
      rw [← hfzx]
      exact (hopen z).mp hz1
    · intro hxlt
      have hxle : ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2 := le_of_lt hxlt
      obtain ⟨z, hz⟩ := (hmem x).mpr hxle
      have hzlt : ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 := by
        have := (hopen z).mpr (by rw [hz]; exact hxlt)
        exact this
      have hxS : ((x : Work.Smooth.SphereJordan.Disc) : ℂ) = S.e z := by
        rw [← hfval z, hz]
      rw [hxS]
      rw [← Work.Smooth.Jordan.plane_schoenflies_openDisc_eq S]
      exact ⟨z, hzlt, rfl⟩
  · -- the closed disc is carried onto the closed half-disc
    intro x
    rw [← hrange_f x]
    exact hmem x

/-- **The planar annulus theorem (strict form).**

For a simple closed plane curve `γ` whose trace lies in the open unit disc and a planar
Schoenflies datum `S` for `γ`, there is a homeomorphism `Θ` of the closed unit disc which fixes the
boundary circle pointwise, carries the bounded side `S.V` onto the open half-disc
`{‖z‖ < 1/2}` and its closure onto the closed half-disc `{‖z‖ ≤ 1/2}`.

The content is the two-dimensional annulus theorem (the region between `γ` and the boundary circle
is a standard annulus).  It is proved in the sibling module
`Submission.Work.Smooth.SphereJordan.annulusTheoremOfPlaneHypothesis` by the classical "two cuts"
construction, and is recorded here under the name fixed by the caller.  The auxiliary lemma
`annulusStrict_of_plain` below records the (independent) reduction of the statement from the plain
set-level annulus form `PlainAnnulusSchoenflies`. -/
theorem annulus_of_planeHypothesis_strict (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ Θ : Work.Smooth.SphereJordan.Disc ≃ₜ Work.Smooth.SphereJordan.Disc,
      (∀ θ : ℝ, Θ (Work.Smooth.SphereJordan.circlePoint θ) = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ x : Work.Smooth.SphereJordan.Disc,
        (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ S.V) ↔
        ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ < 1 / 2) ∧
      (∀ x : Work.Smooth.SphereJordan.Disc,
        (((x : Work.Smooth.SphereJordan.Disc) : ℂ) ∈ closure S.V) ↔
        ‖((Θ x : Work.Smooth.SphereJordan.Disc) : ℂ)‖ ≤ 1 / 2) :=
  Work.Smooth.SphereJordan.annulusTheoremOfPlaneHypothesis h hs hball S

end

end Work.Smooth.SphereJordan
