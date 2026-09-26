import Submission.Work.InnermostDisk.Defs
import Submission.Work.InnermostDisk.isEssential_iff_of_homotopic
import Submission.Work.InnermostDisk.not_isEssential_iff_homotopic_const
import Submission.Work.InnermostDisk.not_isEssential_of_boundsDiscInSurface
import Submission.Work.InnermostDisk.boundsDiscInSurface_of_not_isEssential
import Submission.Work.InnermostDisk.Reduction
import Submission.Work.InnermostDisk.not_isEssential_of_section
import Submission.Work.InnermostDisk.isEmbeddedSphere_sphere

/-!
# Basic API for the winding vector, homotopy and discs

The small consequences of the bridge lemmas `isEssential_iff_hasWinding`,
`homotopic_iff_homotopicClosed`, `not_isEssential_iff_homotopic_const`,
`not_isEssential_of_boundsDiscInSurface` which the main theorems are stated with:

* `not_isEssential_iff_winding_eq_zero` — inessentiality is the statement that *every* lift has
  winding vector `(0,0)` (the lift-independent form of the definition);
* `not_isEssential_iff_of_homotopic` — inessentiality is a homotopy invariant;
* `isEssential_of_not_boundsDiscInSurface` — an essential loop of `F` never bounds a disc in
  `F` (Pardon's "essential = non-trivial isotopy class"), the form in which the criterion is
  applied to decide essentiality;
* `innermostDiscInput_sphere_of_input` — the sphere-conditioned first input gives the input at
  every round sphere.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section

/-- Inessentiality is the statement that every lift has winding vector `(0,0)`. -/
theorem not_isEssential_iff_winding_eq_zero {P : ParamTorus} (γ : ClosedCurve P) :
    ¬ IsEssential P γ ↔ ∀ L : LiftOf P γ, L.winding = (0, 0) := by
  rw [IsEssential]
  constructor
  · intro h L
    by_contra hL
    exact h ⟨L, hL⟩
  · rintro h ⟨L, hL⟩
    exact hL (h L)

/-- Inessentiality is a homotopy invariant. -/
theorem not_isEssential_iff_of_homotopic {P : ParamTorus} {α β : ClosedCurve P}
    (h : Homotopic P α β) : ¬ IsEssential P α ↔ ¬ IsEssential P β :=
  not_congr (isEssential_iff_of_homotopic h)

/-- A loop homotopic in `F` to an inessential loop is inessential. -/
theorem not_isEssential_of_homotopic {P : ParamTorus} {α β : ClosedCurve P}
    (h : Homotopic P α β) (hβ : ¬ IsEssential P β) : ¬ IsEssential P α :=
  (not_isEssential_iff_of_homotopic h).mpr hβ

theorem boundsDiscInSurface_iff_not_isEssential {P : ParamTorus} (α : ClosedCurve P) :
    BoundsDiscInSurface P α ↔ ¬ IsEssential P α :=
  ⟨fun h => not_isEssential_of_boundsDiscInSurface P h,
    fun h => boundsDiscInSurface_of_not_isEssential P h⟩

/-- **An essential loop of `F` does not bound a disc in `F`.**  This is the contrapositive of
`not_isEssential_of_boundsDiscInSurface`, and the direction in which the criterion
"inessential = bounds a disc in the surface" is used to detect essentiality. -/
theorem isEssential_of_not_boundsDiscInSurface {P : ParamTorus} {α : ClosedCurve P}
    (h : IsEssential P α) : ¬ BoundsDiscInSurface P α :=
  fun hb => not_isEssential_of_boundsDiscInSurface P hb h

/-- The meridian circle of the standard torus is essential, hence does *not* bound a disc in the
torus. -/
theorem not_boundsDiscInSurface_meridianCurve (θ : ℝ) :
    ¬ BoundsDiscInSurface standard (meridianCurve standard θ) :=
  isEssential_of_not_boundsDiscInSurface (meridianCurve_essential standard θ)

/-- The longitude circle of the standard torus is essential, hence does *not* bound a disc in the
torus. -/
theorem not_boundsDiscInSurface_longitudeCurve (φ : ℝ) :
    ¬ BoundsDiscInSurface standard (longitudeCurve standard φ) :=
  isEssential_of_not_boundsDiscInSurface (longitudeCurve_essential standard φ)

/-- **Consequence of Pardon's Lemma in the form used by the sphere-family argument**: every
curve of `F` inside a sphere meeting `β` in fewer than `I(F, β)` points is null-homotopic in `F`.

This is Pardon's conclusion ("every curve in `S ∩ F` is inessential in `F`") transported through
`not_isEssential_iff_homotopic_const`. -/
theorem homotopic_const_of_mem_sphere_of_inputs {P : ParamTorus} {β : ClosedCurve P} {S : Set R3}
    (hIn : InnermostDiscInput P S) (hCl : CleansDiscs P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) {γ : ClosedCurve P}
    (hγ : ∀ t : ℝ, γ.γ t ∈ S) :
    ∃ (x : R3) (hx : x ∈ P.carrier), Homotopic P γ (constCurve P x hx) :=
  (not_isEssential_iff_homotopic_const P γ).mp
    (mustbeinessential_of_inputs P β S hIn hCl hSβ γ hγ)

/-- The same, in the form needed to see that a component of `S ∩ F` bounds a disc *in `F`*: every
curve of `F` inside `S` bounds a disc in the surface. -/
theorem boundsDiscInSurface_of_mem_sphere_of_inputs {P : ParamTorus} {β : ClosedCurve P}
    {S : Set R3} (hIn : InnermostDiscInput P S) (hCl : CleansDiscs P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) {γ : ClosedCurve P}
    (hγ : ∀ t : ℝ, γ.γ t ∈ S) : BoundsDiscInSurface P γ :=
  boundsDiscInSurface_of_not_isEssential P
    (mustbeinessential_of_inputs P β S hIn hCl hSβ γ hγ)

/-- The sphere-conditioned first innermost input holds at every round sphere of positive radius. -/
theorem innermostDiscInput_sphere_of_sphereInput {P : ParamTorus} (c : R3) {r : ℝ} (hr : 0 < r)
    (h : SphereInnermostInput P) : InnermostDiscInput P (Metric.sphere c r) :=
  InnermostDiscInput.of_sphere h (isEmbeddedSphere_sphere c hr)

end

end Work.InnermostDisk
