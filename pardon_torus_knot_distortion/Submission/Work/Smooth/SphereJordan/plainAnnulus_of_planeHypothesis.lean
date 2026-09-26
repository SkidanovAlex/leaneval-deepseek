import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.BoundedSide
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.injOn_circlePoint
import Submission.Work.Smooth.SphereJordan.no_retraction_disc
import Submission.Work.Smooth.SphereJordan.discEmbedding_surjective
import Submission.Work.Smooth.SphereJordan.disc_spans_schoenflies_clean
import Submission.Work.Smooth.SphereJordan.annulus_of_planeHypothesis_strict
import Submission.Work.Smooth.Jordan.All

/-!
# The plain (set-level) annulus form of Schoenflies in the plane, from the planar theorem

This module proves

`Work.Smooth.SphereJordan.plainAnnulus_of_planeHypothesis`:
from the planar Jordan–Schoenflies theorem (`PlaneHypothesis`) the **plain annulus form of
Schoenflies** (`PlainAnnulusSchoenflies`) follows: an embedding `h : 𝔻 ↪ 𝔻` whose boundary circle
lies in the open unit disc can be "straightened" — there is a homeomorphism `Θ` of the closed unit
disc fixing the boundary circle pointwise and carrying `h(𝔻)` onto the closed disc of radius
`1/2` (equivalently `Θ ∘ h` reparametrises the inner disc by the half-disc).

The proof uses three ingredients, each proved in its own module of this directory:

* `discEmbedding_surjective` / `no_retraction_disc` — a continuous injective self-map of the closed
  disc fixing the boundary circle pointwise and mapping the open disc into itself is surjective
  (the "Brouwer degree one" input, obtained from the non-null-homotopy of the standard loop in the
  punctured plane via Mathlib's covering space theory);
* `disc_spans_schoenflies_clean` — the image of such a map is exactly the closure of the bounded
  side of the simple closed plane curve it traces on the boundary (the planar Schoenflies theorem
  applied to that curve), so in particular `h(𝔻) = closure V` and `h(int 𝔻) = V`;
* `annulus_of_planeHypothesis_strict` — the planar annulus theorem: for a Jordan curve `γ` whose
  trace lies in the open unit disc and whose bounded side is `V`, there is a homeomorphism of `𝔻`
  fixing the boundary circle pointwise and carrying `V` onto the open half-disc and `closure V`
  onto the closed half-disc ("the region between `γ` and the boundary circle is a standard
  annulus", with prescribed behaviour on both boundary circles).
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.SphereJordan

noncomputable section

namespace PlainAnnulusAux

/-- The standard parametrisation `θ ↦ e^{iθ}` of the boundary circle is continuous. -/
theorem continuous_circlePoint : Continuous (circlePoint : ℝ → Disc) := by
  apply Continuous.subtype_mk
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

/-- The standard parametrisation `θ ↦ e^{iθ}` of the boundary circle is `2π`-periodic. -/
theorem circlePoint_add_two_pi (θ : ℝ) : circlePoint (θ + 2 * Real.pi) = circlePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  rw [show (((θ + 2 * Real.pi : ℝ)) : ℂ) * Complex.I =
      (θ : ℂ) * Complex.I + (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

end PlainAnnulusAux

/-- **The plain annulus form of the Schoenflies theorem, from the planar Jordan–Schoenflies
theorem.**

Let `h : 𝔻 → 𝔻` be a continuous injection whose boundary circle `θ ↦ h (e^{iθ})` lies in the open
unit disc.  Then there is a homeomorphism `Θ` of the closed unit disc which fixes the boundary
circle pointwise, carries `h(𝔻)` onto the closed half-disc `{‖z‖ ≤ 1/2}` and carries `h(int 𝔻)`
onto its interior.

The two ingredients are the planar Schoenflies theorem (`PlaneHypothesis`), which identifies
`h(𝔻)` with the closure of the bounded side of the traced curve and hence gives the parametrisation
of the inner boundary circle, and the planar annulus theorem
(`Work.Smooth.SphereJordan.annulus_of_planeHypothesis_strict`, proved in the sibling module of this
directory from the same planar theorem), which straightens the region between that curve and the
boundary circle. -/
theorem plainAnnulus_of_planeHypothesis (h : Work.Smooth.SphereJordan.PlaneHypothesis) :
    Work.Smooth.SphereJordan.PlainAnnulusSchoenflies := by
  intro hf hinj hbd
  -- the simple closed plane curve traced by the boundary circle of `hf`
  have hcont : Continuous (fun θ : ℝ => ((hf (circlePoint θ) : Disc) : ℂ)) :=
    continuous_subtype_val.comp (hf.continuous.comp PlainAnnulusAux.continuous_circlePoint)
  have hperv : Function.Periodic (fun θ : ℝ => ((hf (circlePoint θ) : Disc) : ℂ)) (2 * Real.pi) := by
    intro θ
    show ((hf (circlePoint (θ + 2 * Real.pi)) : Disc) : ℂ) = ((hf (circlePoint θ) : Disc) : ℂ)
    rw [PlainAnnulusAux.circlePoint_add_two_pi]
  have hinjv : Set.InjOn (fun θ : ℝ => ((hf (circlePoint θ) : Disc) : ℂ))
      (Set.Ico 0 (2 * Real.pi)) := by
    intro a ha b hb hab
    exact injOn_circlePoint ha hb (hinj (Subtype.ext hab))
  let γ : Work.Smooth.Jordan.PlaneCurve :=
    ⟨fun θ : ℝ => ((hf (circlePoint θ) : Disc) : ℂ), hcont, hperv⟩
  have hγcoe : ∀ θ : ℝ, γ.γ θ = ((hf (circlePoint θ) : Disc) : ℂ) := fun _ => rfl
  have hs : γ.IsSimple := hinjv
  have hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1 := fun θ => by rw [hγcoe]; exact hbd θ
  obtain ⟨S⟩ := h γ hs
  -- the image of `hf` is the Schoenflies disc of the traced curve
  obtain ⟨hrange, hinter⟩ :=
    disc_spans_schoenflies_clean (γ := γ) hball S (F := hf) hinj (fun θ => (hγcoe θ).symm)
  -- the planar annulus theorem straightens the region between `closure S.V` and the boundary
  obtain ⟨Θ, hfix, hstrict, hclosed⟩ := annulus_of_planeHypothesis_strict h hs hball S
  refine ⟨Θ, hfix, ?_, ?_⟩
  · -- `h(𝔻)` is carried onto the closed half-disc
    intro x
    constructor
    · rintro ⟨z, rfl⟩
      exact (hclosed (hf z)).mp (by rw [← hrange]; exact ⟨z, rfl⟩)
    · intro hx
      have hmem : ((x : Disc) : ℂ) ∈ closure S.V := (hclosed x).mpr hx
      rw [← hrange] at hmem
      obtain ⟨z, hz⟩ := hmem
      exact ⟨z, Subtype.ext hz⟩
  · -- the open disc is carried onto the open half-disc
    intro z
    rw [← hstrict (hf z)]
    constructor
    · intro hz
      rw [← hinter]
      exact ⟨z, hz, rfl⟩
    · intro hz
      have hmem : ((hf z : Disc) : ℂ) ∈
          (fun z : Disc => ((hf z : Disc) : ℂ)) '' {z : Disc | ‖((z : Disc) : ℂ)‖ < 1} := by
        rw [hinter]; exact hz
      obtain ⟨w, hw, hwe⟩ := hmem
      have hwz : w = z := hinj (Subtype.ext hwe)
      rwa [hwz] at hw

end

end Work.Smooth.SphereJordan
