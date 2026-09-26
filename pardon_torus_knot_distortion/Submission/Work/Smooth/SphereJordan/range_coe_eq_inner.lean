import Mathlib
import Submission.Work.Smooth.SphereJordan.outerDiscAux
import Submission.Work.Smooth.SphereJordan.discCurveSpans
import Submission.Work.Smooth.Schoenflies.Unconditional

/-!
# The disc spanned by an injective disc map into the plane is the disc not containing `∞`

Let `c` be a simple closed curve of the Riemann sphere missing `∞`, `T : TwoDiscs c` a two-disc
datum for it, and `g : 𝔻 → ℂ` an injective continuous disc map whose boundary circle traces `c`
(through the coercion `ℂ ↪ ℂ ∪ {∞}`).  Then the image of `g` is exactly the piece of `T` that
*does not* contain `∞`.

The proof is the uniqueness of the spanning disc of a Jordan curve, transported to the Riemann
sphere: since `∞ ∉ range c`, the piece `T.inner ∞` avoids `∞` (`inner_ne_infty`), so it has a
plane avatar `gl = planeLift (T.inner ∞)`.  The maps `g` and `gl` are injective continuous disc
maps into `ℂ` whose boundary circles agree pointwise
(`((gl (circlePoint θ) : ℂ) : ℂ ∪ {∞}) = T.inner ∞ (circlePoint θ) = c θ = ((g (circlePoint θ) : ℂ) : ℂ ∪ {∞})`),
so by `range_eq_closure_of_boundary_eq` applied to the *same* planar Jordan–Schoenflies datum of
the common boundary curve `discCurve g`, both ranges are the closure of its bounded side, hence
equal.  Coercing back into the Riemann sphere gives the claim.
-/

namespace Work.Smooth.SphereJordan

open Set

theorem range_coe_eq_inner {c : ℝ → RiemannSphere} (T : TwoDiscs c)
    (hc : OnePoint.infty ∉ Set.range c) {g : C(Disc, ℂ)} (hg : Function.Injective g)
    (hbd : ∀ θ : ℝ, ((g (circlePoint θ) : ℂ) : RiemannSphere) = c θ) :
    Set.range (fun z : Disc => ((g z : ℂ) : RiemannSphere)) =
      Set.range (T.inner OnePoint.infty) := by
  -- the inner piece of `T` avoids `∞`
  have hne : ∀ z : Disc, T.inner OnePoint.infty z ≠ OnePoint.infty := inner_ne_infty T hc
  -- its plane avatar
  let gl : C(Disc, ℂ) := planeLift (T.inner OnePoint.infty) hne
  have hgl_coe : ∀ z : Disc, ((gl z : ℂ) : RiemannSphere) = T.inner OnePoint.infty z :=
    fun z => planeLift_coe (T.inner OnePoint.infty) hne z
  -- `g` and `gl` agree on the boundary circle
  have hbdy : ∀ θ : ℝ, gl (circlePoint θ) = g (circlePoint θ) := by
    intro θ
    exact OnePoint.coe_injective (by
      rw [hgl_coe (circlePoint θ), T.inner_boundary OnePoint.infty θ]
      exact (hbd θ).symm)
  -- the common boundary curve spans a planar disc
  obtain ⟨S⟩ := Work.Smooth.Schoenflies.planeHypothesis (discCurve g) (discCurve_isSimple hg)
  have hg_range : Set.range (⇑g) = closure S.V :=
    (range_eq_closure_of_boundary_eq S hg (fun θ => (discCurve_apply g θ).symm)).1
  have hgl_range : Set.range (⇑gl) = closure S.V :=
    (range_eq_closure_of_boundary_eq S (planeLift_injective (T.inner OnePoint.infty) hne
        (T.inner_injective OnePoint.infty)) (by
          intro θ
          rw [discCurve_apply]
          exact hbdy θ)).1
  have hrange : Set.range (⇑g) = Set.range (⇑gl) := hg_range.trans hgl_range.symm
  calc Set.range (fun z : Disc => ((g z : ℂ) : RiemannSphere))
      = (fun x : ℂ => (x : RiemannSphere)) '' Set.range (⇑g) := image_coe_range g
    _ = (fun x : ℂ => (x : RiemannSphere)) '' Set.range (⇑gl) := by rw [hrange]
    _ = Set.range (fun z : Disc => ((gl z : ℂ) : RiemannSphere)) := (image_coe_range gl).symm
    _ = Set.range (T.inner OnePoint.infty) := by
          apply congrArg Set.range
          funext z
          exact hgl_coe z

end Work.Smooth.SphereJordan
