import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.GoodDrawingFamily

/-!
# The model pullback for a *band* (`GoodDrawingOn` form)

`Work.Drive.N2.goodDrawing_of_modelPullback` takes a **globally** smooth `Φ : M → N`.  The block
diffeomorphisms of the compact `n = 2` construction are only smooth *near the window* they are built
for (outside it the definition is arbitrary), so this file records the band-localised form: the
smoothness of `Φ` is required only at the points whose `f`-value lies in the band `A`, and the two
separation rows only for such points.  The conclusion is `GoodDrawingOn f A (S ∘ Φ)`, which is
exactly what `Work.Drive.N2.goodDrawing_of_family` consumes.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff
open Set Function

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
  [IsManifold (𝓡 2) ∞ N]

/-- **The band-localised model pullback.**  If `S : N → ℝ³` is an injective immersion, `Φ : M → N`
is smooth at every point of the band `A`, injective on the `f`-levels inside `A` and immersive on
`ker (df)` there, then `S ∘ Φ` is a `GoodDrawingOn f A`. -/
theorem goodDrawingOn_of_modelPullback
    (f : M → ℝ) (A : Set ℝ) (Phi : M → N) (S : N → EuclideanSpace ℝ (Fin 3))
    (hPhism : ∀ x : M, f x ∈ A → ContMDiffAt (𝓡 2) (𝓡 2) ∞ Phi x)
    (hSsm : ContMDiff (𝓡 2) (𝓡 3) ∞ S)
    (hSinj : Function.Injective S)
    (hSimm : ∀ y : N, Function.Injective (mfderiv (𝓡 2) (𝓡 3) S y))
    (hPhiinj : ∀ x y : M, f x ∈ A → f y ∈ A → f x = f y → Phi x = Phi y → x = y)
    (hPhiimm : ∀ x : M, f x ∈ A → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 2) Phi x v = 0 → v = 0) :
    GoodDrawingOn f A (fun x => S (Phi x)) := by
  have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (hSsm.contMDiffAt).comp x (hPhism x hx)
  · intro x hx v hv hvS
    have hmd : MDifferentiableAt (𝓡 2) (𝓡 2) Phi x := (hPhism x hx).mdifferentiableAt hn
    have hms : MDifferentiableAt (𝓡 2) (𝓡 3) S (Phi x) := hSsm.contMDiffAt.mdifferentiableAt hn
    have hcomp := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
      (f := Phi) (g := S) x hms hmd v
    have hzero : mfderiv (𝓡 2) (𝓡 3) S (Phi x) (mfderiv (𝓡 2) (𝓡 2) Phi x v) = 0 := by
      rw [← hcomp]; exact hvS
    exact hPhiimm x hx v hv ((hSimm (Phi x)) (hzero.trans (map_zero _).symm))
  · intro x y hx hy hfxy hSeq
    exact hPhiinj x y hx hy hfxy (hSinj hSeq)

end Work.Drive.N2
