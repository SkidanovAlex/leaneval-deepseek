import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.windowPieceAssembly
import Submission.Work.Drive.N2.saddleWindowBlock

/-!
# The chart-coordinate model drawing of a window (H8 lane)

The model piece of a window in the parked-window design of the compact `n = 2` movie
(`Submission/Work/Drive/N2/parkedWindowsAssembly.lean`,
`Work.Drive.N2.levelSeparatingMap_of_parkedWindows`) is needed **only on its own model region**
`D j`, where it is separated from the parked picture by the sign of the first coordinate.  So the
model is *free* on `D j` — in particular **no Morse structure is needed for its rows**: it is enough
that the coordinate map is a chart on `D j`.

This file records that observation as a brick.  It supersedes the heavy `saddlePsi`-based model rows
(`Work.Drive.N2.goodDrawingOf_saddlePsi_pullback`, `…saddleChartDrawing_immersive`) *in the parked
design*: the level-injectivity and the `ker df`-immersivity of the drawing follow from the
injectivity of the chart and of its differential alone, with no hypothesis on `f` at all — because
the cross half of the level-injectivity row is settled by the *sign* separation, not by an
agreement.

* `Work.Drive.N2.goodDrawingOnK_of_chartCoord` — for an injective continuous linear map `L` and a
  chart `Z` on the open set `U`, the drawing `x ↦ L (Z x) + v` satisfies the rows of
  `GoodDrawingOnK f U A` for *every* level function `f` and every value set `A`.
* `Work.Drive.N2.goodDrawingOnK_of_chartCoord_cE3` — the window form, `L = cE3`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

/-- **The model rows of a window need only a chart.**  Let `Z : M → E` be a chart of `M` on the open
set `U` (smooth at the points of `U`, injective on `U`, with injective differential at the points of
`U`), let `L : E →L[ℝ] ℝ³` be injective and let `v : ℝ³`.  Then for *every* level function `f` and
every value set `A` the drawing `x ↦ L (Z x) + v` satisfies the rows of a good drawing on `U`.

The two separation rows do not use the level function: `L ∘ Z` is injective on `U` (being a translate
of an injective map) and its differential is injective, `L` and `dZ` both being injective. -/
theorem goodDrawingOnK_of_chartCoord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : M → ℝ} {U : Set M} {Z : M → E} (L : E →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hLinj : Function.Injective L) (v : EuclideanSpace ℝ (Fin 3))
    (hZsm : ∀ x : M, x ∈ U → ContMDiffAt (𝓡 2) 𝓘(ℝ, E) ∞ Z x)
    (hZinj : ∀ x : M, x ∈ U → ∀ y : M, y ∈ U → Z x = Z y → x = y)
    (hZimm : ∀ x : M, x ∈ U → Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) Z x))
    (A : Set ℝ) :
    GoodDrawingOnK f U A (fun x : M => L (Z x) + v) := by
  have hn : ((∞ : WithTop ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro x hx _
    have h1 : ContMDiffAt (𝓡 2) (𝓡 3) ∞ (fun y : M => L (Z y)) x :=
      (L.contMDiff.contMDiffAt).comp x (hZsm x hx)
    exact h1.add contMDiffAt_const
  · intro x hx _ w _ hwS
    have hZmd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, E) Z x := (hZsm x hx).mdifferentiableAt hn
    have hLmd : MDifferentiableAt 𝓘(ℝ, E) (𝓡 3) (⇑L) (Z x) :=
      L.contMDiff.contMDiffAt.mdifferentiableAt hn
    have hLmf : mfderiv 𝓘(ℝ, E) (𝓡 3) (⇑L) (Z x) = L := (L.hasMFDerivAt (x := Z x)).mfderiv
    have hLZsm : ContMDiffAt (𝓡 2) (𝓡 3) ∞ (fun y : M => L (Z y)) x :=
      (L.contMDiff.contMDiffAt).comp x (hZsm x hx)
    have hSsm : ContMDiffAt (𝓡 2) (𝓡 3) ∞ (fun y : M => L (Z y) + v) x :=
      hLZsm.add contMDiffAt_const
    have htrsm : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        (fun e : EuclideanSpace ℝ (Fin 3) => e - v) (L (Z x) + v) :=
      contMDiffAt_id.sub contMDiffAt_const
    have hcomp : ((fun e : EuclideanSpace ℝ (Fin 3) => e - v) ∘
        (fun y : M => L (Z y) + v)) = (fun y : M => L (Z y)) := by
      funext y
      simp only [Function.comp_apply]
      abel
    have hchain := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 3) (I'' := 𝓡 3)
      (f := fun y : M => L (Z y) + v) (g := fun e : EuclideanSpace ℝ (Fin 3) => e - v)
      (x := x) (htrsm.mdifferentiableAt hn) (hSsm.mdifferentiableAt hn) w
    -- undo the shift: the derivative of `L ∘ Z` vanishes
    have hLZzero : mfderiv (𝓡 2) (𝓡 3) (fun y : M => L (Z y)) x w = 0 := by
      have h3 := congrArg (fun g : M → EuclideanSpace ℝ (Fin 3) =>
        mfderiv (𝓡 2) (𝓡 3) g x w) hcomp.symm
      rw [h3, hchain, hwS]
      exact map_zero _
    -- the chain rule for `L ∘ Z`
    have h := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓘(ℝ, E)) (I'' := 𝓡 3)
      (f := Z) (g := ⇑L) (x := x) hLmd hZmd w
    rw [hLmf] at h
    have h2 : mfderiv (𝓡 2) (𝓡 3) ((⇑L) ∘ Z) x w = 0 := by
      have hone : (⇑L) ∘ Z = (fun y : M => L (Z y)) := rfl
      rw [hone]; exact hLZzero
    rw [h2] at h
    have hzw0 : mfderiv (𝓡 2) 𝓘(ℝ, E) Z x w = (0 : E) :=
      hLinj (h.symm.trans (map_zero L : L (0 : E) = 0).symm)
    have hz0 : mfderiv (𝓡 2) 𝓘(ℝ, E) Z x (0 : TangentSpace (𝓡 2) x) = (0 : E) := map_zero _
    exact hZimm x hx (hzw0.trans hz0.symm)

  · intro x y hx hy _ _ _ hxy
    have h1 : L (Z x) = L (Z y) := add_right_cancel hxy
    exact hZinj x hx y hy (hLinj h1)

/-- The window form of the brick: the drawing `x ↦ cE3 (Z x) + v` of a chart `Z : M → ℂ`. -/
theorem goodDrawingOnK_of_chartCoord_cE3 {f : M → ℝ} {U : Set M} {Z : M → ℂ}
    (v : EuclideanSpace ℝ (Fin 3))
    (hZsm : ∀ x : M, x ∈ U → ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ Z x)
    (hZinj : ∀ x : M, x ∈ U → ∀ y : M, y ∈ U → Z x = Z y → x = y)
    (hZimm : ∀ x : M, x ∈ U → Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x))
    (A : Set ℝ) :
    GoodDrawingOnK f U A (fun x : M => cE3 (Z x) + v) :=
  goodDrawingOnK_of_chartCoord (E := ℂ) cE3 (fun _ _ h => cE3_injective h) v hZsm hZinj hZimm A

end Work.Drive.N2

namespace Work.Drive.N2

open scoped _root_.Manifold _root_.ContDiff _root_.Topology
open Set Function Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M]

/-- The *unshifted* window form of the chart-model brick: `x ↦ cE3 (Z x)`. -/
theorem goodDrawingOnK_of_chartCoord_cE3_plain {f : M → ℝ} {U : Set M} {Z : M → ℂ}
    (hZsm : ∀ x : M, x ∈ U → ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ Z x)
    (hZinj : ∀ x : M, x ∈ U → ∀ y : M, y ∈ U → Z x = Z y → x = y)
    (hZimm : ∀ x : M, x ∈ U → Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x))
    (A : Set ℝ) :
    GoodDrawingOnK f U A (fun x : M => cE3 (Z x)) := by
  have h := goodDrawingOnK_of_chartCoord (f := f) (E := ℂ) cE3 (fun _ _ h => cE3_injective h)
    (0 : EuclideanSpace ℝ (Fin 3)) hZsm hZinj hZimm A
  have h2 : (fun x : M => cE3 (Z x) + (0 : EuclideanSpace ℝ (Fin 3)))
      = fun x : M => cE3 (Z x) := by
    funext x
    simp
  rwa [h2] at h

end Work.Drive.N2
