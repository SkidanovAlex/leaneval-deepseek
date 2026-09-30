import Mathlib
import Submission.Work.Space.Metric

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Space.ModelAtlas

open Set Topology Function Filter
open scoped Manifold ContDiff Topology Bundle
open Bundle

/-! **The metric section of a model atlas is `C^∞`.**

The plan: at a point `x`, apply `Bundle.contMDiffAt_section` at `x`, which rewrites smoothness of
the section `y ↦ ⟨y, A.gM.inner y⟩` of the trivial bundle into smoothness of its coordinate
function in the trivialization at `x`.  The bundle
`fun y ↦ TangentSpace I4 y →L[ℝ] TangentSpace I4 y →L[ℝ] ℝ` is (definitionally) the trivial bundle
with fiber `E4 →L[ℝ] E4 →L[ℝ] ℝ`, and its trivialization at `x` is the hom-bundle trivialization
induced from the tangent trivialization at `x` (and the trivialization of the trivial `ℝ`-bundle).
`hom₂_trivializationAt_apply` computes it: the coordinate function is

  `fun y a b => A.gM.inner y ((trivializationAt E4 (TangentSpace I4) x).symmL ℝ y a) (…)`

`TangentBundle.symmL_trivializationAt_eq_core` identifies `symmL ℝ y` with `tangentCoordChange I4 x y y`,
so this is the left-hand side of `A.Isometry x`, which is eventually equal to

  `fun y a b => A.model (A.indexOf x) (chartAt E4 x y) a b`.

The latter is smooth in `y`, being `A.model (A.indexOf x)` (smooth by `A.model_smooth`) composed with
the chart `chartAt E4 x` (smooth by `contMDiffOn_chart`). -/

/-- **The coordinate expression of a section of the hom-bundle `TM →L (TM →L ℝ)`.**

Applying the hom-bundle trivialization at `x` — induced from the tangent trivialization at `x` and
the trivialization of the trivial bundle `fun _ : M => ℝ` — to an element `L` of the fibre at `y`
returns the bilinear form whose value on `(a, b)` is `L` evaluated on the chart-frame tangent
vectors, i.e. on `tangentCoordChange I4 x y y a` and `tangentCoordChange I4 x y y b`. -/
theorem hom₂_trivializationAt_apply {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold I4 1 M] (x y : M) (hy : y ∈ (chartAt E4 x).source)
    (L : TangentSpace I4 y →L[ℝ] (TangentSpace I4 y →L[ℝ] ℝ)) (a b : E4) :
    ((trivializationAt (E4 →L[ℝ] E4 →L[ℝ] ℝ)
        (fun z => TangentSpace I4 z →L[ℝ] (TangentSpace I4 z →L[ℝ] ℝ)) x) ⟨y, L⟩).2 a b
    = L (tangentCoordChange I4 x y y a) (tangentCoordChange I4 x y y b) := by
  have h1 : y ∈ (trivializationAt E4 (TangentSpace I4) x).baseSet := by
    simpa [TangentBundle.trivializationAt_baseSet] using hy
  have h3 : y ∈ (trivializationAt ℝ (fun _ : M => ℝ) x).baseSet := by simp
  -- unfold the outer hom-bundle trivialization and compute with `inCoordinates`
  rw [hom_trivializationAt_apply]
  rw [inCoordinates_apply_eq₂ (E₁ := TangentSpace I4) (E₂ := TangentSpace I4)
      (E₃ := fun _ : M => ℝ) (F₂ := E4) (F₃ := ℝ) (𝕜 := ℝ) (ϕ := L) (v := a) (w := b) h1 h1 h3]
  -- the linear map of the trivial `ℝ`-bundle is the identity
  have htriv : ∀ t : ℝ, (trivializationAt ℝ (fun _ : M => ℝ) x).linearMapAt ℝ y t = t := by
    intro t; rw [Trivialization.linearMapAt_apply]; simp
  rw [htriv]
  -- identify `symm` with `symmL`
  rw [← Trivialization.symmL_apply (R := ℝ) (e := trivializationAt E4 (TangentSpace I4) x) h1 a,
      ← Trivialization.symmL_apply (R := ℝ) (e := trivializationAt E4 (TangentSpace I4) x) h1 b]
  -- and the chart-frame vector with the tangent coordinate change
  rw [TangentBundle.symmL_trivializationAt_eq_core (b₀ := x) (b := y) hy]
  rfl

theorem contMDiff_inner {M : Type*} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold I4 (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    (A : ModelAtlas M) (hA : A.Isometry) :
    ContMDiff I4 (ModelWithCorners.prod I4 (modelWithCornersSelf ℝ (E4 →L[ℝ] E4 →L[ℝ] ℝ)))
      (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun y : M => Bundle.TotalSpace.mk' (E4 →L[ℝ] E4 →L[ℝ] ℝ) y (A.gM.inner y)) := by
  intro x
  rw [Bundle.contMDiffAt_section (x₀ := x)]
  -- the coordinate function agrees near `x` with the smooth model expression
  have heq : (fun y : M => ((trivializationAt (E4 →L[ℝ] E4 →L[ℝ] ℝ)
          (fun z => TangentSpace I4 z →L[ℝ] (TangentSpace I4 z →L[ℝ] ℝ)) x) ⟨y, A.gM.inner y⟩).2)
      =ᶠ[𝓝 x] (fun y : M => A.model (A.indexOf x) (chartAt E4 x y)) := by
    filter_upwards [hA x, (chartAt E4 x).open_source.mem_nhds (mem_chart_source E4 x)] with y hiso hy
    ext a b
    rw [hom₂_trivializationAt_apply x y hy (A.gM.inner y) a b]
    exact hiso a b
  rw [heq.contMDiffAt_iff]
  -- and the model expression is smooth
  have hchart : ContMDiffAt I4 (𝓘(ℝ, E4)) (((⊤ : ℕ∞) : WithTop ℕ∞)) (chartAt E4 x) x :=
    (contMDiffOn_chart (H := E4) (I := I4) (x := x) (n := (((⊤ : ℕ∞) : WithTop ℕ∞)))).contMDiffAt
      ((chartAt E4 x).open_source.mem_nhds (mem_chart_source E4 x))
  have hmodel : ContMDiffAt (𝓘(ℝ, E4)) (𝓘(ℝ, E4 →L[ℝ] E4 →L[ℝ] ℝ))
      (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun q => A.model (A.indexOf x) q) (chartAt E4 x x) := by
    have h : ContMDiffAt (𝓘(ℝ, E4)) ((𝓘(ℝ, E4)).prod (𝓘(ℝ, E4 →L[ℝ] E4 →L[ℝ] ℝ)))
        (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun q => Bundle.TotalSpace.mk' (E4 →L[ℝ] E4 →L[ℝ] ℝ) q (A.model (A.indexOf x) q))
        (chartAt E4 x x) := (A.model_smooth (A.indexOf x)).contMDiffAt
    rw [Bundle.contMDiffAt_totalSpace] at h
    exact h.2
  exact hmodel.comp x hchart

end Work.Space.ModelAtlas
