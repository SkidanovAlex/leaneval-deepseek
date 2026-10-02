import Mathlib
import Submission.Work.Model.prod_transfer
import Submission.Work.Projective.Model
import Submission.Work.Gen.Cp2Cp2Smooth

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The *explicit* re-charting of `ℂP² × ℂP²` over `ℝ⁸`

`Work.Model.prod_transfer` states its conclusion as an **`∃`**:

```lean
theorem prod_transfer : ∃ c : ChartedSpace (EuclideanSpace ℝ (Fin (m + n))) M,
    (letI := c; IsManifold (𝓡 (m + n)) ∞ M)
```

and `Work.Gen.Cp2Cp2Smooth` re-exports it as an `∃`; hence
`Work.Gen.cp2cp2ChartedSpaceEuclid := Classical.choose Cp2Cp2Smooth` is an **opaque**
`Classical.choice` (`Classical.choice` has no computation rule: `Classical.choice ⟨a⟩ = a` is not
derivable, and `Exists.choose` is `Classical.choose`).  Consequently

* the charts of `cp2cp2ChartedSpaceEuclid` are opaque, and
* so is the tangent bundle `Work.TangentClasses.tangentBundle 𝓘(ℝ,ℝ⁸) (ℂP² × ℂP²)` built over its
  atlas, and therefore so are `Work.Thom.p1Tangent'`/`p2Tangent'` of `ℂP² × ℂP²` — the two
  quantities that `Work.Gen.cp2cp2_model` must identify with the Künneth model's `p₁`, `p₂`.

This module removes the opacity by exhibiting the *same* charted-space structure as a **definitional
term** (`prodChartedSpaceTransfer`), namely the pushforward of the product atlas along the linear
isometry `ℝ^m × ℝ^n ≅ ℝ^{m+n}`, and proving that it is a `C^∞` structure
(`prodChartedSpaceTransfer_isManifold`, the proof of `Work.Model.prod_transfer` repeated outside the
`∃`).  `Work.Gen.Cp2Cp2Smooth8` then *defines*
`Work.Gen.cp2cp2ChartedSpaceEuclid`/`cp2cp2IsManifoldEuclid` to be these explicit objects (keeping
the names), so that every downstream statement — `cp2cp2Smooth8Of`, and the statement of
`Work.Gen.cp2cp2_model` — is about charts that are *given* rather than *chosen*.
-/

open scoped Manifold ContDiff Topology

namespace Work.Gen

noncomputable section

open Work.Projective

/-- The linear isometry `ℝ^m × ℝ^n ≅ ℝ^{m+n}` used to re-chart a product manifold. -/
def prodLinEquiv (m n : ℕ) :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m + n)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)).symm

/-- **The pushforward of a charted-space structure over the product model along the linear isometry
`ℝ^m × ℝ^n ≅ ℝ^{m+n}`** — the explicit (choice-free) charted-space structure whose existence is
`Work.Model.prod_transfer`. -/
def prodChartedSpaceTransfer {m n : ℕ} (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) M] :
    ChartedSpace (EuclideanSpace ℝ (Fin (m + n))) M where
  atlas := (fun φ : OpenPartialHomeomorph M
      (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) =>
      φ.trans (prodLinEquiv m n).toHomeomorph.toOpenPartialHomeomorph) ''
      atlas (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) M
  chartAt x := (chartAt (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) x).trans
    (prodLinEquiv m n).toHomeomorph.toOpenPartialHomeomorph
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨mem_chart_source _ x, by simp⟩
  chart_mem_atlas x := ⟨chartAt _ x, chart_mem_atlas _ x, rfl⟩

@[simp] theorem prodChartedSpaceTransfer_atlas {m n : ℕ} (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) M]
    (φ : OpenPartialHomeomorph M
      (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))) :
    (prodChartedSpaceTransfer (m := m) (n := n) M).atlas =
      (fun φ : OpenPartialHomeomorph M
        (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) =>
        φ.trans (prodLinEquiv m n).toHomeomorph.toOpenPartialHomeomorph) ''
        atlas (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) M := rfl

/-- **`Work.Model.prod_transfer` in *definitional* form**: the explicit pushforward of the product
atlas along `ℝ^m × ℝ^n ≅ ℝ^{m+n}` is a `C^∞` structure.  (The `∃`-statement of
`Work.Model.prod_transfer` follows from this by `⟨_, prodChartedSpaceTransfer_isManifold ..⟩`.) -/
theorem prodChartedSpaceTransfer_isManifold {m n : ℕ} (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) M]
    [IsManifold ((𝓡 m).prod (𝓡 n)) ∞ M] :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (m + n))) _ _ (EuclideanSpace ℝ (Fin (m + n))) _
      (𝓡 (m + n)) ∞ M _ (prodChartedSpaceTransfer (m := m) (n := n) M) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (m + n))) M :=
    prodChartedSpaceTransfer (m := m) (n := n) M
  let Φ := prodLinEquiv m n
  let f : (ModelProd (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) ≃ₜ
      EuclideanSpace ℝ (Fin (m + n)) := Φ.toHomeomorph
  refine IsManifold.mk' (𝓡 (m + n)) ∞ M (gr := ⟨fun {e e'} he he' => ?_⟩)
  rcases he with ⟨φ, hφ, rfl⟩
  rcases he' with ⟨ψ, hψ, rfl⟩
  have hbase : (φ.symm ≫ₕ ψ) ∈ contDiffGroupoid ∞
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) := by
    have h := (contDiffGroupoid ∞ ((𝓡 m).prod (𝓡 n))).compatible hφ hψ
    rwa [← modelWithCornersSelf_prod] at h
  have hconj := Work.Model.conj_mem f Φ.contDiff Φ.symm.contDiff hbase
  have hsymm : (φ.trans f.toOpenPartialHomeomorph).symm ≫ₕ (ψ.trans f.toOpenPartialHomeomorph)
      = f.toOpenPartialHomeomorph.symm.trans
          ((φ.symm ≫ₕ ψ).trans f.toOpenPartialHomeomorph) := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    simp only [OpenPartialHomeomorph.trans_assoc]
  rw [hsymm]
  exact hconj

/-! ## The instance for `ℂP² × ℂP²` -/

/-- **The explicit charted-space structure of `ℂP² × ℂP²` over `ℝ⁸`**: the pushforward of the
product atlas of the two Euclidean atlases of `ℂP²` along `ℝ⁴ × ℝ⁴ ≅ ℝ⁸`. -/
def cp2cp2ChartedSpaceExplicit : ChartedSpace (EuclideanSpace ℝ (Fin 8)) (CP 2 × CP 2) :=
  prodChartedSpaceTransfer (m := 4) (n := 4) (CP 2 × CP 2)

/-- The explicit structure is a `C^∞` structure. -/
theorem cp2cp2IsManifoldExplicit :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 8)) _ _ (EuclideanSpace ℝ (Fin 8)) _
      (𝓡 8) ∞ (CP 2 × CP 2) _ cp2cp2ChartedSpaceExplicit :=
  prodChartedSpaceTransfer_isManifold (m := 4) (n := 4) (CP 2 × CP 2)

end

end Work.Gen
