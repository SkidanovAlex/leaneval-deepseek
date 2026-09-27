import Mathlib
import Submission.Work.PL.Defs

/-!
# Charts from open cells: `PL.IsOpenCell n W → ∃ c, c.toFun '' openCube 1 = W`

Blueprint `A8`/`C2` (Connell's cell-count reduction) repeatedly needs to replace an open
`n`-cell `W ⊆ M` by a `PL.CubeChart` whose *distinguished* open unit cube has image exactly
`W`: the engulfing theorem (`PL.EngulfForm`) is stated in terms of images of `PL.openCube (1/2)`
of a `PL.CubeChart`, and the local criterion in `PL.EngulfForm` also uses `PL.closedCube 1`.

Given `PL.IsOpenCell n W` — i.e. `W` open in `M` and `W ≃ₜ PL.E n` — such a chart is obtained
by choosing a homeomorphism `PL.openCube 1 ≃ₜ PL.E n` (the open unit sup-cube is homeomorphic
to the whole Euclidean space, coordinatewise via `orderIsoIooNegOneOne ℝ`), composing it with
the given `W ≃ₜ PL.E n` to get `φ : PL.openCube 1 ≃ₜ W`, and then extending `φ` to all of
`PL.E n` by a constant off the cube.

No topological input beyond the product structure of `PL.E n = PiLp 2 (Fin n → ℝ)` is used, so
the result holds for every `n` (including `n = 0`, where `openCube 1 = univ`).
-/

open Set Metric

namespace Work.Cells.Connell

/-- The "`Set.pi` is a product of subtypes" homeomorphism: for a family `t` of subsets of `ℝ`,
`↥(⨅ᵢ tᵢ)` is homeomorphic to `∀ i, ↥(tᵢ)`.  (`Set.pi univ t` is the `Set.pi` of `t` over all
indices.) -/
private noncomputable def piSetHomeo {ι : Type*} (t : ι → Set ℝ) :
    ↥(Set.pi Set.univ t) ≃ₜ ((i : ι) → ↥(t i)) where
  toFun x := fun i => ⟨x.1 i, (Set.mem_pi.mp x.2) i trivial⟩
  invFun f := ⟨fun i => (f i : ℝ), by rw [Set.mem_pi]; intro i _; exact (f i).2⟩
  left_inv x := by ext i; rfl
  right_inv f := by ext i; rfl
  continuous_toFun := by
    apply continuous_pi; intro i
    exact Continuous.subtype_mk ((continuous_apply i).comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi; intro i
    exact continuous_subtype_val.comp (continuous_apply i)

/-- The open unit sup-cube `PL.openCube (n := n) 1 ⊆ PL.E n` is homeomorphic to all of
`PL.E n`.  Concretely, `PL.E n = PiLp 2 (Fin n → ℝ)` is homeomorphic to `Fin n → ℝ` by
`PiLp.homeomorph`, `openCube 1` is the product of the intervals `Ioo (-1) 1`, and each such
interval is homeomorphic to `ℝ` by `orderIsoIooNegOneOne ℝ`. -/
private noncomputable def openCubeHomeo (n : ℕ) :
    ↥(PL.openCube (n := n) 1) ≃ₜ PL.E n :=
  (Homeomorph.subtype (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) (fun x => by
      simp only [PL.openCube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_Ioo, PiLp.homeomorph]
      constructor <;> intro h i
      · exact abs_lt.mp (h i)
      · rw [abs_lt]; exact h i)).trans
    ((piSetHomeo (fun _ : Fin n => Set.Ioo (-1:ℝ) 1)).trans
      ((Homeomorph.piCongrRight
          (fun _ : Fin n => (orderIsoIooNegOneOne ℝ).toHomeomorph.symm)).trans
        (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm))

/-- **Charts from open cells.**  Every open `n`-cell `W ⊆ M` is the image of the open unit cube
of some cube chart `PL.CubeChart n M`.

The chart is built from a homeomorphism `φ : PL.openCube 1 ≃ₜ W` (which exists because both
spaces are homeomorphic to `PL.E n`); it is `φ` on the cube and a fixed point off it.  Being
`φ` on the cube, its image is `W`, it is continuous on the cube, and it restricts to the open
embedding `W ↪ M` there. -/
theorem cubeChart_of_isOpenCell {n : ℕ} {M : Type*} [TopologicalSpace M] {W : Set M}
    (hW : PL.IsOpenCell n W) :
    ∃ c : PL.CubeChart n M, c.toFun '' PL.openCube (n := n) 1 = W := by
  classical
  obtain ⟨hWopen, ⟨e⟩⟩ := hW
  set φ : ↥(PL.openCube (n := n) 1) ≃ₜ W := (openCubeHomeo n).trans e.symm with hφ
  let w0 : M := (e.symm 0 : W)
  let toFun : PL.E n → M :=
    fun x => if h : x ∈ PL.openCube (n := n) 1 then (φ ⟨x, h⟩ : M) else w0
  have htoFun_on : ∀ x (hx : x ∈ PL.openCube (n := n) 1), toFun x = (φ ⟨x, hx⟩ : M) :=
    fun x hx => dite_eq_left hx
  have hdom : (PL.openCube (n := n) 1).domRestrict toFun = fun x => (φ x : M) := by
    funext x
    rw [Set.domRestrict_apply, htoFun_on x.1 x.2]
  have himg : toFun '' PL.openCube (n := n) 1 = W := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [htoFun_on x hx]
      exact (φ ⟨x, hx⟩).2
    · intro hy
      refine ⟨(φ.symm ⟨y, hy⟩ : ↥(PL.openCube (n := n) 1)), (φ.symm ⟨y, hy⟩).2, ?_⟩
      rw [htoFun_on _ (φ.symm ⟨y, hy⟩).2]
      simp
  exact ⟨{ toFun := toFun
           cont := continuousOn_iff_continuous_domRestrict.mpr (by
             rw [hdom]; exact continuous_subtype_val.comp φ.continuous)
           emb := by
             rw [hdom]
             exact (IsOpen.isOpenEmbedding_subtypeVal hWopen).comp φ.isOpenEmbedding }, himg⟩

end Work.Cells.Connell
