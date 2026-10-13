import Mathlib
import Submission.Work.WilG5.Face.Defs

/-!
# The dimension bound for a face

`DimLE X μ` (BNZ's `dim X ≤ μ`) says that every projection of `X` to `μ + 1`
coordinates has empty interior.  We show that cutting out one coordinate
hyperplane `x i = c` lowers the dimension bound to `min μ (n - 1)`.

The mathematical content is completely elementary.  Let `ν = min μ (n - 1)`,
let `Y = faceProj i c X ⊆ ℝ^{n-1}` and let `e : Fin (ν+1) ↪ Fin (n-1)` be a
choice of `ν+1` coordinates of `ℝ^{n-1}`.

* If `ν = n - 1` there is no such `e` at all (cardinality), so there is nothing
  to prove.
* Otherwise `ν = μ`, and `E := delSplit i ∘ e : Fin (μ+1) ↪ Fin n` is a choice
  of `μ+1` coordinates of `ℝ^n`, injective because `delSplit i` is.  If
  `w = y ∘ e` with `y ∈ Y`, then `x := insCoord i c y ∈ X` (this is
  `insCoord_mem_faceProj`) and `x ∘ E = (x ∘ delSplit i) ∘ e = y ∘ e = w`
  (because `x (delSplit i j) = y j`, i.e. `insCoord_delSplit`).  Hence the
  `e`-projection of `Y` is contained in the `E`-projection of `X`, whose
  interior is empty by `h : DimLE X μ`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.WilG5.Face

open WilkiesDesign WilkiesConjecture

theorem face_dimle {n μ : ℕ} (hμ : μ ≤ n) (i : Fin n) (c : ℝ) {X : Set (Fin n → ℝ)}
    (h : WilkiesDesign.DimLE X μ) :
    WilkiesDesign.DimLE (Work.WilG5.Face.faceProj i c X) (min μ (n - 1)) := by
  by_cases hcase : n - 1 ≤ μ
  · -- the bound is the ambient dimension `n - 1`, which is vacuous
    have hν : min μ (n - 1) = n - 1 := min_eq_right_iff.mpr hcase
    rw [hν]
    intro e
    have hcard := Fintype.card_le_of_injective e e.injective
    simp only [Fintype.card_fin] at hcard
    omega
  · -- here `min μ (n - 1) = μ`, and `delSplit i ∘ e` is a valid `μ+1`-projection of `X`
    have hν : min μ (n - 1) = μ := min_eq_left_iff.mpr (by omega)
    rw [hν]
    intro e
    let E : Fin (μ + 1) ↪ Fin n :=
      ⟨fun j => delSplit i (e j), fun a b hab => e.injective (delSplit_injective i hab)⟩
    have hsub : (fun y : Fin (n - 1) → ℝ => y ∘ e) '' faceProj i c X ⊆
        (fun x : Fin n → ℝ => x ∘ E) '' X := by
      rintro w ⟨y, hy, rfl⟩
      refine ⟨insCoord i c y, (insCoord_mem_faceProj i c X y).mpr hy, ?_⟩
      funext j
      show insCoord i c y (delSplit i (e j)) = y (e j)
      exact insCoord_delSplit i c y (e j)
    have hempty : interior ((fun x : Fin n → ℝ => x ∘ E) '' X) = ∅ := h E
    rw [← Set.subset_empty_iff]
    intro z hz
    have hz' : z ∈ interior ((fun x : Fin n → ℝ => x ∘ E) '' X) := interior_mono hsub hz
    rw [hempty] at hz'
    exact hz'

end Work.WilG5.Face
