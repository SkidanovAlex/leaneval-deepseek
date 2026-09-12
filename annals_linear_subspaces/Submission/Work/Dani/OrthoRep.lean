import Submission.GeometryOfNumbers.WedgeBlocks
import Submission.GeometryOfNumbers.PlaneFinrank

/-!
# Orthogonal representatives of `ℓ`-planes

For every `ℓ`-dimensional subspace `x ≤ ℝᵈ` there is a **linear isometry** `s` of `ℝᵈ` with
`s(x) = x₀ = modelX ℓ`.  The paper's representative `s_x` of the point `x = P s_x` may thus
always be taken orthogonal, which makes the `s_x`-transport of Prop 1 part 2 exact (see
`Submission.Work.Dani.Part2`).

Construction: an orthonormal basis of `ℝᵈ` whose first `ℓ` elements are an orthonormal basis
of `x` (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`), transported onto the
standard basis by `OrthonormalBasis.equiv`.

Module `Submission.Work.Dani.OrthoRep`, namespace `Submission.DaniOrthoRep`, sorry-free.
-/

noncomputable section

open Module Real InnerProductGeometry
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Submission.ExteriorCoordinates

namespace Submission.DaniOrthoRep

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Existence of an orthogonal representative**: for an `ℓ`-dimensional subspace `x` of `ℝᵈ`
there is a linear isometry `s` with `s(x) = x₀ = modelX ℓ`. -/
theorem exists_isometry_map_eq_modelX {ℓ : ℕ} (hℓd : ℓ ≤ d) (x : Submodule ℝ ℝᵈ)
    (hx : Module.finrank ℝ x = ℓ) :
    ∃ s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ,
      Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x = Submission.WedgeBlocks.modelX (d := d) ℓ := by
  classical
  have hcard : Fintype.card (Fin ℓ) = Module.finrank ℝ x := by
    rw [Fintype.card_fin, hx]
  let bx : OrthonormalBasis (Fin ℓ) ℝ x :=
    (stdOrthonormalBasis ℝ x).reindex (Fintype.equivFinOfCardEq hcard).symm
  let v : Fin d → ℝᵈ := fun i => if h : i.val < ℓ then (bx ⟨i.val, h⟩ : x) else 0
  have hv : Orthonormal ℝ
      ((({i : Fin d | i.val < ℓ} : Set (Fin d))).domRestrict v) := by
    have hbase : Orthonormal ℝ (fun j : Fin ℓ => (bx j : ℝᵈ)) :=
      bx.orthonormal.comp_linearIsometry x.subtypeₗᵢ
    have hcomp : Orthonormal ℝ
        (fun i : {i : Fin d // i.val < ℓ} => (bx ⟨i.1.val, i.2⟩ : ℝᵈ)) :=
      hbase.comp (fun i : {i : Fin d // i.val < ℓ} => (⟨i.1.val, i.2⟩ : Fin ℓ)) (by
        intro i j hij
        exact Subtype.ext (Fin.ext (by simpa using congrArg Fin.val hij)))
    rw [Set.domRestrict_eq]
    change Orthonormal ℝ (fun i : {i : Fin d // i.val < ℓ} => v ↑i)
    have hfun : (fun i : {i : Fin d // i.val < ℓ} => v ↑i) =
        (fun i : {i : Fin d // i.val < ℓ} => (bx ⟨i.1.val, i.2⟩ : ℝᵈ)) := by
      funext i
      dsimp only [v]
      rw [dif_pos i.2]
    rw [hfun]
    exact hcomp
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (E := ℝᵈ) (by simp [finrank_euclideanSpace, Fintype.card_fin])
    (v := v) (s := ({i : Fin d | i.val < ℓ} : Set (Fin d))) hv
  let s : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ := b.equiv (EuclideanSpace.basisFun (Fin d) ℝ) (Equiv.refl (Fin d))
  refine ⟨s, ?_⟩
  -- the transported ON basis of `x` spans `(B d) '' {i | i.val < ℓ}`
  have hstep : ∀ j : Fin ℓ, s ((bx j : x) : ℝᵈ) = (B d) (Fin.castLE hℓd j) := by
    intro j
    have hsmall : (Fin.castLE hℓd j).val < ℓ := j.isLt
    have hbv : b (Fin.castLE hℓd j) = v (Fin.castLE hℓd j) := hb _ (by simp)
    have hvval : v (Fin.castLE hℓd j) = ((bx j : x) : ℝᵈ) := by
      dsimp only [v]
      rw [dif_pos hsmall]
      exact congrArg (fun z : x => (z : ℝᵈ)) (congrArg bx (Fin.ext rfl))
    rw [← hvval, ← hbv]
    exact OrthonormalBasis.equiv_apply_basis b (EuclideanSpace.basisFun (Fin d) ℝ)
      (Equiv.refl (Fin d)) (Fin.castLE hℓd j)
  have hxeq : x = Submodule.span ℝ (Set.range (x.subtype ∘ ⇑bx)) := by
    have hspan := bx.toBasis.span_eq
    simp only [OrthonormalBasis.coe_toBasis] at hspan
    rw [Set.range_comp, Submodule.span_image, hspan, Submodule.map_subtype_top]
  have hxspan : Submodule.map (s : ℝᵈ →ₗ[ℝ] ℝᵈ) x =
      Submodule.span ℝ (Set.range (fun j : Fin ℓ => (B d) (Fin.castLE hℓd j))) := by
    rw [hxeq, Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨z, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (hstep j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨((bx j : x) : ℝᵈ), ⟨j, rfl⟩, hstep j⟩
  rw [hxspan]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro y ⟨j, rfl⟩
    exact Submission.WedgeBlocks.std_mem_modelX ℓ (Fin.castLE hℓd j) j.isLt
  · unfold Submission.WedgeBlocks.modelX
    rw [Submodule.span_le]
    rintro e ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨⟨i.val, hi⟩, by simp [Fin.castLE]⟩

/-- A **choice** of orthogonal representative of `x`: a linear isometry `s` with
`s(x) = x₀ = modelX ℓ`. -/
noncomputable def orthRep {ℓ : ℕ} (hℓd : ℓ ≤ d) (x : Submodule ℝ ℝᵈ)
    (hx : Module.finrank ℝ x = ℓ) : ℝᵈ ≃ₗᵢ[ℝ] ℝᵈ :=
  Classical.choose (exists_isometry_map_eq_modelX hℓd x hx)

/-- The defining property of `orthRep`. -/
theorem orthRep_spec {ℓ : ℕ} (hℓd : ℓ ≤ d) (x : Submodule ℝ ℝᵈ)
    (hx : Module.finrank ℝ x = ℓ) :
    Submodule.map (orthRep hℓd x hx : ℝᵈ →ₗ[ℝ] ℝᵈ) x =
      Submission.WedgeBlocks.modelX (d := d) ℓ :=
  Classical.choose_spec (exists_isometry_map_eq_modelX hℓd x hx)

end Submission.DaniOrthoRep
