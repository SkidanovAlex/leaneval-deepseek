import Mathlib
import Submission.Work.DeltaHomology.CellData
import Submission.Work.DeltaHomology.eq_of_cls_eq_of_pos
import Submission.Work.DeltaHomology.exists_collar_punctStdSimplex
import Submission.Work.DeltaHomology.PunctSimplex
import Submission.Work.DeltaHomology.PunctSkelBasic
import Submission.Work.DeltaHomology.isClosed_skelSet
import Submission.Work.DeltaHomology.isIso_relHomologyMap_of_deformationRetract
import Submission.Work.DeltaHomology.relHomology_iso_clopen_sum
import Submission.Work.Homology.Spheres
import Submission.Work.Homology.Point
import Submission.Work.HomologyExtra.SimplexDisk
import Submission.Work.HomologyExtra.isIso_relHomologyMap_pairHomOfHomeomorph
import Submission.Work.Cohomology.localHomology
import Submission.Work.DeltaHomology.exists_homeomorph_intCell
import Submission.Work.DeltaHomology.relHomology_stdSimplexBoundary

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.DeltaHomology

open CategoryTheory AlgebraicTopology CategoryTheory.Limits Convexity Work.Homology

noncomputable section

variable {K : DeltaCx} {X : TopCat}

/-! ## Two elementary utilities -/

/-- The canonical homeomorphism between a subtype whose defining predicate holds for every point
and the ambient space. -/
def homeoOfForallSubtype {α : Type*} [TopologicalSpace α] (p : α → Prop) (h : ∀ x, p x) :
    ↥{x | p x} ≃ₜ α where
  toFun x := x.1
  invFun y := ⟨y, h y⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk continuous_id h

/-- **Homeomorphism invariance of relative homology.**  A homeomorphism `e : X ≃ₜ Y` carrying the
subspace `A ⊆ X` onto the subspace `B ⊆ Y` induces an isomorphism
`H_m(X, A) ≅ H_m(Y, B)` in every degree. -/
theorem relHomology_iso_of_homeomorph {X Y : TopCat} (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (he : ∀ x : X, x ∈ A ↔ e x ∈ B) (m : ℕ) :
    Nonempty (relHomology ZMod m X A ≅ relHomology ZMod m Y B) := by
  obtain ⟨inv, h1, h2⟩ :=
    (Work.HomologyExtra.isIso_relHomologyMap_pairHomOfHomeomorph e he m).out
  exact ⟨{ hom := relHomologyMap ZMod m (Work.HomologyExtra.pairHomOfHomeomorph e he),
           inv := inv, hom_inv_id := h1, inv_hom_id := h2 }⟩

/-- **Excision in open-cover form.**  If `U, A ⊆ X` are open and `U ∪ A = X`, the inclusion of
pairs `(U, U ∩ A) ⟶ (X, A)` induces an isomorphism `H_m(U, U ∩ A) ≅ H_m(X, A)`. -/
theorem relHomology_iso_of_open_cover {X : TopCat} {U A : Set X} (hU : IsOpen U) (hA : IsOpen A)
    (hcov : U ∪ A = Set.univ) (m : ℕ) :
    Nonempty (relHomology ZMod m (TopCat.of U) {y : ↥U | (y : X) ∈ A} ≅
      relHomology ZMod m X A) := by
  have hIso : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMap X U A) m) :=
    Work.Cohomology.excision_relChainsMap_isIso X U A hU hA hcov m
  obtain ⟨inv, h1, h2⟩ := hIso.out
  exact ⟨{ hom := HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap X U A) m,
           inv := inv, hom_inv_id := h1, inv_hom_id := h2 }⟩

/-- **Good pairs.**  If `A ⊆ U ⊆ X` and `A` is a deformation retract of `U`, then the map of pairs
`(X, A) ⟶ (X, U)` induces an isomorphism `H_m(X, A) ≅ H_m(X, U)`. -/
theorem relHomology_iso_of_deformationRetract {X : TopCat} {A U : Set X} (hAU : A ⊆ U)
    (h : DeformationRetract (TopCat.of U) {x : ↥U | (x : X) ∈ A}) (m : ℕ) :
    Nonempty (relHomology ZMod m X A ≅ relHomology ZMod m X U) := by
  have hIso : IsIso (relHomologyMap ZMod m (pairHomOfSubset hAU)) :=
    isIso_relHomologyMap_of_deformationRetract hAU h m
  obtain ⟨inv, h1, h2⟩ := hIso.out
  exact ⟨{ hom := relHomologyMap ZMod m (pairHomOfSubset hAU), inv := inv,
           hom_inv_id := h1, inv_hom_id := h2 }⟩

/-! ## The collar of the boundary of the standard simplex -/

/-- The boundary of the standard `n`-simplex is a deformation retract of the punctured simplex
`Δⁿ ∖ {barycentre}`: the radial collar of `exists_collar_punctStdSimplex`. -/
theorem nonempty_deformationRetract_punctStdSimplex (n : ℕ) :
    Nonempty (DeformationRetract (TopCat.of (punctStdSimplex n))
      {x : ↥(punctStdSimplex n) | (x : StdSimplex ℝ (Fin (n + 1))) ∈ StdSimplexBoundary n}) := by
  obtain ⟨H, Hzero, Hone, Hfix⟩ := exists_collar_punctStdSimplex n
  exact ⟨{ retract := TopCat.ofHom ⟨fun u => ⟨H (1, u), Hone u⟩, by
              exact Continuous.subtype_mk (H.continuous.comp (by fun_prop)) Hone⟩,
            retract_incl := by
              apply TopCat.hom_ext
              apply ContinuousMap.ext
              intro z
              apply Subtype.ext
              exact Hfix (z : ↥(punctStdSimplex n)) z.2 1,
            homotopy := ⟨ContinuousMap.Homotopy.symm (ContinuousMap.Homotopy.mk H
              (fun u => Hzero u) (fun u => rfl))⟩ }⟩

/-- The open standard `n`-simplex, the set of points of `Δⁿ` with strictly positive barycentric
weights. -/
abbrev openSimplexSet (n : ℕ) : Set (StdSimplex ℝ (Fin (n + 1))) := {w | IsOpenSimplexPoint n w}

theorem mem_openSimplexSet_iff {n : ℕ} {w : StdSimplex ℝ (Fin (n + 1))} :
    w ∈ openSimplexSet n ↔ ∀ i, 0 < w.weights i := Iff.rfl

/-- The complement of the boundary of `Δⁿ` is the open simplex. -/
theorem compl_stdSimplexBoundary_eq_openSimplexSet (n : ℕ) :
    (StdSimplexBoundary n)ᶜ = openSimplexSet n := by
  ext w
  constructor
  · intro hw i
    exact lt_of_le_of_ne (w.weights_nonneg i) (fun h => hw ⟨i, h.symm⟩)
  · intro hw
    rintro ⟨i, hi⟩
    exact absurd hi (ne_of_gt (hw i))

/-- The boundary of `Δⁿ` lies in the punctured simplex (`n ≥ 1`; for `n = 0` the punctured
simplex is empty and so is the boundary, and the statement is still true). -/
theorem stdSimplexBoundary_subset_punctStdSimplex (n : ℕ) :
    StdSimplexBoundary n ⊆ punctStdSimplex n := by
  intro w hw
  rw [mem_punctStdSimplex_iff]
  obtain ⟨i, hi⟩ := hw
  intro h
  have h' := eq_simplexBarycenter_iff_weights.mp h i
  rw [hi] at h'
  have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  exact (inv_ne_zero this) h'.symm

/-- The boundary of `Δⁿ` is closed. -/
theorem isClosed_stdSimplexBoundary (n : ℕ) : IsClosed (StdSimplexBoundary n) := by
  have : StdSimplexBoundary n = ⋃ i : Fin (n + 1),
      (fun w : StdSimplex ℝ (Fin (n + 1)) => w.weights i) ⁻¹' ({0} : Set ℝ) := by
    ext w
    simp only [StdSimplexBoundary, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff]
  rw [this]
  exact isClosed_iUnion_of_finite fun i =>
    isClosed_singleton.preimage (StdSimplex.continuous_weights_apply ℝ i)

/-- The punctured standard simplex is open. -/
theorem isOpen_punctStdSimplex (n : ℕ) : IsOpen (punctStdSimplex n) := by
  have : punctStdSimplex n = ⋃ i : Fin (n + 1),
      (fun w : StdSimplex ℝ (Fin (n + 1)) => w.weights i) ⁻¹'
        ({c : ℝ | c ≠ ((n + 1 : ℕ) : ℝ)⁻¹}) := by
    ext w
    rw [mem_punctStdSimplex_iff_exists_ne]
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_setOf_eq]
  rw [this]
  exact isOpen_iUnion fun i => isOpen_ne.preimage (StdSimplex.continuous_weights_apply ℝ i)

/-- The closure of the boundary of `Δⁿ` lies in the interior of the punctured simplex. -/
theorem closure_stdSimplexBoundary_subset_interior_punctStdSimplex (n : ℕ) :
    closure (StdSimplexBoundary n) ⊆ interior (punctStdSimplex n) := by
  rw [(isClosed_stdSimplexBoundary n).closure_eq, (isOpen_punctStdSimplex n).interior_eq]
  exact stdSimplexBoundary_subset_punctStdSimplex n


/-- The complement of the boundary of `Δⁿ`, as a set of points of `Δⁿ`. -/
theorem stdSimplexBoundary_compl_eq_openSimplexSet (n : ℕ) :
    {x : StdSimplex ℝ (Fin (n + 1)) | x ∉ StdSimplexBoundary n} = openSimplexSet n := by
  ext w
  constructor
  · intro hw i
    exact lt_of_le_of_ne (w.weights_nonneg i) (fun h => hw ⟨i, h.symm⟩)
  · intro hw
    rintro ⟨i, hi⟩
    exact absurd hi (ne_of_gt (hw i))

/-! ## The relative homology of the standard simplex pair -/

/-- **The collar**: `H_m(Δⁿ, ∂Δⁿ) ≅ H_m(Δⁿ, Δⁿ ∖ {barycentre})`, since the boundary is a
deformation retract of the punctured simplex. -/
theorem relHomology_stdSimplexBoundary_iso_punctStdSimplex (n m : ℕ) :
    Nonempty (relHomology ZMod m (TopCat.of (StdSimplex ℝ (Fin (n + 1))))
        (StdSimplexBoundary n) ≅
      relHomology ZMod m (TopCat.of (StdSimplex ℝ (Fin (n + 1)))) (punctStdSimplex n)) := by
  obtain ⟨h⟩ := nonempty_deformationRetract_punctStdSimplex n
  exact relHomology_iso_of_deformationRetract (stdSimplexBoundary_subset_punctStdSimplex n) h m

/-- **Excision of the boundary**: removing the boundary `∂Δⁿ` from the pair `(Δⁿ, Δⁿ ∖ {b})`
leaves the pair `(intΔⁿ, intΔⁿ ∖ {b})` of the open simplex. -/
theorem relHomology_punctStdSimplex_iso_openSimplexSet (n m : ℕ) :
    Nonempty (relHomology ZMod m (TopCat.of (StdSimplex ℝ (Fin (n + 1)))) (punctStdSimplex n) ≅
      relHomology ZMod m (TopCat.of (openSimplexSet n))
        {w : ↥(openSimplexSet n) |
          (w : StdSimplex ℝ (Fin (n + 1))) ≠ simplexBarycenter n}) := by
  obtain ⟨e⟩ := relHomology_excision (TopCat.of (StdSimplex ℝ (Fin (n + 1))))
    (punctStdSimplex n) (StdSimplexBoundary n)
    (closure_stdSimplexBoundary_subset_interior_punctStdSimplex n) m
  let e₀ : ↥{x : StdSimplex ℝ (Fin (n + 1)) | x ∉ StdSimplexBoundary n} ≃ₜ
      ↥(openSimplexSet n) := Homeomorph.setCongr (stdSimplexBoundary_compl_eq_openSimplexSet n)
  let S₁ : Set ↥{x : StdSimplex ℝ (Fin (n + 1)) | x ∉ StdSimplexBoundary n} :=
    {z | (z : StdSimplex ℝ (Fin (n + 1))) ∈ punctStdSimplex n}
  let S₂ : Set ↥(openSimplexSet n) :=
    {w | (w : StdSimplex ℝ (Fin (n + 1))) ≠ simplexBarycenter n}
  have he : ∀ y : ↥{x : StdSimplex ℝ (Fin (n + 1)) | x ∉ StdSimplexBoundary n},
      y ∈ S₁ ↔ e₀ y ∈ S₂ := by
    intro y
    show (y : StdSimplex ℝ (Fin (n + 1))) ∈ punctStdSimplex n ↔
      (e₀ y : StdSimplex ℝ (Fin (n + 1))) ≠ simplexBarycenter n
    rw [mem_punctStdSimplex_iff]
    rfl
  obtain ⟨e'⟩ := relHomology_iso_of_homeomorph
    (X := TopCat.of ↑{x : StdSimplex ℝ (Fin (n + 1)) | x ∉ StdSimplexBoundary n})
    (Y := TopCat.of ↑(openSimplexSet n)) (A := S₁) (B := S₂) e₀ he m
  exact ⟨e ≪≫ e'⟩

/-! ## Excision of the boundary of a cell -/

/-- **Excision of the boundary of a cell.**  The pair `(cell, cell ∖ {b})` and the pair
`(intCell, intCell ∖ {b})` have isomorphic relative homology in every degree: the boundary of the
cell is closed and contained in the interior of the punctured cell. -/
theorem relHomology_cell_intCell_iso {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n m : ℕ) (σ : Fin (K.card n)) :
    Nonempty (relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.cell n σ))
        {x : ↥(R.toDeltaSimplexMap.cell n σ) |
          (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter n σ} ≅
      relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.intCell n σ))
        {x : ↥(R.toDeltaSimplexMap.intCell n σ) |
          (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter n σ}) := by
  classical
  let χ := R.toDeltaSimplexMap
  let b : X := χ.cellBarycenter n σ
  let C : Set X := χ.cell n σ
  let A : Set ↥C := {x | (x : X) ≠ b}
  let U : Set ↥C := {x | (x : X) ∈ χ.intCell n σ}
  have hInt : χ.intCell n σ = C ∩ (⋃ i : {j : ℕ // j < n}, χ.skelSet i)ᶜ := by
    rw [DeltaSimplexMap.intCell_eq_sdiff, Set.sdiff_eq]
  have hUeq : U = (Subtype.val) ⁻¹' (⋃ i : {j : ℕ // j < n}, χ.skelSet i)ᶜ := by
    ext x
    simp only [U, Set.mem_preimage, Set.mem_setOf_eq]
    rw [hInt]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨x.2, h⟩
  have hU : IsOpen U := by
    haveI : Finite {j : ℕ // j < n} := Set.finite_Iio n
    rw [hUeq]
    exact (isClosed_iUnion_of_finite fun i : {j : ℕ // j < n} =>
      isClosed_skelSet R i).isOpen_compl.preimage continuous_subtype_val
  have hA : IsOpen A := by
    haveI : T1Space X := R.t2.t1Space
    have h : IsOpen ((Subtype.val : ↥C → X) ⁻¹' ({b}ᶜ : Set X)) :=
      (isOpen_compl_singleton (x := b)).preimage continuous_subtype_val
    have h' : A = (Subtype.val : ↥C → X) ⁻¹' ({b}ᶜ : Set X) := by
      ext x
      simp only [A, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
    rw [h']
    exact h
  have hcov : U ∪ A = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hx : (x : X) = b
    · left
      show (x : X) ∈ χ.intCell n σ
      rw [hx]
      exact DeltaSimplexMap.cellBarycenter_mem_intCell R n σ
    · exact Or.inr hx
  obtain ⟨e₁⟩ := relHomology_iso_of_open_cover (X := TopCat.of C) (U := U) (A := A) hU hA hcov m
  let eC : ↥U ≃ₜ ↥(χ.intCell n σ) :=
    (homeoSubtypes1 C (χ.intCell n σ)).trans
      (homeoOfForallSubtype (fun x : ↥(χ.intCell n σ) => (x : X) ∈ C)
        (fun x => DeltaSimplexMap.intCell_subset_cell χ n σ x.2))
  let T₁ : Set ↥U := {y | (y : ↥C) ∈ A}
  let T₂ : Set ↥(χ.intCell n σ) := {x | (x : X) ≠ b}
  have heC : ∀ y : ↥U, y ∈ T₁ ↔ eC y ∈ T₂ := by
    intro y
    show (y : ↥C) ∈ A ↔ (eC y : X) ≠ b
    rfl
  obtain ⟨e₂⟩ := relHomology_iso_of_homeomorph (X := TopCat.of ↑U)
    (Y := TopCat.of ↑(χ.intCell n σ)) (A := T₁) (B := T₂) eC heC m
  exact ⟨e₁.symm ≪≫ e₂⟩


/-! ## The open cell of a simplex -/

/-- **The open cell is the open simplex.**  The characteristic map `χ.cls n σ` restricts to a
homeomorphism from the open standard `n`-simplex to the open cell `χ.intCell n σ`
(`exists_homeomorph_intCell`), and it carries the barycentre of `Δⁿ` to the barycentre of the
cell; hence the *punctured* pairs have isomorphic relative homology. -/
theorem relHomology_intCell_openSimplex_iso {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n m : ℕ) (σ : Fin (K.card n)) :
    Nonempty (relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.intCell n σ))
        {x : ↥(R.toDeltaSimplexMap.intCell n σ) |
          (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter n σ} ≅
      relHomology ZMod m (TopCat.of (openSimplexSet n))
        {w : ↥(openSimplexSet n) |
          (w : StdSimplex ℝ (Fin (n + 1))) ≠ simplexBarycenter n}) := by
  obtain ⟨e, he⟩ := exists_homeomorph_intCell R n σ
  -- the characteristic map sends the barycentre of `Δⁿ` to the barycentre of the cell, and is
  -- injective on the open simplex
  have hkey : ∀ w : ↥(openSimplexSet n),
      (e w : X) = R.toDeltaSimplexMap.cellBarycenter n σ →
        (w : StdSimplex ℝ (Fin (n + 1))) = simplexBarycenter n := by
    intro w hw
    have h1 : R.toDeltaSimplexMap.cls n σ (w : StdSimplex ℝ (Fin (n + 1))) =
        R.toDeltaSimplexMap.cls n σ (simplexBarycenter n) := by
      rw [← he w, hw]
      rfl
    exact (eq_of_cls_eq_of_pos R w.2 h1).2
  have hAB : ∀ w : ↥(openSimplexSet n),
      w ∈ ({w : ↥(openSimplexSet n) |
          (w : StdSimplex ℝ (Fin (n + 1))) ≠ simplexBarycenter n} : Set _) ↔
        e w ∈ ({x : ↥(R.toDeltaSimplexMap.intCell n σ) |
          (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter n σ} : Set _) := by
    intro w
    exact ⟨fun h hh => h (hkey w hh), fun h hh => h (by rw [he w, hh]; rfl)⟩
  exact ⟨(relHomology_iso_of_homeomorph
    (X := TopCat.of ↑(openSimplexSet n)) (Y := TopCat.of ↑(R.toDeltaSimplexMap.intCell n σ))
    (A := {w : ↥(openSimplexSet n) |
      (w : StdSimplex ℝ (Fin (n + 1))) ≠ simplexBarycenter n})
    (B := {x : ↥(R.toDeltaSimplexMap.intCell n σ) |
      (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter n σ}) e hAB m).some.symm⟩

/-! ## The local homology of a cell -/

/-- **The local homology of a cell is that of a disc.**  For a realized `Δ`-complex and an
`n`-simplex `σ`, the relative homology of the pair consisting of the closed cell `χ.cell n σ`
and that cell with its barycentre removed is `ℤ` in degree `n` and `0` in every other degree.

This is assembled from four isomorphisms of relative homology: excision of the boundary of the
cell (`relHomology_cell_intCell_iso`), the homeomorphism between the open cell and the open
simplex (`relHomology_intCell_openSimplex_iso`), the excision of the boundary of the standard
simplex (`relHomology_punctStdSimplex_iso_openSimplexSet`, reversed) and the collar
(`relHomology_stdSimplexBoundary_iso_punctStdSimplex`, reversed), reducing to the computation
`relHomology_stdSimplexBoundary`. -/
theorem cell_relHomology_iso {K : DeltaCx} {X : TopCat} (R : DeltaRealization K X)
    (n : ℕ) (σ : Fin (K.card n)) (m : ℕ) :
    Nonempty (relHomology ZMod m (TopCat.of (R.toDeltaSimplexMap.cell n σ))
        {x : ↥(R.toDeltaSimplexMap.cell n σ) |
          (x : X) ≠ R.toDeltaSimplexMap.cellBarycenter n σ} ≅
      (if m = n then ModuleCat.of ℤ ℤ else ModuleCat.of ℤ PUnit)) := by
  obtain ⟨e₁⟩ := relHomology_cell_intCell_iso R n m σ
  obtain ⟨e₂⟩ := relHomology_intCell_openSimplex_iso R n m σ
  obtain ⟨e₃⟩ := relHomology_punctStdSimplex_iso_openSimplexSet n m
  obtain ⟨e₄⟩ := relHomology_stdSimplexBoundary_iso_punctStdSimplex n m
  obtain ⟨e₅⟩ := relHomology_stdSimplexBoundary n m
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃.symm ≪≫ e₄.symm ≪≫ e₅⟩

end

end Work.DeltaHomology
