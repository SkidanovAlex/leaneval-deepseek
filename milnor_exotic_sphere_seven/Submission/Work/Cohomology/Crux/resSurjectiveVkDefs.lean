import Mathlib
import Submission.Work.Cohomology.Crux.vkOvlDefs
import Submission.Work.Cohomology.Ovl.OvlDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.Cohomology.Crux

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology

noncomputable section

/-- The chart homeomorphism `ℝ⁴ × ℍ ≅ U` of the first chart of `Vk (-2)`. -/
def chartU : Submission.Milnor.MSpace8 ≃ₜ ↥vkU :=
  (Submission.Milnor.vData (-2)).isOpenEmbedding_ιX.isEmbedding.toHomeomorph

theorem chartU_coe (p : Submission.Milnor.MSpace8) :
    ((chartU p : ↥vkU) : vkPairX) = (Submission.Milnor.vData (-2)).ιX p := rfl

/-- The base point over which the detecting fibre sits. -/
def basePt : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single (0 : Fin 4) (1 : ℝ)

theorem basePt_ne_zero : basePt ≠ 0 := by
  intro h
  have h1 : ‖basePt‖ = 1 := by
    rw [basePt, EuclideanSpace.norm_single]
    norm_num
  rw [h, norm_zero] at h1
  norm_num at h1

/-- The fibre `{x = basePt}` of the first chart, a copy of `ℍ`. -/
abbrev fibU : Set ↥vkU := {y | (chartU.symm y).1 = basePt}

/-- The sphere bundle `Mk (-2)` over the first chart. -/
abbrev AU : Set ↥vkU :=
  {y | (y : Submission.Milnor.Vk (-2)) ∈ Set.range (Work.Milnor.mkToVkFun (-2))}

/-- In the chart, the sphere bundle is `{‖·‖ = 1}` on the fibre coordinate. -/
theorem AU_chart (p : Submission.Milnor.MSpace8) :
    (chartU p : ↥vkU) ∈ AU ↔ ‖p.2‖ = 1 := by
  show ((chartU p : ↥vkU) : Submission.Milnor.Vk (-2)) ∈
      Set.range (Work.Milnor.mkToVkFun (-2)) ↔ ‖p.2‖ = 1
  rw [chartU_coe, Work.Milnor.mem_range_mkToVkFun_iff, Work.Milnor.fibreNormFun_ιX]

/-- The detecting fibre lies in the overlap of the two charts. -/
theorem fibU_subset_W (z : ↥vkU) (hz : z ∈ fibU) :
    (z : vkPairX) ∈ vkU ∩ vkV := by
  refine ⟨z.2, ?_⟩
  have hne : (chartU.symm z).1 ≠ 0 := by
    intro h0
    have hz' : (chartU.symm z).1 = basePt := hz
    rw [h0] at hz'
    exact basePt_ne_zero hz'.symm
  have hmem : chartU.symm z ∈ (Submission.Milnor.vData (-2)).U := by
    have h : chartU.symm z ∈ Submission.Milnor.vOpens := Submission.Milnor.mem_vOpens.mpr hne
    exact h
  have hX : (z : vkPairX) = (Submission.Milnor.vData (-2)).ιX (chartU.symm z) := by
    rw [← chartU_coe (chartU.symm z), Homeomorph.apply_symm_apply]
  rw [hX]
  exact Set.mem_range.mpr ⟨(Submission.Milnor.vData (-2)).φ (chartU.symm z),
    ((Submission.Milnor.vData (-2)).ιX_eq_ιY_iff.mpr ⟨hmem, rfl⟩).symm⟩

/-! ## The spaces -/

/-- The first chart as a space. -/
abbrev USpace : TopCat := TopCat.of ↥vkU

/-- The detecting fibre as a space. -/
abbrev FibSpace : TopCat := TopCat.of ↥fibU

/-- The overlap `U ∩ V` of the two charts, as a space. -/
abbrev WSpace : TopCat := TopCat.of ↥(vkU ∩ vkV)

/-- The sphere-bundle part of the detecting fibre, as a subset of `fibU`. -/
abbrev fibA : Set ↥fibU := {z | (z : ↥vkU) ∈ AU}

/-- The sphere bundle over the detecting fibre, as a space. -/
abbrev FibASpace : TopCat := TopCat.of ↥fibA

/-- The sphere bundle over the first chart, as a space. -/
abbrev AUSpace : TopCat := TopCat.of ↥AU

/-- The sphere bundle over the overlap `(U ∩ V) ∩ Mk(-2)`. -/
abbrev ovlASet : Set ↥(vkU ∩ vkV) := vkOvlA

/-! ## The canonical maps -/

/-- The inclusion `fibU ⊆ U`. -/
abbrev inclFibU : FibSpace ⟶ USpace := subtypeIncl USpace fibU

/-- The inclusion `fibA ⊆ AU`. -/
abbrev inclFibA : FibASpace ⟶ AUSpace :=
  TopCat.ofHom ⟨fun x : ↥fibA => (⟨((x : ↥fibU) : ↥vkU), x.2⟩ : ↥AU),
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
      (fun x : ↥fibA => x.2)⟩

/-- The inclusion `fibU ⊆ U ∩ V`. -/
abbrev inclFibW : FibSpace ⟶ WSpace :=
  TopCat.ofHom ⟨fun z : ↥fibU =>
      (⟨((z : ↥vkU) : vkPairX), fibU_subset_W (z : ↥vkU) z.2⟩ : ↥(vkU ∩ vkV)),
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
      (fun z : ↥fibU => fibU_subset_W (z : ↥vkU) z.2)⟩

/-- The inclusion `U ∩ V ⊆ U`. -/
abbrev inclWU : WSpace ⟶ USpace :=
  TopCat.ofHom ⟨fun z : ↥(vkU ∩ vkV) => (⟨(z : vkPairX), z.2.1⟩ : ↥vkU),
    Continuous.subtype_mk continuous_subtype_val (fun z : ↥(vkU ∩ vkV) => z.2.1)⟩

theorem inclFibW_comp_inclWU : inclFibW ≫ inclWU = inclFibU := by
  apply TopCat.hom_ext
  ext z
  rfl


/-! ## The canonical maps of relative cochain complexes

The implicit space arguments of `relComplexMap` are passed explicitly: with them inferred the
unifier blows up on the (large) `relComplex` types.  See `Endgame/vkOvlRestrNeZero.lean` §33. -/

/-- The map `H⁴(X,A) → H⁴(U, U ∩ A)` of relative cochains induced by the inclusion of pairs
`(U, U ∩ A) → (X, A)`. -/
noncomputable def rUmap : relComplex ℤ vkPairX vkPairA ⟶ relComplex ℤ USpace AU :=
  relComplexMap (X₁ := USpace) (X₂ := vkPairX) ℤ AU vkPairA
    (subtypeIncl vkPairX vkU) (fun _ hx => hx)

/-- The map `H⁴(U, U ∩ A) → H⁴(U ∩ V, ovlA)` of relative cochains induced by the inclusion of
pairs `(U ∩ V, ovlA) → (U, U ∩ A)`. -/
noncomputable def rhoUmap : relComplex ℤ USpace AU ⟶ relComplex ℤ WSpace ovlASet :=
  relComplexMap (X₁ := WSpace) (X₂ := USpace) ℤ ovlASet AU inclWU (fun _ hx => hx)

/-- The map `H⁴(X, A) → H⁴(U ∩ V, ovlA)` of relative cochains induced by the inclusion of pairs
`(U ∩ V, ovlA) → (X, A)`. -/
noncomputable def rhoMap : relComplex ℤ vkPairX vkPairA ⟶ relComplex ℤ WSpace ovlASet :=
  relComplexMap (X₁ := WSpace) (X₂ := vkPairX) ℤ ovlASet vkPairA
    (subtypeIncl vkPairX (vkU ∩ vkV)) (fun _ hx => hx)

/-- The map `H⁴(U, U ∩ A) → H⁴(fib, fibA)` of relative cochains induced by the inclusion of pairs
`(fib, fibA) → (U, U ∩ A)`. -/
noncomputable def thetaMap : relComplex ℤ USpace AU ⟶ relComplex ℤ FibSpace fibA :=
  relComplexMap (X₁ := FibSpace) (X₂ := USpace) ℤ fibA AU inclFibU (fun _ hx => hx)

/-- The map `H⁴(U ∩ V, ovlA) → H⁴(fib, fibA)` of relative cochains induced by the inclusion of
pairs `(fib, fibA) → (U ∩ V, ovlA)`. -/
noncomputable def etaMap : relComplex ℤ WSpace ovlASet ⟶ relComplex ℤ FibSpace fibA :=
  relComplexMap (X₁ := FibSpace) (X₂ := WSpace) ℤ fibA ovlASet inclFibW (fun _ hx => hx)

/-- The inclusion `U ∩ V ⊆ U` followed by `U ⊆ X` is the inclusion `U ∩ V ⊆ X`. -/
theorem inclWU_comp_subtypeIncl :
    inclWU ≫ subtypeIncl vkPairX vkU = subtypeIncl vkPairX (vkU ∩ vkV) := by
  apply TopCat.hom_ext
  ext z
  rfl

/-- `relComplexMap` does not depend on the proof that the first set is carried into the second. -/
theorem relComplexMap_hcongr {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) (f : X₁ ⟶ X₂)
    (h h' : ∀ x ∈ A₁, f x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h = relComplexMap ℤ A₁ A₂ f h' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- `relComplexMap` does not depend on the chosen spelling of the map of pairs. -/
theorem relComplexMap_congr_map {X₁ X₂ : TopCat} (A₁ : Set X₁) (A₂ : Set X₂) {f g : X₁ ⟶ X₂}
    (hfg : f = g) (h : ∀ x ∈ A₁, f x ∈ A₂) (h' : ∀ x ∈ A₁, g x ∈ A₂) :
    relComplexMap ℤ A₁ A₂ f h = relComplexMap ℤ A₁ A₂ g h' := by
  subst hfg
  exact relComplexMap_hcongr A₁ A₂ _ h h'

/-- **Factorization of the restriction to the overlap through the first chart:**
`ρ = rU ≫ ρ₁`. -/
theorem rhoMap_comp : rhoMap = rUmap ≫ rhoUmap := by
  rw [rUmap, rhoUmap]
  calc rhoMap
      = relComplexMap (X₁ := WSpace) (X₂ := vkPairX) ℤ ovlASet vkPairA
          (subtypeIncl vkPairX (vkU ∩ vkV)) (fun _ hx => hx) := rfl
    _ = relComplexMap (X₁ := WSpace) (X₂ := vkPairX) ℤ ovlASet vkPairA
          (inclWU ≫ subtypeIncl vkPairX vkU) (fun _ hx => hx) :=
        relComplexMap_congr_map (X₁ := WSpace) (X₂ := vkPairX) ovlASet vkPairA
          inclWU_comp_subtypeIncl.symm (fun _ hx => hx) (fun _ hx => hx)
    _ = relComplexMap (X₁ := USpace) (X₂ := vkPairX) ℤ AU vkPairA
            (subtypeIncl vkPairX vkU) (fun _ hx => hx)
          ≫ relComplexMap (X₁ := WSpace) (X₂ := USpace) ℤ ovlASet AU inclWU (fun _ hx => hx) :=
        Work.Cohomology.Ovl.relComplexMap_comp_ovl (X₁ := WSpace) (X₂ := USpace) (X₃ := vkPairX) ovlASet AU vkPairA
          inclWU (subtypeIncl vkPairX vkU) (fun _ hx => hx) (fun _ hx => hx)

/-- **Factorization of the restriction to the detecting fibre through the overlap:**
`θ = ρ₁ ≫ η`. -/
theorem thetaMap_comp : thetaMap = rhoUmap ≫ etaMap := by
  rw [rhoUmap, etaMap]
  calc thetaMap
      = relComplexMap (X₁ := FibSpace) (X₂ := USpace) ℤ fibA AU inclFibU (fun _ hx => hx) := rfl
    _ = relComplexMap (X₁ := FibSpace) (X₂ := USpace) ℤ fibA AU
          (inclFibW ≫ inclWU) (fun _ hx => hx) :=
        relComplexMap_congr_map (X₁ := FibSpace) (X₂ := USpace) fibA AU
          inclFibW_comp_inclWU.symm (fun _ hx => hx) (fun _ hx => hx)
    _ = relComplexMap (X₁ := WSpace) (X₂ := USpace) ℤ ovlASet AU inclWU (fun _ hx => hx)
          ≫ relComplexMap (X₁ := FibSpace) (X₂ := WSpace) ℤ fibA ovlASet inclFibW
              (fun _ hx => hx) :=
        Work.Cohomology.Ovl.relComplexMap_comp_ovl (X₁ := FibSpace) (X₂ := WSpace) (X₃ := USpace) fibA ovlASet AU
          inclFibW inclWU (fun _ hx => hx) (fun _ hx => hx)

end
end Work.Cohomology.Crux
