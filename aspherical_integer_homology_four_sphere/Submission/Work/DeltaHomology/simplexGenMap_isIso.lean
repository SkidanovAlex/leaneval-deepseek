import Mathlib
import Submission.Work.HomologyExtra.SimplexClass
import Submission.Work.HomologyExtra.GeneratorReduction
import Submission.Work.HomologyExtra.epi_simplexBoundaryClass
import Submission.Work.HomologyExtra.SimplexPairHomology

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.DeltaHomology

open Work.HomologyExtra

noncomputable section

/-! ## The case `n = 1`

For `n = 1` the connecting map of the pair `(Δ¹, ∂Δ¹)` is injective but not surjective, so the
general argument does not apply.  Instead we produce an explicit retraction of
`simplexGenMap 1`: the functional on `H₀(∂Δ¹; ℤ)` which reads off the coefficient of the
component of the first vertex agrees with `1` on the class `[v₀] - [v₁]` of the fundamental
cycle of `∂Δ¹`, whence `simplexGenMap 1 ≫ (pairδ ≫ pr) = 𝟙` and `simplexGenMap 1` is an
epimorphism — and an epimorphism `ℤ ⟶ ℤ` is an isomorphism. -/

/-- The vertex of `∂Δ¹` that is the value of the `i`-th `0`-face simplex. -/
def bndVertex (i : Fin 2) : boundarySpace 1 :=
  simplexFaceToBoundaryCM 0 i (Convexity.StdSimplex.single 0)

/-- The `i`-th `0`-face simplex of the fundamental cycle of `∂Δ¹` is the point `bndVertex i`. -/
lemma simplexBoundaryFaceSimplex_zero_eq (i : Fin 2) :
    simplexBoundaryFaceSimplex 0 i = simplexPoint (X := boundarySpace 1) (bndVertex i) := by
  apply simplexPoint_eq_of_apply_eq
  intro z
  rw [toSSetObjEquiv_simplexOf]
  have hz : z = Convexity.StdSimplex.single (0 : Fin 1) := Subsingleton.elim _ _
  rw [hz]
  rfl

lemma bndVertex_eq (i : Fin 2) :
    bndVertex i = (⟨Convexity.StdSimplex.single (i.succAbove 0),
      ⟨i, by rw [Convexity.StdSimplex.weights_single]; simp⟩⟩ :
        boundarySpace 1) := by
  unfold bndVertex
  simp only [simplexFaceToBoundaryCM, ContinuousMap.coe_mk, Subtype.mk.injEq]
  show Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.single 0)
    = Convexity.StdSimplex.single (i.succAbove 0)
  rw [Convexity.StdSimplex.map_single]

lemma bndVertex_weights (i : Fin 2) (j : Fin 2) :
    (bndVertex i : simplex 1).weights j = if j = i.succAbove 0 then 1 else 0 := by
  rw [bndVertex_eq i, Convexity.StdSimplex.weights_single]
  by_cases h : j = i.succAbove 0
  · simp [h]
  · simp [h, Finsupp.single_eq_of_ne (Ne.symm h)]

lemma bndVertex_zero_weights_zero : (bndVertex 0 : simplex 1).weights 0 = 0 := by
  rw [bndVertex_weights]; simp [Fin.succAbove]

lemma bndVertex_one_weights_zero : (bndVertex 1 : simplex 1).weights 0 = 1 := by
  rw [bndVertex_weights]; simp [Fin.succAbove]

/-- In `∂Δ¹` the first barycentric coordinate takes only the values `0` and `1`. -/
lemma bndWeight_zero_or_one (x : boundarySpace 1) :
    (x : simplex 1).weights 0 = 0 ∨ (x : simplex 1).weights 0 = 1 := by
  obtain ⟨i, hi⟩ := x.2
  have hsum : (x : simplex 1).weights 0 + (x : simplex 1).weights 1 = 1 := by
    have h := (x : simplex 1).total_of_fintype
    rwa [Fin.sum_univ_two] at h
  fin_cases i
  · exact Or.inl hi
  · right
    have hi' : (x : simplex 1).weights (1 : Fin 2) = 0 := hi
    linarith

/-- The two vertices of `∂Δ¹` lie in different path components. -/
lemma not_joined_bndVertex : ¬ Joined (bndVertex 0) (bndVertex 1) := by
  rintro ⟨p⟩
  have hcont : Continuous fun t : unitInterval =>
      (((p t : boundarySpace 1)) : simplex 1).weights 0 :=
    (Convexity.StdSimplex.continuous_weights_apply ℝ (0 : Fin 2)).comp
      (continuous_subtype_val.comp p.continuous)
  have h0 : ((((p 0 : boundarySpace 1)) : simplex 1).weights 0) = 0 := by
    rw [show p 0 = bndVertex 0 from p.source, bndVertex_zero_weights_zero]
  have h1 : ((((p 1 : boundarySpace 1)) : simplex 1).weights 0) = 1 := by
    rw [show p 1 = bndVertex 1 from p.target, bndVertex_one_weights_zero]
  have hmem : (1/2 : ℝ) ∈ Set.Icc ((((p 0 : boundarySpace 1)) : simplex 1).weights 0)
      ((((p 1 : boundarySpace 1)) : simplex 1).weights 0) := by rw [h0, h1]; norm_num
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc (a := (0 : unitInterval)) (b := 1)
    zero_le_one hcont.continuousOn hmem
  have ht' : ((((p t : boundarySpace 1)) : simplex 1).weights 0) = 1/2 := ht
  rcases bndWeight_zero_or_one (p t) with h | h <;> linarith

lemma piZero_mk_bndVertex_ne :
    SSet.π₀.mk (simplexPoint (X := boundarySpace 1) (bndVertex 0))
      ≠ SSet.π₀.mk (simplexPoint (X := boundarySpace 1) (bndVertex 1)) := by
  intro h
  have h3 : ZerothHomotopy.mk (bndVertex 0) = ZerothHomotopy.mk (bndVertex 1) := by
    have h4 := congrArg TopCat.zerothHomotopyEquiv.symm h
    rw [TopCat.zerothHomotopyEquiv_symm_mk, TopCat.zerothHomotopyEquiv_symm_mk] at h4
    rw [toSSetObj₀Equiv_simplexPoint, toSSetObj₀Equiv_simplexPoint] at h4
    exact h4
  exact not_joined_bndVertex (Quotient.exact h3)

abbrev bndSSet : SSet := TopCat.toSSet.obj (boundarySpace 1)

/-- The functional on `H₀(∂Δ¹; ℤ)` reading off the coefficient of the component of
`bndVertex 0`. -/
def bndPsi : Work.Homology.singHomology Work.Homology.ZMod 0 (boundarySpace 1)
    ⟶ Work.Homology.ZMod := by
  classical
  exact (bndSSet.homology₀Iso Work.Homology.ZMod).hom ≫
    Sigma.desc (fun c => if c = SSet.π₀.mk (simplexPoint (X := boundarySpace 1) (bndVertex 0))
      then 𝟙 Work.Homology.ZMod else 0)

lemma sbChain_zero_eq :
    simplexBoundaryChain 0
      = simplexBoundaryFaceChain 0 0 - simplexBoundaryFaceChain 0 1 := by
  simp [simplexBoundaryChain, Fin.sum_univ_two, sub_eq_add_neg]

lemma sbChain_zero_eq' :
    simplexBoundaryChain 0
      = bndSSet.ιChainComplex (simplexBoundaryFaceSimplex 0 0)
        - bndSSet.ιChainComplex (simplexBoundaryFaceSimplex 0 1) := by
  rw [sbChain_zero_eq]

lemma sbChain_zero_d' :
    (bndSSet.ιChainComplex (simplexBoundaryFaceSimplex 0 0)
        - bndSSet.ιChainComplex (simplexBoundaryFaceSimplex 0 1)) ≫
      (bndSSet.chainComplex Work.Homology.ZMod).d 0 ((ComplexShape.down ℕ).next 0) = 0 := by
  rw [← sbChain_zero_eq']
  exact simplexBoundaryChain_d 0

lemma sbClass_zero_A : simplexBoundaryClass 0
    = cycleClass (bndSSet.ιChainComplex (simplexBoundaryFaceSimplex 0 0)
        - bndSSet.ιChainComplex (simplexBoundaryFaceSimplex 0 1)) sbChain_zero_d' := by
  unfold simplexBoundaryClass
  rw [sbChain_zero_eq']

/-- **The functional `bndPsi` pairs to `1` with the fundamental class of `∂Δ¹`.** -/
lemma bnd_class : simplexBoundaryClass 0 ≫ bndPsi = 𝟙 Work.Homology.ZMod := by
  have h0 : bndSSet.ιChainComplex (simplexBoundaryFaceSimplex 0 0) ≫
      (bndSSet.chainComplex Work.Homology.ZMod).d 0 ((ComplexShape.down ℕ).next 0) = 0 :=
    iChainComplex_d_next_zero bndSSet _ _
  have h1 : bndSSet.ιChainComplex (simplexBoundaryFaceSimplex 0 1) ≫
      (bndSSet.chainComplex Work.Homology.ZMod).d 0 ((ComplexShape.down ℕ).next 0) = 0 :=
    iChainComplex_d_next_zero bndSSet _ _
  rw [sbClass_zero_A, cycleClass_sub _ _ h0 h1 sbChain_zero_d', Preadditive.sub_comp]
  dsimp only [bndPsi]
  rw [← Category.assoc, cycleClass_ιChainComplex_homology₀Iso bndSSet Work.Homology.ZMod
    (simplexBoundaryFaceSimplex 0 0) h0]
  rw [← Category.assoc, cycleClass_ιChainComplex_homology₀Iso bndSSet Work.Homology.ZMod
    (simplexBoundaryFaceSimplex 0 1) h1]
  rw [Sigma.ι_comp_desc, Sigma.ι_comp_desc, simplexBoundaryFaceSimplex_zero_eq 0,
    simplexBoundaryFaceSimplex_zero_eq 1]
  rw [if_pos rfl, if_neg (fun h => piZero_mk_bndVertex_ne h.symm), sub_zero]

/-- **`simplexGenMap 1` is an isomorphism**: the class of the identity `1`-simplex generates
`H₁(Δ¹, ∂Δ¹; ℤ) ≅ ℤ`. -/
lemma simplexGenMap_one_isIso : IsIso (Work.HomologyExtra.simplexGenMap 1) := by
  have hcomp : Work.HomologyExtra.simplexGenMap 1 ≫
      (Work.Homology.pairδ Work.Homology.ZMod (Work.HomologyExtra.simplex 1)
        (Work.HomologyExtra.simplexBoundary 1) 0 ≫ bndPsi) = 𝟙 Work.Homology.ZMod := by
    rw [← Category.assoc, simplexGenMap_pairdelta 0]
    exact bnd_class
  haveI : Epi (Work.HomologyExtra.simplexGenMap 1) :=
    epi_of_comp_eq_id_of_iso_zmod (relHomology_simplexPair_top 1 le_rfl).some
      (Work.HomologyExtra.simplexGenMap 1)
      (Work.Homology.pairδ Work.Homology.ZMod (Work.HomologyExtra.simplex 1)
        (Work.HomologyExtra.simplexBoundary 1) 0 ≫ bndPsi) hcomp
  exact isIso_simplexGenMap_of_epi 1 ‹Epi (Work.HomologyExtra.simplexGenMap 1)›
    (relHomology_simplexPair_top 1 le_rfl)

end

/-- **The class of the identity simplex generates the top relative homology of the simplex pair.**
`Work.HomologyExtra.simplexGenMap n : ℤ ⟶ Hₙ(Δⁿ, ∂Δⁿ; ℤ)` is an isomorphism for `n ≥ 1`, i.e. the
class of the identity singular simplex is a generator of `Hₙ(Δⁿ, ∂Δⁿ; ℤ) ≅ ℤ` (the local degree
of the identity is `1`).  All the ingredients are already proved in
`Submission/Work/HomologyExtra/`; this statement only assembles them (you may add further imports
of that directory as needed, e.g. `Submission.Work.HomologyExtra.SimplexPairHomology`).

Route: for `n ≥ 2` write `n = k + 2` and use `Work.HomologyExtra.isIso_simplexGenMap_of_epi`
(`Submission/Work/HomologyExtra/GeneratorReduction.lean`) applied to
`Work.HomologyExtra.epi_simplexGenMap_of_epi_simplexBoundaryClass k`
(`Submission/Work/HomologyExtra/epi_simplexBoundaryClass.lean`), which in turn needs
`Work.HomologyExtra.epi_simplexBoundaryClass (k+1) (by omega)` (proved there by the Mayer–Vietoris
induction); the required `Hₙ(Δⁿ,∂Δⁿ) ≅ ℤ` is `Work.HomologyExtra.relHomology_simplexPair_top`.  The
case `n = 1` must be handled separately: the connecting map of the pair `(Δ¹, ∂Δ¹)` is injective
but not surjective, so use the explicit description of `H₁(Δ¹, ∂Δ¹)` as the kernel of
`H₀(∂Δ¹) ≅ ℤ² → H₀(Δ¹) ≅ ℤ` together with `Work.HomologyExtra.simplexGenMap_pairdelta 0`, or the
corresponding results in `Submission/Work/HomologyExtra/simplexBoundary_homologyOne.lean`. -/
theorem simplexGenMap_isIso (n : ℕ) (hn : 1 ≤ n) :
    IsIso (Work.HomologyExtra.simplexGenMap n) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    exact simplexGenMap_one_isIso
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    exact isIso_simplexGenMap_of_epi (k + 2)
      (epi_simplexGenMap_of_epi_simplexBoundaryClass k
        (epi_simplexBoundaryClass (k + 1) (by omega)))
      (relHomology_simplexPair_top (k + 2) (by omega))

end Work.DeltaHomology
