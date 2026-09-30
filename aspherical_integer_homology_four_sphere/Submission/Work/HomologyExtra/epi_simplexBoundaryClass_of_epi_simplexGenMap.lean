import Mathlib
import Submission.Work.HomologyExtra.SimplexStar
import Submission.Work.HomologyExtra.GeneratorReduction
import Submission.Work.HomologyExtra.simplexStar_contractible
import Submission.Work.HomologyExtra.cycleClass_naturality
import Submission.Work.HomologyExtra.simplexBoundaryChain_d
import Submission.Work.HomologyExtra.simplexRelChain_d
import Submission.Work.Homology.Corollaries
import Submission.Work.Homology.BallHomology
import Submission.Work.HomologyExtra.relHomologyMap_simplexFacePairHom_epi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Epi (simplexGenMap n) → Epi (simplexBoundaryClass n)`

The geometric transfer from the pair `(Δⁿ, ∂Δⁿ)` to the sphere `∂Δⁿ⁺¹`: the fundamental cycle
`zₙ = ∑ᵢ (-1)ⁱ Fᵢ` of `∂Δⁿ⁺¹` splits as `zₙ = z_B + (-1)^last • F_last`, where `z_B` is carried by
the closed star `B` of the last vertex.  Hence in the relative homology `Hₙ(∂Δⁿ⁺¹, B)` the class of
`zₙ` is (up to sign) the class of the face `F_last`, which is the image of the class of the identity
simplex of `Δⁿ` under the map of pairs `(Δⁿ, ∂Δⁿ) → (∂Δⁿ⁺¹, B)`.

Since `B` is contractible, `Hₙ(∂Δⁿ⁺¹) → Hₙ(∂Δⁿ⁺¹, B)` is injective, and the conclusion follows:
`simplexBoundaryClass n` is an epimorphism as soon as `simplexGenMap n` is.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

namespace Work.HomologyExtra

noncomputable section

/-! ## Elementary rewriting lemmas -/

/-- The `n`-simplex of the singular simplicial set of `Y` induced by a map `g : Δⁿ ⟶ Y` is the
image of the identity simplex of `Δⁿ` under `g`. -/
lemma toSSet_map_simplexId {n : ℕ} {Y : TopCat} (g : simplex n ⟶ Y) :
    (TopCat.toSSet.map g).app (Opposite.op (SimplexCategory.mk n)) (simplexId n) =
      simplexOf n g.hom := by
  apply (TopCat.toSSetObjEquiv Y _).injective
  ext z
  rw [toSSetObjEquiv_simplexOf, toSSetObjEquiv_map_apply, toSSetObjEquiv_simplexId]
  rfl

/-- The chain of the identity simplex of `Δⁿ`, pushed forward along the last face map, is the chain
of the last face of `∂Δⁿ⁺¹`. -/
theorem simplexIdChain_comp_singChainMap_lastFace (n : ℕ) :
    simplexIdChain n ≫ (Work.Homology.singChainMap Work.Homology.ZMod
        (simplexFaceToBoundary n (Fin.last (n + 1)))).f n =
      simplexBoundaryFaceChain n (Fin.last (n + 1)) := by
  show SSet.ιChainComplex (TopCat.toSSet.obj (simplex n)) (simplexId n) ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (simplexFaceToBoundary n (Fin.last (n + 1))))
        Work.Homology.ZMod).f n = _
  rw [SSet.ι_chainComplexMap_f, toSSet_map_simplexId]
  rfl

/-- The inclusion of the chains of a subspace followed by the projection to the relative chains is
zero, in every degree. -/
theorem inclChain_f_comp_relProj_f_gen (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (m : ℕ) :
    (Work.Homology.inclChain R X A).f m ≫ (Work.Homology.relProj R X A).f m = 0 := by
  rw [← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f]

/-! ## The closed star part of the fundamental cycle -/

/-- The `i`-th face of `Δⁿ⁺¹` (`i ≠ last`), viewed as a simplex of the closed star
`B = simplexStar n` of the last vertex. -/
noncomputable def simplexFaceStarSimplex (n : ℕ) (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
    (TopCat.toSSet.obj (TopCat.of (simplexStar n))).obj (Opposite.op (SimplexCategory.mk n)) :=
  simplexOf n ⟨fun w => ⟨⟨simplexFace n i w, simplexFace_mem_boundary n i w⟩,
      simplexFaceToBoundary_mem_star n i hi w⟩, by fun_prop⟩

/-- The inclusion of the closed star sends `simplexFaceStarSimplex` to the corresponding face of the
boundary. -/
theorem incl_simplexFaceStarSimplex (n : ℕ) (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
    (TopCat.toSSet.map (Work.Homology.incl (simplexStar n))).app
        (Opposite.op (SimplexCategory.mk n)) (simplexFaceStarSimplex n i hi) =
      simplexBoundaryFaceSimplex n i := by
  apply (TopCat.toSSetObjEquiv (boundarySpace (n + 1)) _).injective
  simp only [toSSetObjEquiv_map_apply, toSSetObjEquiv_simplexOf, simplexFaceStarSimplex]
  rfl

/-- The chain of the `i`-th face (`i ≠ last`) lies in the image of the chains of the closed star of
the last vertex. -/
theorem simplexBoundaryFaceChain_eq_star (n : ℕ) (i : Fin (n + 2)) (hi : i ≠ Fin.last (n + 1)) :
    simplexBoundaryFaceChain n i =
      simpChain n (simplexFaceStarSimplex n i hi) ≫
        (Work.Homology.inclChain Work.Homology.ZMod (boundarySpace (n + 1))
          (simplexStar n)).f n := by
  have h := SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of (simplexStar n)))
      (Y := TopCat.toSSet.obj (boundarySpace (n + 1)))
      (f := TopCat.toSSet.map (Work.Homology.incl (simplexStar n)))
      (R := Work.Homology.ZMod) (x := simplexFaceStarSimplex n i hi)
  show SSet.ιChainComplex (TopCat.toSSet.obj (boundarySpace (n + 1)))
        (simplexBoundaryFaceSimplex n i) =
      SSet.ιChainComplex (TopCat.toSSet.obj (TopCat.of (simplexStar n)))
        (simplexFaceStarSimplex n i hi) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (Work.Homology.incl (simplexStar n)))
          Work.Homology.ZMod).f n
  rw [h, incl_simplexFaceStarSimplex n i hi]

/-- The part of the fundamental cycle carried by the closed star of the last vertex is killed by the
projection onto the relative chains of the pair `(∂Δⁿ⁺¹, B)`. -/
theorem simplexStarPartChain_comp_relProj (n : ℕ) :
    simplexStarPartChain n ≫ (Work.Homology.relProj Work.Homology.ZMod
        (boundarySpace (n + 1)) (simplexStar n)).f n = 0 := by
  rw [simplexStarPartChain, Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_erase] at hi
  obtain ⟨hine, -⟩ := hi
  rw [Preadditive.zsmul_comp, simplexBoundaryFaceChain_eq_star n i hine, Category.assoc,
    inclChain_f_comp_relProj_f_gen, comp_zero, smul_zero]

/-- The sign of the last face in the fundamental cycle. -/
def lastSign (n : ℕ) : ℤ := (-1 : ℤ) ^ ((Fin.last (n + 1) : Fin (n + 2)) : ℕ)

theorem lastSign_sq (n : ℕ) : lastSign n * lastSign n = 1 := by
  rw [lastSign, ← pow_two, ← pow_mul, mul_comm ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) 2, pow_mul]
  norm_num

/-- The fundamental cycle splits into the part carried by the closed star and the last face. -/
theorem simplexBoundaryChain_eq_starPart_add (n : ℕ) :
    simplexBoundaryChain n = simplexStarPartChain n +
      lastSign n • simplexBoundaryFaceChain n (Fin.last (n + 1)) := by
  rw [simplexBoundaryChain, simplexStarPartChain, lastSign]
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ _)).symm

/-! ## `cycleClass` and scalar multiplication -/

theorem liftCycles_zsmul {K : ChainComplex (ModuleCat ℤ) ℕ} {A : ModuleCat ℤ} {i j : ℕ}
    (c : ℤ) (k : A ⟶ K.X i) (hj : (ComplexShape.down ℕ).next i = j)
    (hk : k ≫ K.d i j = 0) (hk' : (c • k) ≫ K.d i j = 0) :
    K.liftCycles (c • k) j hj hk' = c • K.liftCycles k j hj hk := by
  rw [← cancel_mono (K.iCycles i), HomologicalComplex.liftCycles_i, Preadditive.zsmul_comp,
    HomologicalComplex.liftCycles_i]

theorem cycleClass_zsmul {K : ChainComplex (ModuleCat ℤ) ℕ} {A : ModuleCat ℤ} {i : ℕ}
    (c : ℤ) (x : A ⟶ K.X i) (hx : x ≫ K.d i ((ComplexShape.down ℕ).next i) = 0)
    (hx' : (c • x) ≫ K.d i ((ComplexShape.down ℕ).next i) = 0) :
    cycleClass (c • x) hx' = c • cycleClass x hx := by
  rw [cycleClass_def, cycleClass_def, liftCycles_zsmul c x rfl hx hx', Preadditive.zsmul_comp]

/-- If a cycle `x` is a scalar multiple of a cycle `x'`, then the class of `x` is that scalar
times the class of `x'`. -/
theorem cycleClass_eq_zsmul_of_eq {K : ChainComplex (ModuleCat ℤ) ℕ} {A : ModuleCat ℤ} {i : ℕ}
    (c : ℤ) (x x' : A ⟶ K.X i)
    (hx : x ≫ K.d i ((ComplexShape.down ℕ).next i) = 0)
    (hx' : x' ≫ K.d i ((ComplexShape.down ℕ).next i) = 0)
    (h : x = c • x') :
    cycleClass x hx = c • cycleClass x' hx' := by
  have hx'' : (c • x') ≫ K.d i ((ComplexShape.down ℕ).next i) = 0 := by
    rw [Preadditive.zsmul_comp, hx', smul_zero]
  have hz : cycleClass (c • x') hx'' = c • cycleClass x' hx' :=
    cycleClass_zsmul c x' hx' hx''
  rw [← hz]
  exact cycleClass_eq hx hx'' h

/-! ## The main computation -/

/-- **The fundamental class of `∂Δⁿ⁺¹` and the class of the identity simplex of `Δⁿ` agree in the
relative homology of the pair `(∂Δⁿ⁺¹, B)`**, `B` the closed star of the last vertex, up to the sign
of the last face. -/
theorem simplexBoundaryClass_comp_relProjHom (n : ℕ) :
    simplexBoundaryClass n ≫
        Work.Homology.relProjHom Work.Homology.ZMod n (boundarySpace (n + 1)) (simplexStar n)
      = lastSign n •
        (simplexGenMap n ≫
          Work.Homology.relHomologyMap Work.Homology.ZMod n (simplexFacePairHom n)) := by
  let R := Work.Homology.ZMod
  let X := boundarySpace (n + 1)
  let B := simplexStar n
  let Φ := simplexFacePairHom n
  have hL := cycleClass_naturality (Work.Homology.relProj R X B) (simplexBoundaryChain n)
      (simplexBoundaryChain_d n)
  have hR := cycleClass_naturality (Work.Homology.relChainMap R Φ) (simplexRelChain n)
      (simplexRelChain_d n)
  have hcyc : simplexBoundaryChain n ≫ (Work.Homology.relProj R X B).f n
      = lastSign n • (simplexRelChain n ≫ (Work.Homology.relChainMap R Φ).f n) := by
    have hsplit : simplexBoundaryChain n ≫ (Work.Homology.relProj R X B).f n
        = lastSign n • (simplexBoundaryFaceChain n (Fin.last (n + 1)) ≫
            (Work.Homology.relProj R X B).f n) := by
      rw [simplexBoundaryChain_eq_starPart_add, Preadditive.add_comp, Preadditive.zsmul_comp,
        simplexStarPartChain_comp_relProj, zero_add]
    have hface : simplexRelChain n ≫ (Work.Homology.relChainMap R Φ).f n
        = simplexBoundaryFaceChain n (Fin.last (n + 1)) ≫ (Work.Homology.relProj R X B).f n := by
      show (simplexIdChain n ≫
          (Work.Homology.relProj R (simplex n) (simplexBoundary n)).f n) ≫
            (Work.Homology.relChainMap R Φ).f n = _
      rw [Category.assoc, ← HomologicalComplex.comp_f,
        ← Work.Homology.relChainMap_comp_relProj]
      rw [HomologicalComplex.comp_f, ← Category.assoc]
      rw [show Φ.hom = simplexFaceToBoundary n (Fin.last (n + 1)) from rfl]
      rw [simplexIdChain_comp_singChainMap_lastFace]
    rw [hsplit, hface]
  show cycleClass (simplexBoundaryChain n) (simplexBoundaryChain_d n) ≫
      HomologicalComplex.homologyMap (Work.Homology.relProj R X B) n
      = lastSign n • (cycleClass (simplexRelChain n) (simplexRelChain_d n) ≫
          HomologicalComplex.homologyMap (Work.Homology.relChainMap R Φ) n)
  rw [hL, hR]
  exact cycleClass_eq_zsmul_of_eq (lastSign n)
    (simplexBoundaryChain n ≫ (Work.Homology.relProj R X B).f n)
    (simplexRelChain n ≫ (Work.Homology.relChainMap R Φ).f n) _ _ hcyc

/-! ## The injectivity of the projection to the relative pair `(∂Δⁿ⁺¹, B)` -/

theorem mono_relProjHom_of_isZero (R : ModuleCat ℤ) (X : TopCat) (A : Set X) (n : ℕ)
    (h : IsZero (Work.Homology.singHomology R n (TopCat.of A))) :
    Mono (Work.Homology.relProjHom R n X A) := by
  have hf : (Work.Homology.pairHomHX R X A n).f = 0 := h.eq_of_src _ 0
  exact (ShortComplex.exact_iff_mono _ hf).1 (Work.Homology.pairHomHX_exact R X A n)

/-! ## The transfer theorem -/

theorem epi_simplexBoundaryClass_of_epi_simplexGenMap (n : ℕ) (hn : 1 ≤ n)
    (h : CategoryTheory.Epi (Work.HomologyExtra.simplexGenMap n)) :
    CategoryTheory.Epi (Work.HomologyExtra.simplexBoundaryClass n) := by
  let R := Work.Homology.ZMod
  let X := boundarySpace (n + 1)
  let B := simplexStar n
  let Φ := simplexFacePairHom n
  haveI hcontr : ContractibleSpace (TopCat.of B) := simplexStar_contractible n
  have hz : IsZero (Work.Homology.singHomology R n (TopCat.of B)) := by
    have hh := Work.Homology.isZero_singHomology_succ_of_contractibleSpace R (TopCat.of B) (n - 1)
    simpa [Nat.sub_add_cancel hn] using hh
  haveI hmono : Mono (Work.Homology.relProjHom R n X B) := mono_relProjHom_of_isZero R X B n hz
  haveI hepiφ : CategoryTheory.Epi (Work.Homology.relHomologyMap R n Φ) :=
    relHomologyMap_simplexFacePairHom_epi n hn
  haveI hEpi : CategoryTheory.Epi (Work.HomologyExtra.simplexGenMap n) := h
  haveI hW : CategoryTheory.Epi
      (Work.HomologyExtra.simplexGenMap n ≫ Work.Homology.relHomologyMap R n Φ) :=
    epi_comp _ _
  have hsq : (lastSign n • 𝟙 R) ≫ (lastSign n • 𝟙 R) = 𝟙 R := by
    rw [Preadditive.zsmul_comp, Category.id_comp, smul_smul, lastSign_sq, one_smul]
  haveI hisoS : IsIso (lastSign n • 𝟙 R) := ⟨lastSign n • 𝟙 R, hsq, hsq⟩
  haveI hfgepi : CategoryTheory.Epi
      (simplexBoundaryClass n ≫ Work.Homology.relProjHom R n X B) := by
    rw [simplexBoundaryClass_comp_relProjHom]
    rw [show lastSign n • (Work.HomologyExtra.simplexGenMap n ≫
        Work.Homology.relHomologyMap R n Φ)
        = (lastSign n • 𝟙 R) ≫
          (Work.HomologyExtra.simplexGenMap n ≫ Work.Homology.relHomologyMap R n Φ) from by
      rw [Preadditive.zsmul_comp, Category.id_comp]]
    exact epi_comp _ _
  haveI hepig : CategoryTheory.Epi (Work.Homology.relProjHom R n X B) :=
    epi_of_epi (simplexBoundaryClass n) (Work.Homology.relProjHom R n X B)
  haveI hisog : IsIso (Work.Homology.relProjHom R n X B) := isIso_of_mono_of_epi _
  have heq : simplexBoundaryClass n =
      (simplexBoundaryClass n ≫ Work.Homology.relProjHom R n X B) ≫
        inv (Work.Homology.relProjHom R n X B) := by
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]
  exact epi_comp _ _

end

end Work.HomologyExtra
