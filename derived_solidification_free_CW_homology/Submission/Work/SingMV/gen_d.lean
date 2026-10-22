import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# The boundary of a singular chain generator

`Work.SingMV.gen X n σ` is the generator of the singular `n`-chains of `X` attached to a
continuous map `σ : Δⁿ ⟶ X`. This file computes its boundary: the differential of the
simplicial chain complex is the alternating sum of the face maps, and under the
identification `singEquiv` of simplices of `TopCat.toSSet.obj X` with continuous maps out of
the standard simplex, the `i`-th face of `σ` is the composite of `σ` with the `i`-th coface
inclusion `Δⁿ ⟶ Δⁿ⁺¹`.

The computation is Mathlib's `SSet.ιChainComplex_d` (the boundary of the summand inclusion
`R ⟶ (X.chainComplex R).X (n+1)` is the alternating sum of the summand inclusions of the
faces), transported to the element level and rewritten with
`TopCat.toSSetObjEquiv_δ_apply`.
-/

open CategoryTheory

namespace Work.SingMV

theorem gen_d (X : TopCat) (n : ℕ) (σ : Work.SingMV.singMap X (n+1)) :
    (((Submission.Blueprint.singC).obj X).d (n+1) n) (Work.SingMV.gen X (n+1) σ) =
      ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
        Work.SingMV.gen X n (σ.comp ((Work.SingMV.coface n i).hom)) := by
  -- The simplex of the singular simplicial set underlying `σ`.
  let x := (Work.SingMV.singEquiv X (n+1)).symm σ
  -- The `i`-th face of `σ` is `σ` composed with the `i`-th coface inclusion.
  have hface : ∀ i : Fin (n+2),
      Work.SingMV.singEquiv X n ((TopCat.toSSet.obj X).δ i x) =
        σ.comp ((Work.SingMV.coface n i).hom) := by
    intro i
    ext z
    simp only [Work.SingMV.coface, ContinuousMap.comp_apply, Work.SingMV.singEquiv]
    rw [TopCat.toSSetObjEquiv_δ_apply]
    rfl
  -- At the level of the chain complex of `TopCat.toSSet.obj X`, the boundary of `gen` is the
  -- alternating sum of the boundaries of its faces.
  have hgen : ∀ i : Fin (n+2),
      Work.SingMV.gen X n (σ.comp ((Work.SingMV.coface n i).hom)) =
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj X).δ i x)) (1:ℤ) := by
    intro i
    rw [← hface i]
    simp only [Work.SingMV.gen, Equiv.symm_apply_apply]
    rfl
  -- Mathlib's computation of the differential on the summand inclusion, applied to `1`.
  have hmain : (CategoryTheory.CategoryStruct.comp
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) x)
        (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n+1) n)) (1:ℤ) =
      (∑ i : Fin (n+2), (-1:ℤ)^(i:ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) ((TopCat.toSSet.obj X).δ i x))) (1:ℤ) :=
    congrArg (fun f => f (1:ℤ))
      (SSet.ιChainComplex_d (X := TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ) (n := n) x)
  change (CategoryTheory.CategoryStruct.comp
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) x)
        (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n+1) n)) (1:ℤ) = _
  rw [hmain]
  simp only [hgen, LinearMap.sum_apply, LinearMap.smul_apply, ModuleCat.hom_sum,
    ModuleCat.hom_smul]
  rfl

end Work.SingMV
