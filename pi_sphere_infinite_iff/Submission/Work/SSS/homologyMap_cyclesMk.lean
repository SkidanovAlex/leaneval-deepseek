import Mathlib
import Submission.Work.SSS.Filtration

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- `homologyπ` is natural with respect to `homologyMap`. -/
lemma hmcm_homologyπ_map {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (i : ℕ)
    (x : K.cycles i) :
    (L.homologyπ i) ((HomologicalComplex.cyclesMap φ i) x)
      = (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) x) :=
  (congrArg (fun (f : K.cycles i ⟶ L.homology i) => f x)
    (HomologicalComplex.homologyπ_naturality φ i)).symm

/-- The `iCycles` inclusion of a `cyclesMk`. -/
lemma hmcm_iCycles_cyclesMk {K : ChainComplex (ModuleCat ℤ) ℕ} {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i)
    (hx : (ModuleCat.Hom.hom (K.d i j)) x = 0) :
    (ConcreteCategory.hom (K.iCycles i)) (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) x j hj hx

/-- `cyclesMap` on a `cyclesMk`. -/
lemma hmcm_cyclesMap_cyclesMk {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) {i j : ℕ}
    (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i)
    (hx : (ModuleCat.Hom.hom (K.d i j)) x = 0)
    (hx' : (ModuleCat.Hom.hom (L.d i j)) ((φ.f i) x) = 0) :
    (HomologicalComplex.cyclesMap φ i) (K.cyclesMk x j hj hx) = L.cyclesMk ((φ.f i) x) j hj hx' := by
  apply (Preadditive.mono_iff_injective (L.iCycles i)).1 inferInstance
  show (ConcreteCategory.hom (L.iCycles i))
      ((ConcreteCategory.hom (HomologicalComplex.cyclesMap φ i)) (K.cyclesMk x j hj hx))
    = (ConcreteCategory.hom (L.iCycles i)) (L.cyclesMk ((φ.f i) x) j hj hx')
  have hmap := congrArg (fun (f : K.cycles i ⟶ L.X i) =>
    (ConcreteCategory.hom f) (K.cyclesMk x j hj hx)) (HomologicalComplex.cyclesMap_i φ i)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at hmap
  rw [hmap, hmcm_iCycles_cyclesMk hj x hx, hmcm_iCycles_cyclesMk hj ((φ.f i) x) hx']

/-- **The elementwise description of `homologyMap` on a cycle class.**  For a morphism of chain
complexes `φ : K ⟶ L` and an element `x` of `K.X i` which is a cycle for the differential
`K.d i j` (where `j = next i`), the induced map on homology sends the class of `x` to the class of
`φ x` (which is automatically a cycle for `L.d i j`).

A proof of this statement (in the same workspace, in the file
`Submission/Work/SSS/pieceIso_ezSimplexZero.lean`, as the local lemma
`Work.SSS.pEZ_homologyπ_sCCMap_cyclesMk`, together with the auxiliary local lemmas
`pEZ_cyclesMap_cyclesMk`, `pEZ_iCycles_cyclesMk`, `pEZ_homologyπ_map` just above it) may be read
and adapted; the only reason it is not imported is that that module depends on a statement that
was still being proved at the time. -/
theorem homologyMap_cyclesMk {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L)
    {i j : ℕ} (hj : (ComplexShape.down ℕ).next i = j) (x : K.X i)
    (hx : (ModuleCat.Hom.hom (K.d i j)) x = 0)
    (hx' : (ModuleCat.Hom.hom (L.d i j)) ((φ.f i) x) = 0) :
    (L.homologyπ i) (L.cyclesMk ((φ.f i) x) j hj hx')
      = (HomologicalComplex.homologyMap φ i) ((K.homologyπ i) (K.cyclesMk x j hj hx)) := by
  rw [← hmcm_cyclesMap_cyclesMk φ hj x hx hx']
  exact hmcm_homologyπ_map φ i (K.cyclesMk x j hj hx)

end Work.SSS
