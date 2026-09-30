import Mathlib
import Submission.Work.Cohomology.CapProduct
import Submission.Work.SSSR.SZero.Defs
import Submission.Work.SSSR.serreE1PieceIsoZero
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Capping with the unit cochain is the identity

`Work.Cohomology.cap R X (unitCochain R X) k` is the degree transport `(0+k) → k` on the
singular chains of a simplicial set, i.e. the identity up to the cast `0 + k = k`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

namespace Work.Pi6.MSSK

noncomputable section

/-- The inclusion `backIncl 0 k : ⦋k⦌ ⟶ ⦋0+k⦌` of the last `k+1` vertices of `Δ[0+k]` is the
canonical identification `⦋k⦌ ≅ ⦋0+k⦌` of the two objects of the simplex category. -/
theorem capUnit_backIncl_zero_eq (k : ℕ) :
    Work.Cohomology.backIncl 0 k =
      eqToHom (congrArg SimplexCategory.mk (Nat.zero_add k).symm) := by
  apply SimplexCategory.Hom.ext
  rw [SimplexCategory.eqToHom_toOrderHom]
  apply OrderHom.ext
  funext i
  apply Fin.ext
  show (Work.Cohomology.backIncl 0 k i).val = _
  simp

/-- Transport of a simplex along a degree equality is `Y.map` of the corresponding morphism of
the simplex category. -/
lemma capUnit_castSimp_eq_map_op_eqToHom {Y : SSet.{0}} {m n : ℕ} (h : m = n) (x : Y _⦋m⦌) :
    Work.SSSR.SZero.castSimp h x
      = Y.map (eqToHom (congrArg SimplexCategory.mk h.symm)).op x := by
  cases h
  simp [Work.SSSR.SZero.castSimp]

/-- The back `k`-face of a `(0+k)`-simplex is its transport along `0 + k = k`. -/
lemma capUnit_backFace_eq_castSimp (X : SSet.{0}) (k : ℕ) (σ : X _⦋0 + k⦌) :
    Work.Cohomology.backFace X 0 k σ = Work.SSSR.SZero.castSimp (Nat.zero_add k) σ := by
  rw [capUnit_castSimp_eq_map_op_eqToHom, Work.Cohomology.backFace, capUnit_backIncl_zero_eq]

/-- `eqToHom` of a degree equality acts on elements by the degree transport `castElem`. -/
lemma capUnit_eqToHom_apply_castElem {R : Type} [CommRing R] {K : ChainComplex (ModuleCat R) ℕ}
    {i j : ℕ} (h : i = j) (x : K.X i) :
    (eqToHom (congrArg (fun m => K.X m) h)).hom x = Work.SSSR.castElem K h x := by
  subst h
  simp [Work.SSSR.castElem]

/-- The cap product with the unit `0`-cochain is the chain map induced by taking the back
`k`-face. -/
theorem capUnit_capHom_unit_eq_backChain (R : Type) [CommRing R] (X : SSet.{0}) (k : ℕ) :
    Work.Cohomology.capHom R X (Work.Cohomology.unitCochain R X) k
      = Work.Cohomology.backChain R X 0 k := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [Work.Cohomology.ιChainComplex_capHom, Work.Cohomology.ιChainComplex_backChain,
    Work.Cohomology.genEval_unitCochain]
  have h1 : ModuleCat.ofHom (LinearMap.toSpanSingleton R R (1 : R)) = 𝟙 (ModuleCat.of R R) := by
    have h2 : LinearMap.toSpanSingleton R R (1 : R) = LinearMap.id := by
      apply LinearMap.ext
      intro x
      simp [LinearMap.toSpanSingleton_apply]
    rw [h2]
    exact ModuleCat.ofHom_id
  rw [h1, Category.id_comp]

/-- The back-face chain map of degree `0` is the transport of the degrees `0 + k → k`. -/
theorem capUnit_backChain_eq_eqToHom (R : Type) [CommRing R] [Nontrivial R] (X : SSet.{0}) (k : ℕ) :
    Work.Cohomology.backChain R X 0 k
      = eqToHom (congrArg (fun n => (Work.SSSR.sCC R X).X n) (Nat.zero_add k)) := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [Work.Cohomology.ιChainComplex_backChain]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  rw [ModuleCat.hom_comp, LinearMap.comp_apply]
  let v : (Work.SSSR.sCC R X).X (0 + k) :=
    (ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of R R) σ)) 1
  have h1 : (ModuleCat.Hom.hom (eqToHom (congrArg (fun n => (Work.SSSR.sCC R X).X n)
        (Nat.zero_add k)))) v
      = Work.SSSR.castElem (Work.SSSR.sCC R X) (Nat.zero_add k) v :=
    capUnit_eqToHom_apply_castElem (K := Work.SSSR.sCC R X) (Nat.zero_add k) v
  rw [h1]
  have h2 : Work.SSSR.castElem (Work.SSSR.sCC R X) (Nat.zero_add k) v
      = (ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of R R)
          (Work.SSSR.SZero.castSimp (Nat.zero_add k) σ))) 1 :=
    Work.SSSR.SZero.zc_castElem_sCC_ιChainComplex (X := X) (Nat.zero_add k) σ
  rw [h2, ← capUnit_backFace_eq_castSimp X k σ]

/-- **Capping with the unit cochain is the identity** (up to the degree transport
`0 + k = k`). -/
theorem capUnitCast (R : Type) [CommRing R] [Nontrivial R] (X : SSet.{0}) (k : ℕ)
    (x : (Work.SSSR.sCC R X).X (0 + k)) :
    Work.Cohomology.cap R X (Work.Cohomology.unitCochain R X) k x
      = Work.SSSR.castElem (Work.SSSR.sCC R X) (Nat.zero_add k) x := by
  show (Work.Cohomology.capHom R X (Work.Cohomology.unitCochain R X) k).hom x
      = Work.SSSR.castElem (Work.SSSR.sCC R X) (Nat.zero_add k) x
  rw [capUnit_capHom_unit_eq_backChain R X k, capUnit_backChain_eq_eqToHom R X k]
  exact capUnit_eqToHom_apply_castElem (K := Work.SSSR.sCC R X) (Nat.zero_add k) x

end

end Work.Pi6.MSSK
