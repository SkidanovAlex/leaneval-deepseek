import Mathlib
import Submission.Work.Cohomology.Crux33.ezModel

/-!
# The bridge between the simplicial chain complex and the free module on simplices

`Work.Cohomology.Crux33.coords X n` extracts, from a singular `n`-chain of a simplicial set `X`,
its coordinate function: the `ℤ`-linear map `C_n(X) ⟶ (X_n →₀ ℤ)` sending the generator of a
simplex `x` to `Finsupp.single x 1`.  `Work.Cohomology.Crux33.mk X n` is the reverse map.  They
satisfy `mk ∘ coords = id`, so an equality of chains follows from the equality of their
coordinate functions (`eq_of_coords_eq`); this reduces chain-level identities about explicit sums
of generators to finite computations on coordinates.
-/

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Cohomology.Crux33

noncomputable section

/-- The coordinate function of an `n`-chain of a simplicial set: the `ℤ`-linear map which sends
the generator attached to a simplex `x` to `Finsupp.single x 1`. -/
def coords (X : SSet) (n : ℕ) :
    (X.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ] (X _⦋n⦌ →₀ ℤ) :=
  ModuleCat.Hom.hom (Cofan.IsColimit.desc (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun x => ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℤ _ (Finsupp.single x (1 : ℤ)))))

/-- The coordinate function of the generator attached to a simplex. -/
@[simp]
theorem coords_ι (X : SSet) (n : ℕ) (x : X _⦋n⦌) :
    coords X n ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1)
      = Finsupp.single x (1 : ℤ) := by
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun y => ModuleCat.ofHom
      (LinearMap.toSpanSingleton ℤ _ (Finsupp.single y (1 : ℤ)))) x
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ((X _⦋n⦌) →₀ ℤ)) =>
    g.hom (1 : ℤ)) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 : (LinearMap.toSpanSingleton ℤ ((X _⦋n⦌) →₀ ℤ)
      (Finsupp.single x (1 : ℤ))) (1 : ℤ) = Finsupp.single x (1 : ℤ) := by
    rw [LinearMap.toSpanSingleton_apply]
    exact one_zsmul _
  rw [ModuleCat.hom_ofHom, h3] at h2
  exact h2

/-- The `ℤ`-linear map from the free module on the `n`-simplices of `X` back to the `n`-chains. -/
def mk (X : SSet) (n : ℕ) :
    (X _⦋n⦌ →₀ ℤ) →ₗ[ℤ] (X.chainComplex (ModuleCat.of ℤ ℤ)).X n where
  toFun c := (Finsupp.liftAddHom (fun x =>
    ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x)).hom.toAddMonoidHom)) c
  map_add' a b := map_add _ a b
  map_smul' r c := by
    have hmod : (AddCommGroup.toIntModule ↑((X.chainComplex (ModuleCat.of ℤ ℤ)).X n))
        = (inferInstance : Module ℤ ↑((X.chainComplex (ModuleCat.of ℤ ℤ)).X n)) :=
      Subsingleton.elim _ _
    have hsm : (ZSMul.toSMul : SMul ℤ ↑((X.chainComplex (ModuleCat.of ℤ ℤ)).X n))
        = (inferInstance : Module ℤ ↑((X.chainComplex (ModuleCat.of ℤ ℤ)).X n)
          ).toDistribSMul.toSMul := by
      rw [← hmod]
      rfl
    rw [← hsm]
    exact map_zsmul _ r c

/-- The value of `mk` on a generator. -/
theorem mk_single (X : SSet) (n : ℕ) (x : X _⦋n⦌) (b : ℤ) :
    mk X n (Finsupp.single x b) = ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x)).hom b := by
  show (Finsupp.liftAddHom (fun y =>
      ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) y)).hom.toAddMonoidHom))
    (Finsupp.single x b) = ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x)).hom b
  rw [Finsupp.liftAddHom_apply_single]
  rfl

/-- `mk` is a left inverse of `coords`. -/
theorem mk_comp_coords (X : SSet) (n : ℕ) :
    (mk X n).comp (coords X n) = LinearMap.id := by
  have h : ModuleCat.ofHom ((mk X n).comp (coords X n))
      = ModuleCat.ofHom (LinearMap.id :
          (X.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ]
            (X.chainComplex (ModuleCat.of ℤ ℤ)).X n) := by
    apply SSet.chainComplex_hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show mk X n (coords X n ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1))
      = (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1
    rw [coords_ι, mk_single]
  exact congrArg ModuleCat.Hom.hom h

/-- `coords` is injective. -/
theorem coords_injective (X : SSet) (n : ℕ) : Function.Injective (coords X n) := by
  intro a b h
  have h1 := LinearMap.congr_fun (mk_comp_coords X n) a
  have h2 := LinearMap.congr_fun (mk_comp_coords X n) b
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
  rw [← h1, h, h2]

/-- An equality of chains follows from an equality of their coordinate functions. -/
theorem eq_of_coords_eq {X : SSet} {n : ℕ}
    {a b : (X.chainComplex (ModuleCat.of ℤ ℤ)).X n} (h : coords X n a = coords X n b) :
    a = b :=
  coords_injective X n h

end
end Work.Cohomology.Crux33
