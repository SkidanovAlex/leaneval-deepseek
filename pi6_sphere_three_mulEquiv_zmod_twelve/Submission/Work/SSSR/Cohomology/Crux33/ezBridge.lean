import Mathlib
import Submission.Work.Cohomology.Crux33.ezModel
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R]

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.SSSR.Cohomology.Crux33

noncomputable section

/-- The coordinate function of an `n`-chain of a simplicial set: the `R`-linear map which sends
the generator attached to a simplex `x` to `Finsupp.single x 1`. -/
def coords (X : SSet) (n : ℕ) :
    (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] (X _⦋n⦌ →₀ R) :=
  ModuleCat.Hom.hom (Cofan.IsColimit.desc (X.isColimitChainComplexXCofan (ModuleCat.of R R) n)
    (fun x => ModuleCat.ofHom
      (LinearMap.toSpanSingleton R _ (Finsupp.single x (1 : R)))))

/-- The coordinate function of the generator attached to a simplex. -/
@[simp]
theorem coords_ι (X : SSet) (n : ℕ) (x : X _⦋n⦌) :
    coords X n ((X.ιChainComplex (R := ModuleCat.of R R) x).hom 1)
      = Finsupp.single x (1 : R) := by
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of R R) n)
    (fun y => ModuleCat.ofHom
      (LinearMap.toSpanSingleton R _ (Finsupp.single y (1 : R)))) x
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ ModuleCat.of R ((X _⦋n⦌) →₀ R)) =>
    g.hom (1 : R)) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  have h3 : (LinearMap.toSpanSingleton R ((X _⦋n⦌) →₀ R)
      (Finsupp.single x (1 : R))) (1 : R) = Finsupp.single x (1 : R) := by
    rw [LinearMap.toSpanSingleton_apply, one_smul]
  rw [ModuleCat.hom_ofHom, h3] at h2
  exact h2

/-- The `R`-linear map from the free module on the `n`-simplices of `X` back to the `n`-chains. -/
noncomputable def mk (X : SSet) (n : ℕ) :
    (X _⦋n⦌ →₀ R) →ₗ[R] (X.chainComplex (ModuleCat.of R R)).X n :=
  Finsupp.lsum R (fun x => (X.ιChainComplex (R := ModuleCat.of R R) x).hom)

/-- The value of `mk` on a generator. -/
theorem mk_single (X : SSet) (n : ℕ) (x : X _⦋n⦌) (b : R) :
    mk X n (Finsupp.single x b) = ((X.ιChainComplex (R := ModuleCat.of R R) x)).hom b := by
  rw [mk, Finsupp.lsum_single]

/-- `mk` is a left inverse of `coords`. -/
theorem mk_comp_coords (X : SSet) (n : ℕ) :
    (mk (R := R) X n).comp (coords (R := R) X n) = LinearMap.id := by
  have h : ModuleCat.ofHom ((mk (R := R) X n).comp (coords (R := R) X n))
      = ModuleCat.ofHom (LinearMap.id :
          (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R]
            (X.chainComplex (ModuleCat.of R R)).X n) := by
    apply SSet.chainComplex_hom_ext
    intro x
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show mk (R := R) X n (coords (R := R) X n ((X.ιChainComplex (R := ModuleCat.of R R) x).hom 1))
      = (X.ιChainComplex (R := ModuleCat.of R R) x).hom 1
    rw [coords_ι, mk_single]
  exact congrArg ModuleCat.Hom.hom h

/-- `coords` is injective. -/
theorem coords_injective (X : SSet) (n : ℕ) : Function.Injective (coords (R := R) X n) := by
  intro a b h
  have h1 := LinearMap.congr_fun (mk_comp_coords X n) a
  have h2 := LinearMap.congr_fun (mk_comp_coords X n) b
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1 h2
  rw [← h1, h, h2]

/-- An equality of chains follows from an equality of their coordinate functions. -/
theorem eq_of_coords_eq {X : SSet} {n : ℕ}
    {a b : (X.chainComplex (ModuleCat.of R R)).X n} (h : coords X n a = coords X n b) :
    a = b :=
  coords_injective X n h

end

end Work.SSSR.Cohomology.Crux33
