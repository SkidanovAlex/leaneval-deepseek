import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.SSSR.Serre.simpHomPrism
import Submission.Work.SSSR.Cohomology.Crux33.ezBridge
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open Work.Serre
variable {R : Type} [CommRing R] [Nontrivial R]

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial
open Work.SSSR.RatHurewicz.Bridge (coface coface_apply)
namespace Work.SSSR.Serre

noncomputable section

/-- The singular simplicial set of `X`, as an `SSet`. -/
abbrev singX (X : Type) [TopologicalSpace X] : SSet := TopCat.toSSet.obj (TopCat.of X)

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

/-- The type of `n`-simplices of the singular simplicial set of `X`, written without the
`SimplexCategory` notation so that statements can be delegated without opening the `Simplicial`
scope. -/
abbrev SSetSimplex (X : Type) [TopologicalSpace X] (n : ℕ) : Type :=
  (singX X).obj (Opposite.op (SimplexCategory.mk n))

/-- The *(n+1)*-simplex of the singular simplicial set attached to the `k`-th prism piece of an
`n`-simplex. -/
def hSimplex (H : SimpHom X A N) (n : ℕ) (k : Fin (n + 1)) (σ : singX X _⦋n⦌) :
    singX X _⦋n + 1⦌ :=
  ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n + 1⦌)).symm
    (prismSimplex H n k ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌) σ))

/-- The `n`-simplex of the singular simplicial set which is the top of the homotopy of `σ`. -/
def gSimplex (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) : singX X _⦋n⦌ :=
  ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌)).symm
    (topSimplex H n ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌) σ))

theorem toSSetObjEquiv_hSimplex (H : SimpHom X A N) (n : ℕ) (k : Fin (n + 1))
    (σ : singX X _⦋n⦌) :
    (TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n + 1⦌) (hSimplex H n k σ)
      = prismSimplex H n k ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌) σ) :=
  Equiv.apply_symm_apply _ _

theorem toSSetObjEquiv_gSimplex (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) :
    (TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌) (gSimplex H n σ)
      = topSimplex H n ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌) σ) :=
  Equiv.apply_symm_apply _ _

/-- Face maps of the singular simplicial set, in terms of the continuous simplices. -/
theorem toSSetObjEquiv_δ (n : ℕ) (i : Fin (n + 2)) (x : singX X _⦋n + 1⦌) :
    (TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌) ((singX X).δ i x)
      = ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n + 1⦌) x).comp (coface n i) := by
  refine ContinuousMap.ext (fun z => ?_)
  rw [ContinuousMap.comp_apply, coface_apply]
  exact TopCat.toSSetObjEquivT_δ_apply x i z

/-! ## The face identities at the level of the singular simplicial set -/

theorem δ_hSimplex_zero (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N) (σ : singX X _⦋n⦌) :
    (singX X).δ (0 : Fin (n + 2)) (hSimplex H n 0 σ) = gSimplex H n σ := by
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_gSimplex, toSSetObjEquiv_hSimplex]
  exact prismSimplex_coface_zero H n hn _

theorem δ_hSimplex_last (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N) (σ : singX X _⦋n⦌) :
    (singX X).δ (Fin.last (n + 1)) (hSimplex H n (Fin.last n) σ) = σ := by
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋n⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_hSimplex, prismSimplex_coface_last H n hn]

theorem δ_hSimplex_diag (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N)
    (σ : singX X _⦋m + 1⦌) (j : Fin (m + 1)) :
    (singX X).δ (j.castSucc.succ) (hSimplex H (m + 1) j.castSucc σ)
      = (singX X).δ (j.castSucc.succ) (hSimplex H (m + 1) j.succ σ) := by
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋m + 1⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_δ, toSSetObjEquiv_hSimplex, toSSetObjEquiv_hSimplex]
  exact prismSimplex_coface_diag H hm j _

theorem δ_hSimplex_lt (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N)
    (σ : singX X _⦋m + 1⦌) (f : Fin (m + 3)) (k : Fin (m + 2))
    (hfk : (f : ℕ) < (k : ℕ)) :
    (singX X).δ f (hSimplex H (m + 1) k σ)
      = hSimplex H m ⟨(k : ℕ) - 1, by omega⟩ ((singX X).δ ⟨(f : ℕ), by omega⟩ σ) := by
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋m + 1⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_hSimplex, toSSetObjEquiv_hSimplex, toSSetObjEquiv_δ]
  exact prismSimplex_coface_lt H hm k f hfk _

theorem δ_hSimplex_gt (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N)
    (σ : singX X _⦋m + 1⦌) (f : Fin (m + 3)) (k : Fin (m + 2))
    (hfk : (k : ℕ) + 1 < (f : ℕ)) :
    (singX X).δ f (hSimplex H (m + 1) k σ)
      = hSimplex H m ⟨(k : ℕ), by omega⟩ ((singX X).δ ⟨(f : ℕ) - 1, by omega⟩ σ) := by
  apply ((TopCat.of X).toSSetObjEquivT (Opposite.op ⦋m + 1⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_hSimplex, toSSetObjEquiv_hSimplex, toSSetObjEquiv_δ]
  exact prismSimplex_coface_gt H hm k f hfk _


/-! ## The chain homotopy and the top map -/

/-- Abbreviation for the singular chain complex of `X` with `ℤ` coefficients. -/
abbrev singChainC (R : Type) [CommRing R] [Nontrivial R] (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat R) ℕ :=
  (singX X).chainComplex (ModuleCat.of R R)

/-- The value of the chain homotopy on the generator of an `n`-simplex. -/
noncomputable def prismVal (R : Type) [CommRing R] [Nontrivial R] (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) :
    (singChainC R X).X (n + 1) :=
  ∑ k : Fin (n + 1), ((-1 : ℤ) ^ ((k : ℕ) + 1)) •
    ((singX X).ιChainComplex (R := ModuleCat.of R R) (hSimplex H n k σ)).hom (1 : R)

/-- The value of the "top" map on the generator of an `n`-simplex. -/
noncomputable def topVal (R : Type) [CommRing R] [Nontrivial R] (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) :
    (singChainC R X).X n :=
  ((singX X).ιChainComplex (R := ModuleCat.of R R) (gSimplex H n σ)).hom (1 : R)

/-- **The chain homotopy** attached to the family `G` of homotopies. -/
noncomputable def prismHom (R : Type) [CommRing R] [Nontrivial R] (H : SimpHom X A N) (n : ℕ) :
    (singChainC R X).X n ⟶ (singChainC R X).X (n + 1) :=
  Cofan.IsColimit.desc ((singX X).isColimitChainComplexXCofan (ModuleCat.of R R) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton R ((singChainC R X).X (n + 1))
      (prismVal R H n σ)))

/-- **The "top" map** attached to the family `G`. -/
noncomputable def topChainMap (R : Type) [CommRing R] [Nontrivial R] (H : SimpHom X A N) (n : ℕ) :
    (singChainC R X).X n ⟶ (singChainC R X).X n :=
  Cofan.IsColimit.desc ((singX X).isColimitChainComplexXCofan (ModuleCat.of R R) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton R ((singChainC R X).X n)
      (topVal R H n σ)))

/-- The value of the chain homotopy on the generator of a simplex. -/
lemma prismHom_gen (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) :
    (prismHom R H n).hom (((singX X).ιChainComplex (R := ModuleCat.of R R) σ).hom (1 : R))
      = prismVal R H n σ := by
  have hfac := Cofan.IsColimit.fac ((singX X).isColimitChainComplexXCofan (ModuleCat.of R R) n)
    (fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton R ((singChainC R X).X (n + 1))
      (prismVal R H n τ))) σ
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ (singChainC R X).X (n + 1)) =>
    (ModuleCat.Hom.hom g) (1 : R)) hfac
  rw [show (singX X).ιChainComplex (R := ModuleCat.of R R) σ
      = ((singX X).chainComplexXCofan (ModuleCat.of R R) n).inj σ from rfl]
  change (ModuleCat.Hom.hom (prismHom R H n)) ((ModuleCat.Hom.hom
    (((singX X).chainComplexXCofan (ModuleCat.of R R) n).inj σ)) (1 : R)) = prismVal R H n σ
  simp only [prismHom, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  exact h2

/-- The value of the top map on the generator of a simplex. -/
lemma topChainMap_gen (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) :
    (topChainMap R H n).hom (((singX X).ιChainComplex (R := ModuleCat.of R R) σ).hom (1 : R))
      = topVal R H n σ := by
  have hfac := Cofan.IsColimit.fac ((singX X).isColimitChainComplexXCofan (ModuleCat.of R R) n)
    (fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton R ((singChainC R X).X n)
      (topVal R H n τ))) σ
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ (singChainC R X).X n) =>
    (ModuleCat.Hom.hom g) (1 : R)) hfac
  rw [show (singX X).ιChainComplex (R := ModuleCat.of R R) σ
      = ((singX X).chainComplexXCofan (ModuleCat.of R R) n).inj σ from rfl]
  change (ModuleCat.Hom.hom (topChainMap R H n)) ((ModuleCat.Hom.hom
    (((singX X).chainComplexXCofan (ModuleCat.of R R) n).inj σ)) (1 : R)) = topVal R H n σ
  simp only [topChainMap, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  exact h2

/-- The differential of the simplicial chain complex on the generator attached to a simplex. -/
lemma singChain_d_gen (n : ℕ) (a : singX X _⦋n + 1⦌) :
    ((singChainC R X).d (n + 1) n).hom
        (((singX X).ιChainComplex (R := ModuleCat.of R R) a).hom (1 : R))
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (((singX X).ιChainComplex (R := ModuleCat.of R R) ((singX X).δ i a)).hom (1 : R)) := by
  have hh := congrArg (fun (g : ModuleCat.of R R ⟶ (singChainC R X).X n) =>
    (ModuleCat.Hom.hom g) (1 : R)) (SSet.ιChainComplex_d (singX X) (ModuleCat.of R R) a)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply] at hh
  exact hh

end

end Work.SSSR.Serre
