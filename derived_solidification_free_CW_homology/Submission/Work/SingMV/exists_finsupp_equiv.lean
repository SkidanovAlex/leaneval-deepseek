import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# The singular `n`-chains as the free module on the singular `n`-simplices

The singular `n`-chains of a topological space `X` are the coproduct of copies of `ℤ` indexed
by the singular `n`-simplices of `X`, hence the free `ℤ`-module on those simplices.  This file
exhibits that identification as a linear equivalence `singChainEquiv`, together with the
statement that it sends a basis element to the corresponding singular chain generator.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.SingMV

open CategoryTheory Limits

/-- The coproduct of copies of `ℤ` indexed by the singular `n`-simplices of `X` is the free
`ℤ`-module on those simplices, i.e. the module of finitely supported functions
`singMap X n →₀ ℤ`. -/
noncomputable def singChainEquiv (X : TopCat) (n : ℕ) :
    (singMap X n →₀ ℤ) ≃ₗ[ℤ]
      ↥(∐ fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) =>
          ModuleCat.of ℤ ℤ) :=
  let ι := (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))
  letI : DecidableEq ι := Classical.decEq ι
  let Z : ι → ModuleCat ℤ := fun _ => ModuleCat.of ℤ ℤ
  (Finsupp.domLCongr (singEquiv X n).symm).trans
    ((finsuppLEquivDirectSum ℤ ℤ ι).trans
      (Iso.toLinearEquiv (ModuleCat.coprodIsoDirectSum Z).symm))

/-- `singChainEquiv` sends the basis element on a singular simplex to the corresponding
coproduct inclusion applied to `1`. -/
lemma singChainEquiv_single (X : TopCat) (n : ℕ) (σ : singMap X n) :
    singChainEquiv X n (Finsupp.single σ 1) =
      (Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) =>
        ModuleCat.of ℤ ℤ) ((singEquiv X n).symm σ)) (1 : ℤ) := by
  rw [singChainEquiv]
  simp only [LinearEquiv.trans_apply, Finsupp.domLCongr_single]
  rw [finsuppLEquivDirectSum_single, Iso.toLinearEquiv_apply, Iso.symm_hom,
    ModuleCat.lof_coprodIsoDirectSum_inv_apply]

/-- `singChainEquiv` sends the basis element on a singular simplex `σ` to the corresponding
generator `gen X n σ` of the singular chain group. -/
lemma singChainEquiv_gen (X : TopCat) (n : ℕ) (σ : singMap X n) :
    singChainEquiv X n (Finsupp.single σ 1) = gen X n σ := by
  rw [singChainEquiv_single]
  rfl

theorem exists_finsupp_equiv (X : TopCat) (n : ℕ) :
    ∃ e : (Work.SingMV.singMap X n →₀ ℤ) ≃ₗ[ℤ]
        ↥(((Submission.Blueprint.singC).obj X).X n),
      ∀ σ : Work.SingMV.singMap X n, e (Finsupp.single σ 1) = Work.SingMV.gen X n σ := by
  refine ⟨singChainEquiv X n, fun σ => ?_⟩
  exact singChainEquiv_gen X n σ

end Work.SingMV
