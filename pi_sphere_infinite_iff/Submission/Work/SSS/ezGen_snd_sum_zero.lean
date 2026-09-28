import Mathlib
import Submission.Work.KunnethEZ.ezGen_boundary
import Submission.Work.KunnethEZ.Defs
import Submission.Work.KunnethEZ.ezChain_isCycle
import Submission.Work.KunnethEZ.ez23_eq_ezGen
import Submission.Work.SSS.serreE1Defs

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

/-- The coefficient ring `ℤ`, as a module over itself, spelled once. -/
abbrev ezR : ModuleCat ℤ := ModuleCat.of ℤ ℤ

/-- **The linear extension of the Eilenberg–Zilber shuffle chain in the second variable.**

For a fixed `n`-simplex `σ` of `X`, the assignment `τ' ↦ ezGen n q X Y σ τ'` on `q`-simplices of
`Y` extends uniquely to a `ℤ`-linear map out of the `q`-chains of `Y` (the `q`-chains are the free
`ℤ`-module on the `q`-simplices, so there is no compatibility condition to check). -/
def ezLinSnd (n q : ℕ) (X Y : SSet.{0}) (σ : X _⦋n⦌) :
    (Y.chainComplex ezR).X q ⟶ ((X ⊗ Y).chainComplex ezR).X (n + q) :=
  (Y.isColimitChainComplexXCofan ezR q).desc
    (Cofan.mk (((X ⊗ Y).chainComplex ezR).X (n + q))
      (fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
        ↥(((X ⊗ Y).chainComplex ezR).X (n + q))
        (Work.Cohomology.Crux33.ezGen n q X Y σ τ))))

/-- The defining property of `ezLinSnd` on the generators of the chain complex. -/
lemma ezLinSnd_ι (n q : ℕ) (X Y : SSet.{0}) (σ : X _⦋n⦌) (τ : Y _⦋q⦌) :
    (Y.ιChainComplex (R := ezR) τ) ≫ ezLinSnd n q X Y σ
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ
          ↥(((X ⊗ Y).chainComplex ezR).X (n + q))
          (Work.Cohomology.Crux33.ezGen n q X Y σ τ)) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of `ezLinSnd` on a generator simplex is the shuffle chain. -/
lemma ezLinSnd_apply (n q : ℕ) (X Y : SSet.{0}) (σ : X _⦋n⦌) (τ : Y _⦋q⦌) :
    (ezLinSnd n q X Y σ).hom ((Y.ιChainComplex (R := ezR) τ).hom 1)
      = Work.Cohomology.Crux33.ezGen n q X Y σ τ := by
  have h := congrArg
    (fun (f : ezR ⟶ ((X ⊗ Y).chainComplex ezR).X (n + q)) => f.hom (1 : ℤ))
    (ezLinSnd_ι n q X Y σ τ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h
  exact h

/-- The boundary of the generator attached to a `(q+1)`-simplex, in the chain complex of `Y`. -/
lemma ιChainComplex_d_apply (Y : SSet.{0}) (q : ℕ) (τ : Y _⦋q+1⦌) :
    (ModuleCat.Hom.hom ((Y.chainComplex ezR).d (q + 1) q))
        (((Y.ιChainComplex (R := ezR) τ)).hom 1)
      = ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          ((Y.ιChainComplex (R := ezR) (Y.δ j τ)).hom 1) := by
  have h := congrArg (fun (f : ezR ⟶ (Y.chainComplex ezR).X q) => f.hom (1 : ℤ))
    (SSet.ιChainComplex_d Y ezR (n := q) τ)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.comp_apply] at h
  exact h

theorem ezGen_snd_sum_zero (X Y : SSet.{0}) (n q : ℕ) (σ : X _⦋n⦌) (τ : Y _⦋q+1⦌)
    (hτ : (ModuleCat.Hom.hom ((Y.chainComplex (ModuleCat.of ℤ ℤ)).d (q+1) q))
        (((Y.ιChainComplex (R := ModuleCat.of ℤ ℤ) τ)).hom 1) = 0) :
    (∑ j : Fin (q+2), ((-1 : ℤ) ^ (j : ℕ)) •
      Work.Cohomology.Crux33.ezGen n q X Y σ (Y.δ j τ)) = 0 := by
  have key : (∑ j : Fin (q+2), ((-1 : ℤ) ^ (j : ℕ)) •
        Work.Cohomology.Crux33.ezGen n q X Y σ (Y.δ j τ))
      = (ezLinSnd n q X Y σ).hom
          (∑ j : Fin (q+2), ((-1 : ℤ) ^ (j : ℕ)) •
            (Y.ιChainComplex (R := ezR) (Y.δ j τ)).hom 1) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_zsmul, ezLinSnd_apply]
  rw [key, ← ιChainComplex_d_apply Y q τ]
  have hτ' : (ModuleCat.Hom.hom ((Y.chainComplex ezR).d (q + 1) q))
      (((Y.ιChainComplex (R := ezR) τ)).hom 1) = 0 := hτ
  rw [hτ', map_zero]

end

end Work.SSS
