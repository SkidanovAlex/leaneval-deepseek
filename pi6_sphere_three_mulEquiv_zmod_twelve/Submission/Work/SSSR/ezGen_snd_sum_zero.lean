import Mathlib
import Submission.Work.SSSR.KunnethEZ.ezGen_boundary
import Submission.Work.SSSR.KunnethEZ.Defs
import Submission.Work.SSSR.KunnethEZ.ezChain_isCycle
import Submission.Work.SSSR.KunnethEZ.ez23_eq_ezGen
import Submission.Work.SSSR.serreE1Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

/-- The coefficient ring `ℤ`, as a module over itself, spelled once. -/
abbrev ezR (R : Type) [CommRing R] [Nontrivial R] : ModuleCat R := ModuleCat.of R R

/-- **The linear extension of the Eilenberg–Zilber shuffle chain in the second variable.**

For a fixed `n`-simplex `σ` of `X`, the assignment `τ' ↦ ezGen n q X Y σ τ'` on `q`-simplices of
`Y` extends uniquely to a `ℤ`-linear map out of the `q`-chains of `Y` (the `q`-chains are the free
`ℤ`-module on the `q`-simplices, so there is no compatibility condition to check). -/
def ezLinSnd (n q : ℕ) (X Y : SSet.{0}) (σ : X _⦋n⦌) :
    (Y.chainComplex (ezR R)).X q ⟶ ((X ⊗ Y).chainComplex (ezR R)).X (n + q) :=
  (Y.isColimitChainComplexXCofan (ezR R) q).desc
    (Cofan.mk (((X ⊗ Y).chainComplex (ezR R)).X (n + q))
      (fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton R
        ↥(((X ⊗ Y).chainComplex (ezR R)).X (n + q))
        (Work.SSSR.Cohomology.Crux33.ezGen n q X Y σ τ))))

/-- The defining property of `ezLinSnd` on the generators of the chain complex. -/
lemma ezLinSnd_ι (n q : ℕ) (X Y : SSet.{0}) (σ : X _⦋n⦌) (τ : Y _⦋q⦌) :
    (Y.ιChainComplex (R := (ezR R)) τ) ≫ ezLinSnd n q X Y σ
      = ModuleCat.ofHom (LinearMap.toSpanSingleton R
          ↥(((X ⊗ Y).chainComplex (ezR R)).X (n + q))
          (Work.SSSR.Cohomology.Crux33.ezGen n q X Y σ τ)) :=
  Cofan.IsColimit.fac _ _ _

/-- The value of `ezLinSnd` on a generator simplex is the shuffle chain. -/
lemma ezLinSnd_apply (n q : ℕ) (X Y : SSet.{0}) (σ : X _⦋n⦌) (τ : Y _⦋q⦌) :
    (ezLinSnd n q X Y σ).hom ((Y.ιChainComplex (R := (ezR R)) τ).hom 1)
      = Work.SSSR.Cohomology.Crux33.ezGen n q X Y σ τ := by
  have h := congrArg
    (fun (f : (ezR R) ⟶ ((X ⊗ Y).chainComplex (ezR R)).X (n + q)) => f.hom (1 : R))
    (ezLinSnd_ι n q X Y σ τ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h
  exact h

end

end Work.SSSR
