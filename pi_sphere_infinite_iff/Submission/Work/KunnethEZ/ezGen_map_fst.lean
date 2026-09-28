import Mathlib
import Submission.Work.KunnethEZ.ezGen_boundary
import Submission.Work.SSS.serreE1Defs
import Submission.Work.Cohomology.Crux33.EzGen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KunnethEZ

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial

/-- Naturality of the simplicial map `u ⊗ₘ 𝟙 Y` on a pair of simplices obtained by pulling back
along a pair of monotone maps. -/
private lemma tensorHom_app_aux {A Z Y : SSet} (u : A ⟶ Z) {p q : ℕ}
    (ψ : ⦋p+q⦌ ⟶ ⦋p⦌) (χ : ⦋p+q⦌ ⟶ ⦋q⦌) (σ : A _⦋p⦌) (τ : Y _⦋q⦌) :
    (u ⊗ₘ 𝟙 Y).app (op ⦋p+q⦌) (A.map ψ.op σ, Y.map χ.op τ)
      = (Z.map ψ.op (u.app (op ⦋p⦌) σ), Y.map χ.op τ) := by
  have h := SSet.tensorHom_app_apply u (𝟙 Y) (A.map ψ.op σ, Y.map χ.op τ)
  refine Prod.ext ?_ ?_
  · rw [show (((u ⊗ₘ 𝟙 Y).app (op ⦋p+q⦌)) (A.map ψ.op σ, Y.map χ.op τ)).1
        = (u.app (op ⦋p+q⦌)) (A.map ψ.op σ) from congrArg Prod.fst h]
    rw [← ConcreteCategory.comp_apply, u.naturality ψ.op, ConcreteCategory.comp_apply]
  · simp

/-- **Naturality of the Eilenberg–Zilber shuffle chain in the first factor.**

`Work.Cohomology.Crux33.ezGen n q X Y σ τ` is the shuffle chain of `σ ∈ X_n` and `τ ∈ Y_q`, a chain
of `X ⊗ Y` in degree `n + q` whose summands are `shufSign S • (σ ∘ a_S, τ ∘ b_S)` over the
`(n,q)`-shuffles `S`.  Since the first coordinate is `σ` composed with a map into `X`, the shuffle
chain is natural in that coordinate: for `u : A ⟶ Z` and `σ ∈ A_n`, applying `u` to `σ` gives the
image of the shuffle chain of `(σ,τ)` under the chain map induced by `u ⊗ₘ 𝟙 Y`.

Key inputs: `SSet.ι_chainComplexMap_f` (the chain map on a generator), `SSet.tensorHom_app_apply`
(`(f ⊗ₘ g).app Δ x = (f.app Δ x.1, g.app Δ x.2)`) and `u`'s naturality. -/
theorem ezGen_map_fst {A Z Y : SSet.{0}} (n q : ℕ) (u : A ⟶ Z) (σ : A _⦋n⦌)
    (τ : Y _⦋q⦌) :
    Work.Cohomology.Crux33.ezGen n q Z Y (u.app (op ⦋n⦌) σ) τ
      = (Work.SSS.sCCMap (u ⊗ₘ 𝟙 Y)).f (n+q) (Work.Cohomology.Crux33.ezGen n q A Y σ τ) := by
  classical
  -- The chain map `sCCMap (u ⊗ₘ 𝟙 Y)` in degree `n+q`, as a linear map (so that it is additive
  -- and `ℤ`-linear on the shuffle sum).
  let F : ((A ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X (n + q) →ₗ[ℤ]
      ((Z ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X (n + q) :=
    ((Work.SSS.sCCMap (u ⊗ₘ 𝟙 Y)).f (n + q)).hom
  change Work.Cohomology.Crux33.ezGen n q Z Y (u.app (op ⦋n⦌) σ) τ
    = F (Work.Cohomology.Crux33.ezGen n q A Y σ τ)
  -- On generators, the chain map is the induced map on simplices.
  have hFgen : ∀ x : (A ⊗ Y) _⦋n+q⦌,
      F (((A ⊗ Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1)
        = (((Z ⊗ Y).ιChainComplex (R := ModuleCat.of ℤ ℤ)
              ((u ⊗ₘ 𝟙 Y).app (op ⦋n+q⦌) x)).hom 1) := by
    intro x
    change ((Work.SSS.sCCMap (u ⊗ₘ 𝟙 Y)).f (n+q)).hom
        (((A ⊗ Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) x).hom 1) = _
    have h := SSet.ι_chainComplexMap_f (f := u ⊗ₘ 𝟙 Y) (R := ModuleCat.of ℤ ℤ) (x := x)
    have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶
        ((Z ⊗ Y).chainComplex (ModuleCat.of ℤ ℤ)).X (n+q)) => g.hom (1 : ℤ)) h
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2
  -- Unfold the shuffle chains and push `F` through the sum.
  rw [Work.Cohomology.Crux33.ezGen, Work.Cohomology.Crux33.ezGen]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [map_zsmul]
  congr 1
  rw [hFgen]
  rw [tensorHom_app_aux u (Work.Cohomology.Crux33.aHom S.1 S.2)
    (Work.Cohomology.Crux33.bHom S.1 S.2) σ τ]

end Work.KunnethEZ
