import Mathlib
import Submission.Work.KunnethEZ.ezGen_boundary
import Submission.Work.SSS.serreE1Defs
import Submission.Work.Cohomology.Crux33.EzGen

namespace Work.KunnethEZ

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped Simplicial

/-- **Naturality of the Eilenberg–Zilber shuffle chain in the second factor.**

`Work.Cohomology.Crux33.ezGen n q X Y σ τ` is the shuffle chain of `σ ∈ X_n` and `τ ∈ Y_q`, a chain
of `X ⊗ Y` in degree `n + q` whose summands are `shufSign S • (σ ∘ a_S, τ ∘ b_S)` over the
`(n,q)`-shuffles `S`.  Since the second coordinate is `τ` composed with a map into `Y`, the shuffle
chain is natural in that coordinate: for `u : B ⟶ Z` and `τ ∈ B_q`, applying `u` to `τ` gives the
image of the shuffle chain of `(σ,τ)` under the chain map induced by `𝟙 X ⊗ₘ u`.

Key inputs: `SSet.ι_chainComplexMap_f` (the chain map on a generator), `SSet.tensorHom_app_apply`
(`(f ⊗ₘ g).app Δ x = (f.app Δ x.1, g.app Δ x.2)`) and `u`'s naturality.  This is the exact mirror of
`Work.KunnethEZ.ezGen_map_fst`. -/
theorem ezGen_map_snd {X B Z : SSet.{0}} (n q : ℕ) (u : B ⟶ Z) (σ : X _⦋n⦌)
    (τ : B _⦋q⦌) :
    Work.Cohomology.Crux33.ezGen n q X Z σ (u.app (op ⦋q⦌) τ)
      = (Work.SSS.sCCMap (𝟙 X ⊗ₘ u)).f (n+q) (Work.Cohomology.Crux33.ezGen n q X B σ τ) := by
  -- Unfold the two shuffle chains and push the (linear) chain map through the finite sum and the
  -- integer scalar multiples; it then suffices to match the summands shuffle by shuffle.
  simp only [Work.Cohomology.Crux33.ezGen, map_sum, map_zsmul]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  refine congrArg (fun t => Work.Cohomology.Crux33.shufSign S.1 • t) ?_
  -- Rewrite the second coordinate `Z.map b.op (u.app τ)` of the target shuffle cell into the form
  -- `u.app (B.map b.op τ)` produced by the chain map, using the naturality of `u`.
  rw [← NatTrans.naturality_apply u (Work.Cohomology.Crux33.bHom S.1 S.2).op τ]
  -- `SSet.ι_chainComplexMap_f` computes the chain map on the generator attached to a simplex.
  have h := congrArg (fun (g : Work.KunnethEZ.eZR ⟶
        ((X ⊗ Z).chainComplex Work.KunnethEZ.eZR).X (n+q)) => g.hom (1 : ℤ))
    (SSet.ι_chainComplexMap_f (X := X ⊗ B) (Y := X ⊗ Z) (f := 𝟙 X ⊗ₘ u)
      (R := Work.KunnethEZ.eZR) (n := n+q)
      (x := ((X.map (Work.Cohomology.Crux33.aHom S.1 S.2).op) σ,
             (B.map (Work.Cohomology.Crux33.bHom S.1 S.2).op) τ)))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

end Work.KunnethEZ
