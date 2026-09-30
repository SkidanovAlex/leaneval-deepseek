import Mathlib
import Submission.Work.SSSR.ezGen_snd_sum_zero
import Submission.Work.SSSR.KunnethEZ.ezGen_map_fst
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
noncomputable section

/-- **Naturality of the linearised shuffle chain in the first variable.**  For a simplicial map
`u : A ⟶ Z`, a simplex `σ` of `A` and an arbitrary chain `v` of `Y`, the shuffle chain of `σ` and
`v` is carried by `u ⊗ₘ 𝟙 Y` to the shuffle chain of `u σ` and `v`. -/
lemma ezLinSnd_map_fst {A Z Y : SSet.{0}} (n q : ℕ) (u : A ⟶ Z) (σ : A _⦋n⦌)
    (v : (Y.chainComplex (Work.SSSR.ezR R)).X q) :
    (Work.SSSR.sCCMap R (u ⊗ₘ 𝟙 Y)).f (n+q) ((Work.SSSR.ezLinSnd n q A Y σ).hom v)
      = (Work.SSSR.ezLinSnd n q Z Y (u.app (op ⦋n⦌) σ)).hom v := by
  conv_lhs => rw [Work.SSSR.KunnethEZ.chain_eq_sum_gen Y q v]
  conv_rhs => rw [Work.SSSR.KunnethEZ.chain_eq_sum_gen Y q v]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [show Work.SSSR.KunnethEZ.genC Y τ = (Y.ιChainComplex (R := (Work.SSSR.ezR R)) τ).hom 1 from rfl,
    Work.SSSR.ezLinSnd_apply, Work.SSSR.ezLinSnd_apply]
  exact congrArg (fun x => ((Work.SSSR.Cohomology.Crux33.coords Y q) v) τ • x)
    (Work.SSSR.KunnethEZ.ezGen_map_fst n q u σ τ).symm


end

end Work.SSSR
