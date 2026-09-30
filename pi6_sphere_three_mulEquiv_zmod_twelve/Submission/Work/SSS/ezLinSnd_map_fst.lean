import Mathlib
import Submission.Work.SSS.ezGen_snd_sum_zero
import Submission.Work.KunnethEZ.ezGen_map_fst

/-!
# Naturality of the linearised Eilenberg–Zilber shuffle chain in the first variable

`Work.SSS.ezLinSnd n q X Y σ` is the ℤ-linear extension, in the second variable, of the
simplex-level shuffle chain `ezGen n q X Y σ`.  This file records that this extension is natural in
the first variable: pushing the shuffle chain of `σ` along a simplicial map `u` gives the shuffle
chain of `u σ`.
-/

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial

noncomputable section

/-- **Naturality of the linearised shuffle chain in the first variable.**  For a simplicial map
`u : A ⟶ Z`, a simplex `σ` of `A` and an arbitrary chain `v` of `Y`, the shuffle chain of `σ` and
`v` is carried by `u ⊗ₘ 𝟙 Y` to the shuffle chain of `u σ` and `v`. -/
lemma ezLinSnd_map_fst {A Z Y : SSet.{0}} (n q : ℕ) (u : A ⟶ Z) (σ : A _⦋n⦌)
    (v : (Y.chainComplex Work.SSS.ezR).X q) :
    (Work.SSS.sCCMap (u ⊗ₘ 𝟙 Y)).f (n+q) ((Work.SSS.ezLinSnd n q A Y σ).hom v)
      = (Work.SSS.ezLinSnd n q Z Y (u.app (op ⦋n⦌) σ)).hom v := by
  conv_lhs => rw [Work.KunnethEZ.chain_eq_sum_gen Y q v]
  conv_rhs => rw [Work.KunnethEZ.chain_eq_sum_gen Y q v]
  simp only [map_sum, map_zsmul]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [show Work.KunnethEZ.genC Y τ = (Y.ιChainComplex (R := Work.SSS.ezR) τ).hom 1 from rfl,
    Work.SSS.ezLinSnd_apply, Work.SSS.ezLinSnd_apply]
  exact congrArg (fun x => ((Work.Cohomology.Crux33.coords Y q) v) τ • x)
    (Work.KunnethEZ.ezGen_map_fst n q u σ τ).symm


end

end Work.SSS
