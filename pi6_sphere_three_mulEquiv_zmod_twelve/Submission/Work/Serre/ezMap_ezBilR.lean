import Mathlib
import Submission.Work.Serre.ezShuffleRat
import Submission.Work.Serre.ezShuffleEval
import Submission.Work.Kunneth.CrossCup

/-!
# The Eilenberg–Zilber shuffle map on a pure tensor is the bilinear shuffle chain

`Work.Kunneth.ezMap X Y : C_*(X) ⊗_ℤ C_*(Y) ⟶ C_*(X ⊗ Y)` is the Eilenberg–Zilber shuffle chain
map of `Work.Kunneth`; `Work.Serre.ezBilR ℤ p q X Y` is the bilinear shuffle chain of
`Work.Serre.ezShuffleRat`, characterised on a pair of generators by `ezBilR_gen`.

The present file identifies the two:

* `Work.Serre.ezChain_eq_ezBilR` — the shuffle chain `Work.KunnethEZ.ezChain` of two chains is the
  value of the bilinear shuffle map (both are the bilinear extension of the shuffle chain of a pair
  of simplices, `Work.Cohomology.Crux33.ezGen`);
* `Work.Serre.ezMap_ezBilR` — consequently the shuffle chain map sends the summand generator
  `u ⊗ v` of the tensor product to `ezBilR ℤ p q X Y u v`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Serre

noncomputable section

/-- The pointwise description of a `ℤ`-scalar multiple of a linear map.  Stated with abstract
types and instances so that the instance arguments of the two `ℤ`-actions are unified at
elaboration time (the two `Module ℤ` structures on a `ModuleCat` object are only propositionally
equal, so a blind rewrite with `LinearMap.smul_apply` would fail to match). -/
lemma smul_apply_zsmul {B M : Type*} [AddCommGroup B] [AddCommGroup M] [Module ℤ B]
    [Module ℤ M] (c : ℤ) (F : B →ₗ[ℤ] M) (y : B) : (c • F) y = c • (F y) := rfl

/-- **The shuffle chain of two chains is the value of the bilinear shuffle map.**  Both sides are
the bilinear extension of the shuffle chain of a pair of simplices; the proof expands the two
chains in the generators attached to their simplices
(`Work.KunnethEZ.chain_eq_sum_gen`) and compares the resulting double sums term by term. -/
lemma ezChain_eq_ezBilR (X Y : SSet) (p q : ℕ)
    (u : (X.chainComplex (ModuleCat.of ℤ ℤ)).X p)
    (v : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X q) :
    Work.KunnethEZ.ezChain p q X Y u v = (ezBilR ℤ p q X Y).hom u v := by
  rw [Work.KunnethEZ.chain_eq_sum_gen X p u, Work.KunnethEZ.chain_eq_sum_gen Y q v]
  rw [Work.KunnethEZ.ezChain_sum_left]
  simp only [Work.KunnethEZ.ezChain_sum_right]
  rw [map_sum]
  simp only [map_zsmul]
  rw [map_sum]
  simp only [map_zsmul]
  simp only [LinearMap.sum_apply]
  simp only [smul_apply_zsmul]
  simp only [← Work.KunnethEZ.zsmul_mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [mul_comm]
  congr 1
  rw [Work.KunnethEZ.ezChain_gen, Work.Serre.ezBilR_gen]
  rfl

theorem ezMap_ezBilR (X Y : SSet) (p q : ℕ) (u : (Work.Kunneth.sChain X).X p)
    (v : (Work.Kunneth.sChain Y).X q) :
    ((Work.Kunneth.ezMap X Y).f (p + q))
        (Work.Kunneth.tpLof (Work.Kunneth.sChain X) (Work.Kunneth.sChain Y) (p + q)
          ⟨(p, q), rfl⟩ (TensorProduct.tmul ℤ u v))
      = Work.Serre.ezBilR ℤ p q X Y u v := by
  rw [Work.Kunneth.ezMap_tpLof]
  exact ezChain_eq_ezBilR X Y p q u v

end

end Work.Serre
