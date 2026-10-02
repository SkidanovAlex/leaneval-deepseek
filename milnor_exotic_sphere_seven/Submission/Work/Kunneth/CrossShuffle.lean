import Mathlib
import Submission.Work.Kunneth.ShuffleGood
import Submission.Work.Kunneth.crossCochain_apply
import Submission.Work.Kunneth.crossCochain_isCocycle
import Submission.Work.KunnethEZ.ezChain_eval_pp
import Submission.Work.KunnethEZ.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Kronecker rule for the cross product on the Eilenberg–Zilber shuffle

For cochains `α` of `X` (degree `p`) and `β` of `Y` (degree `q`) with `β` **normalized** (it
annihilates the degenerate `q`-simplices of `Y`), the cross product cochain
`Work.Kunneth.crossCochain X Y p q α β` evaluates on the Eilenberg–Zilber shuffle chain of a
`p`-chain `u` of `X` and a `q`-chain `v` of `Y` as

  `⟨α × β, ezChain u v⟩ = α(u) · β(v)`.

This is the chain-level Kronecker rule `⟨a × b, x × y⟩ = ⟨a,x⟩⟨b,y⟩` for the cohomology cross
product and the homology cross product carried by the shuffle.  There is **no sign**: of the
`C(p+q, q)` shuffle cells, only the exceptional shuffle `Work.Kunneth.goodShuf p q` (all `N`-steps
last) survives the normalized `β`, and its Eilenberg–Zilber sign is `+1`.

## Main results

* `crossCochain_ezCellGen` — the value of `α × β` on a single shuffle cell;
* `crossCochain_ezGen` — the value on the shuffle chain of a pair of simplices;
* `crossCochain_ezChain` — the value on the shuffle chain of a pair of chains.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial TensorProduct

namespace Work.Kunneth

noncomputable section

open Work.Cohomology
open Work.Cohomology.Crux33

/-- **The value of the cross product on a single shuffle cell.**  For the shuffle cell
`(σ ∘ a_S, τ ∘ b_S)` of the tensor product, the cross product `α × β` reads `α` on the front
`p`-face of the first coordinate and `β` on the back `q`-face of the second. -/
theorem crossCochain_ezCellGen (X Y : SSet) (p q : ℕ)
    (α : Cochain ℤ X p) (β : Cochain ℤ Y q)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) (S : PShuffle p q) :
    genEval ℤ (sProd X Y) (crossCochain X Y p q α β)
        (Work.KunnethEZ.ezCellGen p q X Y σ τ S)
      = genEval ℤ X α (X.map ((frontIncl p (p + q) (Nat.le_add_right p q)) ≫
            (aHom S.1 S.2)).op σ)
        * genEval ℤ Y β (Y.map ((backIncl p q) ≫ (bHom S.1 S.2)).op τ) := by
  rw [crossCochain_apply, backFaceLE_eq_backFace]
  simp only [Work.KunnethEZ.ezCellGen, Work.Cohomology.frontFace, Work.Cohomology.backFace]
  rw [Work.Cohomology.map_op_comp (aHom S.1 S.2)
        (frontIncl p (p + q) (Nat.le_add_right p q)) σ,
      Work.Cohomology.map_op_comp (bHom S.1 S.2) (backIncl p q) τ]

/-- **The value of the cross product on the shuffle chain of a pair of simplices.**  If `β`
annihilates the degenerate `q`-simplices of `Y`, then of all the shuffle cells only the exceptional
one survives, and it has sign `+1`. -/
theorem crossCochain_ezGen (X Y : SSet) (p q : ℕ)
    (α : Cochain ℤ X p) (β : Cochain ℤ Y q)
    (hβ : ∀ (x : Y _⦋q⦌), x ∈ Y.degenerate q → genEval ℤ Y β x = 0)
    (σ : X _⦋p⦌) (τ : Y _⦋q⦌) :
    crossCochain X Y p q α β (ezGen p q X Y σ τ) = genEval ℤ X α σ * genEval ℤ Y β τ := by
  have key : ∀ S : PShuffle p q,
      (crossCochain X Y p q α β)
        (shufSign S.1 • (((X ⊗ Y).ιChainComplex (R := Work.KunnethEZ.ezR)
          (Work.KunnethEZ.ezCellGen p q X Y σ τ S)).hom 1))
      = shufSign S.1 •
          (genEval ℤ X α (X.map ((frontIncl p (p + q) (Nat.le_add_right p q)) ≫
              (aHom S.1 S.2)).op σ)
            * genEval ℤ Y β (Y.map ((backIncl p q) ≫ (bHom S.1 S.2)).op τ)) := by
    intro S
    rw [Work.KunnethEZ.cochain_smul_chain (X ⊗ Y) _ (shufSign S.1) _]
    congr 1
    simpa only [genEval, Work.KunnethEZ.ezCellGen] using crossCochain_ezCellGen X Y p q α β σ τ S
  change (crossCochain X Y p q α β) (ezGen p q X Y σ τ)
      = genEval ℤ X α σ * genEval ℤ Y β τ
  rw [ezGen, map_sum]
  rw [Finset.sum_congr rfl (fun S _ => key S)]
  rw [Finset.sum_eq_single (goodShuf p q)]
  · have h1 : (ConcreteCategory.hom (X.map ((frontIncl p (p + q) (Nat.le_add_right p q)) ≫
        (aHom (goodShuf p q).1 (goodShuf p q).2)).op)) σ = σ := by
      have h := congrArg (fun (g : ⦋p⦌ ⟶ ⦋p⦌) => X.map g.op σ)
        (frontIncl_comp_aHom_goodShuf p q)
      simpa using h
    have h2 : (ConcreteCategory.hom (Y.map ((backIncl p q) ≫
        (bHom (goodShuf p q).1 (goodShuf p q).2)).op)) τ = τ := by
      have h := congrArg (fun (g : ⦋q⦌ ⟶ ⦋q⦌) => Y.map g.op τ)
        (backIncl_comp_bHom_goodShuf p q)
      simpa using h
    rw [h1, h2, shufSign_goodShuf, one_smul]
  · intro S _ hS
    have hns := not_surjective_backIncl_bHom_goodShufF p q S hS
    have hdeg : Y.map ((backIncl p q) ≫ (bHom S.1 S.2)).op τ ∈ Y.degenerate q :=
      mem_degenerate_of_not_surjective_self' _ hns τ
    rw [hβ _ hdeg, mul_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The scalar bookkeeping of the cross product evaluation**: the double sum of the products of
coordinates and values is the product of the two evaluations. -/
theorem crossSum_mul_cell (p q : ℕ) (X Y : SSet)
    (α : Cochain ℤ X p) (β : Cochain ℤ Y q)
    (u : (X.chainComplex Work.KunnethEZ.ezR).X p)
    (v : (Y.chainComplex Work.KunnethEZ.ezR).X q) :
    (∑ σ ∈ (coords X p u).support,
      ∑ τ ∈ (coords Y q v).support,
        (coords X p u σ * coords Y q v τ) •
          (genEval ℤ X α σ * genEval ℤ Y β τ))
      = α u * β v := by
  have hpu := Work.KunnethEZ.ezpp_eval_chain X p α u
  have hpv := Work.KunnethEZ.ezpp_eval_chain Y q β v
  calc (∑ σ ∈ (coords X p u).support,
      ∑ τ ∈ (coords Y q v).support,
        (coords X p u σ * coords Y q v τ) •
          (genEval ℤ X α σ * genEval ℤ Y β τ))
      = ∑ σ ∈ (coords X p u).support,
        ∑ τ ∈ (coords Y q v).support,
          (coords X p u σ * genEval ℤ X α σ) * (coords Y q v τ * genEval ℤ Y β τ) := by
        refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => ?_))
        rw [smul_eq_mul]; ring
    _ = (∑ σ ∈ (coords X p u).support, coords X p u σ * genEval ℤ X α σ)
          * (∑ τ ∈ (coords Y q v).support, coords Y q v τ * genEval ℤ Y β τ) := by
        rw [← Finset.sum_mul_sum]
    _ = α u * β v := by rw [hpu, hpv]

/-- **The Kronecker rule for the cross product, chain level.**  For a `p`-cochain `α` of `X` and a
normalized `q`-cochain `β` of `Y`, the cross product evaluates on the Eilenberg–Zilber shuffle
chain of a `p`-chain `u` of `X` and a `q`-chain `v` of `Y` as `α(u) · β(v)`. -/
theorem crossCochain_ezChain (X Y : SSet) (p q : ℕ)
    (α : Cochain ℤ X p) (β : Cochain ℤ Y q)
    (hβ : ∀ (x : Y _⦋q⦌), x ∈ Y.degenerate q → genEval ℤ Y β x = 0)
    (u : (X.chainComplex Work.KunnethEZ.ezR).X p)
    (v : (Y.chainComplex Work.KunnethEZ.ezR).X q) :
    crossCochain X Y p q α β (Work.KunnethEZ.ezChain p q X Y u v) = α u * β v :=
  (Work.KunnethEZ.ezChain_eval_double_sum p q X Y (crossCochain X Y p q α β)
    (fun σ τ => genEval ℤ X α σ * genEval ℤ Y β τ)
    (fun σ τ => crossCochain_ezGen X Y p q α β hβ σ τ) u v).trans
    (crossSum_mul_cell p q X Y α β u v)

end

end Work.Kunneth
