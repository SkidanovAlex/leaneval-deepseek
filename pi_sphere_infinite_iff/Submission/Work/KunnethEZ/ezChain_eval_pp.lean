import Mathlib
import Submission.Work.KunnethEZ.Defs
import Submission.Work.KunnethEZ.ezGen_eval_pp
import Submission.Work.Cohomology.Kunneth.ezEval
import Submission.Work.Cohomology.CupRing

/-!
# The evaluation half of the general `(p,p)` Eilenberg–Zilber shuffle computation, for chains

`Work.KunnethEZ.ezChain p p X Y u v` is the shuffle chain of a `p`-chain `u` of `X` and a
`p`-chain `v` of `Y`, the `ℤ`-bilinear extension of the simplex-level shuffle chain
`Work.Cohomology.Crux33.ezGen p p X Y σ τ`.  This file proves that the Alexander–Whitney cup
product of the pullbacks of a cochain `θ` on the second factor (pulled back along `snd`) and a
cochain `β` on the first factor (pulled back along `fst`) evaluates on it as

`⟨(snd^*θ) ⌣ (fst^*β), ezChain u v⟩ = (-1)^(p*p) · θ(v) · β(u)`

whenever `θ` annihilates the degenerate `p`-simplices of `Y`.

This is the chain-level form of `Work.KunnethEZ.ezGen_eval_pp`; it is obtained by expanding the
chains into their generators and using bilinearity, the simplex-level computation supplying the
value on each pair of generators.

## Main results

* `ezpp_mk_eq_sum_gen`, `ezpp_chain_eq_sum_gen` — a chain is the sum of its generators;
* `ezpp_eval_chain` — the evaluation of a cochain on a chain, as a sum over generators;
* `ezChain_eval_double_sum` — the shuffle chain, with the pairing expanded over the generators;
* `pp_sum_mul_cell` — the scalar bookkeeping of the evaluation;
* `ezChain_eval_of_cell` — the evaluation given the value on generators;
* `ezChain_eval_pp` — the statement.
-/

set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.KunnethEZ

open Work.Cohomology

noncomputable section

/-! ## Chains as sums of their generators -/

/-- `Work.Cohomology.Crux33.mk` on a finitely supported function, expanded. -/
lemma ezpp_mk_eq_sum_gen (X : SSet) (n : ℕ) (c : X _⦋n⦌ →₀ ℤ) :
    Work.Cohomology.Crux33.mk X n c
      = ∑ x ∈ c.support, (c x) • (X.ιChainComplex (R := ezR) x).hom 1 := by
  change (Finsupp.liftAddHom
    (fun x : X _⦋n⦌ => (ModuleCat.Hom.hom (X.ιChainComplex (R := ezR) x)).toAddMonoidHom)) c
    = ∑ x ∈ c.support, (c x) • (X.ιChainComplex (R := ezR) x).hom 1
  rw [Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  show (ModuleCat.Hom.hom (X.ιChainComplex (R := ezR) x)) (c x) = _
  rw [show c x = (c x) • (1 : ℤ) from ((smul_eq_mul _ _).trans (mul_one _)).symm, map_zsmul,
    show (c x) • (1 : ℤ) = c x from (smul_eq_mul _ _).trans (mul_one _)]

/-- **A chain is the sum of its generators.** -/
lemma ezpp_chain_eq_sum_gen (X : SSet) (n : ℕ) (u : (X.chainComplex ezR).X n) :
    u = ∑ x ∈ (Work.Cohomology.Crux33.coords X n u).support,
          (Work.Cohomology.Crux33.coords X n u x) • (X.ιChainComplex (R := ezR) x).hom 1 := by
  rw [← ezpp_mk_eq_sum_gen X n (Work.Cohomology.Crux33.coords X n u)]
  exact (LinearMap.congr_fun (Work.Cohomology.Crux33.mk_comp_coords X n) u).symm

/-- The evaluation of a cochain `β` on a chain `u`, as a sum over the generators of `u`. -/
lemma ezpp_eval_chain (X : SSet) (n : ℕ) (β : Work.Cohomology.Cochain ℤ X n)
    (u : (X.chainComplex ezR).X n) :
    (∑ σ ∈ (Work.Cohomology.Crux33.coords X n u).support,
        Work.Cohomology.Crux33.coords X n u σ * Work.Cohomology.genEval ℤ X β σ) = β u := by
  have e : (∑ σ ∈ (Work.Cohomology.Crux33.coords X n u).support,
        Work.Cohomology.Crux33.coords X n u σ * Work.Cohomology.genEval ℤ X β σ)
      = ∑ σ ∈ (Work.Cohomology.Crux33.coords X n u).support,
          β ((Work.Cohomology.Crux33.coords X n u σ) •
            (X.ιChainComplex (R := ezR) σ).hom 1) := by
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [show Work.Cohomology.genEval ℤ X β σ
        = β ((X.ιChainComplex (R := ezR) σ).hom 1) from rfl]
    rw [← smul_eq_mul]
    exact (map_zsmul β (Work.Cohomology.Crux33.coords X n u σ) _).symm
  rw [e, ← map_sum, ← ezpp_chain_eq_sum_gen X n u]

/-! ## The shuffle chain of two chains, expanded over the generators -/

/-- **The shuffle chain of two chains, expanded over the generators.**  For any cochain `γ` on
`X ⊗ Y` whose value on a shuffle cell `ezGen p q X Y σ τ` is `F σ τ`, the pairing of `γ` with the
shuffle chain of `u` and `v` is the double sum of `(coeff of σ)·(coeff of τ)·F σ τ`. -/
lemma ezChain_eval_double_sum (p q : ℕ) (X Y : SSet)
    (γ : Work.Cohomology.Cochain ℤ (X ⊗ Y) (p + q))
    (F : (σ : X _⦋p⦌) → (τ : Y _⦋q⦌) → ℤ)
    (hcell : ∀ (σ : X _⦋p⦌) (τ : Y _⦋q⦌),
      γ (Work.Cohomology.Crux33.ezGen p q X Y σ τ) = F σ τ)
    (u : (X.chainComplex ezR).X p) (v : (Y.chainComplex ezR).X q) :
    γ (ezChain p q X Y u v)
      = ∑ σ ∈ (Work.Cohomology.Crux33.coords X p u).support,
        ∑ τ ∈ (Work.Cohomology.Crux33.coords Y q v).support,
          (Work.Cohomology.Crux33.coords X p u σ * Work.Cohomology.Crux33.coords Y q v τ) •
            F σ τ := by
  simp only [ezChain, map_sum, map_zsmul]
  refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => ?_))
  rw [hcell σ τ]

/-! ## The scalar bookkeeping -/

/-- **The scalar bookkeeping of the `(p,p)` evaluation**: the double sum of the cell values
`(a σ · b τ) • ((-1)^(p·p) · θ τ · β σ)` is `(-1)^(p·p) · θ v · β u`, by bilinearity. -/
lemma pp_sum_mul_cell (p : ℕ) (X Y : SSet) (β : Work.Cohomology.Cochain ℤ X p)
    (θ : Work.Cohomology.Cochain ℤ Y p)
    (u : (X.chainComplex ezR).X p) (v : (Y.chainComplex ezR).X p) :
    (∑ σ ∈ (Work.Cohomology.Crux33.coords X p u).support,
      ∑ τ ∈ (Work.Cohomology.Crux33.coords Y p v).support,
        (Work.Cohomology.Crux33.coords X p u σ * Work.Cohomology.Crux33.coords Y p v τ) •
          (((-1 : ℤ) ^ (p*p)) * Work.Cohomology.genEval ℤ Y θ τ *
            Work.Cohomology.genEval ℤ X β σ))
      = ((-1 : ℤ) ^ (p*p)) * θ v * β u := by
  have hpu := ezpp_eval_chain X p β u
  have hpv := ezpp_eval_chain Y p θ v
  calc (∑ σ ∈ (Work.Cohomology.Crux33.coords X p u).support,
      ∑ τ ∈ (Work.Cohomology.Crux33.coords Y p v).support,
        (Work.Cohomology.Crux33.coords X p u σ * Work.Cohomology.Crux33.coords Y p v τ) •
          (((-1 : ℤ) ^ (p*p)) * Work.Cohomology.genEval ℤ Y θ τ *
            Work.Cohomology.genEval ℤ X β σ))
      = ∑ σ ∈ (Work.Cohomology.Crux33.coords X p u).support,
        ∑ τ ∈ (Work.Cohomology.Crux33.coords Y p v).support,
          ((-1 : ℤ) ^ (p*p)) *
            ((Work.Cohomology.Crux33.coords X p u σ * Work.Cohomology.genEval ℤ X β σ) *
             (Work.Cohomology.Crux33.coords Y p v τ * Work.Cohomology.genEval ℤ Y θ τ)) := by
        refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun τ _ => ?_))
        rw [smul_eq_mul]; ring
    _ = ((-1 : ℤ) ^ (p*p)) *
          (∑ σ ∈ (Work.Cohomology.Crux33.coords X p u).support,
            ∑ τ ∈ (Work.Cohomology.Crux33.coords Y p v).support,
              (Work.Cohomology.Crux33.coords X p u σ * Work.Cohomology.genEval ℤ X β σ) *
              (Work.Cohomology.Crux33.coords Y p v τ * Work.Cohomology.genEval ℤ Y θ τ)) := by
        rw [Finset.sum_congr rfl (fun σ _ => (Finset.mul_sum
          (Work.Cohomology.Crux33.coords Y p v).support
          (fun τ => (Work.Cohomology.Crux33.coords X p u σ * Work.Cohomology.genEval ℤ X β σ) *
              (Work.Cohomology.Crux33.coords Y p v τ * Work.Cohomology.genEval ℤ Y θ τ))
          ((-1 : ℤ) ^ (p*p))).symm)]
        rw [← Finset.mul_sum (Work.Cohomology.Crux33.coords X p u).support
          (fun σ => ∑ τ ∈ (Work.Cohomology.Crux33.coords Y p v).support,
            (Work.Cohomology.Crux33.coords X p u σ * Work.Cohomology.genEval ℤ X β σ) *
            (Work.Cohomology.Crux33.coords Y p v τ * Work.Cohomology.genEval ℤ Y θ τ))
          ((-1 : ℤ) ^ (p*p))]
    _ = ((-1 : ℤ) ^ (p*p)) *
          ((∑ σ ∈ (Work.Cohomology.Crux33.coords X p u).support,
              Work.Cohomology.Crux33.coords X p u σ * Work.Cohomology.genEval ℤ X β σ) *
            (∑ τ ∈ (Work.Cohomology.Crux33.coords Y p v).support,
              Work.Cohomology.Crux33.coords Y p v τ * Work.Cohomology.genEval ℤ Y θ τ)) := by
        rw [← Finset.sum_mul_sum (Work.Cohomology.Crux33.coords X p u).support
          (Work.Cohomology.Crux33.coords Y p v).support
          (fun σ => Work.Cohomology.Crux33.coords X p u σ * Work.Cohomology.genEval ℤ X β σ)
          (fun τ => Work.Cohomology.Crux33.coords Y p v τ * Work.Cohomology.genEval ℤ Y θ τ)]
    _ = ((-1 : ℤ) ^ (p*p)) * β u * θ v := by rw [hpu, hpv]; ring
    _ = ((-1 : ℤ) ^ (p*p)) * θ v * β u := by ring

/-! ## The evaluation -/

/-- **The evaluation of the cup product on the shuffle chain, given its value on the shuffle
cells.** -/
lemma ezChain_eval_of_cell (p : ℕ) (X Y : SSet)
    (γ : Work.Cohomology.Cochain ℤ (X ⊗ Y) (p + p))
    (β : Work.Cohomology.Cochain ℤ X p) (θ : Work.Cohomology.Cochain ℤ Y p)
    (hcell : ∀ (σ : X _⦋p⦌) (τ : Y _⦋p⦌),
      γ (Work.Cohomology.Crux33.ezGen p p X Y σ τ)
        = ((-1 : ℤ) ^ (p*p)) * Work.Cohomology.genEval ℤ Y θ τ *
            Work.Cohomology.genEval ℤ X β σ)
    (u : (X.chainComplex ezR).X p) (v : (Y.chainComplex ezR).X p) :
    γ (ezChain p p X Y u v) = ((-1 : ℤ) ^ (p*p)) * θ v * β u :=
  (ezChain_eval_double_sum p p X Y γ
      (fun σ τ => ((-1 : ℤ) ^ (p*p)) * Work.Cohomology.genEval ℤ Y θ τ *
        Work.Cohomology.genEval ℤ X β σ) hcell u v).trans
    (pp_sum_mul_cell p X Y β θ u v)

theorem ezChain_eval_pp (p : ℕ) (hp : 1 ≤ p) (X Y : SSet)
    (β : Work.Cohomology.Cochain ℤ X p) (θ : Work.Cohomology.Cochain ℤ Y p)
    (hθ : ∀ (x : Y.obj (Opposite.op (SimplexCategory.mk p))), x ∈ Y.degenerate p →
        Work.Cohomology.genEval ℤ Y θ x = 0)
    (u : (X.chainComplex (ModuleCat.of ℤ ℤ)).X p) (v : (Y.chainComplex (ModuleCat.of ℤ ℤ)).X p) :
    Work.Cohomology.cup ℤ (CategoryTheory.MonoidalCategory.tensorObj X Y)
        (Work.Cohomology.Kunneth.ssetPullback (CategoryTheory.MonoidalCategory.tensorObj X Y) Y
          (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) p θ)
        (Work.Cohomology.Kunneth.ssetPullback (CategoryTheory.MonoidalCategory.tensorObj X Y) X
          (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p β)
      (Work.KunnethEZ.ezChain p p X Y u v)
      = ((-1 : ℤ) ^ (p*p)) * θ v * β u :=
  ezChain_eval_of_cell p X Y
    (Work.Cohomology.cup ℤ (X ⊗ Y)
      (Work.Cohomology.Kunneth.ssetPullback (X ⊗ Y) Y
        (SemiCartesianMonoidalCategory.snd X Y) p θ)
      (Work.Cohomology.Kunneth.ssetPullback (X ⊗ Y) X
        (SemiCartesianMonoidalCategory.fst X Y) p β))
    β θ
    (fun σ τ => Work.KunnethEZ.ezGen_eval_pp p hp X Y β θ σ τ hθ)
    u v

end

end Work.KunnethEZ
