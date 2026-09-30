import Mathlib
import Submission.Work.Cohomology.Kunneth.ezSetup
import Submission.Work.Cohomology.Crux33.witnessAux
import Submission.Work.Cohomology.cupLeibniz

/-!
# The evaluation half of the Eilenberg–Zilber shuffle computation

For the `(3,3)`-shuffle chain `Work.Cohomology.Kunneth.ezGen X Y σ τ` (the sum over the twenty
shuffles `S` of `shufSign S • (σ ∘ a_S, τ ∘ b_S)` in the tensor product `X ⊗ Y`), the
Alexander–Whitney cup product of the pullbacks of a `3`-cocycle `β` on `X` (first factor) and a
`3`-cocycle `θ` on `Y` (second factor) evaluates as

`⟨(snd^*θ) ⌣ (fst^*β), ezGen σ τ⟩ = shufSign(good) · θ(τ) · β(σ)`,

where `good` is the shuffle `E E E N N N` (all `N`-steps last).  Of the twenty cells, only `good`
has both relevant faces equal to the identity: the front `3`-face of the first coordinate is
`a_S ∘ frontIncl(3,6)`, which is non-surjective for every other `S`, and then the back `3`-face of
the second coordinate is `b_S ∘ backIncl(3,3)`, non-surjective for every other `S`.  The junk terms
are therefore killed by any cocycle `θ` which annihilates such composites; concretely we use the
hypothesis that `θ` vanishes on `Y.map g.op τ` for every non-surjective monotone `g : ⦋3⦌ ⟶ ⦋3⦌`
(this holds for instance for the *normalized* cocycles `α ∘ PInfty`, which annihilate all
degenerate simplices).

## Main results

* `ssetPullback`, `ssetPullback_genEval` — the pullback of a cochain along a simplicial map and
  its evaluation on a generator;
* `frontFace_prod`, `backFace_prod` — the front and back faces of a simplex of a product of
  simplicial sets are computed componentwise;
* `ezGen_eval_ne_zero_of_cocycles` — the evaluated form of the shuffle computation.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Cohomology.Kunneth

noncomputable section

open Work.Cohomology

/-- The pullback of a cochain along a morphism of simplicial sets. -/
def ssetPullback (X Y : SSet) (f : X ⟶ Y) (n : ℕ) (β : Cochain ℤ Y n) : Cochain ℤ X n :=
  ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).f n).hom.dualMap β

/-- The value of a pulled-back cochain on a generator. -/
lemma ssetPullback_genEval (X Y : SSet) (f : X ⟶ Y) (n : ℕ) (β : Cochain ℤ Y n)
    (x : X _⦋n⦌) :
    genEval ℤ X (ssetPullback X Y f n β) x
      = genEval ℤ Y β ((ConcreteCategory.hom (f.app (Opposite.op ⦋n⦌))) x) := by
  have h := SSet.ι_chainComplexMap_f X Y f (ModuleCat.of ℤ ℤ) x
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (Y.chainComplex (ModuleCat.of ℤ ℤ)).X n)
    => β (g.hom (1 : ℤ))) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
  rw [genEval, genEval, ssetPullback, LinearMap.dualMap_apply]
  exact h2

/-- The front face of a product simplex, componentwise. -/
lemma frontFace_prod_mk (X Y : SSet) (n N : ℕ) (h : n ≤ N) (u : X _⦋N⦌) (v : Y _⦋N⦌) :
    frontFace (X ⊗ Y) n N h (u, v) = (frontFace X n N h u, frontFace Y n N h v) := rfl

/-- The back face of a product simplex, componentwise. -/
lemma backFace_prod_mk (X Y : SSet) (n m : ℕ) (u : X _⦋n + m⦌) (v : Y _⦋n + m⦌) :
    backFace (X ⊗ Y) n m (u, v) = (backFace X n m u, backFace Y n m v) := rfl

/-- The product projections on simplices, componentwise. -/
@[simp] lemma fst_apply_prod (X Y : SSet) (n : ℕ) (u : X _⦋n⦌) (v : Y _⦋n⦌) :
    (SemiCartesianMonoidalCategory.fst X Y).app (Opposite.op ⦋n⦌) (u, v) = u := rfl

@[simp] lemma snd_apply_prod (X Y : SSet) (n : ℕ) (u : X _⦋n⦌) (v : Y _⦋n⦌) :
    (SemiCartesianMonoidalCategory.snd X Y).app (Opposite.op ⦋n⦌) (u, v) = v := rfl

/-- The front face of the `N`-coordinate of a shuffle cell, as a composite. -/
lemma frontFace_bHom_comp (Y : SSet) (S : Shuf) (τ : Y _⦋3⦌) :
    frontFace Y 3 (3 + 3) (Nat.le_add_right 3 3) (Y.map (bHom S.1 S.2).op τ)
      = Y.map (((frontIncl 3 (3 + 3) (Nat.le_add_right 3 3)) ≫ (bHom S.1 S.2))).op τ := by
  show Y.map (frontIncl 3 (3 + 3) (Nat.le_add_right 3 3)).op (Y.map (bHom S.1 S.2).op τ) = _
  exact map_op_comp (bHom S.1 S.2) (frontIncl 3 (3 + 3) (Nat.le_add_right 3 3)) τ

/-- The back face of the `E`-coordinate of a shuffle cell, as a composite. -/
lemma backFace_aHom_comp (X : SSet) (S : Shuf) (σ : X _⦋3⦌) :
    backFace X 3 3 (X.map (aHom S.1 S.2).op σ)
      = X.map (((backIncl 3 3) ≫ (aHom S.1 S.2))).op σ := by
  show X.map (backIncl 3 3).op (X.map (aHom S.1 S.2).op σ) = _
  exact map_op_comp (aHom S.1 S.2) (backIncl 3 3) σ

/-- The special `(3,3)`-shuffle `N N N E E E` (the `N`-steps are the first three positions): the
unique cell whose relevant faces are the identity, hence the only cell contributing to the
evaluation. -/
def goodS : Shuf := ⟨{0, 1, 2}, by decide⟩

/-- The sign of the special shuffle is `(-1)^9 = -1`. -/
lemma shufSign_goodS : shufSign goodS.1 = -1 := by decide

/-- On the special shuffle the face of the second coordinate is the identity. -/
lemma goodS_fst :
    ((frontIncl 3 (3 + 3) (Nat.le_add_right 3 3)) ≫ (bHom goodS.1 goodS.2)) = 𝟙 ⦋3⦌ := by decide

/-- On the special shuffle the face of the first coordinate is the identity. -/
lemma goodS_snd : ((backIncl 3 3) ≫ (aHom goodS.1 goodS.2)) = 𝟙 ⦋3⦌ := by decide

/-- **Finite check.**  For every other `(3,3)`-shuffle the composite
`frontIncl 3 6 ≫ bHom S` is not surjective (so the corresponding face of the second coordinate is
a degenerate simplex). -/
lemma bHom_not_surjective (S : Shuf) (hS : S ≠ goodS) :
    ¬ Function.Surjective ⇑((frontIncl 3 (3 + 3) (Nat.le_add_right 3 3)) ≫ (bHom S.1 S.2)) := by
  revert S
  decide

/-- **The evaluation of the cup product on one shuffle cell.** -/
lemma kronecker_cell (X Y : SSet) (β : Cochain ℤ X 3) (θ : Cochain ℤ Y 3)
    (σ : X _⦋3⦌) (τ : Y _⦋3⦌) (S : Shuf) :
    kronecker ℤ (X ⊗ Y)
      (cup ℤ (X ⊗ Y) (ssetPullback (X ⊗ Y) Y (SemiCartesianMonoidalCategory.snd X Y) 3 θ)
                        (ssetPullback (X ⊗ Y) X (SemiCartesianMonoidalCategory.fst X Y) 3 β))
      (((X ⊗ Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) (ezCell X Y σ τ S)).hom 1)
      = genEval ℤ Y θ (Y.map (((frontIncl 3 (3 + 3) (Nat.le_add_right 3 3)) ≫ (bHom S.1 S.2))).op τ)
        * genEval ℤ X β (X.map (((backIncl 3 3) ≫ (aHom S.1 S.2))).op σ) := by
  simp only [ezCell]
  rw [kronecker_gen, cup_apply, frontFace_prod_mk, backFace_prod_mk,
    ssetPullback_genEval, ssetPullback_genEval, fst_apply_prod, snd_apply_prod,
    frontFace_bHom_comp, backFace_aHom_comp]

/-- Extracting a `ℤ`-scalar on the chain side of the Kronecker pairing (the instance needs to be
transported along `Int.cast_smul_eq_zsmul`). -/
lemma kronecker_smul_chain (X : SSet) (γ : Cochain ℤ X 6) (r : ℤ)
    (c : (X.chainComplex (ModuleCat.of ℤ ℤ)).X 6) :
    kronecker ℤ X γ (r • c) = r • kronecker ℤ X γ c := by
  show γ (r • c) = r • γ c
  rw [← Int.cast_smul_eq_zsmul ℤ r c, ← Int.cast_smul_eq_zsmul ℤ r (γ c)]
  exact LinearMap.map_smul γ (r : ℤ) c

/-- The shuffle chain, with the cup-product evaluation expanded into a sum over the shuffles. -/
lemma kronecker_ezGen (X Y : SSet) (γ : Cochain ℤ (X ⊗ Y) 6)
    (σ : X _⦋3⦌) (τ : Y _⦋3⦌) :
    kronecker ℤ (X ⊗ Y) γ (ezGen X Y σ τ)
      = ∑ S : Shuf, shufSign S.1 • kronecker ℤ (X ⊗ Y) γ
          (((X ⊗ Y).ιChainComplex (R := ModuleCat.of ℤ ℤ) (ezCell X Y σ τ S)).hom 1) := by
  simp only [ezGen, kronecker]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun S _ => kronecker_smul_chain (X ⊗ Y) γ (shufSign S.1) _)

/-- **The evaluation half of the Eilenberg–Zilber shuffle computation.**

If the `3`-cochain `θ` on the second factor annihilates the composites `Y.map g.op τ` for every
non-surjective monotone `g : ⦋3⦌ ⟶ ⦋3⦌` (which holds for instance for the normalized cocycles
`α ∘ PInfty`, which annihilate all degenerate simplices), then the Alexander–Whitney cup product of
the pullbacks of `θ` (second factor) and `β` (first factor) evaluates on the shuffle chain of a
pair of `3`-simplices as `- θ(τ) · β(σ)`: of the twenty cells only `N N N E E E` survives, with
sign `-1`. -/
theorem ezGen_eval (X Y : SSet) (β : Cochain ℤ X 3) (θ : Cochain ℤ Y 3)
    (σ : X _⦋3⦌) (τ : Y _⦋3⦌)
    (hθ : ∀ (g : ⦋3⦌ ⟶ ⦋3⦌), ¬ Function.Surjective ⇑g → genEval ℤ Y θ (Y.map g.op τ) = 0) :
    kronecker ℤ (X ⊗ Y)
      (cup ℤ (X ⊗ Y) (ssetPullback (X ⊗ Y) Y (SemiCartesianMonoidalCategory.snd X Y) 3 θ)
                        (ssetPullback (X ⊗ Y) X (SemiCartesianMonoidalCategory.fst X Y) 3 β))
      (ezGen X Y σ τ)
      = - genEval ℤ X β σ * genEval ℤ Y θ τ := by
  rw [kronecker_ezGen]
  rw [Finset.sum_congr rfl (fun S _ =>
    congrArg (fun x => shufSign S.1 • x) (kronecker_cell X Y β θ σ τ S))]
  rw [Finset.sum_eq_single goodS]
  · rw [shufSign_goodS]
    have h1 : Y.map (((frontIncl 3 (3 + 3) (Nat.le_add_right 3 3)) ≫
        (bHom goodS.1 goodS.2))).op τ = τ := by
      have h := congrArg (fun (f : ⦋3⦌ ⟶ ⦋3⦌) => Y.map f.op τ) goodS_fst
      simpa using h
    have h2 : X.map (((backIncl 3 3) ≫ (aHom goodS.1 goodS.2))).op σ = σ := by
      have h := congrArg (fun (f : ⦋3⦌ ⟶ ⦋3⦌) => X.map f.op σ) goodS_snd
      simpa using h
    rw [h1, h2]
    simp [mul_comm]
  · intro S _ hS
    have hns := bHom_not_surjective S hS
    rw [hθ _ hns]
    simp
  · intro h
    exact absurd (Finset.mem_univ goodS) h

end

end Work.Cohomology.Kunneth
