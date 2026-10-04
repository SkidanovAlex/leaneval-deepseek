import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TInvDefs
import Submission.Work.Diff.EXT.ConnCov.RicFlip.packTower_val_dep
import Submission.Work.Diff.EXT.ConnCov.RicFlip.pkTower_succ_rec_alt
import Submission.Work.Diff.EXT.ConnCov.RicFlip.PInv_zero
import Submission.Work.Diff.EXT.ConnCov.RicFlip.packTower_sm
import Submission.Work.Diff.EXT.ConnCov.RicFlip.packTower_lin_dir
import Submission.Work.Diff.EXT.ConnCov.RicFlip.packTower_lin_tail
import Submission.Work.Diff.EXT.ConnCov.RicFlip.packTower_loc
import Submission.Work.Diff.EXT.ConnCov.RicFlip.packTower_target

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.EXT.ConnCov.RicFlip.towerSlotAddSmValDep`

The tower `Work.Diff.EXT.ATower.tower (lcOf g) base k` of iterated covariant derivatives of a base
operator `base : Op3 0` is additive in every slot, smooth on smooth tuples and depends only on the
values of its slot fields at the point, **provided** these three properties hold for `base` itself
(the hypotheses `hadd`/`hsm`/`hvd`/`hlinA`/`hlinB`/`hlinC` of the statement).

The proof is an induction on `k` on the *packed* recursion `packTower`/`packStep` of
`TInvDefs.lean`:

* `PInv g base 0` is the base case (`PInv_zero`);
* `PInv g base k → PInv g base (k+1)` (the induction step `PInv_succ`) is assembled from the four
  pieces `packTower_sm`, `packTower_lin_dir`, `packTower_lin_tail`, `packTower_loc`;
* the packed invariants are transported back to the unpacked tower `tower (lcOf g) base k` along
  `packTower = pkTower` (`packTower_eq_pkTower`, from the recursion `pkTower_succ_rec`) and the
  slot bookkeeping `mkT3`/`trip3` (`pkTower_mkT3`), giving the three conclusions of the statement
  (`tower_conj_of_PInv`); the value-dependence clause uses the `Finset` induction
  `packTower_val_dep`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ConnCov.RicFlip

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- The induction step of `PInv`, assembled from its four pieces. -/
theorem PInv_succ (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (h : PInv g base k) : PInv g base (k + 1) := by
  intro F hF
  refine ⟨?_, ?_, ?_⟩
  · exact packTower_sm hLC g base k h hF
  · intro s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    refine Fin.cases ?_ ?_ s
    · exact packTower_lin_dir hLC g base k h hF hX₁ hX₂ hf₁ hf₂
    · intro j
      exact packTower_lin_tail hLC g base k h hF j hX₁ hX₂ hf₁ hf₂
  · intro x F' hF' heq
    exact packTower_loc hLC g base k h hF hF' x heq

/-- **The bridge** `packTower = pkTower`, from the recursion `pkTower_succ_rec`. -/
theorem packTower_eq_pkTower (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0)
    (hrec : ∀ (k : ℕ) (F : Fin (k + 4) → (Π y : M, TangentSpace I y)),
      pkTower g base (k + 1) F = packStep g (pkTower g base k) F) :
    ∀ (k : ℕ) (F : Fin (k + 3) → (Π y : M, TangentSpace I y)),
      packTower g base k F = pkTower g base k F := by
  intro k
  induction k with
  | zero =>
      intro F
      change base (fun i : Fin 0 => i.elim0) (F (Fin.natAdd 0 0)) (F (Fin.natAdd 0 1))
          (F (Fin.natAdd 0 2)) = pkTower g base 0 F
      simp only [pkTower, Work.Diff.EXT.ATower.tower]
      rw [show (fun j : Fin 0 => F (Fin.castAdd 3 j)) = (fun i : Fin 0 => i.elim0) from
        funext (fun j => Fin.elim0 j)]
  | succ k ih =>
      intro F
      rw [packTower_succ,
        show packTower g base k = pkTower g base k from funext ih, hrec k F]
theorem towerSlotAddSmValDep
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    {base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0}
    (hadd : Work.Diff.EXT.ATower.SlotAdd base)
    (hsm : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmF I M (base v A B C))
    (hvd : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (A A' B B' C C' : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M A' →
      Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M B' →
      Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmE I M C' →
      A x = A' x → B x = B' x → C x = C' x →
      base b0 A B C x = base b0 A' B' C' x)
    (hlinA : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (B C : Π y : M, TangentSpace I y) (x : M),
      base b0 (f₁ • X₁ + f₂ • X₂) B C x
        = f₁ x * base b0 X₁ B C x + f₂ x * base b0 X₂ B C x)
    (hlinB : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (A C : Π y : M, TangentSpace I y) (x : M),
      base b0 A (f₁ • X₁ + f₂ • X₂) C x
        = f₁ x * base b0 A X₁ C x + f₂ x * base b0 A X₂ C x)
    (hlinC : ∀ (b0 : Fin 0 → (Π y : M, TangentSpace I y))
      (X₁ X₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M X₁ → Work.Diff.EXT.ATower.SmE I M X₂ →
      ∀ (A B : Π y : M, TangentSpace I y) (x : M),
      base b0 A B (f₁ • X₁ + f₂ • X₂) x
        = f₁ x * base b0 A B X₁ x + f₂ x * base b0 A B X₂ x) :
    ∀ k : ℕ,
      Work.Diff.EXT.ATower.SlotAdd (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k) ∧
      (∀ (v : Fin k → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
        (∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) → Work.Diff.EXT.ATower.SmE I M A →
        Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M C →
        Work.Diff.EXT.ATower.SmF I M
          (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v A B C)) ∧
      (∀ (v v' : Fin k → (Π y : M, TangentSpace I y))
        (A A' B B' C C' : Π y : M, TangentSpace I y) (x : M),
        (∀ j, Work.Diff.EXT.ATower.SmE I M (v j)) →
        (∀ j, Work.Diff.EXT.ATower.SmE I M (v' j)) → (∀ j, v j x = v' j x) →
        Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M A' →
        Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M B' →
        Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmE I M C' →
        A x = A' x → B x = B' x → C x = C' x →
        Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v A B C x
          = Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf g) base k v' A' B' C' x) :=
  tower_conj_of_PInv (base := base) hLC g
    (fun k' => Nat.rec (PInv_zero g hsm hvd hlinA hlinB hlinC)
      (fun k'' ih => PInv_succ hLC g base k'' ih) k')
    (packTower_eq_pkTower g base (fun k'' F => pkTower_succ_rec_alt g base k'' F))

end Work.Diff.EXT.ConnCov.RicFlip
