import Mathlib
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.GE.Rfa.reactionW_contMDiffAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the level-`(a,b)` monomial `MonoD`

`Work.Diff.EXT.MonoD g N a b d₁ d₂ s e F` is the contraction of the two tower arrays
`∇^a Rm`, `∇^b Rm` (in the frame `e`, on the directions selected by `d₁`, `d₂`) with the four slot
pairings against the fields `F (s t)`.  This module proves that it is `C^∞` in the base point when
all the fields involved are `C^∞`.

The proof is the closure of `C^∞` under finite sums and products:

* `fun y => ckt g k U y` is `C^∞` for a smooth tuple `U` — this is `Work.Diff.EXT.tensProp_all`
  (`TensProp` in `curvNormK_frame_indep`), which is imported by `reactBase`;
* `fun y => g.inner y (X y) (Y y)` is `C^∞` for smooth fields `X Y` —
  `Work.Diff.GE.Rfa.contMDiffAt_inner_fields`;
* the algebraic operations on `Curv4 n` (`ricF`, `rmPair`, `rmSym`) are finite sums and products of
  components, hence preserve componentwise `C^∞`.

The module is named `_T2` because, unlike the workspace copies in the `GE` area, it needs no
`[I.Boundaryless]` nor compactness: this is the form required by
`Submission.Work.Diff.EXT.reaction0_jets`.
-/

namespace Work.Diff.EXT.Mono

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The algebraic operations on curvature arrays preserve componentwise `C^∞` -/

/-- Componentwise `C^∞` of `ricF`. -/
theorem contMDiffAt_ricF_apply {n : ℕ} (Z : M → Curv4 n) (x : M)
    (hZ : ∀ p q r s, ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y => Z y p q r s) x)
    (i j : Fin n) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y => Work.Diff.GE.ricF (Z y) i j) x := by
  rw [show (fun y : M => Work.Diff.GE.ricF (Z y) i j) = fun y : M => ∑ a, Z y a i a j from rfl]
  exact ContMDiffAt.sum (fun a _ => hZ a i a j)

/-- Componentwise `C^∞` of `rmPair`. -/
theorem contMDiffAt_rmPair_apply {n : ℕ} (X Y : M → Curv4 n) (x : M)
    (hX : ∀ p q r s, ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y => X y p q r s) x)
    (hY : ∀ p q r s, ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y => Y y p q r s) x)
    (i j k l : Fin n) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y => Work.Diff.EXT.rmPair (X y) (Y y) i j k l) x := by
  have hricX : ∀ a b : Fin n,
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y => Work.Diff.GE.ricF (X y) a b) x :=
    fun a b => contMDiffAt_ricF_apply X x hX a b
  have hricY : ∀ a b : Fin n,
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y => Work.Diff.GE.ricF (Y y) a b) x :=
    fun a b => contMDiffAt_ricF_apply Y x hY a b
  rw [show (fun y : M => Work.Diff.EXT.rmPair (X y) (Y y) i j k l) = fun y : M =>
      (∑ p, ∑ q, (X y i j p q * Y y k l p q + 2 * X y i p k q * Y y j p l q
          - 2 * X y i p l q * Y y j p k q))
        - ∑ p, (Work.Diff.GE.ricF (X y) i p * Y y p j k l
              + Work.Diff.GE.ricF (X y) j p * Y y i p k l
              + Work.Diff.GE.ricF (X y) l p * Y y i j k p
              + Work.Diff.GE.ricF (X y) k p * Y y i j p l) from rfl]
  refine ContMDiffAt.sub ?_ ?_
  · refine ContMDiffAt.sum (fun p _ => ContMDiffAt.sum (fun q _ => ?_))
    refine ContMDiffAt.sub (ContMDiffAt.add ((hX i j p q).mul (hY k l p q)) ?_) ?_
    · exact (((contMDiffAt_const (c := (2 : ℝ))).mul (hX i p k q)).mul (hY j p l q))
    · exact (((contMDiffAt_const (c := (2 : ℝ))).mul (hX i p l q)).mul (hY j p k q))
  · refine ContMDiffAt.sum (fun p _ => ?_)
    refine ContMDiffAt.add (ContMDiffAt.add (ContMDiffAt.add ?_ ?_) ?_) ?_
    · exact (hricX i p).mul (hY p j k l)
    · exact (hricX j p).mul (hY i p k l)
    · exact (hricX l p).mul (hY i j k p)
    · exact (hricX k p).mul (hY i j p l)

/-- Componentwise `C^∞` of `rmSym`. -/
theorem contMDiffAt_rmSym_apply {n : ℕ} (X Y : M → Curv4 n) (x : M)
    (hX : ∀ p q r s, ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y => X y p q r s) x)
    (hY : ∀ p q r s, ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y => Y y p q r s) x)
    (i j k l : Fin n) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞ (fun y => Work.Diff.EXT.rmSym (X y) (Y y) i j k l) x := by
  rw [show (fun y : M => Work.Diff.EXT.rmSym (X y) (Y y) i j k l) = fun y : M =>
      (Work.Diff.EXT.rmPair (X y) (Y y) i j k l + Work.Diff.EXT.rmPair (Y y) (X y) i j k l) / 2
      from rfl]
  exact ((contMDiffAt_rmPair_apply X Y x hX hY i j k l).add
    (contMDiffAt_rmPair_apply Y X x hY hX i j k l)).div_const 2

/-! ## Smoothness of the tower array in a frame -/

/-- Componentwise `C^∞` of `TowerArr` (the components of `∇^a Rm` in the frame `e`), from the
smoothness of the frame fields and of the direction fields. -/
theorem contMDiffAt_TowerArr_apply (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (a : ℕ) (dirs : Fin a → TField (I := I) (M := M))
    (hdirs : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (dirs r))
    (e : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (x : M) (p q r s : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ∞
      (fun y => Work.Diff.EXT.TowerArr g a dirs e y p q r s) x := by
  have htuple : ∀ u : Fin (a + 4),
      Work.Diff.EXT.SmoothF ((Fin.append dirs ![e p, e q, e r, e s]) u) := by
    intro u
    refine Fin.addCases (m := a) (n := 4) (fun r' => ?_) (fun t => ?_) u
    · rw [Fin.append_left]; exact hdirs r'
    · rw [Fin.append_right]
      fin_cases t
      · exact he p
      · exact he q
      · exact he r
      · exact he s
  have h := (Work.Diff.EXT.tensProp_all hLC g a (Fin.append dirs ![e p, e q, e r, e s]) htuple).1
  exact h.contMDiffAt

/-! ## The target -/

/-- **Smoothness of the monomial `MonoD`.** -/
theorem smooth_MonoD_T2
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (N a b : ℕ) (d₁ : Fin a → Fin N) (d₂ : Fin b → Fin N) (s : Fin 4 → Fin N)
    (e : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M))
    (he : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (e i))
    (F : Fin N → Work.Diff.EXT.TField (I := I) (M := M))
    (hF : ∀ r, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (F r)) :
    ContMDiff I (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun y : M => Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e F y) := by
  intro x
  rw [show (fun y : M => Work.Diff.EXT.MonoD (I := I) (M := M) g N a b d₁ d₂ s e F y)
      = fun y : M => ∑ i, ∑ j, ∑ k, ∑ l,
          Work.Diff.EXT.rmSym (Work.Diff.EXT.TowerArr g a (fun r => F (d₁ r)) e y)
            (Work.Diff.EXT.TowerArr g b (fun r => F (d₂ r)) e y) i j k l
          * (g.inner y (e i y) (F (s 0) y) * g.inner y (e j y) (F (s 1) y)
            * g.inner y (e k y) (F (s 2) y) * g.inner y (e l y) (F (s 3) y)) from rfl]
  refine ContMDiffAt.sum (fun i _ => ContMDiffAt.sum (fun j _ =>
    ContMDiffAt.sum (fun k _ => ContMDiffAt.sum (fun l _ => ?_))))
  refine (contMDiffAt_rmSym_apply
    (fun y => Work.Diff.EXT.TowerArr g a (fun r => F (d₁ r)) e y)
    (fun y => Work.Diff.EXT.TowerArr g b (fun r => F (d₂ r)) e y) x
    (fun p q r s => contMDiffAt_TowerArr_apply hLC g a (fun r => F (d₁ r))
      (fun r => hF (d₁ r)) e he x p q r s)
    (fun p q r s => contMDiffAt_TowerArr_apply hLC g b (fun r => F (d₂ r))
      (fun r => hF (d₂ r)) e he x p q r s) i j k l).mul ?_
  refine ContMDiffAt.mul (ContMDiffAt.mul (ContMDiffAt.mul ?_ ?_) ?_) ?_
  · exact Work.Diff.GE.Rfa.contMDiffAt_inner_fields g (he i) (hF (s 0)) x
  · exact Work.Diff.GE.Rfa.contMDiffAt_inner_fields g (he j) (hF (s 1)) x
  · exact Work.Diff.GE.Rfa.contMDiffAt_inner_fields g (he k) (hF (s 2)) x
  · exact Work.Diff.GE.Rfa.contMDiffAt_inner_fields g (he l) (hF (s 3)) x

end Work.Diff.EXT.Mono
