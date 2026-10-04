import Mathlib
import Submission.Work.Diff.EXT.ConnCov.Kit
import Submission.Work.Diff.EXT.mvfderiv_metric_pairing_split
import Submission.Work.Diff.EXT.ATower.Defs
import Submission.Work.Diff.EXT.ATower.connDiff_flip_input

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `towerEqLoweringDeltaTowerM`: the metric pairing commutes with the covariant tower

The statement proved here is the **metric-compatibility collapse** for the `∇^{G t}`-towers of the
lowered connection difference.  Writing `g = G t`, `δ = ∇^{g} − ∇^{G 0}` and
`aOf A B C = g(δ B A, C)`, the claim is, for every `c`,

  `∇^{g,c} aOf = g ⊙ ∇^{g,c} δ`,

i.e. `tower (lcOf g) aOf c v A B C y = g_y (deltaTowerM G t c v B A y) (C y)`.

This holds because `∇^{g} g = 0`: the covariant derivative of a pairing of two sections is the
pairing of the covariant derivatives, so the `(k+1)`-st step of the *scalar* tower (`step`, with its
four connection corrections) matches the `(k+1)`-st step of the *vector* tower (`vstepM`) exactly,
the only non-trivial ingredient being the product rule
`Work.Diff.EXT.mvfderiv_metric_pairing_split` (metric compatibility of `lcOf g`), whose "second half"
cancels the last connection correction of `step`.

The proof is the induction

* level `0`: definitional (`aOf A B C = g(δ B A, C)`);
* level `k+1`: unfold `step` and `vstepM`, rewrite every `k`-level tower with the induction
  hypothesis, apply the product rule to the differentiating term, and use linearity of the pairing.

The smoothness hypothesis `SmE` on the fields is needed twice: to apply the product rule
(`MDifferentiableAt` of the `δ`-tower section, which is the `smE_vtowerM` induction below) and to
make the `step` recursion compute the *tensor* derivative rather than the junk value `0`.

## A note on the declarations of `Work.Diff.EXT.ConnCov.RicFlip`

`deltaTowerM` and its recursion `vstepM`/`vtowerM`/`deltaBaseM` were first written in
`Submission/Work/Diff/EXT/ConnCov/ricFlipOfMoving.lean`, which *also* states the present theorem
(with a `sorry`).  Since a module may not declare a name twice, this file restates those four
definitions (verbatim) so that it can hold the proof; `ricFlipOfMoving.lean` should import this
module instead of writing them again.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

namespace RicFlip

open Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]
  [T2Space M]

/-! ## The `δ`-tower of the connection difference -/

/-- Vector-valued operators with `k` derivative slots and two section slots. -/
abbrev VOpM (k : ℕ) : Type _ := (Fin k → TF (I := I) (M := M)) → TF (I := I) (M := M) →
  TF (I := I) (M := M) → TF (I := I) (M := M)

/-- The Leibniz recursion for the covariant derivative of a vector-valued `(1,2)`-tensor tower. -/
noncomputable def vstepM (g : SMet I M) {k : ℕ} (τ : VOpM (I := I) (M := M) k) :
    VOpM (I := I) (M := M) (k+1) :=
  fun v X Y x =>
    (lcOf g) (τ (fun i : Fin k => v i.succ) X Y) x (v 0 x)
      - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => (lcOf g) (v i.succ) y (v 0 y))) X Y x
      - τ (fun i : Fin k => v i.succ) (fun y => (lcOf g) X y (v 0 y)) Y x
      - τ (fun i : Fin k => v i.succ) X (fun y => (lcOf g) Y y (v 0 y)) x

/-- The iterated covariant derivatives of a vector-valued `(1,2)` tensor. -/
noncomputable def vtowerM (g : SMet I M) (base : VOpM (I := I) (M := M) 0) :
    ∀ k : ℕ, VOpM (I := I) (M := M) k
  | 0 => base
  | k + 1 => vstepM g (vtowerM g base k)

/-- The connection difference as a base for `vtowerM`. -/
noncomputable def deltaBaseM (G : ℝ → SMet I M) (t : ℝ) : VOpM (I := I) (M := M) 0 :=
  fun _ X Y => Work.Diff.EXT.ConnCov.covDiff G t X Y

/-- **The moving `δ`-tower** `∇^{G t, c}(∇^{G t} − ∇^{G 0})`. -/
noncomputable def deltaTowerM (G : ℝ → SMet I M) (t : ℝ) (c : ℕ) :
    VOpM (I := I) (M := M) c :=
  vtowerM (G t) (deltaBaseM G t) c

/-! ## Smoothness of the `δ`-tower -/

/-- Smoothness of a one-slot update of a tuple of smooth fields. -/
lemma smE_updateM {k : ℕ} {v : Fin k → TF (I := I) (M := M)} (i : Fin k)
    {W : TF (I := I) (M := M)} (hv : ∀ j, SmE I M (v j)) (hW : SmE I M W) :
    ∀ j, SmE I M (Function.update v i W j) := by
  intro j
  by_cases h : j = i
  · rw [h, Function.update_self]; exact hW
  · rw [Function.update_of_ne h (f := v)]; exact hv j

/-- **Smoothness of the vector-valued covariant tower.**  If the level-`0` tensor `δ` sends smooth
fields to smooth fields, then so does its whole `∇^{g}`-tower. -/
lemma smE_vtowerM (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    (δ : VOpM (I := I) (M := M) 0)
    (hδ : ∀ (w : Fin 0 → TF (I := I) (M := M)) (X Y : TF (I := I) (M := M)),
      SmE I M X → SmE I M Y → SmE I M (δ w X Y)) :
    ∀ (k : ℕ) (v : Fin k → TF (I := I) (M := M)) (X Y : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M X → SmE I M Y → SmE I M (vtowerM g δ k v X Y) := by
  intro k
  induction k with
  | zero =>
      intro v X Y hv hX hY
      exact hδ v X Y hX hY
  | succ k ih =>
      intro v X Y hv hX hY
      have hv' : ∀ i : Fin k, SmE I M (v i.succ) := fun i => hv i.succ
      have hv0 : SmE I M (v 0) := hv 0
      have hU : ∀ i : Fin k, SmE I M (fun y => (lcOf g) (v i.succ) y (v 0 y)) :=
        fun i => lcOf_apply_smE hLC g (v i.succ) (v 0) (hv i.succ) hv0
      change SmE I M (vstepM g (vtowerM g δ k) v X Y)
      intro x
      have h1x := (lcOf_apply_smE hLC g
        (vtowerM g δ k (fun i : Fin k => v i.succ) X Y) (v 0)
        (ih _ X Y hv' hX hY) hv0) x
      have h2x : ContMDiffAt I I.tangent ∞ (T% (fun y : M => ∑ i : Fin k, vtowerM g δ k
            (Function.update (fun j : Fin k => v j.succ) i
              (fun z => (lcOf g) (v i.succ) z (v 0 z))) X Y y)) x := by
        exact ContMDiffAt.sum_section (s := (Finset.univ : Finset (Fin k)))
          (fun i _ => (ih _ X Y (smE_updateM i hv' (hU i)) hX hY) x)
      have h3x := (ih _ _ Y hv' (lcOf_apply_smE hLC g X (v 0) hX hv0) hY) x
      have h4x := (ih _ X _ hv' hX (lcOf_apply_smE hLC g Y (v 0) hY hv0)) x
      exact ((h1x.sub_section h2x).sub_section h3x).sub_section h4x

/-! ## The one-step compatibility of the scalar and the vector recursion -/

/-- **One recursion step of the pairing collapse.**  If a scalar operator `τ` is the lowering
(`g`-pairing) of a vector-valued operator `τ'`, then one covariant derivative step of `τ` (with the
`step` recursion) is the lowering of one covariant derivative step of `τ'` (with `vstepM`).

This is the technical heart of the induction: `step` has four connection corrections, of which
three match the three corrections of `vstepM`, while the fourth combines with the explicit
`mvfderiv` of `step` through metric compatibility. -/
lemma step_lowering (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    {k : ℕ} {τ : Op3 (I := I) (M := M) k} {τ' : VOpM (I := I) (M := M) k}
    (hτ : ∀ (w : Fin k → TF (I := I) (M := M)) (X Y Z : TF (I := I) (M := M)),
      (∀ i, SmE I M (w i)) → SmE I M X → SmE I M Y → SmE I M Z →
      τ w X Y Z = fun y => g.inner y (τ' w Y X y) (Z y))
    (hτ' : ∀ (w : Fin k → TF (I := I) (M := M)) (X Y : TF (I := I) (M := M)),
      (∀ i, SmE I M (w i)) → SmE I M X → SmE I M Y → SmE I M (τ' w X Y))
    (v : Fin (k+1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ i, SmE I M (v i)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    step (lcOf g) τ v A B C
      = fun y => g.inner y (vstepM g τ' v B A y) (C y) := by
  have hv' : ∀ i : Fin k, SmE I M (v i.succ) := fun i => hv i.succ
  have hv0 : SmE I M (v 0) := hv 0
  have hU : ∀ i : Fin k, SmE I M (fun y => (lcOf g) (v i.succ) y (v 0 y)) :=
    fun i => lcOf_apply_smE hLC g (v i.succ) (v 0) (hv i.succ) hv0
  have hA' : SmE I M (fun y => (lcOf g) A y (v 0 y)) := lcOf_apply_smE hLC g A (v 0) hA hv0
  have hB' : SmE I M (fun y => (lcOf g) B y (v 0 y)) := lcOf_apply_smE hLC g B (v 0) hB hv0
  have hC' : SmE I M (fun y => (lcOf g) C y (v 0 y)) := lcOf_apply_smE hLC g C (v 0) hC hv0
  have e1 : τ (fun i : Fin k => v i.succ) A B C
      = fun y => g.inner y (τ' (fun i : Fin k => v i.succ) B A y) (C y) :=
    hτ _ A B C hv' hA hB hC
  have e2 : ∀ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
        (fun y => (lcOf g) (v i.succ) y (v 0 y))) A B C
      = fun y => g.inner y (τ' (Function.update (fun j : Fin k => v j.succ) i
          (fun y => (lcOf g) (v i.succ) y (v 0 y))) B A y) (C y) :=
    fun i => hτ _ A B C (smE_updateM i hv' (hU i)) hA hB hC
  have e3 : τ (fun i : Fin k => v i.succ) (fun y => (lcOf g) A y (v 0 y)) B C
      = fun y => g.inner y (τ' (fun i : Fin k => v i.succ) B
          (fun y => (lcOf g) A y (v 0 y)) y) (C y) := hτ _ _ B C hv' hA' hB hC
  have e4 : τ (fun i : Fin k => v i.succ) A (fun y => (lcOf g) B y (v 0 y)) C
      = fun y => g.inner y (τ' (fun i : Fin k => v i.succ)
          (fun y => (lcOf g) B y (v 0 y)) A y) (C y) := hτ _ A _ C hv' hA hB' hC
  have e5 : τ (fun i : Fin k => v i.succ) A B (fun y => (lcOf g) C y (v 0 y))
      = fun y => g.inner y (τ' (fun i : Fin k => v i.succ) B A y)
          ((lcOf g) C y (v 0 y)) := hτ _ A B _ hv' hA hB hC'
  funext x
  simp only [step]
  rw [e1]
  have hprod : mvfderiv I
      (fun y => g.inner y (τ' (fun i : Fin k => v i.succ) B A y) (C y)) x (v 0 x)
      = g.inner x ((lcOf g) (τ' (fun i : Fin k => v i.succ) B A) x (v 0 x)) (C x)
        + g.inner x (τ' (fun i : Fin k => v i.succ) B A x) ((lcOf g) C x (v 0 x)) :=
    mvfderiv_metric_pairing_split hLC g (W := τ' (fun i : Fin k => v i.succ) B A) (Z := C)
      (y := x) (v := v 0 x)
      (((hτ' (fun i : Fin k => v i.succ) B A hv' hB hA) x).mdifferentiableAt (by simp))
      ((hC x).mdifferentiableAt (by simp))
  rw [hprod]
  have hsum : (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
        (fun y => (lcOf g) (v i.succ) y (v 0 y))) A B C x)
      = ∑ i : Fin k, g.inner x (τ' (Function.update (fun j : Fin k => v j.succ) i
          (fun y => (lcOf g) (v i.succ) y (v 0 y))) B A x) (C x) :=
    Finset.sum_congr rfl (fun i _ => congrFun (e2 i) x)
  rw [hsum]
  rw [congrFun e3 x, congrFun e4 x, congrFun e5 x]
  rw [show vstepM g τ' v B A x
      = (lcOf g) (τ' (fun i : Fin k => v i.succ) B A) x (v 0 x)
        - (∑ i : Fin k, τ' (Function.update (fun j : Fin k => v j.succ) i
            (fun y => (lcOf g) (v i.succ) y (v 0 y))) B A x)
        - τ' (fun i : Fin k => v i.succ) (fun y => (lcOf g) B y (v 0 y)) A x
        - τ' (fun i : Fin k => v i.succ) B (fun y => (lcOf g) A y (v 0 y)) x from rfl]
  simp only [map_sub, sub_apply, map_sum, sum_apply]
  ring

/-! ## The pairing collapse -/

/-- **The metric pairing commutes with the covariant tower** (general form): for a metric `g` and a
`(1,2)`-tensor `δ` whose values on smooth fields are smooth, the `∇^{g}`-tower of the lowering
`g ⊙ δ` is the lowering of the `∇^{g}`-tower of `δ`. -/
theorem tower_lowering (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    (δ : VOpM (I := I) (M := M) 0)
    (hδ : ∀ (w : Fin 0 → TF (I := I) (M := M)) (X Y : TF (I := I) (M := M)),
      SmE I M X → SmE I M Y → SmE I M (δ w X Y)) :
    ∀ (k : ℕ) (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C →
      tower (lcOf g) (fun (w : Fin 0 → TF (I := I) (M := M)) (X Y Z : TF (I := I) (M := M))
          (y : M) => g.inner y (δ w Y X y) (Z y)) k v A B C
        = fun y => g.inner y (vtowerM g δ k v B A y) (C y) := by
  intro k
  induction k with
  | zero =>
      intro v A B C hv hA hB hC
      rfl
  | succ k ih =>
      intro v A B C hv hA hB hC
      rw [show tower (lcOf g) (fun (w : Fin 0 → TF (I := I) (M := M))
            (X Y Z : TF (I := I) (M := M)) (y : M) => g.inner y (δ w Y X y) (Z y)) (k+1) v A B C
          = step (lcOf g) (tower (lcOf g) (fun (w : Fin 0 → TF (I := I) (M := M))
              (X Y Z : TF (I := I) (M := M)) (y : M) => g.inner y (δ w Y X y) (Z y)) k) v A B C
          from rfl]
      rw [show vtowerM g δ (k+1) = vstepM g (vtowerM g δ k) from rfl]
      exact step_lowering hLC g (τ := tower (lcOf g) (fun (w : Fin 0 → TF (I := I) (M := M))
              (X Y Z : TF (I := I) (M := M)) (y : M) => g.inner y (δ w Y X y) (Z y)) k)
        (τ' := vtowerM g δ k)
        (fun w X Y Z hw hX hY hZ => ih w X Y Z hw hX hY hZ)
        (fun w X Y hw hX hY => smE_vtowerM hLC g δ hδ k w X Y hw hX hY)
        v A B C hv hA hB hC

theorem towerEqLoweringDeltaTowerM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (c : ℕ)
    (v : Fin c → (Π y : M, TangentSpace I y))
    (A B C : Π y : M, TangentSpace I y)
    (hv : ∀ i, Work.Diff.EXT.ATower.SmE I M (v i))
    (hA : Work.Diff.EXT.ATower.SmE I M A) (hB : Work.Diff.EXT.ATower.SmE I M B)
    (hC : Work.Diff.EXT.ATower.SmE I M C) (y : M) :
    Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G t)) (fun _ => Work.Diff.EXT.aOf G t) c
        v A B C y
      = (G t).inner y
          (Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v B A y) (C y) := by
  have hδ : ∀ (w : Fin 0 → TF (I := I) (M := M)) (X Y : TF (I := I) (M := M)),
      SmE I M X → SmE I M Y → SmE I M (deltaBaseM G t w X Y) := by
    intro w X Y hX hY
    have h1 : SmE I M (fun q : M => (lcOf (G t)) X q (Y q)) :=
      lcOf_apply_smE hLC (G t) X Y hX hY
    have h2 : SmE I M (fun q : M => (lcOf (G 0)) X q (Y q)) :=
      lcOf_apply_smE hLC (G 0) X Y hX hY
    exact h1.sub_section h2
  have h := tower_lowering hLC (G t) (deltaBaseM G t) hδ c v A B C hv hA hB hC
  exact congrFun h y

end RicFlip

end Work.Diff.EXT.ConnCov
