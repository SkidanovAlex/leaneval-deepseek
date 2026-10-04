import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicTr.DTB.DeltaTower
import Submission.Work.Diff.EXT.ATower.tower_slotAdd_smF
import Submission.Work.Diff.EXT.ConnCov.step_linear_ext

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The metric tower `∇^{g_0,i+1} g_t` is the symmetrised `aOf`-tower

`Work.Diff.EXT.ConnCov.DTB.gtTower G t k` (`deltaTower.lean`) is the `k`-th iterated covariant
derivative, with respect to the *fixed* background connection `∇^{g_0} = lcOf (G 0)`, of the moving
metric `G t`; it is an `Op2` (two value slots, `k` direction slots).

The Koszul identity `gtTower_one_eq` identifies the first derivative as the symmetrisation
`∇g_t = aOf + swap aOf` (`(∇^{g_0}_X g_t)(Y,Z) = aOf X Y Z + aOf X Z Y`).  The theorem below is the
`i`-th iterated version of that identity:

> `∇^{g_0,i+1} g_t (d_0 … d_i; Y, Z)`
>   `= ∇^{g_0,i} aOf (d_0 … d_{i-1}; d_i, Y, Z) + ∇^{g_0,i} aOf (d_0 … d_{i-1}; d_i, Z, Y)`,

i.e. the order-`i+1` metric tower is the sum of the two order-`i` `aOf`-towers obtained by inserting
the *last* direction `d_i` into the first value slot, with the two remaining value slots in the two
possible orders.

## The proof

Everything is proved on the nose for `C^∞` fields: `mvfderiv` is a genuine derivative only on
differentiable functions, and both the induction step (where `mvfderiv` has to be distributed over
the sum of the two `aOf`-towers) and the identification `∇g_t = aOf + swap aOf` (Koszul) require the
relevant fields to be smooth.  The smoothness of the `aOf`-tower on smooth fields is
`aOfTower_smF` below (a `T2Space`-free version of `ATower.tower_slotAdd_smF`, which is not
applicable because the ambient hypotheses do not include `T2Space M`).

The combinatorial core is `RhA_succ`: for a tuple `d : Fin (i+2) → TF` the object
`RhA i (d∘succ)` (the order-`i` `aOf`-tower with directions `d_1 … d_i` and first value slot
`d_{i+1}`) reproduces exactly the `i+1`-st iterated covariant derivative: the whole content is the
splitting of the `Fin (i+1)`-sum of `Function.update`-terms into `Fin i` terms plus the term of
`Fin.last i` (which changes the *value* slot `d_{i+1}` of the inner tower, not a direction), together
with the `Fin`-bookkeeping `Fin.succ_castSucc` / `Fin.succ_last`.  Lean closes it by
`simp only [...]` followed by `ring`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.EXT.ConnCov.DTB

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## 1. Smoothness of the metric pairing and of `aOf` on smooth fields -/

/-- **The metric pairing of two smooth fields is smooth** (the `T2Space`-free form of
`Work.Diff.GE.katoMetricPairingSmooth`; its proof uses only Mathlib's
`ContMDiffAt.inner_bundle`). -/
lemma inner_pairing_smF (g : SMet I M) {X Y : TF (I := I) (M := M)}
    (hX : SmE I M X) (hY : SmE I M Y) :
    SmF I M (fun y : M => g.inner y (X y) (Y y)) := by
  intro x
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact ContMDiffAt.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id)
    (v := X) (w := Y) (hX x) (hY x)

/-- **Smoothness of the lowered connection difference `aOf G t X Y Z`** on smooth fields: it is the
metric `G t` paired with the smooth field `∇^{G t}_Y X − ∇^{G 0}_Y X`. -/
lemma aOf_smF (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ)
    {X Y Z : TF (I := I) (M := M)} (hX : SmE I M X) (hY : SmE I M Y) (hZ : SmE I M Z) :
    SmF I M (fun y : M => Work.Diff.EXT.aOf G t X Y Z y) := by
  have hU : SmE I M ((fun y => (lcOf (G t)) Y y (X y)) - (fun y => (lcOf (G 0)) Y y (X y))) :=
    (lcOf_apply_smE hLC (G t) Y X hY hX).sub_section (lcOf_apply_smE hLC (G 0) Y X hY hX)
  have hfun : (fun y : M => Work.Diff.EXT.aOf G t X Y Z y)
      = fun y : M => (G t).inner y
          (((fun y => (lcOf (G t)) Y y (X y)) - (fun y => (lcOf (G 0)) Y y (X y))) y) (Z y) := by
    funext y
    simp only [Work.Diff.EXT.aOf, Pi.sub_apply]
  rw [hfun]
  exact inner_pairing_smF (G t) hU hZ

/-- **The `aOf`-tower is smooth on smooth fields** (induction on the order, the recursion step being
`ATower.stepAux_smF`). -/
lemma aOfTower_smF (hLC : LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) :
    ∀ (k : ℕ) (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ j, SmE I M (v j)) → SmE I M A → SmE I M B → SmE I M C →
      SmF I M (tower (lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G t) k v A B C) := by
  intro k
  induction k with
  | zero =>
      intro v A B C _ hA hB hC
      exact aOf_smF hLC G t hA hB hC
  | succ k ih =>
      intro v A B C hv hA hB hC
      have hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
          SmE I M (fun y => (lcOf (G 0)) Y y (Z y)) :=
        fun Y Z hY hZ => lcOf_apply_smE hLC (G 0) Y Z hY hZ
      have h := stepAux_smF (lcOf (G 0)) (tower (lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G t) k)
        ih hcov (hv 0) (fun i => hv i.succ) hA hB hC
      simpa only [tower, step_eq_stepAux] using h

/-! ## 2. `Fin` / `Function.update` bookkeeping

These are the four rewriting rules that convert `Function.update` on a `Fin (i+1)`-tuple, composed
with `Fin.castSucc` or evaluated at `Fin.last i`, into the corresponding expression on the
`Fin i`-tuple of `castSucc`-entries.  They are the only place where the sum splitting of
`RhA_succ` uses the structure of `Fin`. -/

lemma upd_cs_comp {X : Type*} {i : ℕ} (w : Fin (i+1) → X) (k : Fin i) (C : X) :
    (fun j : Fin i => (Function.update w k.castSucc C) j.castSucc)
      = Function.update (fun j : Fin i => w j.castSucc) k C := by
  funext j
  rw [Function.update_apply, Function.update_apply]
  by_cases h : j = k
  · subst h; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg (fun hc => h (Fin.castSucc_inj.mp hc)), if_neg h]

lemma upd_last_comp {X : Type*} {i : ℕ} (w : Fin (i+1) → X) (C : X) :
    (fun j : Fin i => (Function.update w (Fin.last i) C) j.castSucc)
      = fun j : Fin i => w j.castSucc := by
  funext j
  rw [Function.update_apply, if_neg (Fin.castSucc_ne_last j)]

lemma upd_cs_last {X : Type*} {i : ℕ} (w : Fin (i+1) → X) (k : Fin i) (C : X) :
    (Function.update w k.castSucc C) (Fin.last i) = w (Fin.last i) :=
  Function.update_of_ne (Fin.castSucc_ne_last k).symm C w

lemma upd_last_last {X : Type*} {i : ℕ} (w : Fin (i+1) → X) (C : X) :
    (Function.update w (Fin.last i) C) (Fin.last i) = C := Function.update_self _ _ _

/-! ## 3. The packed operator and its recursion step -/

/-- **The packed `aOf`-tower**: the order-`i` `aOf`-tower applied to the tuple
`d : Fin (i+1) → TF`, the first `i` entries being the directions and the last one `d (Fin.last i)`
being the *first value slot*.  This is the operator whose symmetrisation is the target. -/
noncomputable def RhA (G : ℝ → SMet I M) (t : ℝ) (i : ℕ) : Op2 (I := I) (M := M) (i+1) :=
  fun d X Y x => tower (lcOf (G 0)) (fun _ => Work.Diff.EXT.aOf G t) i
    (fun j : Fin i => d j.castSucc) (d (Fin.last i)) X Y x

/-- **The recursion step for the packed operator.**  The `i`-th `gstep` of `RhA i` (i.e. the
expression produced by one application of the metric-tower recursion to `RhA i`, in which the
`gtTower`-values are replaced by their packed form) equals `RhA (i+1)`: the `Fin (i+1)`-sum
splits into the `Fin i`-directions of the inner tower plus the single term that differentiates the
inner *value* slot `d_{i+1}`. -/
lemma RhA_succ (G : ℝ → SMet I M) (t : ℝ) (i : ℕ)
    (d : Fin (i+2) → TF (I := I) (M := M)) (P Q : TF (I := I) (M := M)) (x : M) :
    mvfderiv I (fun y => RhA G t i (fun l : Fin (i+1) => d l.succ) P Q y) x (d 0 x)
      - (∑ j : Fin (i+1), RhA G t i (Function.update (fun l : Fin (i+1) => d l.succ) j
            (fun y => (lcOf (G 0)) ((fun l : Fin (i+1) => d l.succ) j) y (d 0 y))) P Q x)
      - RhA G t i (fun l : Fin (i+1) => d l.succ)
          (fun y => (lcOf (G 0)) P y (d 0 y)) Q x
      - RhA G t i (fun l : Fin (i+1) => d l.succ) P
          (fun y => (lcOf (G 0)) Q y (d 0 y)) x
      = RhA G t (i+1) d P Q x := by
  simp only [RhA, tower, step_eq_stepAux, stepAux, Fin.sum_univ_castSucc, Fin.castSucc_zero,
    Fin.succ_castSucc, Fin.succ_last, Nat.succ_eq_add_one, upd_cs_comp, upd_last_comp,
    upd_cs_last, upd_last_last, Function.comp_def]
  ring

/-! ## 4. The theorem -/

theorem gtTower_succ_eq_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (i : ℕ)
    (d : Fin (i+1) → (Π y : M, TangentSpace I y))
    (Y Z : Π y : M, TangentSpace I y)
    (hd : ∀ j, Work.Diff.EXT.ATower.SmE I M (d j))
    (hY : Work.Diff.EXT.ATower.SmE I M Y) (hZ : Work.Diff.EXT.ATower.SmE I M Z) (x : M) :
    Work.Diff.EXT.ConnCov.DTB.gtTower G t (i+1) d Y Z x
      = Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (fun _ => Work.Diff.EXT.aOf G t) i
          (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y Z x
        + Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (fun _ => Work.Diff.EXT.aOf G t) i
          (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z Y x := by
  have key : ∀ (i : ℕ) (d : Fin (i+1) → (Π y : M, TangentSpace I y))
      (Y Z : Π y : M, TangentSpace I y),
      (∀ j, Work.Diff.EXT.ATower.SmE I M (d j)) →
      Work.Diff.EXT.ATower.SmE I M Y → Work.Diff.EXT.ATower.SmE I M Z → ∀ x : M,
      Work.Diff.EXT.ConnCov.DTB.gtTower G t (i+1) d Y Z x
        = Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (fun _ => Work.Diff.EXT.aOf G t) i
            (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Y Z x
          + Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
              (fun _ => Work.Diff.EXT.aOf G t) i
            (fun j : Fin i => d (Fin.castSucc j)) (d (Fin.last i)) Z Y x := by
    intro i
    induction i with
    | zero =>
      intro d Y Z hd hY hZ x
      rw [gtTower_one_eq hLC G t d Y Z (hd 0) hY hZ x]
      simp only [tower, Fin.last_zero]
    | succ i ih =>
      intro d Y Z hd hY hZ x
      -- write the target's right-hand side in the packed form
      show gtTower G t (i+1+1) d Y Z x = RhA G t (i+1) d Y Z x + RhA G t (i+1) d Z Y x
      -- smoothness of the two functions whose derivative occurs
      have hd' : ∀ j : Fin (i+1), SmE I M ((fun l : Fin (i+1) => d l.succ) j) :=
        fun j => hd j.succ
      have hsmYZ : SmF I M (fun y : M => RhA G t i (fun l : Fin (i+1) => d l.succ) Y Z y) :=
        aOfTower_smF hLC G t i (fun j : Fin i => (fun l : Fin (i+1) => d l.succ) j.castSucc)
          ((fun l : Fin (i+1) => d l.succ) (Fin.last i)) Y Z
          (fun j => hd' j.castSucc) (hd' (Fin.last i)) hY hZ
      have hsmZY : SmF I M (fun y : M => RhA G t i (fun l : Fin (i+1) => d l.succ) Z Y y) :=
        aOfTower_smF hLC G t i (fun j : Fin i => (fun l : Fin (i+1) => d l.succ) j.castSucc)
          ((fun l : Fin (i+1) => d l.succ) (Fin.last i)) Z Y
          (fun j => hd' j.castSucc) (hd' (Fin.last i)) hZ hY
      -- unfold the left-hand side one step
      rw [show gtTower G t (i+1+1) d Y Z x
            = gstep (lcOf (G 0)) (gtTower G t (i+1)) d Y Z x from rfl, gstep]
      -- the derivative term: substitute the induction hypothesis, distribute `mvfderiv`
      rw [show (fun y : M => gtTower G t (i+1) (fun l : Fin (i+1) => d l.succ) Y Z y)
            = (fun y : M => RhA G t i (fun l : Fin (i+1) => d l.succ) Y Z y)
              + (fun y : M => RhA G t i (fun l : Fin (i+1) => d l.succ) Z Y y) from by
        funext y
        rw [Pi.add_apply]
        exact ih _ Y Z hd' hY hZ y]
      rw [connCov_mvfderiv_add_val (hsmYZ.mdifferentiableAt (by simp))
        (hsmZY.mdifferentiableAt (by simp))]
      -- the sum term
      have hupd : ∀ j : Fin (i+1), ∀ k, SmE I M (Function.update (fun l : Fin (i+1) => d l.succ) j
          (fun y => (lcOf (G 0)) ((fun l : Fin (i+1) => d l.succ) j) y (d 0 y)) k) := by
        intro j k
        have hsrc : SmE I M (fun y => (lcOf (G 0)) ((fun l : Fin (i+1) => d l.succ) j) y (d 0 y)) :=
          lcOf_apply_smE hLC (G 0) ((fun l : Fin (i+1) => d l.succ) j) (d 0) (hd' j) (hd 0)
        by_cases hk : k = j
        · subst hk; rw [Function.update_self]; exact hsrc
        · rw [Function.update_of_ne hk]; exact hd' k
      rw [show (∑ j : Fin (i+1), gtTower G t (i+1)
              (Function.update (fun l : Fin (i+1) => d l.succ) j
                (fun y => (lcOf (G 0)) ((fun l : Fin (i+1) => d l.succ) j) y (d 0 y))) Y Z x)
            = (∑ j : Fin (i+1), RhA G t i
                (Function.update (fun l : Fin (i+1) => d l.succ) j
                  (fun y => (lcOf (G 0)) ((fun l : Fin (i+1) => d l.succ) j) y (d 0 y))) Y Z x)
              + (∑ j : Fin (i+1), RhA G t i
                (Function.update (fun l : Fin (i+1) => d l.succ) j
                  (fun y => (lcOf (G 0)) ((fun l : Fin (i+1) => d l.succ) j) y (d 0 y))) Z Y x)
            from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => ih _ Y Z (hupd j) hY hZ x]
      -- the two correction terms
      rw [ih (fun l : Fin (i+1) => d l.succ) (fun y => (lcOf (G 0)) Y y (d 0 y)) Z
        hd' (lcOf_apply_smE hLC (G 0) Y (d 0) hY (hd 0)) hZ]
      rw [ih (fun l : Fin (i+1) => d l.succ) Y (fun y => (lcOf (G 0)) Z y (d 0 y))
        hd' hY (lcOf_apply_smE hLC (G 0) Z (d 0) hZ (hd 0))]
      -- both sides are now sums of the two packed expressions
      rw [← RhA_succ G t i d Y Z x, ← RhA_succ G t i d Z Y x]
      simp only [RhA]
      ring
  exact key i d Y Z hd hY hZ x

end Work.Diff.EXT.ConnCov.DTB
