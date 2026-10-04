import Mathlib
import Submission.Work.Diff.EXT.ATower.DA3Defs
import Submission.Work.Diff.EXT.ConnCov.RicTowerDefs
import Submission.Work.Diff.EXT.ATower.tower_slotAdd_smF
import Submission.Work.EXT.contMDiffCovariantDerivative_lcOf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.EXT.ATower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-! ## The combinatorial core

The target identity is the combination of two facts:

* the `(0,3)`-recursion `step` of `Work.Diff.EXT.ATower` is matched by the `(0,2)`-recursion `step2`
  on the *Koszul combination* of a `(0,2)`-object:  `step cov (Comb τ) = Comb (step2 cov τ)`;
* the base case `Comb (tower2 (baseRic2 g) 1) = dR3 G t`, which is definitional.

The differentiability input is exactly `SmF2 (tower2 (baseRic2 (G t)) (k+1))`: for smooth fields the
fixed `(0,2)`-Ricci tower is smooth, so `mvfderiv` may be split over the `±`-combination. -/

/-- The constant type family of tangent fields on `Fin (n+1)`, used to instantiate `Fin.snoc` so
that the statements below elaborate without relying on type-family inference. -/
abbrev TFfam (n : ℕ) : Fin (n + 1) → Type _ := fun _ => TF (I := I) (M := M)

/-- `Fin.snoc` on tuples of tangent fields, with the constant type family made explicit. -/
def TFsnoc {n : ℕ} (v : Fin n → TF (I := I) (M := M)) (A : TF (I := I) (M := M)) :
    Fin (n + 1) → TF (I := I) (M := M) :=
  Fin.snoc (α := TFfam (I := I) (M := M) n) v A

@[simp] theorem TFsnoc_castSucc {n : ℕ} (v : Fin n → TF (I := I) (M := M))
    (A : TF (I := I) (M := M)) (j : Fin n) : TFsnoc v A j.castSucc = v j :=
  Fin.snoc_castSucc (α := TFfam (I := I) (M := M) n) A v j

@[simp] theorem TFsnoc_last {n : ℕ} (v : Fin n → TF (I := I) (M := M))
    (A : TF (I := I) (M := M)) : TFsnoc v A (Fin.last n) = A :=
  Fin.snoc_last (α := TFfam (I := I) (M := M) n) A v

theorem TFsnoc_apply_zero {n : ℕ} (v : Fin (n + 1) → TF (I := I) (M := M))
    (A : TF (I := I) (M := M)) : TFsnoc v A 0 = v 0 := by
  rw [TFsnoc]
  exact Fin.snoc_apply_zero (α := TFfam (I := I) (M := M) (n + 1)) A v

/-- Updating a tuple and appending an element commute (for tangent fields). -/
theorem TFsnoc_update {k : ℕ} (u : Fin k → TF (I := I) (M := M)) (A W : TF (I := I) (M := M))
    (j : Fin k) :
    Function.update (TFsnoc u A) j.castSucc W = TFsnoc (Function.update u j W) A := by
  rw [TFsnoc, TFsnoc]
  exact (Fin.snoc_update (α := TFfam (I := I) (M := M) k) A u j W).symm

/-- Replacing the appended element. -/
theorem TFsnoc_update_last {k : ℕ} (u : Fin k → TF (I := I) (M := M)) (A W : TF (I := I) (M := M)) :
    Function.update (TFsnoc u A) (Fin.last k) W = TFsnoc u W := by
  rw [TFsnoc, TFsnoc]
  exact Fin.update_snoc_last (α := TFfam (I := I) (M := M) k) A u W

/-- The `succ`-restriction of `snoc v A` is `snoc (v ∘ succ) A`. -/
theorem TFsnoc_succ_apply {k : ℕ} (v : Fin (k + 1) → TF (I := I) (M := M))
    (A : TF (I := I) (M := M)) (i : Fin (k + 1)) :
    TFsnoc v A i.succ = TFsnoc (fun j : Fin k => v j.succ) A i := by
  rw [TFsnoc, TFsnoc]
  cases i using Fin.lastCases with
  | last => rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_last]
  | cast j => rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- Function form of `TFsnoc_succ_apply`. -/
theorem TFsnoc_succ_comp {k : ℕ} (v : Fin (k + 1) → TF (I := I) (M := M))
    (A : TF (I := I) (M := M)) :
    (fun i : Fin (k + 1) => TFsnoc v A i.succ) = TFsnoc (fun j : Fin k => v j.succ) A :=
  funext (fun i => TFsnoc_succ_apply v A i)

/-- **The Koszul combination of a `(0,2)`-tower object, as an `Op3`.**  For an `Op2 (k+1)` object
`σ`, `Comb σ` is the `Op3 k` object `-(σ (snoc v A) B C + σ (snoc v B) A C - σ (snoc v C) A B)`:
the first value slot is promoted to the *last direction slot* of the underlying `(0,2)`-tower. -/
noncomputable def Comb {k : ℕ} (σ : Work.Diff.EXT.ConnCov.Op2 (I := I) (M := M) (k + 1)) :
    Op3 (I := I) (M := M) k :=
  fun v A B C x =>
    -(σ (TFsnoc v A) B C x + σ (TFsnoc v B) A C x - σ (TFsnoc v C) A B x)

/-- **Smoothness of an `Op2` object on smooth tuples of fields** (the `Op2`-analogue of the
`SmF`-component of `GoodOp`). -/
def SmF2 {k : ℕ} (σ : Work.Diff.EXT.ConnCov.Op2 (I := I) (M := M) k) : Prop :=
  ∀ (v : Fin k → TF (I := I) (M := M)) (A B : TF (I := I) (M := M)),
    (∀ j, SmE I M (v j)) → SmE I M A → SmE I M B → SmF I M (σ v A B)

/-- The connection applied to two smooth fields is a smooth field. -/
theorem smE_cov_apply {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative cov (⊤ : ℕ∞))
    {Y Z : TF (I := I) (M := M)} (hY : SmE I M Y) (hZ : SmE I M Z) :
    SmE I M (fun y => cov Y y (Z y)) :=
  Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply cov hcov hY hZ

/-- **Smoothness of one recursion step of the `(0,2)`-tower.** -/
theorem step2_SmF2 (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {k : ℕ} (τ : Work.Diff.EXT.ConnCov.Op2 (I := I) (M := M) k) (hτ : SmF2 τ) :
    SmF2 (Work.Diff.EXT.ConnCov.step2 cov τ) := by
  intro v A B hv hA hB x
  have hu : ∀ j : Fin k, SmE I M (v j.succ) := fun j => hv j.succ
  have hW : ∀ i : Fin k,
      (∀ j, SmE I M ((Function.update (fun j : Fin k => v j.succ) i
        (fun y => cov (v i.succ) y (v 0 y))) j)) := by
    intro i j
    by_cases hj : j = i
    · rw [hj, Function.update_self]
      exact hcov (v i.succ) (v 0) (hv i.succ) (hv 0)
    · rw [Function.update_of_ne hj]
      exact hu j
  rw [show (Work.Diff.EXT.ConnCov.step2 cov τ v A B)
      = (fun x : M => (d% (τ (fun i : Fin k => v i.succ) A B) x) (v 0 x)
          - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
              (fun y => cov (v i.succ) y (v 0 y))) A B x
          - τ (fun i : Fin k => v i.succ) (fun y => cov A y (v 0 y)) B x
          - τ (fun i : Fin k => v i.succ) A (fun y => cov B y (v 0 y)) x) from
    funext (fun x => Work.Diff.EXT.ConnCov.step2_apply cov τ v A B x)]
  have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => (d% (τ (fun i : Fin k => v i.succ) A B) y) (v 0 y)) x :=
    Work.Diff.C.mvfderiv_contMDiffAt (hτ (fun j : Fin k => v j.succ) A B hu hA hB x) (hv 0 x)
  have h2 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
        (fun y => cov (v i.succ) y (v 0 y))) A B y) x :=
    ContMDiffAt.sum (t := Finset.univ)
      (f := fun i : Fin k => τ (Function.update (fun j : Fin k => v j.succ) i
        (fun y => cov (v i.succ) y (v 0 y))) A B) (fun i _ => hτ _ A B (hW i) hA hB x)
  have h3 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => τ (fun i : Fin k => v i.succ) (fun y => cov A y (v 0 y)) B y) x :=
    hτ (fun j : Fin k => v j.succ) (fun y => cov A y (v 0 y)) B hu
      (hcov A (v 0) hA (hv 0)) hB x
  have h4 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun y : M => τ (fun i : Fin k => v i.succ) A (fun y => cov B y (v 0 y)) y) x :=
    hτ (fun j : Fin k => v j.succ) A (fun y => cov B y (v 0 y)) hu hA
      (hcov B (v 0) hB (hv 0)) x
  exact ((h1.sub h2).sub h3).sub h4

/-- **Smoothness of the honest `(0,2)`-tower on smooth tuples of fields.** -/
theorem tower2_SmF2 (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    (β : Work.Diff.EXT.ConnCov.Op2 (I := I) (M := M) 0) (hβ : SmF2 β) :
    ∀ k : ℕ, SmF2 (Work.Diff.EXT.ConnCov.tower2 cov β k)
  | 0 => hβ
  | k + 1 => step2_SmF2 cov hcov (Work.Diff.EXT.ConnCov.tower2 cov β k)
      (tower2_SmF2 cov hcov β hβ k)

/-- **Splitting the `step2`-sum over the last direction slot.**  For a tuple `u : Fin k → TF`, a
field `A`, a substitution `Φ : TF → TF` and an evaluation `Z`,

`∑_{i : Fin (k+1)} Z (update (snoc u A) i (Φ ((snoc u A) i)))`
`  = ∑_{j : Fin k} Z (snoc (update u j (Φ (u j))) A) + Z (snoc u (Φ A))`.

The `i = last` term is exactly the correction of the *value* slot `A` of the `(0,3)`-recursion. -/
theorem sum_snoc_split {k : ℕ} (u : Fin k → TF (I := I) (M := M)) (A : TF (I := I) (M := M))
    (Φ : TF (I := I) (M := M) → TF (I := I) (M := M))
    (Z : (Fin (k + 1) → TF (I := I) (M := M)) → ℝ) :
    (∑ i : Fin (k + 1), Z (Function.update (TFsnoc u A) i (Φ (TFsnoc u A i))))
      = (∑ j : Fin k, Z (TFsnoc (Function.update u j (Φ (u j))) A))
        + Z (TFsnoc u (Φ A)) := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    rw [TFsnoc_castSucc, TFsnoc_update]
  · congr 1
    rw [TFsnoc_last, TFsnoc_update_last]

/-! ## The recursion step

The heart of the proof: on smooth tuples the `(0,3)`-recursion `step` of the Koszul combination
`Comb τ` is the Koszul combination `Comb (step2 τ)` of the `(0,2)`-recursion step. -/

/-- **Splitting the `step2`-sum over the last direction slot, for the connection correction
`y ↦ ∇_{·} · (w y)`.**  Specialised form of `sum_snoc_split` in which the substitution is
`Φ X = fun y => cov X y (w y)` *with the lambdas spelled out*, so that both sides of the identity
below contain syntactically identical correction fields. -/
theorem sum_snoc_split_cov (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    {k : ℕ} (u : Fin k → TF (I := I) (M := M)) (A w : TF (I := I) (M := M))
    (Z : (Fin (k + 1) → TF (I := I) (M := M)) → ℝ) :
    (∑ i : Fin (k + 1), Z (Function.update (TFsnoc u A) i
        (fun y => cov (TFsnoc u A i) y (w y))))
      = (∑ j : Fin k, Z (TFsnoc (Function.update u j (fun y => cov (u j) y (w y))) A))
        + Z (TFsnoc u (fun y => cov A y (w y))) := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    rw [TFsnoc_castSucc, TFsnoc_update]
  · congr 1
    rw [TFsnoc_last, TFsnoc_update_last]

/-- **The recursion step of the Koszul combination.**  For an `Op2 (k+1)`-object `τ` which is
`C^∞` on smooth tuples, the `(0,3)`-recursion applied to `Comb τ` is `Comb` of the `(0,2)`-recursion
applied to `τ`. -/
theorem step_Comb (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {k : ℕ} (τ : Work.Diff.EXT.ConnCov.Op2 (I := I) (M := M) (k + 1)) (hτ : SmF2 τ)
    (v : Fin (k + 1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ j, SmE I M (v j)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) (x : M) :
    step cov (Comb τ) v A B C x = Comb (Work.Diff.EXT.ConnCov.step2 cov τ) v A B C x := by
  have hu : ∀ j : Fin k, SmE I M ((fun i : Fin k => v i.succ) j) := fun j => hv j.succ
  have hsn : ∀ (Z : TF (I := I) (M := M)), SmE I M Z →
      ∀ j, SmE I M ((TFsnoc (fun i : Fin k => v i.succ) Z) j) := by
    intro Z hZ j
    cases j using Fin.lastCases with
    | last => rw [TFsnoc_last]; exact hZ
    | cast i => rw [TFsnoc_castSucc]; exact hu i
  -- differentiability of the three tower functions appearing in the split
  have hmdA : MDiffAt (τ (TFsnoc (fun i : Fin k => v i.succ) A) B C) x :=
    (hτ _ B C (hsn A hA) hB hC x).mdifferentiableAt (by simp)
  have hmdB : MDiffAt (τ (TFsnoc (fun i : Fin k => v i.succ) B) A C) x :=
    (hτ _ A C (hsn B hB) hA hC x).mdifferentiableAt (by simp)
  have hmdC : MDiffAt (τ (TFsnoc (fun i : Fin k => v i.succ) C) A B) x :=
    (hτ _ A B (hsn C hC) hA hB x).mdifferentiableAt (by simp)
  have hsplit : mvfderiv I (Comb τ (fun i : Fin k => v i.succ) A B C) x (v 0 x)
      = -(mvfderiv I (τ (TFsnoc (fun i : Fin k => v i.succ) A) B C) x (v 0 x)
          + mvfderiv I (τ (TFsnoc (fun i : Fin k => v i.succ) B) A C) x (v 0 x)
          - mvfderiv I (τ (TFsnoc (fun i : Fin k => v i.succ) C) A B) x (v 0 x)) := by
    have e1 : (Comb τ (fun i : Fin k => v i.succ) A B C)
        = -( (fun y : M => τ (TFsnoc (fun i : Fin k => v i.succ) A) B C y)
              + (fun y : M => τ (TFsnoc (fun i : Fin k => v i.succ) B) A C y)
              - (fun y : M => τ (TFsnoc (fun i : Fin k => v i.succ) C) A B y) ) := rfl
    rw [e1, mvfderiv_neg (I := I)
          (g := (fun y : M => τ (TFsnoc (fun i : Fin k => v i.succ) A) B C y)
              + (fun y : M => τ (TFsnoc (fun i : Fin k => v i.succ) B) A C y)
              - (fun y : M => τ (TFsnoc (fun i : Fin k => v i.succ) C) A B y))
          (x := x),
      mvfderiv_sub (I := I) (x := x) (hmdA.add hmdB) hmdC,
      mvfderiv_add (I := I) (x := x) hmdA hmdB]
    simp only [add_apply, sub_apply, neg_apply]
  rw [step_eq_stepAux]
  simp only [stepAux]
  rw [hsplit]
  simp only [Comb, Work.Diff.EXT.ConnCov.step2_apply]
  -- identify the `snoc`-tuples of the right-hand side
  simp only [TFsnoc_succ_apply, TFsnoc_apply_zero]
  -- split the three sums over `Fin (k+1)` into sums over `Fin k` plus the `last` term
  rw [sum_snoc_split_cov cov (u := fun i : Fin k => v i.succ) (A := A) (w := v 0)
        (Z := fun t => τ t B C x),
    sum_snoc_split_cov cov (u := fun i : Fin k => v i.succ) (A := B) (w := v 0)
        (Z := fun t => τ t A C x),
    sum_snoc_split_cov cov (u := fun i : Fin k => v i.succ) (A := C) (w := v 0)
        (Z := fun t => τ t A B x)]
  -- reduce the left-hand side's sum
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- **Smooth-tuple congruence for `stepAux`.**  If two `Op3 k` objects agree on all tuples of
smooth fields, then the recursion step `stepAux` (whose direction tuple and head are explicit
arguments) takes the same value for them. -/
theorem stepAux_eq_of_smEq (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {k : ℕ} {τ₁ τ₂ : Op3 (I := I) (M := M) k}
    (h : ∀ (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (u i)) → SmE I M A → SmE I M B → SmE I M C →
      ∀ y : M, τ₁ u A B C y = τ₂ u A B C y)
    (w : TF (I := I) (M := M)) (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hw : SmE I M w) (hu : ∀ i, SmE I M (u i)) (hA : SmE I M A) (hB : SmE I M B)
    (hC : SmE I M C) (x : M) :
    stepAux cov τ₁ w u A B C x = stepAux cov τ₂ w u A B C x := by
  have hupd : ∀ i : Fin k,
      (∀ j, SmE I M ((Function.update u i (fun y => cov (u i) y (w y))) j)) := by
    intro i j
    by_cases hj : j = i
    · rw [hj, Function.update_self]
      exact hcov (u i) w (hu i) hw
    · rw [Function.update_of_ne hj]
      exact hu j
  have hfun : τ₁ u A B C = τ₂ u A B C := funext (fun y => h u A B C hu hA hB hC y)
  have hsum : (∑ i : Fin k, τ₁ (Function.update u i (fun y => cov (u i) y (w y))) A B C x)
      = ∑ i : Fin k, τ₂ (Function.update u i (fun y => cov (u i) y (w y))) A B C x :=
    Finset.sum_congr rfl (fun i _ => h _ A B C (hupd i) hA hB hC x)
  have hA' : τ₁ u (fun y => cov A y (w y)) B C x = τ₂ u (fun y => cov A y (w y)) B C x :=
    h u _ B C hu (hcov A w hA hw) hB hC x
  have hB' : τ₁ u A (fun y => cov B y (w y)) C x = τ₂ u A (fun y => cov B y (w y)) C x :=
    h u A _ C hu hA (hcov B w hB hw) hC x
  have hC' : τ₁ u A B (fun y => cov C y (w y)) x = τ₂ u A B (fun y => cov C y (w y)) x :=
    h u A B _ hu hA hB (hcov C w hC hw) x
  simp only [stepAux]
  rw [congrArg (fun F : M → ℝ => mvfderiv I F x (w x)) hfun, hsum, hA', hB', hC']

/-- **Smooth-tuple congruence for the recursion step.** -/
theorem step_eq_of_smEq (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {k : ℕ} {τ₁ τ₂ : Op3 (I := I) (M := M) k}
    (h : ∀ (u : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (u i)) → SmE I M A → SmE I M B → SmE I M C →
      ∀ y : M, τ₁ u A B C y = τ₂ u A B C y)
    (v : Fin (k + 1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ i, SmE I M (v i)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) (x : M) :
    step cov τ₁ v A B C x = step cov τ₂ v A B C x := by
  rw [step_eq_stepAux, step_eq_stepAux]
  exact stepAux_eq_of_smEq cov hcov h (v 0) (fun i : Fin k => v i.succ) A B C (hv 0)
    (fun i => hv i.succ) hA hB hC x

/-- **The base case**: the Koszul combination of the level-`1` fixed `(0,2)`-Ricci tower is the
Koszul combination `dR3` of `∇^{G 0}Ric(G t)`.  Definitional. -/
theorem comb_base (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    Comb (Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ConnCov.baseRic2 (G t)) 1) = dR3 G t := by
  funext v A B C x
  simp only [Comb, TFsnoc, Fin.snoc_zero, Work.Diff.EXT.ConnCov.tower2,
    Work.Diff.EXT.ConnCov.step2, Work.Diff.EXT.ConnCov.baseRic2, dR3, rho3,
    Submission.Diff.covDerivSym2, Finset.univ_eq_empty, Finset.sum_empty, sub_zero,
    neg_sub]
  simp only [show ∀ (X Y Z : TF (I := I) (M := M)),
      (Work.Diff.EXT.ConnCov.baseRic2 (G t) (fun _ : Fin 0 => X) Y Z)
        = (fun y : M => Submission.Diff.ricAt (Submission.Diff.lcOf (G t)) y (Y y) (Z y))
      from fun X Y Z => rfl]

/-- **The tower of `dR3` is the Koszul combination of the fixed `(0,2)`-Ricci tower** (induction on
`k`), assuming only the smoothness of the base `Ric(G t)` on smooth fields. -/
theorem tower_eq_Comb (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (hbase : SmF2 (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) (G t))) :
    ∀ k : ℕ, ∀ (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C → ∀ x : M,
      Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0)) (dR3 G t) k v A B C x
        = Comb (Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)) v A B C x := by
  have hcov : ∀ (Y Z : TF (I := I) (M := M)), SmE I M Y → SmE I M Z →
      SmE I M (fun y => (Submission.Diff.lcOf (G 0)) Y y (Z y)) :=
    fun Y Z hY hZ => smE_cov_apply (Work.EXT.contMDiffCovariantDerivative_lcOf (G 0)) hY hZ
  intro k
  induction k with
  | zero =>
      intro v A B C hv hA hB hC x
      rw [comb_base]
      rfl
  | succ k ih =>
      intro v A B C hv hA hB hC x
      have hsm : SmF2 (Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)) :=
        tower2_SmF2 _ hcov _ hbase (k + 1)
      rw [show Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0)) (dR3 G t) (k + 1)
            v A B C = step (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0)) (dR3 G t) k) v A B C
          from rfl]
      rw [step_eq_of_smEq (Submission.Diff.lcOf (G 0)) hcov
        (fun u A' B' C' hu hA' hB' hC' y => ih u A' B' C' hu hA' hB' hC' y)
        v A B C hv hA hB hC x]
      rw [step_Comb (Submission.Diff.lcOf (G 0)) hcov
        (Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)) hsm v A B C hv hA hB hC x]
      rfl

/-- **The target identity, with the smoothness of the base `Ric(G t)` as an explicit
hypothesis.**  This is the form in which the tower induction is cashed in: the only input still
missing is `Work.Diff.EXT.ricAt_smF_noT2`. -/
theorem dR3_tower_eq_tower2_of_smF
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (hbase : SmF2 (Work.Diff.EXT.ConnCov.baseRic2 (I := I) (M := M) (G t))) :
    ∀ (k : ℕ) (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C → ∀ x : M,
      Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (Work.Diff.EXT.ATower.dR3 G t) k v A B C x
        = -(Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
                (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
                (Fin.snoc v A) B C x
            + Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
                (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
                (Fin.snoc v B) A C x
            - Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
                (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
                (Fin.snoc v C) A B x) := by
  intro k v A B C hv hA hB hC x
  rw [tower_eq_Comb G t hbase k v A B C hv hA hB hC x]
  rfl

/-- **The tower of the Koszul combination `dR3` of `ρ = ∇^{G 0}Ric(G t)` is the same combination
of the fixed `(0,2)`-Ricci tower at level `k + 1`.**

`Work.Diff.EXT.ATower.rho3 G t` is the `(0,3)`-tensor `ρ(X,Y,Z) = (∇^{G 0}_X Ric(G t))(Y,Z)` (its
first value slot is used as a derivation direction), and
`dR3 G t = -(ρ(X,Y,Z) + ρ(Y,X,Z) - ρ(Z,X,Y))` is the Koszul combination of it (see `DA3Defs.lean`,
where `dAOfBase_eq_dR3` identifies the reaction `∂ₜ aOf` with `dR3`).  The `∇^{G 0}`-tower of `dR3`
is the Koszul combination of the `∇^{G 0}`-tower of `ρ`, and that tower of `ρ` is the fixed
`(0,2)`-tower of the Ricci tensor at level `k + 1` with the last value slot `A` promoted to the
innermost derivation direction: this is the identity proved here.

## Route

Induction on `k`.  The fields are assumed smooth (`SmE`): this is necessary, because the induction
step splits `mvfderiv` over the `±` combination of the three tower functions, and `mvfderiv` is
additive only on differentiable functions (`mvfderiv_add`/`mvfderiv_sub`); for smooth fields the
towers are smooth (`Work.Diff.EXT.ATower.tower_slotAdd_smF`, applied to the base `dR3`, whose
`SlotAdd` is `map_add`-linearity of `covDerivSym2` and of the Ricci bilinear form and whose `SmF` is
the smoothness of `Ric(G t)`), so differentiability is available.

* `k = 0`: `tower (dR3 G t) 0 v A B C x = dR3 G t ∅ A B C x = -(ρ(A,B,C) + ρ(B,A,C) - ρ(C,A,B))`
  by definition (`dR3`), and `ρ(W,X,Y) = covDerivSym2 (lcOf (G 0)) Ric W X Y` unfolds to
  `step2 (lcOf (G 0)) (baseRic2 (G t)) (fun _ : Fin 1 => W) X Y`, so the right-hand side is the
  same combination (using `Fin.snoc (Fin.elim0) W = fun _ => W`).
* Step: the recursion `step` of the `Op3` tower treats the three value slots symmetrically, and its
  first value slot has exactly the same correction pattern as a *direction* slot of the `(0,2)`
  recursion `step2`; moreover `(Fin.snoc v A) ∘ Fin.succ = Fin.snoc (v ∘ Fin.succ) A`.  Hence
  `step (tower (dR3 G t) k) v A B C` rewrites into the combination of the three `step2`-expressions
  and the induction hypothesis applied at the tuples `(v ∘ Fin.succ, A, B, C)`,
  `(v ∘ Fin.succ, B, A, C)`, `(v ∘ Fin.succ, C, A, B)` and at their modified tuples closes the goal.
  (The `i`-sum of `step2` for `i = Fin.last k` is exactly the correction of the `A`-slot of `step`;
  no separate permutation statement is needed — the induction may be carried out directly on this
  combined identity.) -/
theorem dR3_tower_eq_tower2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (k : ℕ) (v : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ i, SmE I M (v i)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) (x : M) :
    Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
        (Work.Diff.EXT.ATower.dR3 G t) k v A B C x
      = -(Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
              (Fin.snoc v A) B C x
          + Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
              (Fin.snoc v B) A C x
          - Work.Diff.EXT.ConnCov.tower2 (Submission.Diff.lcOf (G 0))
              (Work.Diff.EXT.ConnCov.baseRic2 (G t)) (k + 1)
              (Fin.snoc v C) A B x) := by
  -- The whole identity is reduced to the smoothness of the base `Ric(G t)` on smooth fields:
  -- `dR3_tower_eq_tower2_of_smF` below proves the target from
  -- `hbase : SmF2 (baseRic2 (G t))`.
  --
  -- That input is *not* available under the hypotheses of this statement: `baseRic2` is defined
  -- through the frozen `Submission.Diff.ricAt`/`rmVec`, which contract the *constant model* basis
  -- vectors into the first curvature slot through `smoothExt`; the ε-specification of `smoothExt`
  -- needs a globally smooth field with value `finBasis ℝ E i` at the point, and the natural
  -- candidate `fun y => (v : TangentSpace I y)` is *not* smooth in general (it is a
  -- nowhere-vanishing section whenever `v ≠ 0`, contradicting the hairy ball theorem on `S²`).
  -- In the workspace the smoothness of `y ↦ ricAt (lcOf g) y (A y) (B y)` is therefore only known
  -- under `[I.Boundaryless] [T2Space M]` (`Work.Diff.EXT.ConnCov.RicTr.baseRic_sm`,
  -- `Work.Diff.EXT.rmP_field_contMDiffAt`), which are exactly the hypotheses that the sole
  -- consumer `Work.Diff.EXT.ATower.dAOfTowerBoundShi_piece` carries.
  sorry

end Work.Diff.EXT.ATower
