import Mathlib
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ConnCov.RicTr.ShiftDefs
import Submission.Work.Diff.EXT.ConnCov.RicTrNT.HtowerSmF
import Submission.Work.Diff.EXT.ConnCov.RicTrNT.SelSumBound
import Submission.Work.Diff.EXT.ConnCov.RicFlip.SelSumSplit
import Submission.Work.Diff.EXT.ConnCov.RicFlip.CoefTelescope
import Submission.Commons.Geometry.Manifold.Riemannian.metricCompatible_scaleMetric
import Submission.Work.Diff.GE.smp_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
/-!
# The bound for the tower from the bound for the honest tower (stand-alone copy)

This module is a copy of `Submission/Work/Diff/EXT/ConnCov/RicTr/towerBound_of_htowerBound.lean`
(kept verbatim apart from the three substitutions listed below), placed in the fresh namespace
`Work.Diff.EXT.ConnCov.RicTrNT` so that it does **not** collide with the original declarations.

Reason for the copy: the original imports `RicTr/htower_smF`, which (unnecessarily) imports
`RicTr/ricTowerBound_fixed` and hence `ConnCov/deltaTower`; the Ricci-tower chapter
(`ConnCov/RicTowerDefs`) declares a constant of the same name `Op2`, so no module can import both
the δ-tower leg and the Ricci-tower leg.  `RicTrNT/HtowerSmF` is a stand-alone copy of that
smoothness lemma with the spurious import removed.

Furthermore the original proof routes its final combinatorics through the three lemmas
`RicTr.SelSumDecomp`, `RicTr.ReindexIdentity`, `RicTr.SelSumBound`, which are *still `sorry`* in
the workspace; here they are replaced by

* `RicFlip.SelSumSplit` (proved; the identical statement of `SelSumDecomp`),
* `RicFlip.CoefTelescope` (proved; the identical statement of `ReindexIdentity`),
* `RicTrNT.SelSumBound` (the re-filed, to-be-proved arithmetic lemma `SelSumBound`).

With these, every declaration below is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

/-!
# The bound for the tower from the bound for the honest tower

`Work.Diff.EXT.ConnCov.honestTower` defines the *honest* recursion `hstep = step + drop` and the
honest tower `htower`; since `step = hstep - drop` definitionally, the tower `tower cov base m` and
the honest tower are related by a fixed signed combination of *selection objects*:

  `tower cov base m v A B C x
     = Σ_{j ≤ m} (-1)^{m+j} (m-j)! · Σ_{f : Fin j ↪o Fin m} htower cov base j (v ∘ f) A B C x`.

This identity is **not** true for arbitrary sections (`mvfderiv` in the recursion is only additive on
differentiable functions, see `tower_eq_htower_expansion.lean`), so it is proved here for *smooth*
sections; the statement of the target only evaluates the tower through `valOp`, i.e. on the
`Classical.epsilon`-chosen smooth extensions `smoothExt x ·`, so this suffices.

The induction on `m` uses

* `step cov (Σ_j c_j • SelSum F j m) = Σ_j c_j • (Σ_f step cov (sel (F j) f))` — the recursion step
  is additive on the locus where the relevant functions are differentiable, and honest towers of a
  smooth base over a smooth connection are `C^∞` on smooth fields
  (`Work.Diff.EXT.ConnCov.RicTr.htower_smF`);
* the *per-selection recursion*
  `step (sel (F j) f) = sel (F (j+1)) (insF f) - (m-j+1) • sel (F j) (shiftF f)`;
* the reindexing `SelSum F (j+1) (m+1) = SelSumIns F j m + SelSumSh F (j+1) m` (`SelSumDecomp`),
  together with the coefficient telescope `ReindexIdentity`.

The final arithmetic is `SelSumBound`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.RicTrNT

open Work.Diff.EXT.ATower Work.Diff.EXT.ConnCov Work.Diff.EXT.ConnCov.RicTr
open Work.Diff.EXT.ConnCov.RicFlip

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## 1. Scalar algebra of the selection operator -/

theorem sel_add_tb {j n : ℕ} (τ τ' : Op3 (I := I) (M := M) j) (f : Fin j → Fin n) :
    sel (τ + τ') f = sel τ f + sel τ' f := rfl

theorem sel_sub_tb {j n : ℕ} (τ τ' : Op3 (I := I) (M := M) j) (f : Fin j → Fin n) :
    sel (τ - τ') f = sel τ f - sel τ' f := rfl

theorem sel_smul_tb {j n : ℕ} (a : ℝ) (τ : Op3 (I := I) (M := M) j) (f : Fin j → Fin n) :
    sel (a • τ) f = a • sel τ f := rfl

theorem sel_sum_tb {j n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → Op3 (I := I) (M := M) j)
    (f : Fin j → Fin n) : sel (∑ i ∈ s, F i) f = ∑ i ∈ s, sel (F i) f := by
  funext v A B C
  simp only [sel_apply, Finset.sum_apply]

/-! ## 2. The insertions on plain functions -/

/-- The insertion of a new first slot, as a plain function on `Fin`-axis maps. -/
noncomputable def insFun {j n : ℕ} (f : Fin j → Fin n) : Fin (j + 1) → Fin (n + 1) :=
  Fin.cases 0 (fun l => (f l).succ)

/-- The shift of all values, as a plain function on `Fin`-axis maps. -/
noncomputable def shFun {j n : ℕ} (f : Fin j → Fin n) : Fin j → Fin (n + 1) := fun l => (f l).succ

@[simp] theorem insFun_zero {j n : ℕ} (f : Fin j → Fin n) : insFun f 0 = 0 := by
  simp only [insFun, Fin.cases_zero]

@[simp] theorem insFun_succ {j n : ℕ} (f : Fin j → Fin n) (l : Fin j) :
    insFun f l.succ = (f l).succ := by
  simp only [insFun, Fin.cases_succ]

@[simp] theorem shFun_apply {j n : ℕ} (f : Fin j → Fin n) (l : Fin j) :
    shFun f l = (f l).succ := rfl

theorem insF_val_eq_insFun {j n : ℕ} (f : Hom j n) : (insF f).val = insFun f.val := rfl

theorem shiftF_val_eq_shFun {j n : ℕ} (f : Hom j n) : (shiftF f).val = shFun f.val := rfl

/-! ## 3. The combinatorics of one recursion step -/

/-- **Splitting a sum over `Fin m` along the image of an injection.** -/
theorem sum_fin_eq_sum_image {j m : ℕ} (f : Fin j → Fin m) (hf : Function.Injective f)
    (g : Fin m → ℝ) (c : ℝ) (hc : ∀ i : Fin m, i ∉ Finset.univ.image f → g i = c) :
    (∑ i : Fin m, g i) = (∑ l : Fin j, g (f l)) + ((m - j : ℕ) : ℝ) * c := by
  classical
  have hsub : Finset.univ.image f ⊆ (Finset.univ : Finset (Fin m)) := Finset.subset_univ _
  have hsplit : (∑ i : Fin m, g i)
      = (∑ i ∈ Finset.univ.image f, g i) + ∑ i ∈ (Finset.univ : Finset (Fin m)) \
          Finset.univ.image f, g i := by
    rw [← Finset.sum_sdiff hsub, add_comm]
  rw [hsplit]
  congr 1
  · rw [Finset.sum_image]
    intro a _ b _ hab
    exact hf hab
  · have hcard : ((Finset.univ : Finset (Fin m)) \ Finset.univ.image f).card = m - j := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_image_of_injective _ hf]
      simp
    have hconst : (∑ i ∈ (Finset.univ : Finset (Fin m)) \ Finset.univ.image f, g i)
        = ∑ _i ∈ (Finset.univ : Finset (Fin m)) \ Finset.univ.image f, c := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      exact hc i (Finset.mem_sdiff.mp hi).2
    rw [hconst, Finset.sum_const, hcard, nsmul_eq_mul]

/-- **The sum over `Fin m` of an update pulled back along an injection.** -/
theorem sum_fin_update_comp {j m : ℕ} {α : Type*} (f : Fin j → Fin m)
    (hf : Function.Injective f) (V W : Fin m → α) (U : (Fin j → α) → ℝ) :
    (∑ i : Fin m, U (fun l : Fin j => Function.update V i (W i) (f l)))
      = (∑ l : Fin j, U (Function.update (fun l : Fin j => V (f l)) l (W (f l))))
        + ((m - j : ℕ) : ℝ) * U (fun l : Fin j => V (f l)) := by
  classical
  have h := sum_fin_eq_sum_image f hf
    (fun i : Fin m => U (fun l : Fin j => Function.update V i (W i) (f l)))
    (U (fun l : Fin j => V (f l))) (fun i hi => by
      have hiff : ∀ l : Fin j, f l ≠ i := by
        intro l hl
        exact hi (Finset.mem_image.mpr ⟨l, Finset.mem_univ l, hl⟩)
      congr 1
      funext l
      rw [Function.update_of_ne (hiff l)])
  have his : ∀ l ∈ (Finset.univ : Finset (Fin j)),
      U (fun l₁ : Fin j => Function.update V (f l) (W (f l)) (f l₁))
        = U (Function.update (fun l : Fin j => V (f l)) l (W (f l))) := by
    intro l _
    congr 1
    funext l₁
    simp only [Function.update_apply]
    by_cases hl : l₁ = l
    · rw [if_pos (by rw [hl]), if_pos hl]
    · rw [if_neg (fun hfl => hl (hf hfl)), if_neg hl]
  rw [h, Finset.sum_congr rfl his]

/-- **The per-selection recursion** (for plain injective maps). -/
theorem step_sel_fun (cov : CovariantDerivative I E (TangentSpace I (M := M))) {j n : ℕ}
    (τ : Op3 (I := I) (M := M) j) (f : Fin j → Fin n) (hf : Function.Injective f) :
    step cov (sel τ f) = sel (step cov τ) (insFun f) - (((n - j : ℕ) : ℝ)) • sel τ (shFun f) := by
  funext v A B C x
  have key : (∑ i : Fin n, τ (fun l : Fin j => Function.update (fun i : Fin n => v i.succ) i
        (fun y : M => cov (v i.succ) y (v 0 y)) (f l)) A B C x)
      = (∑ l : Fin j, τ (Function.update (fun l : Fin j => v (f l).succ) l
          (fun y : M => cov (v (f l).succ) y (v 0 y))) A B C x)
        + ((n - j : ℕ) : ℝ) * τ (fun l : Fin j => v (f l).succ) A B C x :=
    sum_fin_update_comp f hf (fun i : Fin n => v i.succ)
      (fun i : Fin n => fun y : M => cov (v i.succ) y (v 0 y))
      (fun w : Fin j → TF (I := I) (M := M) => τ w A B C x)
  simp only [step, sel, insFun_zero, insFun_succ, shFun, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [key]
  ring

/-- **The per-selection recursion.** -/
theorem step_sel_tb (cov : CovariantDerivative I E (TangentSpace I (M := M))) {j n : ℕ}
    (τ : Op3 (I := I) (M := M) j) (f : Hom j n) :
    step cov (sel τ f.val)
      = sel (step cov τ) (insF f).val - (((n - j : ℕ) : ℝ)) • sel τ (shiftF f).val := by
  rw [step_sel_fun cov τ f.val f.property.injective, insF_val_eq_insFun, shiftF_val_eq_shFun]

/-- `drop` followed by the insertion `insF` is the shift `shiftF`. -/
theorem sel_drop_insF_tb {j n : ℕ} (τ : Op3 (I := I) (M := M) j) (f : Hom j n) :
    sel (drop τ) (insF f).val = sel τ (shiftF f).val := by
  funext v A B C x
  simp only [sel, drop, insF_val_zero, insF_val_succ, shiftF_val]

/-- **The per-selection recursion for the honest tower.** -/
theorem step_sel_htower_tb (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op3 (I := I) (M := M) 0) {j m : ℕ} (f : Hom j m) :
    step cov (sel (htower cov base j) f.val)
      = sel (htower cov base (j + 1)) (insF f).val
        - (((m - j + 1 : ℕ) : ℝ)) • sel (htower cov base j) (shiftF f).val := by
  have h₁ := step_sel_tb cov (htower cov base j) f
  have h₂ : step cov (htower cov base j) = htower cov base (j + 1) - drop (htower cov base j) :=
    step_eq_hstep_sub_drop cov (htower cov base j)
  rw [h₁, h₂, sel_sub_tb, sel_drop_insF_tb]
  funext v A B C x
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hcast : ((m - j + 1 : ℕ) : ℝ) = ((m - j : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  rw [hcast]
  ring

/-! ## 4. Additivity of the recursion step -/

/-- `mvfderiv` of a finite sum of functions differentiable at the point. -/
theorem mvfderiv_sum_tb {ι : Type*} (s : Finset ι) (F : ι → M → ℝ) {x : M}
    {v : TangentSpace I x} (hF : ∀ i ∈ s, MDiffAt (F i) x) :
    mvfderiv I (fun y : M => ∑ i ∈ s, F i y) x v = ∑ i ∈ s, mvfderiv I (F i) x v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hz : (fun y : M => ∑ i ∈ (∅ : Finset ι), F i y) = fun _ : M => (0 : ℝ) := by
        funext y; simp
      rw [hz, Finset.sum_empty]
      show mvfderiv I (fun _ : M => (0 : ℝ)) x v = 0
      rw [mvfderiv_const, ContinuousLinearMap.zero_apply]
  | insert a s ha ih =>
      have hsa : ∀ i ∈ s, MDiffAt (F i) x := fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hsum : MDiffAt (fun y : M => ∑ i ∈ s, F i y) x := by
        have heq : (fun y : M => ∑ i ∈ s, F i y) = (∑ i ∈ s, F i) := by
          funext y; rw [Finset.sum_apply]
        rw [heq]
        exact MDifferentiableAt.sum (t := s) (f := F) hsa
      have hfun : (fun y : M => ∑ i ∈ insert a s, F i y)
          = F a + fun y : M => ∑ i ∈ s, F i y := by
        funext y; rw [Finset.sum_insert ha]; rfl
      rw [Finset.sum_insert ha, hfun,
        mvfderiv_add (hF a (Finset.mem_insert_self a s)) hsum,
        ContinuousLinearMap.add_apply, ih hsa]

/-- The recursion step vanishes on the zero operator. -/
theorem step_zero_tb (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (v : Fin (k + 1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (x : M) :
    step cov (0 : Op3 (I := I) (M := M) k) v A B C x = 0 := by
  have h0 : (0 : Op3 (I := I) (M := M) k)
      = fun (_ : Fin k → TF (I := I) (M := M)) (_ _ _ : TF (I := I) (M := M)) (_ : M) =>
          (0 : ℝ) := rfl
  rw [h0]
  simp only [step, mvfderiv_const, Finset.sum_const_zero, zero_apply, sub_zero]

/-- The recursion step is additive in its operator argument, where the relevant functions are
differentiable at the point. -/
theorem step_add_tb (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ τ' : Op3 (I := I) (M := M) k) (v : Fin (k + 1) → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) (x : M)
    (h : MDiffAt (τ (fun i : Fin k => v i.succ) A B C) x)
    (h' : MDiffAt (τ' (fun i : Fin k => v i.succ) A B C) x) :
    step cov (τ + τ') v A B C x = step cov τ v A B C x + step cov τ' v A B C x := by
  simp only [step, Pi.add_apply]
  rw [mvfderiv_add h h']
  simp only [ContinuousLinearMap.add_apply, Finset.sum_add_distrib]
  ring

/-- The recursion step is additive over a finite sum of operators. -/
theorem step_sum_tb (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    {ι : Type*} (s : Finset ι) (Ψ : ι → Op3 (I := I) (M := M) k)
    (v : Fin (k + 1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (x : M)
    (h : ∀ l ∈ s, MDiffAt (Ψ l (fun i : Fin k => v i.succ) A B C) x) :
    step cov (∑ l ∈ s, Ψ l) v A B C x = ∑ l ∈ s, step cov (Ψ l) v A B C x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, step_zero_tb]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hsa : ∀ l ∈ s, MDiffAt (Ψ l (fun i : Fin k => v i.succ) A B C) x :=
        fun l hl => h l (Finset.mem_insert_of_mem hl)
      have hsum : MDiffAt ((∑ l ∈ s, Ψ l) (fun i : Fin k => v i.succ) A B C) x := by
        have heq : (∑ l ∈ s, Ψ l) (fun i : Fin k => v i.succ) A B C
            = (∑ l ∈ s, Ψ l (fun i : Fin k => v i.succ) A B C) := by
          funext y; simp only [Finset.sum_apply]
        rw [heq]
        exact MDifferentiableAt.sum (t := s)
          (f := fun l => Ψ l (fun i : Fin k => v i.succ) A B C) hsa
      rw [step_add_tb cov (Ψ a) (∑ l ∈ s, Ψ l) v A B C x
        (h a (Finset.mem_insert_self a s)) hsum, ih hsa, Finset.sum_insert ha]

/-- The recursion step commutes with a constant multiple of the operator. -/
theorem step_smul_tb (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (a : ℝ) (τ : Op3 (I := I) (M := M) k) (v : Fin (k + 1) → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) (x : M) :
    step cov (a • τ) v A B C x = a * step cov τ v A B C x := by
  have h1 : (d% (a • (τ (fun i : Fin k => v i.succ) A B C)) x) (v 0 x)
      = a * (d% (τ (fun i : Fin k => v i.succ) A B C) x) (v 0 x) := by
    have hL : d% (a • (τ (fun i : Fin k => v i.succ) A B C)) x
        = a • d% (τ (fun i : Fin k => v i.succ) A B C) x :=
      Commons.Geometry.Manifold.Riemannian.mvfderiv_const_smul a
        (τ (fun i : Fin k => v i.succ) A B C) x
    rw [hL, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [step, Pi.smul_apply, smul_eq_mul]
  rw [h1, ← Finset.mul_sum]
  ring

/-- The recursion step depends only on the values of its operator argument on smooth tuples. -/
theorem step_congr_smooth_tb (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    {k : ℕ} {τ τ' : Op3 (I := I) (M := M) k}
    (h : ∀ (w : Fin k → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)),
      (∀ i, SmE I M (w i)) → SmE I M A → SmE I M B → SmE I M C → τ w A B C = τ' w A B C)
    (v : Fin (k + 1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hv : ∀ i, SmE I M (v i)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    step cov τ v A B C = step cov τ' v A B C := by
  funext x
  have hw : ∀ i, SmE I M ((fun i : Fin k => v i.succ) i) := fun i => hv i.succ
  have e1 : mvfderiv I (τ (fun i : Fin k => v i.succ) A B C) x (v 0 x)
      = mvfderiv I (τ' (fun i : Fin k => v i.succ) A B C) x (v 0 x) :=
    congrArg (fun F : M → ℝ => mvfderiv I F x (v 0 x)) (h _ A B C hw hA hB hC)
  have e2 : ∀ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
        (fun y => cov (v i.succ) y (v 0 y))) A B C
      = τ' (Function.update (fun j : Fin k => v j.succ) i
        (fun y => cov (v i.succ) y (v 0 y))) A B C := by
    intro i
    refine h _ A B C ?_ hA hB hC
    intro l
    by_cases hl : l = i
    · rw [hl, Function.update_self]
      exact hcov (v i.succ) (v 0) (hv _) (hv 0)
    · rw [Function.update_of_ne hl]; exact hv l.succ
  have e2s : (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
        (fun y => cov (v i.succ) y (v 0 y))) A B C x)
      = ∑ i : Fin k, τ' (Function.update (fun j : Fin k => v j.succ) i
        (fun y => cov (v i.succ) y (v 0 y))) A B C x :=
    Finset.sum_congr rfl (fun i _ => congrFun (e2 i) x)
  have e3 : τ (fun i : Fin k => v i.succ) (fun y => cov A y (v 0 y)) B C
      = τ' (fun i : Fin k => v i.succ) (fun y => cov A y (v 0 y)) B C :=
    h _ _ B C hw (hcov A (v 0) hA (hv 0)) hB hC
  have e4 : τ (fun i : Fin k => v i.succ) A (fun y => cov B y (v 0 y)) C
      = τ' (fun i : Fin k => v i.succ) A (fun y => cov B y (v 0 y)) C :=
    h _ _ _ C hw hA (hcov B (v 0) hB (hv 0)) hC
  have e5 : τ (fun i : Fin k => v i.succ) A B (fun y => cov C y (v 0 y))
      = τ' (fun i : Fin k => v i.succ) A B (fun y => cov C y (v 0 y)) :=
    h _ _ _ _ hw hA hB (hcov C (v 0) hC (hv 0))
  simp only [step]
  rw [e1, e2s, congrFun e3 x, congrFun e4 x, congrFun e5 x]

/-! ## 5. Smoothness of the selection sums -/

/-- The selection sum of the honest towers is smooth on smooth fields. -/
theorem SelSum_smF_tb (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    (base : Op3 (I := I) (M := M) 0)
    (hsm : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      SmE I M A → SmE I M B → SmE I M C → SmF I M (base v A B C))
    {j m : ℕ} (w : Fin m → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M))
    (hw : ∀ i, SmE I M (w i)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    SmF I M (SelSum (htower cov base) j m w A B C) := by
  have hfun : SelSum (htower cov base) j m w A B C
      = fun y => ∑ f : Hom j m, sel (htower cov base j) f.val w A B C y := by
    funext y
    simp only [SelSum, Finset.sum_apply]
  rw [hfun]
  intro x
  refine ContMDiffAt.sum (t := Finset.univ)
    (f := fun f : Hom j m => sel (htower cov base j) f.val w A B C) (fun f _ => ?_)
  have h2 : sel (htower cov base j) f.val w A B C
      = htower cov base j (fun l : Fin j => w (f.val l)) A B C := by
    funext y; rw [sel_apply]
  rw [h2]
  exact htower_smF cov hcov base hsm j (fun l => w (f.val l)) A B C
    (fun l => hw _) hA hB hC x

/-! ## 6. The degenerate selection -/

/-- The canonical (unique) strictly monotone map `Fin 0 → Fin n`. -/
noncomputable def hom0 (n : ℕ) : Hom 0 n := ⟨Fin.elim0, fun a => Fin.elim0 a⟩

/-- A sum over `Hom 0 n` has a single term. -/
theorem sum_hom0_eq (n : ℕ) (G : Hom 0 n → ℝ) : (∑ f : Hom 0 n, G f) = G (hom0 n) := by
  have huniv : (Finset.univ : Finset (Hom 0 n)) = {hom0 n} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    exact ⟨Finset.mem_univ _, fun b _ => Subtype.ext (funext fun l => Fin.elim0 l)⟩
  rw [huniv, Finset.sum_singleton]

/-- At level `0` the whole selection sum is the "shift" part. -/
theorem SelSum_zero_tb (F : (k : ℕ) → Op3 (I := I) (M := M) k) (m : ℕ) :
    SelSum F 0 (m + 1) = SelSumSh F 0 m := by
  rw [SelSum, SelSumSh]
  refine Finset.sum_bij (fun (f : Hom 0 (m + 1)) _ => hom0 m)
    (fun a _ => Finset.mem_univ _)
    (fun a _ b _ _ => Subtype.ext (funext fun l => Fin.elim0 l))
    (fun b _ => ⟨hom0 (m + 1), Finset.mem_univ _, Subtype.ext (funext fun l => Fin.elim0 l)⟩)
    (fun a _ => ?_)
  have h : a.val = (shiftF (hom0 m)).val := funext fun l => Fin.elim0 l
  rw [h]

/-- The top "shift" selection is empty. -/
theorem SelSumSh_top_tb (F : (k : ℕ) → Op3 (I := I) (M := M) k) (m : ℕ) :
    SelSumSh F m.succ m = 0 := by
  haveI : IsEmpty (Hom (m + 1) m) :=
    ⟨fun f => by
      have h1 : Fintype.card (Fin (m + 1)) ≤ Fintype.card (Fin m) :=
        Fintype.card_le_of_injective f.val f.property.injective
      simp at h1⟩
  rw [SelSumSh]
  exact Finset.sum_eq_zero (fun f _ => isEmptyElim f)

/-! ## 7. The coefficients of the shift identity -/

/-- The coefficients `c(m,j) = (-1)^{m+j} (m-j)!` of the shift identity. -/
noncomputable def shCo (m j : ℕ) : ℝ := (-1 : ℝ) ^ (m + j) * ((m - j).factorial : ℝ)

/-! ## 8. The recursion step applied to a selection sum -/

/-- **The recursion step on the selection sum.** -/
theorem step_SelSum_tb (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    (base : Op3 (I := I) (M := M) 0)
    (hsm : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      SmE I M A → SmE I M B → SmE I M C → SmF I M (base v A B C))
    {j m : ℕ} (v : Fin (m + 1) → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (x : M)
    (hv : ∀ i, SmE I M (v i)) (hA : SmE I M A) (hB : SmE I M B) (hC : SmE I M C) :
    step cov (SelSum (htower cov base) j m) v A B C x
      = SelSumIns (htower cov base) j m v A B C x
        - (((m - j + 1 : ℕ) : ℝ)) * SelSumSh (htower cov base) j m v A B C x := by
  have hterm : ∀ f : Hom j m,
      step cov (sel (htower cov base j) f.val) v A B C x
        = sel (htower cov base (j + 1)) (insF f).val v A B C x
          - (((m - j + 1 : ℕ) : ℝ)) * sel (htower cov base j) (shiftF f).val v A B C x := by
    intro f
    have h := congrFun (congrFun (congrFun (congrFun (congrFun
      (step_sel_htower_tb cov base f) v) A) B) C) x
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h
  have hMDf : ∀ f ∈ (Finset.univ : Finset (Hom j m)),
      MDiffAt (sel (htower cov base j) f.val (fun i : Fin m => v i.succ) A B C) x := by
    intro f _
    have h0 : MDiffAt (htower cov base j
        (fun l : Fin j => (fun i : Fin m => v i.succ) (f.val l)) A B C) x :=
      (htower_smF cov hcov base hsm j (fun l => (fun i : Fin m => v i.succ) (f.val l)) A B C
        (fun l => hv _) hA hB hC x).mdifferentiableAt (by simp)
    simpa only [sel_apply] using h0
  rw [SelSum]
  rw [step_sum_tb cov (Finset.univ : Finset (Hom j m))
    (fun f : Hom j m => sel (htower cov base j) f.val) v A B C x hMDf]
  rw [Finset.sum_congr rfl (fun f _ => hterm f), Finset.sum_sub_distrib]
  congr 1
  · rw [SelSumIns]
    simp only [Finset.sum_apply]
  · rw [← Finset.mul_sum]
    congr 1
    rw [SelSumSh]
    simp only [Finset.sum_apply]


/-- The selection sum, written as a sum of honest towers. -/
theorem SelSum_eq_sum_htower_tb (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (base : Op3 (I := I) (M := M) 0) {j m : ℕ} (w : Fin m → TF (I := I) (M := M))
    (A B C : TF (I := I) (M := M)) :
    (∑ f : Hom j m, htower cov base j (fun l => w (f.val l)) A B C)
      = SelSum (htower cov base) j m w A B C := by
  funext y
  rw [SelSum]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun f _ => by rw [sel_apply])

/-! ## 9. The shift identity on smooth fields -/

/-- **The shift identity** (on smooth fields): the tower is the signed selection sum of the honest
towers. -/
theorem tower_eval_eq_tb (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), SmE I M Y → SmE I M Z →
      SmE I M (fun y => cov Y y (Z y)))
    (base : Op3 (I := I) (M := M) 0)
    (hsm : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      SmE I M A → SmE I M B → SmE I M C → SmF I M (base v A B C)) :
    ∀ (m : ℕ) (v : Fin m → TF (I := I) (M := M)) (A B C : TF (I := I) (M := M)) (x : M),
      (∀ i, SmE I M (v i)) → SmE I M A → SmE I M B → SmE I M C →
      tower cov base m v A B C x
        = ∑ j ∈ Finset.range (m + 1), shCo m j *
            ∑ f : Hom j m, htower cov base j (fun l => v (f.val l)) A B C x := by
  intro m
  induction m with
  | zero =>
      intro v A B C x hv hA hB hC
      have hco0 : shCo 0 0 = 1 := by norm_num [shCo]
      rw [show tower cov base 0 v A B C x = base v A B C x from rfl, Finset.sum_range_one,
        hco0, one_mul]
      rw [sum_hom0_eq 0 (fun f => htower cov base 0 (fun l => v (f.val l)) A B C x), htower_zero]
      rw [show (fun l : Fin 0 => v ((hom0 0).val l)) = v from funext fun l => Fin.elim0 l]
  | succ m ih =>
      intro v A B C x hv hA hB hC
      have hexp : ∀ (w : Fin m → TF (I := I) (M := M)) (A' B' C' : TF (I := I) (M := M)),
          (∀ i, SmE I M (w i)) → SmE I M A' → SmE I M B' → SmE I M C' →
          tower cov base m w A' B' C'
            = fun y => ∑ j ∈ Finset.range (m + 1), shCo m j *
                ∑ f : Hom j m, htower cov base j (fun l => w (f.val l)) A' B' C' y := by
        intro w A' B' C' hw hA' hB' hC'
        funext y
        exact ih w A' B' C' y hw hA' hB' hC'
      have hexp2 : ∀ (w : Fin m → TF (I := I) (M := M)) (A' B' C' : TF (I := I) (M := M)),
          (∀ i, SmE I M (w i)) → SmE I M A' → SmE I M B' → SmE I M C' →
          tower cov base m w A' B' C'
            = (∑ j ∈ Finset.range (m + 1),
                shCo m j • SelSum (htower cov base) j m) w A' B' C' := by
        intro w A' B' C' hw hA' hB' hC'
        funext y
        rw [congrFun (hexp w A' B' C' hw hA' hB' hC') y]
        simp only [SelSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sel_apply]
      have hMD : ∀ j ∈ Finset.range (m + 1),
          MDiffAt ((shCo m j • SelSum (htower cov base) j m) (fun i : Fin m => v i.succ) A B C) x := by
        intro j hj
        have h0 : MDiffAt (SelSum (htower cov base) j m (fun i : Fin m => v i.succ) A B C) x :=
          ((SelSum_smF_tb cov hcov base hsm (fun i : Fin m => v i.succ) A B C
            (fun i => hv i.succ) hA hB hC) x).mdifferentiableAt (by simp)
        exact h0.const_smul (shCo m j)
      rw [show tower cov base (m + 1) v A B C = step cov (tower cov base m) v A B C from rfl,
        step_congr_smooth_tb cov hcov (τ := tower cov base m)
          (τ' := ∑ j ∈ Finset.range (m + 1), shCo m j • SelSum (htower cov base) j m)
          hexp2 v A B C hv hA hB hC]
      rw [step_sum_tb cov (Finset.range (m + 1))
        (fun j => shCo m j • SelSum (htower cov base) j m) v A B C x hMD]
      rw [Finset.sum_congr rfl (fun j _ => step_smul_tb cov (shCo m j)
        (SelSum (htower cov base) j m) v A B C x)]
      rw [Finset.sum_congr rfl (fun j _ => by
        rw [step_SelSum_tb cov hcov base hsm v A B C x hv hA hB hC])]
      have hRHS : (∑ j ∈ Finset.range (m + 1 + 1), shCo (m + 1) j *
            ∑ f : Hom j (m + 1), htower cov base j (fun l => v (f.val l)) A B C x)
          = ∑ k ∈ Finset.range (m + 2), shCo (m + 1) k *
              SelSum (htower cov base) k (m + 1) v A B C x := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [SelSum, Finset.sum_apply, sel_apply]
      rw [hRHS]
      refine (CoefTelescope m
        (fun j => SelSumIns (htower cov base) j m v A B C x)
        (fun j => SelSumSh (htower cov base) j m v A B C x)
        (fun k => SelSum (htower cov base) k (m + 1) v A B C x) ?_ ?_ ?_).symm
      · exact congrFun (congrFun (congrFun (congrFun (congrFun (SelSum_zero_tb (htower cov base) m)
          v) A) B) C) x
      · intro k
        exact congrFun (congrFun (congrFun (congrFun (congrFun (SelSumSplit (htower cov base) k m)
          v) A) B) C) x
      · exact congrFun (congrFun (congrFun (congrFun (congrFun (SelSumSh_top_tb (htower cov base) m)
          v) A) B) C) x

theorem towerBound_of_htowerBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : Submission.Diff.SMet I M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hcov : ∀ (Y Z : Π y : M, TangentSpace I y), Work.Diff.EXT.ATower.SmE I M Y →
      Work.Diff.EXT.ATower.SmE I M Z →
      Work.Diff.EXT.ATower.SmE I M (fun y => cov Y y (Z y)))
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0)
    (hsm : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y)) (A B C : Π y : M, TangentSpace I y),
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M B →
      Work.Diff.EXT.ATower.SmE I M C →
      Work.Diff.EXT.ATower.SmF I M (base v A B C))
    (hlinA : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y))
      (A₁ A₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ)
      (B C : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M A₁ → Work.Diff.EXT.ATower.SmE I M A₂ →
      Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M C →
      base v (f₁ • A₁ + f₂ • A₂) B C x = f₁ x * base v A₁ B C x + f₂ x * base v A₂ B C x)
    (hlinB : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y))
      (B₁ B₂ : Π y : M, TangentSpace I y) (f₁ f₂ : M → ℝ)
      (A C : Π y : M, TangentSpace I y) (x : M),
      Work.Diff.EXT.ATower.SmF I M f₁ → Work.Diff.EXT.ATower.SmF I M f₂ →
      Work.Diff.EXT.ATower.SmE I M B₁ → Work.Diff.EXT.ATower.SmE I M B₂ →
      Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M C →
      base v A (f₁ • B₁ + f₂ • B₂) C x = f₁ x * base v A B₁ C x + f₂ x * base v A B₂ C x)
    (hvd : ∀ (v : Fin 0 → (Π y : M, TangentSpace I y)) (A A' B B' C C' : Π y : M, TangentSpace I y)
      (x : M), Work.Diff.EXT.ATower.SmE I M A → Work.Diff.EXT.ATower.SmE I M A' →
      Work.Diff.EXT.ATower.SmE I M B → Work.Diff.EXT.ATower.SmE I M B' →
      Work.Diff.EXT.ATower.SmE I M C → Work.Diff.EXT.ATower.SmE I M C' →
      A x = A' x → B x = B' x → C x = C' x → base v A B C x = base v A' B' C' x)
    (hCind : Work.Diff.EXT.ConnCov.CIndep base)
    (m : ℕ) (R : ℕ → ℝ) (hR0 : ∀ j, 0 ≤ R j)
    (hR : ∀ j, j ≤ m → ∀ (x : M) (w : Fin j → TangentSpace I x) (A B : TangentSpace I x),
      |Work.Diff.EXT.ATower.valOp (Work.Diff.EXT.ConnCov.htower cov base j)
          x w A B (0 : TangentSpace I x)|
        ≤ R j * (Finset.univ.prod (fun i : Fin j => Real.sqrt (g.inner x (w i) (w i)))
            * Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B))) :
    ∀ (x : M) (v : Fin m → TangentSpace I x) (A B : TangentSpace I x),
      |Work.Diff.EXT.ATower.valOp (Work.Diff.EXT.ATower.tower cov base m)
          x v A B (0 : TangentSpace I x)|
        ≤ ((Nat.factorial m : ℝ) * (∑ j ∈ Finset.range (m + 1), R j))
            * (Finset.univ.prod (fun i : Fin m => (1 + Real.sqrt (g.inner x (v i) (v i))))
                * Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B)) := by
  intro x v A B
  have hvs : ∀ i, SmE I M (smoothExt x (v i)) :=
    fun i => (Work.Diff.GE.smoothExt_spec (I := I) x (v i)).1
  have hAs : SmE I M (smoothExt x A) := (Work.Diff.GE.smoothExt_spec (I := I) x A).1
  have hBs : SmE I M (smoothExt x B) := (Work.Diff.GE.smoothExt_spec (I := I) x B).1
  have h0s : SmE I M (smoothExt x (0 : TangentSpace I x)) :=
    (Work.Diff.GE.smoothExt_spec (I := I) x (0 : TangentSpace I x)).1
  have hid := tower_eval_eq_tb cov hcov base hsm m (fun i => smoothExt x (v i))
    (smoothExt x A) (smoothExt x B) (smoothExt x (0 : TangentSpace I x)) x hvs hAs hBs h0s
  have hval : valOp (tower cov base m) x v A B (0 : TangentSpace I x)
      = ∑ j ∈ Finset.range (m + 1), shCo m j *
          ∑ f : Hom j m, valOp (htower cov base j) x (fun l => v (f.val l)) A B
            (0 : TangentSpace I x) := by
    simp only [valOp]
    rw [hid]
  rw [hval]
  have hsb := SelSumBound (m := m) (b := fun i => Real.sqrt (g.inner x (v i) (v i)))
    (hb := fun i => Real.sqrt_nonneg _) (R := R) (hR := hR0)
    (Q := Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B))
    (hQ := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (F := fun j (s : Fin j → Fin m) =>
      valOp (htower cov base j) x (fun l => v (s l)) A B (0 : TangentSpace I x))
    (hF := fun j hj s => by
      have h := hR j hj x (fun l => v (s.val l)) A B
      refine le_trans h (le_of_eq ?_)
      ring)
  have hgoal : ((Nat.factorial m : ℝ) * (∑ j ∈ Finset.range (m + 1), R j))
        * (Finset.univ.prod (fun i : Fin m => (1 + Real.sqrt (g.inner x (v i) (v i)))))
        * (Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B))
      = ((Nat.factorial m : ℝ) * (∑ j ∈ Finset.range (m + 1), R j))
        * (Finset.univ.prod (fun i : Fin m => (1 + Real.sqrt (g.inner x (v i) (v i))))
            * Real.sqrt (g.inner x A A) * Real.sqrt (g.inner x B B)) := by ring
  rw [hgoal] at hsb
  exact hsb

end Work.Diff.EXT.ConnCov.RicTrNT
