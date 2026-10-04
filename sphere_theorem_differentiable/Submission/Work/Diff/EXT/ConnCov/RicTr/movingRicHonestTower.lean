import Mathlib
import Submission.Work.Diff.EXT.ConnCov.honestTower
import Submission.Work.Diff.EXT.ConnCov.RicTowerDefs
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.covK_linear
import Submission.Work.Diff.EXT.covKRmExt_tensorial
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.Evol.covRic_eq_sum_covRm_fin
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRicPhi_eq_sum_covRm
import Submission.Work.Diff.GE.kato_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The honest tower of `baseRic` along a Ricci flow is uniformly bounded on `[T/2, T)`

`Work.Diff.EXT.ConnCov.htower (lcOf g) (baseRic g) m` is the *honest* `m`-th covariant derivative
of the Ricci tensor of the metric `g` (encoded as an `Op3` with an unused third value slot; the
third-slot correction of the `ATower` recursion is removed by `hstep = step + drop`).  The target
`Work.Diff.EXT.ConnCov.RicTr.movingRicHonestTower` states that along a Ricci flow `G` on `[0,T)`
with `|Rm| ≤ C` and with Shi's a priori estimates available, the tensors `∇^{g_t,m} Ric` are
uniformly bounded on the *collapsed* interval `[T/2, T)` by a constant times the product of the
metric norms of the arguments.

## Route

1. `htower_baseRic_eq` : the honest tower of `baseRic` is the lift (`liftOF`) of the honest
   `(0,2)`-tensor tower `tower2 (lcOf g) (baseRic2 g)`, whose value is `∇^{g,m} Ric`.
2. `tower2_eq_sum_covKRmExt_aux` — the **trace identity**, the mathematical core: for a smooth
   frame `W` which is `g`-orthonormal near `x`,

     `∇^{g,m} Ric(v; A, B)(y) = ∑ p, (∇^{g,m} Rm)(v; W_p, A, W_p, B)(y)`   for `y` near `x`.

   It is an induction on `m`.  The base case is the pointwise trace identity
   (`Work.Diff.Evol.ricAt_eq_sum_frame_ovf`).  In the induction step the two recursions differ only
   by the *frame correction*

     `∑ p, [ (∇^{g,m}Rm)(v; ∇_{v₀}W_p, A, W_p, B) + (∇^{g,m}Rm)(v; W_p, A, ∇_{v₀}W_p, B) ]`,

   which vanishes identically: expanding `∇_{v₀}W_p = ∑ s, c_{p s} W_s` in the frame and using the
   linearity of `∇^m Rm` in its first and third value slots, it becomes
   `∑_{p,s} c_{p s}(Θ_{s p} + Θ_{p s})`, which is zero for the *skew* matrix
   `c_{p s} = g(∇_{v₀}W_p, W_s)` (skew because the frame is orthonormal near the point) by the
   pure index relabelling `∑_{p,s}c_{p s}Θ_{s p} = -∑_{p,s}c_{p s}Θ_{p s}`
   (`Work.Diff.GE.covRic_skew_sum_zero`).  This is `frame_corr_zero`.
3. The evaluation bound `Work.Diff.EXT.covKRmExt_eval_bound` bounds each summand of the trace
   identity by `(1 + √|∇^m Rm|²)` times the product of the norms; summing the `n = finrank ℝ E`
   terms and using `Work.Diff.EXT.ShiBounds` at `σ = T/2` finishes.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT.ATower Work.Diff.EXT.ConnCov Work.Diff.EXT Work.Diff.GE

namespace Work.Diff.EXT.ConnCov.RicTr

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## The bridge between the *honest* `Op3`-tower of `baseRic` and the `(0,2)`-tower -/

/-- The lift of a two-value-slot operator to three value slots (the third slot is dummy). -/
noncomputable def liftOF {k : ℕ} (τ : Op2 (I := I) (M := M) k) : Op3 (I := I) (M := M) k :=
  fun v A B _ => τ v A B

/-- `liftOF` of `baseRic2` is `baseRic` (definitional). -/
theorem liftOF_baseRic2 (g : SMet I M) :
    liftOF (baseRic2 (I := I) (M := M) g) = baseRic g := rfl

/-- `hstep` commutes with the lift: the third-slot correction of `step` is exactly cancelled by
`drop` on the (third-slot independent) lifted operator. -/
theorem hstep_liftOF (cov : CovariantDerivative I E (TangentSpace I (M := M))) {k : ℕ}
    (τ : Op2 (I := I) (M := M) k) :
    hstep cov (liftOF τ) = liftOF (step2 cov τ) := by
  funext v A B C x
  simp only [hstep, Work.Diff.EXT.ATower.step, drop, liftOF, step2, Pi.add_apply]
  ring

/-- The honest `Op3`-tower of a lifted base is the lift of the `(0,2)`-tower. -/
theorem htower_liftOF (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (β : Op2 (I := I) (M := M) 0) (m : ℕ) :
    htower cov (liftOF β) m = liftOF (tower2 cov β m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [htower_succ, ih, hstep_liftOF]
    funext v A B C x
    exact (tower2_succ cov β m v A B x).symm

/-- **The honest tower of `baseRic`** is the lift of the `(0,2)`-tower of `baseRic2`. -/
theorem htower_baseRic_eq (g : SMet I M) (m : ℕ) :
    htower (lcOf g) (baseRic g) m
      = liftOF (tower2 (lcOf g) (baseRic2 (I := I) (M := M) g) m) := by
  rw [← liftOF_baseRic2 (I := I) (M := M) g]
  exact htower_liftOF (lcOf g) (baseRic2 (I := I) (M := M) g) m

/-- `valOp` of the honest tower of `baseRic` is the `(0,2)`-tower on the `smoothExt` fields. -/
theorem valOp_htower_baseRic_eq (g : SMet I M) (m : ℕ) (x : M)
    (v : Fin m → TangentSpace I x) (A B C : TangentSpace I x) :
    valOp (htower (lcOf g) (baseRic g) m) x v A B C
      = tower2 (lcOf g) (baseRic2 (I := I) (M := M) g) m
          (fun i => smoothExt x (v i)) (smoothExt x A) (smoothExt x B) x := by
  rw [htower_baseRic_eq (I := I) (M := M) g m]
  rfl

/-! ## Tensoriality of `∇^k Rm` in the shape used below -/

/-- The value of `∇^k Rm` at `x` on smooth fields depends only on the values at `x`: here we read
it off `Work.Diff.EXT.covKRm`. -/
theorem covKRmExt_eq_covKRm (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ) (x : M)
    {V : Fin k → TF (I := I) (M := M)} (hV : ∀ i, SmoothFieldT (I := I) (M := M) (V i))
    {A B C D : TF (I := I) (M := M)} (hA : SmoothFieldT (I := I) (M := M) A)
    (hB : SmoothFieldT (I := I) (M := M) B) (hC : SmoothFieldT (I := I) (M := M) C)
    (hD : SmoothFieldT (I := I) (M := M) D) :
    covKRmExt g k V A B C D x
      = covKRm g x k (fun i => V i x) (A x) (B x) (C x) (D x) := by
  have hV' : ∀ i, SmoothFieldT (I := I) (M := M) (fun y => smoothExt x (V i x) y) :=
    fun i => smoothExt_cmdiff x (V i x)
  rw [covKRm]
  exact covKRmExt_tensorial hLC k g x V (fun i => smoothExt x (V i x))
    A (smoothExt x (A x)) B (smoothExt x (B x)) C (smoothExt x (C x)) D (smoothExt x (D x))
    hV hV' hA (smoothExt_cmdiff x (A x)) hB (smoothExt_cmdiff x (B x))
    hC (smoothExt_cmdiff x (C x)) hD (smoothExt_cmdiff x (D x))
    (fun i => (smoothExt_apply x (V i x)).symm) (smoothExt_apply x (A x)).symm
    (smoothExt_apply x (B x)).symm (smoothExt_apply x (C x)).symm (smoothExt_apply x (D x)).symm

/-- Replacing the **first** value slot of `∇^k Rm` by a smooth field with the same value. -/
theorem replace_slot1 (hLC : LCSmooth I M) (g : SMet I M) (m : ℕ) (x : M)
    {v : Fin m → TF (I := I) (M := M)} (hvs : ∀ i, SmoothFieldT (I := I) (M := M) (v i))
    {A B C : TF (I := I) (M := M)} (hAs : SmoothFieldT (I := I) (M := M) A)
    (hBs : SmoothFieldT (I := I) (M := M) B) (hCs : SmoothFieldT (I := I) (M := M) C)
    {E₁ E₂ : TF (I := I) (M := M)} (hE₁ : SmoothFieldT (I := I) (M := M) E₁)
    (hE₂ : SmoothFieldT (I := I) (M := M) E₂) (hval : E₁ x = E₂ x) :
    covKRmExt g m v E₁ A B C x = covKRmExt g m v E₂ A B C x :=
  covKRmExt_tensorial hLC m g x v v E₁ E₂ A A B B C C hvs hvs hE₁ hE₂ hAs hAs hBs hBs
    hCs hCs (fun _ => rfl) hval rfl rfl rfl

/-- Replacing the **third** value slot of `∇^k Rm` by a smooth field with the same value. -/
theorem replace_slot3 (hLC : LCSmooth I M) (g : SMet I M) (m : ℕ) (x : M)
    {v : Fin m → TF (I := I) (M := M)} (hvs : ∀ i, SmoothFieldT (I := I) (M := M) (v i))
    {A B C : TF (I := I) (M := M)} (hAs : SmoothFieldT (I := I) (M := M) A)
    (hBs : SmoothFieldT (I := I) (M := M) B) (hCs : SmoothFieldT (I := I) (M := M) C)
    {E₁ E₂ : TF (I := I) (M := M)} (hE₁ : SmoothFieldT (I := I) (M := M) E₁)
    (hE₂ : SmoothFieldT (I := I) (M := M) E₂) (hval : E₁ x = E₂ x) :
    covKRmExt g m v A B E₁ C x = covKRmExt g m v A B E₂ C x :=
  covKRmExt_tensorial hLC m g x v v A A B B E₁ E₂ C C hvs hvs hAs hAs hBs hBs
    hE₁ hE₂ hCs hCs (fun _ => rfl) rfl rfl hval rfl

/-! ## Smoothness and linearity of `∇^k Rm` in its value slots -/

theorem constsmul_eq (c : ℝ) (U : TF (I := I) (M := M)) : ((fun _ : M => c) • U) = c • U := by
  funext y; simp

theorem smoothFieldT_zero (x : M) : SmoothFieldT (I := I) (M := M) (0 : TF (I := I) (M := M)) := by
  have h := (contMDiff_const (c := (0:ℝ))).smul_section (I := I) (F := E)
    (V := fun y : M => TangentSpace I y) (s := smoothExt x (0 : TangentSpace I x))
    (smoothExt_cmdiff x (0 : TangentSpace I x))
  have e : ((fun _ : M => (0:ℝ)) • (smoothExt x (0 : TangentSpace I x)))
      = (0 : TF (I := I) (M := M)) := by funext y; simp
  rwa [e] at h

theorem smoothFieldT_const_smul' {X : TF (I := I) (M := M)}
    (hX : SmoothFieldT (I := I) (M := M) X) (c : ℝ) :
    SmoothFieldT (I := I) (M := M) (c • X) := by
  simpa only [SmoothFieldT, Pi.smul_apply] using
    hX.const_smul_section (I := I) (F := E) (V := fun y : M => TangentSpace I y) (a := c)

theorem smoothFieldT_add {X Y : TF (I := I) (M := M)}
    (hX : SmoothFieldT (I := I) (M := M) X) (hY : SmoothFieldT (I := I) (M := M) Y) :
    SmoothFieldT (I := I) (M := M) (X + Y) := by
  simpa only [SmoothFieldT, Pi.add_apply] using
    hX.add_section (I := I) (F := E) (V := fun y : M => TangentSpace I y) hY

theorem smoothFieldT_sum {ι : Type*} (x : M) (s : Finset ι) (c : ι → ℝ)
    (U : ι → TF (I := I) (M := M)) (hU : ∀ i, SmoothFieldT (I := I) (M := M) (U i)) :
    SmoothFieldT (I := I) (M := M) (∑ i ∈ s, c i • U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smoothFieldT_zero (I := I) (M := M) x
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact smoothFieldT_add (smoothFieldT_const_smul' (hU a) (c a)) ih

/-- Linearity of `∇^k Rm` in its **first** value slot (the one contracted in the trace identity). -/
theorem linA2 (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ)
    {V : Fin k → TF (I := I) (M := M)} (hV : ∀ i, SmoothFieldT (I := I) (M := M) (V i))
    {B C D : TF (I := I) (M := M)} (hB : SmoothFieldT (I := I) (M := M) B)
    (hC : SmoothFieldT (I := I) (M := M) C) (hD : SmoothFieldT (I := I) (M := M) D)
    (c : ℝ) {U Y : TF (I := I) (M := M)}
    (hU : SmoothFieldT (I := I) (M := M) U) (hY : SmoothFieldT (I := I) (M := M) Y) (x : M) :
    covKRmExt g k V (c • U + Y) B C D x
      = c * covKRmExt g k V U B C D x + covKRmExt g k V Y B C D x := by
  obtain ⟨-, -, haddA, hsmulA, -, -, -, -, -, -⟩ := covK_linear hLC g k
  have h1 : covKRmExt g k V (c • U + Y) B C D x
      = covKRmExt g k V (c • U) B C D x + covKRmExt g k V Y B C D x := by
    have h := congrFun (haddA V (c • U) Y B C D hV
      (hU.const_smul_section (I := I) (F := E) (V := fun y : M => TangentSpace I y) (a := c))
      hY hB hC hD) x
    simpa only [Pi.add_apply] using h
  have h2 : covKRmExt g k V (c • U) B C D x = c * covKRmExt g k V U B C D x := by
    have h := congrFun (hsmulA V (fun _ : M => c) U B C D (contMDiff_const) hV hU hB hC hD) x
    rw [constsmul_eq (I := I) (M := M) c U] at h
    have h4 : (((fun _ : M => c) • (covKRmExt g k V U B C D)) x : ℝ)
        = c * covKRmExt g k V U B C D x := by simp
    rw [h4] at h
    exact h
  rw [h1, h2]

/-- Linearity of `∇^k Rm` in its **third** value slot (the other one contracted). -/
theorem linC2 (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ)
    {V : Fin k → TF (I := I) (M := M)} (hV : ∀ i, SmoothFieldT (I := I) (M := M) (V i))
    {A B D : TF (I := I) (M := M)} (hA : SmoothFieldT (I := I) (M := M) A)
    (hB : SmoothFieldT (I := I) (M := M) B) (hD : SmoothFieldT (I := I) (M := M) D)
    (c : ℝ) {U Y : TF (I := I) (M := M)}
    (hU : SmoothFieldT (I := I) (M := M) U) (hY : SmoothFieldT (I := I) (M := M) Y) (x : M) :
    covKRmExt g k V A B (c • U + Y) D x
      = c * covKRmExt g k V A B U D x + covKRmExt g k V A B Y D x := by
  obtain ⟨-, -, -, -, -, -, haddC, hsmulC, -, -⟩ := covK_linear hLC g k
  have h1 : covKRmExt g k V A B (c • U + Y) D x
      = covKRmExt g k V A B (c • U) D x + covKRmExt g k V A B Y D x := by
    have h := congrFun (haddC V A B (c • U) Y D hV hA hB
      (hU.const_smul_section (I := I) (F := E) (V := fun y : M => TangentSpace I y) (a := c))
      hY hD) x
    simpa only [Pi.add_apply] using h
  have h2 : covKRmExt g k V A B (c • U) D x = c * covKRmExt g k V A B U D x := by
    have h := congrFun (hsmulC V (fun _ : M => c) A B U D (contMDiff_const) hV hA hB hU hD) x
    rw [constsmul_eq (I := I) (M := M) c U] at h
    have h4 : (((fun _ : M => c) • (covKRmExt g k V A B U D)) x : ℝ)
        = c * covKRmExt g k V A B U D x := by simp
    rw [h4] at h
    exact h
  rw [h1, h2]

theorem sumA0 (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ)
    {V : Fin k → TF (I := I) (M := M)} (hV : ∀ i, SmoothFieldT (I := I) (M := M) (V i))
    {B C D : TF (I := I) (M := M)} (hB : SmoothFieldT (I := I) (M := M) B)
    (hC : SmoothFieldT (I := I) (M := M) C) (hD : SmoothFieldT (I := I) (M := M) D)
    (x : M) : covKRmExt g k V (0 : TF (I := I) (M := M)) B C D x = 0 := by
  obtain ⟨-, -, -, hsmulA, -, -, -, -, -, -⟩ := covK_linear hLC g k
  have h := hsmulA V (fun _ : M => (0:ℝ)) B B C D (contMDiff_const) hV hB hB hC hD
  have e : ((fun _ : M => (0:ℝ)) • B) = (0 : TF (I := I) (M := M)) := by funext y; simp
  rw [e] at h
  have hx := congrFun h x
  have h4 : (((fun _ : M => (0:ℝ)) • (covKRmExt g k V B B C D)) x : ℝ) = 0 := by simp
  simpa only [h4] using hx

theorem sumC0 (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ)
    {V : Fin k → TF (I := I) (M := M)} (hV : ∀ i, SmoothFieldT (I := I) (M := M) (V i))
    {A B D : TF (I := I) (M := M)} (hA : SmoothFieldT (I := I) (M := M) A)
    (hB : SmoothFieldT (I := I) (M := M) B) (hD : SmoothFieldT (I := I) (M := M) D)
    (x : M) : covKRmExt g k V A B (0 : TF (I := I) (M := M)) D x = 0 := by
  obtain ⟨-, -, -, -, -, -, -, hsmulC, -, -⟩ := covK_linear hLC g k
  have h := hsmulC V (fun _ : M => (0:ℝ)) A B D D (contMDiff_const) hV hA hB hD hD
  have e : ((fun _ : M => (0:ℝ)) • D) = (0 : TF (I := I) (M := M)) := by funext y; simp
  rw [e] at h
  have hx := congrFun h x
  have h4 : (((fun _ : M => (0:ℝ)) • (covKRmExt g k V A B D D)) x : ℝ) = 0 := by simp
  simpa only [h4] using hx

/-- Linearity of `∇^k Rm` in the first value slot over a finite sum. -/
theorem sumA (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ)
    {V : Fin k → TF (I := I) (M := M)} (hV : ∀ i, SmoothFieldT (I := I) (M := M) (V i))
    {B C D : TF (I := I) (M := M)} (hB : SmoothFieldT (I := I) (M := M) B)
    (hC : SmoothFieldT (I := I) (M := M) C) (hD : SmoothFieldT (I := I) (M := M) D)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (U : ι → TF (I := I) (M := M))
    (hU : ∀ i, SmoothFieldT (I := I) (M := M) (U i)) (x : M) :
    covKRmExt g k V (∑ i ∈ s, c i • U i) B C D x
      = ∑ i ∈ s, c i * covKRmExt g k V (U i) B C D x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact sumA0 hLC g k hV hB hC hD x
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      rw [linA2 hLC g k hV hB hC hD (c a) (hU a) (smoothFieldT_sum x t c U hU) x, ih]
      rw [Finset.sum_insert ha]

/-- Linearity of `∇^k Rm` in the third value slot over a finite sum. -/
theorem sumC (hLC : LCSmooth I M) (g : SMet I M) (k : ℕ)
    {V : Fin k → TF (I := I) (M := M)} (hV : ∀ i, SmoothFieldT (I := I) (M := M) (V i))
    {A B D : TF (I := I) (M := M)} (hA : SmoothFieldT (I := I) (M := M) A)
    (hB : SmoothFieldT (I := I) (M := M) B) (hD : SmoothFieldT (I := I) (M := M) D)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (U : ι → TF (I := I) (M := M))
    (hU : ∀ i, SmoothFieldT (I := I) (M := M) (U i)) (x : M) :
    covKRmExt g k V A B (∑ i ∈ s, c i • U i) D x
      = ∑ i ∈ s, c i * covKRmExt g k V A B (U i) D x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact sumC0 hLC g k hV hA hB hD x
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      rw [linC2 hLC g k hV hA hB hD (c a) (hU a) (smoothFieldT_sum x t c U hU) x, ih]
      rw [Finset.sum_insert ha]

/-! ## The frame correction vanishes -/

/-- **The frame correction of the trace identity vanishes.**  With `c p s = g(∇_{v₀}W_p, W_s)` the
(skew, because `W` is orthonormal near `x`) expansion of `∇_{v₀}W_p` in the frame and the linearity
of `∇^m Rm` in its first and third value slots turn the correction into
`∑_{p,s} c_{p s}(Θ_{s p} + Θ_{p s})`, which vanishes by relabelling the summation indices. -/
theorem frame_corr_zero (hLC : LCSmooth I M) (g : SMet I M) (m : ℕ) (x : M)
    {W : Fin (Module.finrank ℝ E) → TF (I := I) (M := M)}
    (hWs : ∀ p, SmoothFieldT (I := I) (M := M) (W p))
    (hWON : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun p => W p y))
    {v : Fin m → TF (I := I) (M := M)} (hvs : ∀ i, SmoothFieldT (I := I) (M := M) (v i))
    {A B u : TF (I := I) (M := M)} (hAs : SmoothFieldT (I := I) (M := M) A)
    (hBs : SmoothFieldT (I := I) (M := M) B) (hus : SmoothFieldT (I := I) (M := M) u) :
    ∑ p, ( covKRmExt g m v (fun z => (lcOf g (W p) z) (u z)) A (W p) B x
         + covKRmExt g m v (W p) A (fun z => (lcOf g (W p) z) (u z)) B x ) = 0 := by
  classical
  set c : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun p s => g.inner x ((lcOf g (W p) x) (u x)) (W s x) with hc
  have hskew : ∀ p s, c p s = - c s p := by
    intro p s
    have h := covRic_frame_skew (I := I) (M := M) hLC g x (u x) W hWs hWON p s
    rw [g.symm x (W p x) ((lcOf g (W s) x) (u x))] at h
    simp only [hc]
    linarith
  have hval : ∀ p, (fun z => (lcOf g (W p) z) (u z)) x = (∑ s, c p s • W s) x := by
    intro p
    have h := sum_smul_inner_eq_self_gen g x (fun s => W s x) hWON.self_of_nhds
      ((lcOf g (W p) x) (u x))
    rw [show (fun z => (lcOf g (W p) z) (u z)) x = (lcOf g (W p) x) (u x) from rfl, ← h]
    simp only [hc, Finset.sum_apply, Pi.smul_apply]
  have hsmooth : ∀ p, SmoothFieldT (I := I) (M := M) (fun z => (lcOf g (W p) z) (u z)) :=
    fun p => dirF_smooth hLC g (hWs p) hus
  have h1 : ∀ p, covKRmExt g m v (fun z => (lcOf g (W p) z) (u z)) A (W p) B x
      = ∑ s, c p s * covKRmExt g m v (W s) A (W p) B x := by
    intro p
    rw [replace_slot1 hLC g m x hvs hAs (hWs p) hBs (hsmooth p)
      (smoothFieldT_sum x Finset.univ (c p) W hWs) (hval p)]
    exact sumA hLC g m hvs hAs (hWs p) hBs Finset.univ (c p) W hWs x
  have h2 : ∀ p, covKRmExt g m v (W p) A (fun z => (lcOf g (W p) z) (u z)) B x
      = ∑ s, c p s * covKRmExt g m v (W p) A (W s) B x := by
    intro p
    rw [replace_slot3 hLC g m x hvs (hWs p) hAs hBs (hsmooth p)
      (smoothFieldT_sum x Finset.univ (c p) W hWs) (hval p)]
    exact sumC hLC g m hvs (hWs p) hAs hBs Finset.univ (c p) W hWs x
  have hmain : (∑ p, (∑ s, c p s * covKRmExt g m v (W s) A (W p) B x
                      + ∑ s, c p s * covKRmExt g m v (W p) A (W s) B x)) = 0 := by
    rw [Finset.sum_add_distrib]
    exact covRic_skew_sum_zero c (fun s p => covKRmExt g m v (W s) A (W p) B x) hskew
  refine Eq.trans (Finset.sum_congr rfl (fun p _ => ?_)) hmain
  rw [h1 p, h2 p]

/-! ## The trace identity -/

/-- **The trace identity for the honest tower of `Ric`.**  For a smooth frame `W` which is
`g`-orthonormal on the open set `U`, the `m`-th covariant derivative of the Ricci tensor is the
metric trace of the `m`-th covariant derivative of the curvature, at every point of `U`. -/
theorem tower2_eq_sum_covKRmExt_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (m : ℕ)
    {W : Fin (Module.finrank ℝ E) → TF (I := I) (M := M)}
    (hWs : ∀ p, SmoothFieldT (I := I) (M := M) (W p))
    (U : Set M) (hUo : IsOpen U) (hWON : ∀ y ∈ U, IsONFrame g y (fun p => W p y)) :
    ∀ y ∈ U, ∀ (v : Fin m → TF (I := I) (M := M)) (A B : TF (I := I) (M := M)),
      (∀ i, SmoothFieldT (I := I) (M := M) (v i)) →
      SmoothFieldT (I := I) (M := M) A → SmoothFieldT (I := I) (M := M) B →
      tower2 (lcOf g) (baseRic2 (I := I) (M := M) g) m v A B y
        = ∑ p, covKRmExt g m v (W p) A (W p) B y := by
  induction m with
  | zero =>
      intro y hy v A B hvs hAs hBs
      simp only [tower2_zero, covKRmExt, baseRic2]
      exact Work.Diff.Evol.ricAt_eq_sum_frame_ovf hLC g y (fun p => W p y) (hWON y hy) (A y) (B y)
  | succ m ih =>
      intro y hy v A B hvs hAs hBs
      have hUy : U ∈ 𝓝 y := hUo.mem_nhds hy
      have hONy : ∀ᶠ z in 𝓝 y, IsONFrame g z (fun p => W p z) :=
        Filter.eventually_of_mem hUy (fun z hz => hWON z hz)
      have hdir : ∀ i : Fin m,
          SmoothFieldT (I := I) (M := M) (fun z => (lcOf g (v i.succ) z) (v 0 z)) :=
        fun i => dirF_smooth hLC g (hvs i.succ) (hvs 0)
      have hupd : ∀ (i : Fin m) (Y : TF (I := I) (M := M)), SmoothFieldT (I := I) (M := M) Y →
          ∀ j, SmoothFieldT (I := I) (M := M) ((Function.update (fun j : Fin m => v j.succ) i Y) j) := by
        intro i Y hY j
        by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact hY
        · rw [Function.update_of_ne hj]; exact hvs j.succ
      have IH_v : tower2 (lcOf g) (baseRic2 g) m (fun i : Fin m => v i.succ) A B
          =ᶠ[𝓝 y] (fun z => ∑ p, covKRmExt g m (fun i : Fin m => v i.succ) (W p) A (W p) B z) :=
        Filter.eventually_of_mem hUy fun z hz => ih z hz _ A B (fun i => hvs i.succ) hAs hBs
      have IH_i : ∀ i : Fin m,
          tower2 (lcOf g) (baseRic2 g) m
              (Function.update (fun j : Fin m => v j.succ) i
                (fun z => (lcOf g (v i.succ) z) (v 0 z))) A B y
            = ∑ p, covKRmExt g m
                (Function.update (fun j : Fin m => v j.succ) i
                  (fun z => (lcOf g (v i.succ) z) (v 0 z)))
                (W p) A (W p) B y :=
        fun i => ih y hy _ A B (hupd i _ (hdir i)) hAs hBs
      have IH_A : tower2 (lcOf g) (baseRic2 g) m (fun i : Fin m => v i.succ)
            (fun z => (lcOf g A z) (v 0 z)) B y
            = ∑ p, covKRmExt g m (fun i : Fin m => v i.succ) (W p)
                (fun z => (lcOf g A z) (v 0 z)) (W p) B y :=
        ih y hy _ _ B (fun i => hvs i.succ) (dirF_smooth hLC g hAs (hvs 0)) hBs
      have IH_B : tower2 (lcOf g) (baseRic2 g) m (fun i : Fin m => v i.succ) A
            (fun z => (lcOf g B z) (v 0 z)) y
            = ∑ p, covKRmExt g m (fun i : Fin m => v i.succ) (W p) A (W p)
                (fun z => (lcOf g B z) (v 0 z)) y :=
        ih y hy _ A _ (fun i => hvs i.succ) hAs (dirF_smooth hLC g hBs (hvs 0))
      have hder : ((d% (tower2 (lcOf g) (baseRic2 g) m (fun i : Fin m => v i.succ) A B)) y)
            (v 0 y)
          = (∑ p, ((d% (covKRmExt g m (fun i : Fin m => v i.succ) (W p) A (W p) B)) y)
              (v 0 y)) := by
        have h1 := congrArg (fun (L : TangentSpace I y →L[ℝ] ℝ) => L (v 0 y))
          (Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) (M := M) IH_v)
        rw [h1]
        exact Work.Diff.GE.Kato3.mvfderiv_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E))) _
          (fun p => covK_fixedSmooth hLC g m (V := fun i : Fin m => v i.succ)
            (A := W p) (B := A) (C := W p) (D := B)
            (fun i => hvs i.succ) (hWs p) hAs (hWs p) hBs) y (v 0 y)
      have hLHS : tower2 (lcOf g) (baseRic2 g) (m+1) v A B y
          = (∑ p, ((d% (covKRmExt g m (fun i : Fin m => v i.succ) (W p) A (W p) B)) y)
              (v 0 y))
            - (∑ i : Fin m, ∑ p, covKRmExt g m
                (Function.update (fun j : Fin m => v j.succ) i
                  (fun z => (lcOf g (v i.succ) z) (v 0 z)))
                (W p) A (W p) B y)
            - (∑ p, covKRmExt g m (fun i : Fin m => v i.succ) (W p)
                (fun z => (lcOf g A z) (v 0 z)) (W p) B y)
            - (∑ p, covKRmExt g m (fun i : Fin m => v i.succ) (W p) A (W p)
                (fun z => (lcOf g B z) (v 0 z)) y) := by
        rw [tower2_succ, step2_apply]
        rw [hder, Finset.sum_congr rfl (fun i _ => IH_i i), IH_A, IH_B]
      have hRHS : (∑ p, covKRmExt g (m+1) v (W p) A (W p) B y)
          = (∑ p, ((d% (covKRmExt g m (fun i : Fin m => v i.succ) (W p) A (W p) B)) y)
              (v 0 y))
            - (∑ i : Fin m, ∑ p, covKRmExt g m
                (Function.update (fun j : Fin m => v j.succ) i
                  (fun z => (lcOf g (v i.succ) z) (v 0 z)))
                (W p) A (W p) B y)
            - (∑ p, covKRmExt g m (fun i : Fin m => v i.succ)
                (fun z => (lcOf g (W p) z) (v 0 z)) A (W p) B y)
            - (∑ p, covKRmExt g m (fun i : Fin m => v i.succ) (W p)
                (fun z => (lcOf g A z) (v 0 z)) (W p) B y)
            - (∑ p, covKRmExt g m (fun i : Fin m => v i.succ) (W p) A
                (fun z => (lcOf g (W p) z) (v 0 z)) B y)
            - (∑ p, covKRmExt g m (fun i : Fin m => v i.succ) (W p) A (W p)
                (fun z => (lcOf g B z) (v 0 z)) y) := by
        simp only [covKRmExt]
        simp only [Finset.sum_sub_distrib]
        rw [Finset.sum_comm]
      rw [hLHS, hRHS]
      have hFC := frame_corr_zero hLC g m y hWs hONy (fun i => hvs i.succ) hAs hBs (hvs 0)
      have hFCsplit : (∑ p, covKRmExt g m (fun i : Fin m => v i.succ)
              (fun z => (lcOf g (W p) z) (v 0 z)) A (W p) B y)
          + (∑ p, covKRmExt g m (fun i : Fin m => v i.succ) (W p) A
              (fun z => (lcOf g (W p) z) (v 0 z)) B y) = 0 := by
        rw [← Finset.sum_add_distrib]
        exact hFC
      linarith [hFCsplit]

end Helpers

/-! ## The target -/

theorem movingRicHonestTower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (k : ℕ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ k → ∀ x : M,
      ∀ (v : Fin m → TangentSpace I x) (A B Cc : TangentSpace I x),
        |Work.Diff.EXT.ATower.valOp
            (Work.Diff.EXT.ConnCov.htower (Submission.Diff.lcOf (G t))
              (Work.Diff.EXT.ConnCov.baseRic (G t)) m) x v A B Cc|
          ≤ R * (Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (v i) (v i)))
              * Real.sqrt ((G t).inner x A A) * Real.sqrt ((G t).inner x B B)) := by
  classical
  -- the collapsed interval is non-degenerate
  have hT2 : 0 < T / 2 := by linarith
  have hT2T : T / 2 < T := by linarith
  -- Shi's estimate at every order
  have hShi' : ∀ m : ℕ, ∃ Cm : ℝ, ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
      Work.Diff.EXT.curvNormK (G t) x m ≤ Cm :=
    fun m => hShi G T C (T / 2) hT hflow hbound hT2 hT2T m
  choose Csh hCsh using hShi'
  -- the evaluation bound at every order
  have hEval : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : Submission.Diff.SMet I M) (x : M) (v : Fin m → TangentSpace I x)
        (a b c d : TangentSpace I x),
        |Work.Diff.EXT.covKRmExt g m (fun i => smoothExt x (v i)) (smoothExt x a)
          (smoothExt x b) (smoothExt x c) (smoothExt x d) x|
          ≤ C * (1 + Real.sqrt (Work.Diff.EXT.curvNormK g x m))
            * (Finset.univ.prod (fun i : Fin m => Real.sqrt (g.inner x (v i) (v i)))
               * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
               * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) :=
    fun m => Work.Diff.EXT.covKRmExt_eval_bound hLC m
  choose Cev hCev using hEval
  have hCev0 : ∀ m, 0 ≤ Cev m := fun m => (hCev m).1
  have hCevb : ∀ m, ∀ (g : Submission.Diff.SMet I M) (x : M)
      (v : Fin m → TangentSpace I x) (a b c d : TangentSpace I x),
      |Work.Diff.EXT.covKRmExt g m (fun i => smoothExt x (v i)) (smoothExt x a)
        (smoothExt x b) (smoothExt x c) (smoothExt x d) x|
        ≤ Cev m * (1 + Real.sqrt (Work.Diff.EXT.curvNormK g x m))
          * (Finset.univ.prod (fun i : Fin m => Real.sqrt (g.inner x (v i) (v i)))
             * Real.sqrt (g.inner x a a) * Real.sqrt (g.inner x b b)
             * Real.sqrt (g.inner x c c) * Real.sqrt (g.inner x d d)) :=
    fun m => (hCev m).2
  -- the uniform constants
  have h0mem : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.succ_pos k)
  set Mev : ℝ := (Finset.range (k + 1)).sup' ⟨0, h0mem⟩ Cev with hMev
  set Msh : ℝ := (Finset.range (k + 1)).sup' ⟨0, h0mem⟩ Csh with hMsh
  have hMev0 : 0 ≤ Mev := by
    rw [hMev]
    exact le_trans (hCev0 0) (Finset.le_sup' Cev h0mem)
  refine ⟨(Module.finrank ℝ E : ℝ) * Mev * (1 + Real.sqrt (max Msh 0)), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hMev0)
      (by linarith [Real.sqrt_nonneg (max Msh 0)])
  · intro t ht m hm x v A B Cc
    -- the pointwise norms of the arguments
    set Z : ℝ := Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (v i) (v i)))
        * Real.sqrt ((G t).inner x A A) * Real.sqrt ((G t).inner x B B) with hZ
    have hZ0 : 0 ≤ Z := by
      rw [hZ]
      exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    -- the constants at this order
    have hmem : m ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
    have hCevm : Cev m ≤ Mev := by rw [hMev]; exact Finset.le_sup' Cev hmem
    have hCshm : Csh m ≤ Msh := by rw [hMsh]; exact Finset.le_sup' Csh hmem
    have hcurv : Work.Diff.EXT.curvNormK (G t) x m ≤ max Msh 0 :=
      le_trans (le_trans (hCsh m t ht x) hCshm) (le_max_left _ _)
    -- a smooth orthonormal frame near `x`
    have hVs : ∀ i : Fin (Module.finrank ℝ E),
        SmoothFieldT (I := I) (M := M) (smoothExt x (onFrame (G t) x i)) :=
      fun i => smoothExt_cmdiff x (onFrame (G t) x i)
    have hVON : IsONFrame (G t) x (fun i => smoothExt x (onFrame (G t) x i) x) := by
      have h : (fun i => smoothExt x (onFrame (G t) x i) x) = onFrame (G t) x := by
        funext i; exact smoothExt_apply x (onFrame (G t) x i)
      rw [h]; exact isONFrame_onFrame (G t) x
    obtain ⟨hWs0, hWON0, hWx0⟩ := covRic_onFrame_family (G t) x
      (fun i => smoothExt x (onFrame (G t) x i)) hVs hVON
    set W : Fin (Module.finrank ℝ E) → TF (I := I) (M := M) :=
      katoFrame (G t) x (fun i => smoothExt x (onFrame (G t) x i)) with hWdef
    have hWs : ∀ p, SmoothFieldT (I := I) (M := M) (W p) := fun p => by
      rw [hWdef]; exact hWs0 p
    have hWON : ∀ᶠ y in 𝓝 x, IsONFrame (G t) y (fun p => W p y) := by
      rw [hWdef]; exact hWON0
    have hWx : ∀ p : Fin (Module.finrank ℝ E), W p x = onFrame (G t) x p := by
      intro p; rw [hWx0 p, smoothExt_apply]
    -- an *open* set on which the frame is orthonormal
    obtain ⟨U₀, hU₀mem, hU₀sub⟩ := Filter.eventually_iff_exists_mem.mp hWON
    have hUo : IsOpen (interior U₀) := isOpen_interior
    have hUx : x ∈ interior U₀ := mem_interior_iff_mem_nhds.mpr hU₀mem
    have hUON : ∀ y ∈ interior U₀, IsONFrame (G t) y (fun p => W p y) :=
      fun y hy => hU₀sub y (interior_subset hy)
    -- the trace identity
    have hid := tower2_eq_sum_covKRmExt_aux (I := I) (M := M) hLC (G t) m hWs (interior U₀)
      hUo hUON x hUx (fun i => smoothExt x (v i)) (smoothExt x A) (smoothExt x B)
      (fun i => smoothExt_cmdiff x (v i)) (smoothExt_cmdiff x A) (smoothExt_cmdiff x B)
    have hframe : ∀ p : Fin (Module.finrank ℝ E),
        (G t).inner x (onFrame (G t) x p) (onFrame (G t) x p) = 1 := by
      intro p
      have h := isONFrame_onFrame (G t) x p p
      simpa using h
    -- the bound on one summand of the trace
    have hterm : ∀ p : Fin (Module.finrank ℝ E),
        |Work.Diff.EXT.covKRmExt (G t) m (fun i => smoothExt x (v i)) (W p)
          (smoothExt x A) (W p) (smoothExt x B) x|
          ≤ Cev m * (1 + Real.sqrt (Work.Diff.EXT.curvNormK (G t) x m)) * Z := by
      intro p
      have hWsmooth : SmoothFieldT (I := I) (M := M) (W p) := hWs p
      have hnorm : (W p) x = smoothExt x (onFrame (G t) x p) x := by
        rw [smoothExt_apply, hWx p]
      have e1 : Work.Diff.EXT.covKRmExt (G t) m (fun i => smoothExt x (v i)) (W p)
            (smoothExt x A) (W p) (smoothExt x B) x
          = Work.Diff.EXT.covKRmExt (G t) m (fun i => smoothExt x (v i))
              (smoothExt x (onFrame (G t) x p)) (smoothExt x A) (W p) (smoothExt x B) x :=
        replace_slot1 hLC (G t) m x (fun i => smoothExt_cmdiff x (v i))
          (smoothExt_cmdiff x A) hWsmooth (smoothExt_cmdiff x B) hWsmooth
          (smoothExt_cmdiff x (onFrame (G t) x p)) hnorm
      have e2 : Work.Diff.EXT.covKRmExt (G t) m (fun i => smoothExt x (v i))
              (smoothExt x (onFrame (G t) x p)) (smoothExt x A) (W p) (smoothExt x B) x
          = Work.Diff.EXT.covKRmExt (G t) m (fun i => smoothExt x (v i))
              (smoothExt x (onFrame (G t) x p)) (smoothExt x A)
              (smoothExt x (onFrame (G t) x p)) (smoothExt x B) x :=
        replace_slot3 hLC (G t) m x (fun i => smoothExt_cmdiff x (v i))
          (smoothExt_cmdiff x (onFrame (G t) x p)) (smoothExt_cmdiff x A)
          (smoothExt_cmdiff x B) hWsmooth (smoothExt_cmdiff x (onFrame (G t) x p)) hnorm
      rw [e1, e2]
      have hb := hCevb m (G t) x v (onFrame (G t) x p) A (onFrame (G t) x p) B
      have hp1 : Real.sqrt ((G t).inner x (onFrame (G t) x p) (onFrame (G t) x p)) = 1 := by
        rw [hframe p, Real.sqrt_one]
      have hprod : Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (v i) (v i)))
            * Real.sqrt ((G t).inner x (onFrame (G t) x p) (onFrame (G t) x p))
            * Real.sqrt ((G t).inner x A A)
            * Real.sqrt ((G t).inner x (onFrame (G t) x p) (onFrame (G t) x p))
            * Real.sqrt ((G t).inner x B B)
          = Finset.univ.prod (fun i : Fin m => Real.sqrt ((G t).inner x (v i) (v i)))
            * Real.sqrt ((G t).inner x A A) * Real.sqrt ((G t).inner x B B) := by
        rw [hp1]; ring
      rw [hprod] at hb
      exact hb
    -- assemble
    rw [Work.Diff.EXT.ConnCov.RicTr.valOp_htower_baseRic_eq]
    rw [hid]
    calc |∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.EXT.covKRmExt (G t) m (fun i => smoothExt x (v i)) (W p)
              (smoothExt x A) (W p) (smoothExt x B) x|
        ≤ ∑ p : Fin (Module.finrank ℝ E),
            |Work.Diff.EXT.covKRmExt (G t) m (fun i => smoothExt x (v i)) (W p)
              (smoothExt x A) (W p) (smoothExt x B) x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : Fin (Module.finrank ℝ E),
            Cev m * (1 + Real.sqrt (Work.Diff.EXT.curvNormK (G t) x m)) * Z :=
          Finset.sum_le_sum (fun p _ => hterm p)
      _ = (Module.finrank ℝ E : ℝ)
            * (Cev m * (1 + Real.sqrt (Work.Diff.EXT.curvNormK (G t) x m)) * Z) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (Module.finrank ℝ E : ℝ) * (Mev * (1 + Real.sqrt (max Msh 0)) * Z) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ hZ0
          exact mul_le_mul hCevm (by linarith [Real.sqrt_le_sqrt hcurv])
            (by linarith [Real.sqrt_nonneg (Work.Diff.EXT.curvNormK (G t) x m)]) hMev0
      _ = ((Module.finrank ℝ E : ℝ) * Mev * (1 + Real.sqrt (max Msh 0))) * Z := by ring

end Work.Diff.EXT.ConnCov.RicTr
