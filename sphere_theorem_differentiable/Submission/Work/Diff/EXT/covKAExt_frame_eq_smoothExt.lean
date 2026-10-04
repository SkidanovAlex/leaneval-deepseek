import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.EXT.ATens.Defs
import Submission.Work.Diff.EXT.ATens.Kit
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.kato_smooth
import Submission.ChartConnection
import Submission.Work.Diff.T.FrameExt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The frame fields of a chart evaluate the iterated covariant derivatives of the connection
difference like their pointwise smooth extensions

`Work.Diff.EXT.covKAExt G t k v A B C x` is defined through *fields*: the `k`-th covariant
derivative with respect to `∇^{G 0}` of the lowered connection difference `aOf G t`, evaluated on
the direction fields `v i` and the argument fields `A B C` at the point `x`.  Mathematically it is a
tensor, so its value at `x` only depends on the values of those fields at `x`.  This is the content
of `Work.Diff.EXT.covKAExt_tensorial` for *globally* smooth fields.

The coordinate frame `Work.Diff.GE.cFrame x₀ a` of the chart at `x₀`, however, is smooth only *on
that chart*, so the tensoriality statement does not apply to it directly.  The present file supplies
the missing local ingredient (`ka_locAt`: `cktA` is germ-determined for fields which are smooth on
an open neighbourhood of the point) and concludes that evaluating on the frame fields gives the same
number as evaluating on the `smoothExt` extensions of the corresponding tangent vectors.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- **The iteration `cktA` is germ-determined, for fields which are smooth on an open neighbourhood
of the point.**

This is the local counterpart of the locality clause `TensPropA G t k |>.2.2`, which requires the
fields to be globally smooth.  The recursion `cktA_succ` only uses the germ of the fields (through
`mvfderiv` and `∇^{G 0}`), so the induction goes through with `SmLoc` in place of `SmA`. -/
theorem ka_locAt (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ (k : ℕ) {x : M} {F F' : Fin (k + 3) → TfA (I := I) (M := M)},
      (∀ q, SmLoc (I := I) (M := M) (F q) x) →
      (∀ q, SmA (I := I) (M := M) (F' q)) →
      (∀ q, EvEqF (I := I) (M := M) x (F q) (F' q)) →
      EvEqR x (cktA G t k F) (cktA G t k F') := by
  intro k
  induction k with
  | zero =>
      intro x F F' hF hF' heq
      have h1 := dirFA_germEq (G t) (hF 1) (smLoc_of_smA (hF' 1) x) (heq 1) (heq 0)
      have h2 := dirFA_germEq (G 0) (hF 1) (smLoc_of_smA (hF' 1) x) (heq 1) (heq 0)
      filter_upwards [h1, h2, heq 2] with y hy1 hy2 hy3
      show aOf G t (F 0) (F 1) (F 2) y = aOf G t (F' 0) (F' 1) (F' 2) y
      change (G t).inner y (dirFA (G t) (F 1) (F 0) y - dirFA (G 0) (F 1) (F 0) y) (F 2 y)
        = (G t).inner y (dirFA (G t) (F' 1) (F' 0) y - dirFA (G 0) (F' 1) (F' 0) y) (F' 2 y)
      rw [hy1, hy2, hy3]
  | succ k ih =>
      intro x F F' hF hF' heq
      have hSL : ∀ᶠ y in 𝓝 x, ∀ i : Fin (k + 3), SmLoc (I := I) (M := M) (F i.succ) y := by
        rw [Filter.eventually_all]
        exact fun i => smLoc_eventually (hF i.succ)
      have hEQ : ∀ᶠ y in 𝓝 x, ∀ i : Fin (k + 3),
          EvEqF (I := I) (M := M) y (F i.succ) (F' i.succ) := by
        rw [Filter.eventually_all]
        exact fun i => eventuallyEq_nhds_eventuallyA (heq i.succ)
      have hE0 : ∀ᶠ y in 𝓝 x, EvEqF (I := I) (M := M) y (F 0) (F' 0) :=
        eventuallyEq_nhds_eventuallyA (heq 0)
      have hder : (fun y : M =>
            (mvfderiv I (cktA G t k (fun i : Fin (k + 3) => F i.succ)) y) (F 0 y))
          =ᶠ[𝓝 x] (fun y : M =>
            (mvfderiv I (cktA G t k (fun i : Fin (k + 3) => F' i.succ)) y) (F' 0 y)) := by
        filter_upwards [hSL, hEQ, hE0] with y hS hE hE0
        rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq
          (ih (x := y) hS (fun i => hF' i.succ) hE), hE0.eq_of_nhds]
      have hper : ∀ᶠ y in 𝓝 x, ∀ s : Fin (k + 3),
          cktA G t k (Function.update (fun i : Fin (k + 3) => F i.succ) s
              (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y
          = cktA G t k (Function.update (fun i : Fin (k + 3) => F' i.succ) s
              (dirFA (G 0) ((fun i : Fin (k + 3) => F' i.succ) s) (F' 0))) y := by
        rw [Filter.eventually_all]
        intro s
        have hSLu : ∀ᶠ y in 𝓝 x, ∀ i : Fin (k + 3),
            SmLoc (I := I) (M := M)
              ((Function.update (fun i : Fin (k + 3) => F i.succ) s
                (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) i) y := by
          rw [Filter.eventually_all]
          intro i
          by_cases hi : i = s
          · rw [hi, Function.update_self]
            exact smLoc_eventually (smLoc_dirFA hLC (G 0) (hF s.succ) (hF 0))
          · rw [Function.update_of_ne hi]
            exact smLoc_eventually (hF i.succ)
        have hEQu : ∀ᶠ y in 𝓝 x, ∀ i : Fin (k + 3),
            EvEqF (I := I) (M := M) y
              ((Function.update (fun i : Fin (k + 3) => F i.succ) s
                (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) i)
              ((Function.update (fun i : Fin (k + 3) => F' i.succ) s
                (dirFA (G 0) ((fun i : Fin (k + 3) => F' i.succ) s) (F' 0))) i) := by
          rw [Filter.eventually_all]
          intro i
          by_cases hi : i = s
          · rw [hi, Function.update_self, Function.update_self]
            exact eventuallyEq_nhds_eventuallyA
              (dirFA_germEq (G 0) (hF s.succ) (smLoc_of_smA (hF' s.succ) x)
                (heq s.succ) (heq 0))
          · rw [Function.update_of_ne hi, Function.update_of_ne hi]
            exact eventuallyEq_nhds_eventuallyA (heq i.succ)
        filter_upwards [hSLu, hEQu] with y hS hE
        exact (ih (x := y) hS
          (smA_update (fun i => hF' i.succ)
            (dirFA_smooth hLC (G 0) (hF' s.succ) (hF' 0))) hE).eq_of_nhds
      have hsum : (∑ s : Fin (k + 3), cktA G t k
            (Function.update (fun i : Fin (k + 3) => F i.succ) s
              (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0))))
          =ᶠ[𝓝 x] (∑ s : Fin (k + 3), cktA G t k
            (Function.update (fun i : Fin (k + 3) => F' i.succ) s
              (dirFA (G 0) ((fun i : Fin (k + 3) => F' i.succ) s) (F' 0)))) := by
        filter_upwards [hper] with y hy
        rw [Finset.sum_apply, Finset.sum_apply]
        exact Finset.sum_congr rfl (fun s _ => hy s)
      rw [cktA_succ, cktA_succ]
      exact hder.sub hsum

/-! ## The `aOf`-tower is a smooth `C^∞`-multilinear local operation (self-contained) -/

/-- Unfolding of the base case of the recursion. -/
lemma cktA_zero_eq (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (F : Fin 3 → TfA (I := I) (M := M)) :
    cktA G t 0 F = fun y : M => aOf G t (F 0) (F 1) (F 2) y := rfl

lemma aOf_smooth (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    {A B C : TfA (I := I) (M := M)} (hA : SmA (I := I) (M := M) A)
    (hB : SmA (I := I) (M := M) B) (hC : SmA (I := I) (M := M) C) :
    SmFunM (I := I) (M := M) (fun y : M => aOf G t A B C y) := by
  have hX : SmA (I := I) (M := M) (dirFA (G t) B A - dirFA (G 0) B A) :=
    (dirFA_smooth hLC (G t) hB hA).sub_section (dirFA_smooth hLC (G 0) hB hA)
  have hfun : (fun y : M => aOf G t A B C y)
      = fun y : M => (G t).inner y ((dirFA (G t) B A - dirFA (G 0) B A) y) (C y) := by
    funext y
    simp only [aOf, dirFA, Pi.sub_apply]
  rw [hfun]
  exact Work.Diff.GE.katoMetricPairingSmooth (G t) hX hC

lemma aOf_lin_slot0 (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    {X₁ X₂ B C : TfA (I := I) (M := M)} {f₁ f₂ : M → ℝ} :
    aOf G t (f₁ • X₁ + f₂ • X₂) B C = f₁ • aOf G t X₁ B C + f₂ • aOf G t X₂ B C := by
  funext y
  simp only [aOf, dirFA, Pi.add_apply, Pi.mul_apply, Pi.smul_apply', map_sub, map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  try ring_nf

lemma aOf_lin_slot1 (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    {A X₁ X₂ C : TfA (I := I) (M := M)} {f₁ f₂ : M → ℝ}
    (hX₁ : SmA (I := I) (M := M) X₁) (hX₂ : SmA (I := I) (M := M) X₂)
    (hf₁ : SmFunM (I := I) (M := M) f₁) (hf₂ : SmFunM (I := I) (M := M) f₂) :
    aOf G t A (f₁ • X₁ + f₂ • X₂) C = f₁ • aOf G t A X₁ C + f₂ • aOf G t A X₂ C := by
  funext y
  have e1 := congrFun (dirFA_leibniz (g := G t) (X₁ := X₁) (X₂ := X₂) (f₁ := f₁) (f₂ := f₂)
    (v0 := A) hX₁ hX₂ hf₁ hf₂) y
  have e2 := congrFun (dirFA_leibniz (g := G 0) (X₁ := X₁) (X₂ := X₂) (f₁ := f₁) (f₂ := f₂)
    (v0 := A) hX₁ hX₂ hf₁ hf₂) y
  simp only [aOf, dirFA, Pi.sub_apply] at e1 e2 ⊢
  rw [e1, e2]
  simp only [aOf, dirFA, Pi.add_apply, Pi.mul_apply, Pi.smul_apply', map_sub, map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  try ring_nf

lemma aOf_lin_slot2 (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    {A B X₁ X₂ : TfA (I := I) (M := M)} {f₁ f₂ : M → ℝ} :
    aOf G t A B (f₁ • X₁ + f₂ • X₂) = f₁ • aOf G t A B X₁ + f₂ • aOf G t A B X₂ := by
  funext y
  simp only [aOf, dirFA, Pi.add_apply, Pi.mul_apply, Pi.smul_apply', map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  try ring_nf

theorem ka_zero (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    TensPropA G t 0 := by
  intro F hF
  refine ⟨?_, ?_, ?_⟩
  · rw [cktA_zero_eq]
    exact aOf_smooth hLC G t (hF 0) (hF 1) (hF 2)
  · intro s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    fin_cases s
    · simp only [cktA_zero_eq, Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
        Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
      exact aOf_lin_slot0 G t
    · simp only [cktA_zero_eq, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 1),
        Function.update_self, Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1)]
      exact aOf_lin_slot1 G t hX₁ hX₂ hf₁ hf₂
    · simp only [cktA_zero_eq, Function.update_of_ne (by decide : (0 : Fin 3) ≠ 2),
        Function.update_of_ne (by decide : (1 : Fin 3) ≠ 2), Function.update_self]
      exact aOf_lin_slot2 G t
  · intro x F' hF' h
    exact ka_locAt hLC G t 0 (fun q => smLoc_of_smA (hF q) x) hF' h

/-- Linearity in the differentiation slot `0`. -/
theorem ka_lin_dir (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (k : ℕ) (hih : TensPropA G t k)
    {W : Fin (k + 3) → TfA (I := I) (M := M)} (hW : ∀ i, SmA (I := I) (M := M) (W i))
    {X₁ X₂ : TfA (I := I) (M := M)} (hX₁ : SmA (I := I) (M := M) X₁)
    (hX₂ : SmA (I := I) (M := M) X₂)
    {f₁ f₂ : M → ℝ} (hf₁ : SmFunM (I := I) (M := M) f₁)
    (hf₂ : SmFunM (I := I) (M := M) f₂) :
    cktA G t (k + 1) (Fin.cons (f₁ • X₁ + f₂ • X₂) W)
      = f₁ • cktA G t (k + 1) (Fin.cons X₁ W) + f₂ • cktA G t (k + 1) (Fin.cons X₂ W) := by
  have hconsF : ∀ (Y : TfA (I := I) (M := M)),
      (fun i : Fin (k + 3) =>
        (Fin.cons Y W : Fin (k + 4) → TfA (I := I) (M := M)) i.succ) = W := by
    intro Y; funext i
    exact Fin.cons_succ (α := fun _ : Fin (k + 4) => TfA (I := I) (M := M)) Y W i
  have hconsP : ∀ (Y : TfA (I := I) (M := M)) (i : Fin (k + 3)),
      (Fin.cons Y W : Fin (k + 4) → TfA (I := I) (M := M)) i.succ = W i :=
    fun Y i => Fin.cons_succ (α := fun _ : Fin (k + 4) => TfA (I := I) (M := M)) Y W i
  have hzero : ∀ (Y : TfA (I := I) (M := M)),
      (Fin.cons Y W : Fin (k + 4) → TfA (I := I) (M := M)) 0 = Y :=
    fun Y => Fin.cons_zero (α := fun _ : Fin (k + 4) => TfA (I := I) (M := M)) Y W
  rw [cktA_succ, cktA_succ, cktA_succ]
  simp only [hconsF, hconsP, hzero]
  funext y
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply', Finset.sum_apply]
  have ht1 : (mvfderiv I (cktA G t k W) y) (f₁ y • X₁ y + f₂ y • X₂ y)
      = f₁ y • ((mvfderiv I (cktA G t k W) y) (X₁ y))
        + f₂ y • ((mvfderiv I (cktA G t k W) y) (X₂ y)) := by
    simp only [map_add, map_smul]
  have hs : (∑ q : Fin (k + 3), cktA G t k
        (Function.update W q (dirFA (G 0) (W q) (f₁ • X₁ + f₂ • X₂))) y)
      = f₁ y • (∑ q : Fin (k + 3), cktA G t k
            (Function.update W q (dirFA (G 0) (W q) X₁)) y)
        + f₂ y • (∑ q : Fin (k + 3), cktA G t k
            (Function.update W q (dirFA (G 0) (W q) X₂)) y) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [dirFA_add_dir]
    have hq := (hih W hW).2.1 q (dirFA (G 0) (W q) X₁) (dirFA (G 0) (W q) X₂) f₁ f₂
      (dirFA_smooth hLC (G 0) (hW q) hX₁) (dirFA_smooth hLC (G 0) (hW q) hX₂) hf₁ hf₂
    rw [hq]
    simp only [Pi.add_apply, Pi.smul_apply']
  rw [ht1, hs]
  simp only [smul_sub, smul_eq_mul]
  ring

/-- Linearity in a slot of the tail. -/
theorem ka_lin_tail (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (k : ℕ) (hih : TensPropA G t k)
    {Fs : Fin (k + 3) → TfA (I := I) (M := M)} (hFs : ∀ i, SmA (I := I) (M := M) (Fs i))
    {v0 X₁ X₂ : TfA (I := I) (M := M)}
    (hv0 : SmA (I := I) (M := M) v0) (hX₁ : SmA (I := I) (M := M) X₁)
    (hX₂ : SmA (I := I) (M := M) X₂)
    {f₁ f₂ : M → ℝ} (hf₁ : SmFunM (I := I) (M := M) f₁)
    (hf₂ : SmFunM (I := I) (M := M) f₂) (j : Fin (k + 3)) :
    cktA G t (k + 1) (Fin.cons v0 (Function.update Fs j (f₁ • X₁ + f₂ • X₂)))
      = f₁ • cktA G t (k + 1) (Fin.cons v0 (Function.update Fs j X₁))
        + f₂ • cktA G t (k + 1) (Fin.cons v0 (Function.update Fs j X₂)) := by
  have hconsF : ∀ (W : Fin (k + 3) → TfA (I := I) (M := M)),
      (fun i : Fin (k + 3) =>
        (Fin.cons v0 W : Fin (k + 4) → TfA (I := I) (M := M)) i.succ) = W := by
    intro W; funext i
    exact Fin.cons_succ (α := fun _ : Fin (k + 4) => TfA (I := I) (M := M)) v0 W i
  have hconsP : ∀ (W : Fin (k + 3) → TfA (I := I) (M := M)) (i : Fin (k + 3)),
      (Fin.cons v0 W : Fin (k + 4) → TfA (I := I) (M := M)) i.succ = W i :=
    fun W i => Fin.cons_succ (α := fun _ : Fin (k + 4) => TfA (I := I) (M := M)) v0 W i
  have hzero : ∀ (W : Fin (k + 3) → TfA (I := I) (M := M)),
      (Fin.cons v0 W : Fin (k + 4) → TfA (I := I) (M := M)) 0 = v0 :=
    fun W => Fin.cons_zero (α := fun _ : Fin (k + 4) => TfA (I := I) (M := M)) v0 W
  rw [cktA_succ, cktA_succ, cktA_succ]
  simp only [hconsF, hconsP, hzero]
  have hAW : cktA G t k (Function.update Fs j (f₁ • X₁ + f₂ • X₂))
      = f₁ • cktA G t k (Function.update Fs j X₁) + f₂ • cktA G t k (Function.update Fs j X₂) :=
    (hih Fs hFs).2.1 j X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
  have hadd : ∀ {A B : TfA (I := I) (M := M)},
      SmA (I := I) (M := M) A → SmA (I := I) (M := M) B →
      cktA G t k (Function.update Fs j (A + B))
        = cktA G t k (Function.update Fs j A) + cktA G t k (Function.update Fs j B) := by
    intro A B hA hB
    have h := (hih Fs hFs).2.1 j A B (fun _ : M => (1 : ℝ)) (fun _ : M => (1 : ℝ)) hA hB
      (contMDiff_const (c := (1 : ℝ))) (contMDiff_const (c := (1 : ℝ)))
    have hAB : (fun _ : M => (1 : ℝ)) • A + (fun _ : M => (1 : ℝ)) • B = A + B := by
      funext z; simp
    have hA' : (fun _ : M => (1 : ℝ)) • cktA G t k (Function.update Fs j A)
        = cktA G t k (Function.update Fs j A) := by funext z; simp
    have hB' : (fun _ : M => (1 : ℝ)) • cktA G t k (Function.update Fs j B)
        = cktA G t k (Function.update Fs j B) := by funext z; simp
    rw [hAB, hA', hB'] at h
    exact h
  have hS1 : SmFunM (I := I) (M := M) (cktA G t k (Function.update Fs j X₁)) :=
    (hih _ (smA_update hFs hX₁)).1
  have hS2 : SmFunM (I := I) (M := M) (cktA G t k (Function.update Fs j X₂)) :=
    (hih _ (smA_update hFs hX₂)).1
  funext y
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply', Finset.sum_apply]
  have hT : (mvfderiv I (cktA G t k (Function.update Fs j (f₁ • X₁ + f₂ • X₂))) y) (v0 y)
      = f₁ y • ((mvfderiv I (cktA G t k (Function.update Fs j X₁)) y) (v0 y))
        + ((mvfderiv I f₁ y) (v0 y)) • (cktA G t k (Function.update Fs j X₁) y)
        + f₂ y • ((mvfderiv I (cktA G t k (Function.update Fs j X₂)) y) (v0 y))
        + ((mvfderiv I f₂ y) (v0 y)) • (cktA G t k (Function.update Fs j X₂) y) := by
    rw [hAW]
    rw [mvfderiv_two_smulA f₁ f₂ (cktA G t k (Function.update Fs j X₁))
      (cktA G t k (Function.update Fs j X₂)) y (v0 y)
      (hf₁.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))
      (hS1.mdifferentiableAt (by simp)) (hS2.mdifferentiableAt (by simp))]
    simp only [smul_eq_mul]
  have hstep : ∀ q : Fin (k + 3), q ≠ j →
      cktA G t k (Function.update (Function.update Fs j (f₁ • X₁ + f₂ • X₂)) q
        (dirFA (G 0) ((Function.update Fs j (f₁ • X₁ + f₂ • X₂)) q) v0))
      = f₁ • cktA G t k (Function.update (Function.update Fs j X₁) q
            (dirFA (G 0) ((Function.update Fs j X₁) q) v0))
        + f₂ • cktA G t k (Function.update (Function.update Fs j X₂) q
            (dirFA (G 0) ((Function.update Fs j X₂) q) v0)) := by
    intro q hqj
    have h1 : Function.update (Function.update Fs j (f₁ • X₁ + f₂ • X₂)) q
        (dirFA (G 0) ((Function.update Fs j (f₁ • X₁ + f₂ • X₂)) q) v0)
        = Function.update (Function.update Fs q (dirFA (G 0) (Fs q) v0)) j
            (f₁ • X₁ + f₂ • X₂) := by
      rw [Function.update_of_ne hqj (f₁ • X₁ + f₂ • X₂) Fs]
      exact (Function.update_comm hqj (dirFA (G 0) (Fs q) v0) (f₁ • X₁ + f₂ • X₂) Fs).symm
    have h2 : Function.update (Function.update Fs q (dirFA (G 0) (Fs q) v0)) j X₁
        = Function.update (Function.update Fs j X₁) q
            (dirFA (G 0) ((Function.update Fs j X₁) q) v0) := by
      rw [Function.update_of_ne hqj X₁ Fs]
      exact Function.update_comm hqj (dirFA (G 0) (Fs q) v0) X₁ Fs
    have h3 : Function.update (Function.update Fs q (dirFA (G 0) (Fs q) v0)) j X₂
        = Function.update (Function.update Fs j X₂) q
            (dirFA (G 0) ((Function.update Fs j X₂) q) v0) := by
      rw [Function.update_of_ne hqj X₂ Fs]
      exact Function.update_comm hqj (dirFA (G 0) (Fs q) v0) X₂ Fs
    rw [h1]
    have hlin := (hih (Function.update Fs q (dirFA (G 0) (Fs q) v0))
      (smA_update hFs (dirFA_smooth hLC (G 0) (hFs q) hv0))).2.1 j X₁ X₂ f₁ f₂
      hX₁ hX₂ hf₁ hf₂
    rw [hlin, h2, h3]
  have hjterm : cktA G t k (Function.update (Function.update Fs j (f₁ • X₁ + f₂ • X₂)) j
        (dirFA (G 0) ((Function.update Fs j (f₁ • X₁ + f₂ • X₂)) j) v0)) y
      = f₁ y • (cktA G t k (Function.update (Function.update Fs j X₁) j
            (dirFA (G 0) ((Function.update Fs j X₁) j) v0)) y)
        + f₂ y • (cktA G t k (Function.update (Function.update Fs j X₂) j
            (dirFA (G 0) ((Function.update Fs j X₂) j) v0)) y)
        + ((mvfderiv I f₁ y) (v0 y)) • (cktA G t k (Function.update Fs j X₁) y)
        + ((mvfderiv I f₂ y) (v0 y)) • (cktA G t k (Function.update Fs j X₂) y) := by
    have hidem : Function.update (Function.update Fs j (f₁ • X₁ + f₂ • X₂)) j
        (dirFA (G 0) (Function.update Fs j (f₁ • X₁ + f₂ • X₂) j) v0)
        = Function.update Fs j (dirFA (G 0) (f₁ • X₁ + f₂ • X₂) v0) := by
      rw [Function.update_self]
      exact Function.update_idem (α := Fin (k + 3)) (β := fun _ : Fin (k + 3) => TfA (I := I) (M := M))
        (a := j) (f₁ • X₁ + f₂ • X₂) (dirFA (G 0) (f₁ • X₁ + f₂ • X₂) v0) Fs
    rw [hidem, dirFA_leibniz (g := G 0) (X₁ := X₁) (X₂ := X₂) (f₁ := f₁) (f₂ := f₂)
      (v0 := v0) hX₁ hX₂ hf₁ hf₂]
    have hE1 : SmFunM (I := I) (M := M) (fun z : M => (mvfderiv I f₁ z) (v0 z)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hf₁ hv0
    have hE2 : SmFunM (I := I) (M := M) (fun z : M => (mvfderiv I f₂ z) (v0 z)) :=
      Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hf₂ hv0
    rw [add_assoc (f₁ • dirFA (G 0) X₁ v0 + (fun z : M => (mvfderiv I f₁ z) (v0 z)) • X₁)
        (f₂ • dirFA (G 0) X₂ v0) ((fun z : M => (mvfderiv I f₂ z) (v0 z)) • X₂)]
    rw [hadd (SmA_add (SmA_smul hf₁ (dirFA_smooth hLC (G 0) hX₁ hv0)) (SmA_smul hE1 hX₁))
        (SmA_add (SmA_smul hf₂ (dirFA_smooth hLC (G 0) hX₂ hv0)) (SmA_smul hE2 hX₂))]
    rw [(hih Fs hFs).2.1 j (dirFA (G 0) X₁ v0) X₁ f₁ (fun z : M => (mvfderiv I f₁ z) (v0 z))
        (dirFA_smooth hLC (G 0) hX₁ hv0) hX₁ hf₁ hE1]
    rw [(hih Fs hFs).2.1 j (dirFA (G 0) X₂ v0) X₂ f₂ (fun z : M => (mvfderiv I f₂ z) (v0 z))
        (dirFA_smooth hLC (G 0) hX₂ hv0) hX₂ hf₂ hE2]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply', Function.update_idem,
      Function.update_self, smul_eq_mul]
    ring
  have hne : (∑ q ∈ Finset.univ.erase j, cktA G t k
        (Function.update (Function.update Fs j (f₁ • X₁ + f₂ • X₂)) q
          (dirFA (G 0) ((Function.update Fs j (f₁ • X₁ + f₂ • X₂)) q) v0)) y)
      = f₁ y * (∑ q ∈ Finset.univ.erase j, cktA G t k
            (Function.update (Function.update Fs j X₁) q
              (dirFA (G 0) ((Function.update Fs j X₁) q) v0)) y)
        + f₂ y * (∑ q ∈ Finset.univ.erase j, cktA G t k
            (Function.update (Function.update Fs j X₂) q
              (dirFA (G 0) ((Function.update Fs j X₂) q) v0)) y) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    have hqj : q ≠ j := (Finset.mem_erase.mp hq).1
    rw [hstep q hqj]
    simp only [Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  have hS : (∑ q : Fin (k + 3), cktA G t k
        (Function.update (Function.update Fs j (f₁ • X₁ + f₂ • X₂)) q
          (dirFA (G 0) ((Function.update Fs j (f₁ • X₁ + f₂ • X₂)) q) v0)) y)
      = f₁ y • (∑ q : Fin (k + 3), cktA G t k
            (Function.update (Function.update Fs j X₁) q
              (dirFA (G 0) ((Function.update Fs j X₁) q) v0)) y)
        + f₂ y • (∑ q : Fin (k + 3), cktA G t k
            (Function.update (Function.update Fs j X₂) q
              (dirFA (G 0) ((Function.update Fs j X₂) q) v0)) y)
        + ((mvfderiv I f₁ y) (v0 y)) • (cktA G t k (Function.update Fs j X₁) y)
        + ((mvfderiv I f₂ y) (v0 y)) • (cktA G t k (Function.update Fs j X₂) y) := by
    rw [← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j),
        ← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j),
        ← Finset.add_sum_erase Finset.univ _ (a := j) (Finset.mem_univ j)]
    rw [hjterm, hne]
    simp only [smul_add, smul_eq_mul]
    ring
  rw [hT, hS]
  simp only [smul_sub, smul_add, smul_eq_mul]
  ring

/-- Smoothness of the next level of the iteration. -/
theorem ka_smooth (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (k : ℕ) (hih : TensPropA G t k)
    {F : Fin (k + 4) → TfA (I := I) (M := M)}
    (hF : ∀ s, SmA (I := I) (M := M) (F s)) :
    SmFunM (I := I) (M := M) (fun y : M => cktA G t (k + 1) F y) := by
  have hG : ∀ i : Fin (k + 3),
      SmA (I := I) (M := M) ((fun i : Fin (k + 3) => F i.succ) i) := fun i => hF i.succ
  have hΦ : CMDiff ∞ (fun y : M => cktA G t k (fun i : Fin (k + 3) => F i.succ) y) :=
    (hih (fun i : Fin (k + 3) => F i.succ) hG).1
  have h1 : CMDiff ∞ (fun y : M =>
      (mvfderiv I (fun y : M => cktA G t k (fun i : Fin (k + 3) => F i.succ) y) y) (F 0 y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hΦ (hF 0)
  have h2 : ∀ s : Fin (k + 3), CMDiff ∞ (fun y : M => cktA G t k
      (Function.update (fun i : Fin (k + 3) => F i.succ) s
        (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y) := by
    intro s
    exact (hih _ (smA_update hG (dirFA_smooth hLC (G 0) (hG s) (hF 0)))).1
  have h3' : CMDiff ∞ (fun y : M => ∑ s : Fin (k + 3), cktA G t k
      (Function.update (fun i : Fin (k + 3) => F i.succ) s
        (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y) :=
    ContMDiff.sum (t := Finset.univ) (fun s _ => h2 s)
  have h3 : CMDiff ∞ (∑ s : Fin (k + 3), cktA G t k
      (Function.update (fun i : Fin (k + 3) => F i.succ) s
        (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0)))) := by
    have hfun : (∑ s : Fin (k + 3), cktA G t k
        (Function.update (fun i : Fin (k + 3) => F i.succ) s
          (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0))))
        = fun y : M => ∑ s : Fin (k + 3), cktA G t k
          (Function.update (fun i : Fin (k + 3) => F i.succ) s
            (dirFA (G 0) ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y := by
      funext y; rw [Finset.sum_apply]
    rw [hfun]; exact h3'
  rw [cktA_succ]
  exact h1.sub h3

/-- The induction step of `TensPropA`. -/
theorem ka_succ (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ)
    (k : ℕ) (hih : TensPropA G t k) : TensPropA G t (k + 1) := by
  intro F hF
  refine ⟨ka_smooth hLC G t k hih hF, ?_, ?_⟩
  · intro s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    refine Fin.cases ?_ ?_ s
    · rw [update_zero_eq_consA, update_zero_eq_consA, update_zero_eq_consA]
      exact ka_lin_dir hLC G t k hih (fun i => hF i.succ) hX₁ hX₂ hf₁ hf₂
    · intro j
      rw [update_succ_eq_consA, update_succ_eq_consA, update_succ_eq_consA]
      exact ka_lin_tail hLC G t k hih (fun i => hF i.succ) (hF 0) hX₁ hX₂ hf₁ hf₂ j
  · intro x F' hF' h
    exact ka_locAt hLC G t (k + 1) (fun q => smLoc_of_smA (hF q) x) hF' h

theorem ka_all (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) :
    ∀ k, TensPropA G t k := by
  intro k
  induction k with
  | zero => exact ka_zero hLC G t
  | succ k ih => exact ka_succ hLC G t k ih

/-- Single-slot value dependence. -/
theorem ka_val_dep (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (k : ℕ) (x : M) {FS : Fin (k + 3) → TfA (I := I) (M := M)}
    (hFS : ∀ s, SmA (I := I) (M := M) (FS s)) (s : Fin (k + 3))
    {X X' : TfA (I := I) (M := M)} (hX : SmA (I := I) (M := M) X)
    (hX' : SmA (I := I) (M := M) X') (h : X x = X' x) :
    cktA G t k (Function.update FS s X) x = cktA G t k (Function.update FS s X') x := by
  have h1 : ∀ (X₁ X₂ : TfA (I := I) (M := M)) (f₁ f₂ : M → ℝ),
      SmA (I := I) (M := M) X₁ → SmA (I := I) (M := M) X₂ →
      SmFunM (I := I) (M := M) f₁ → SmFunM (I := I) (M := M) f₂ →
      cktA G t k (Function.update FS s (f₁ • X₁ + f₂ • X₂)) x
        = f₁ x * cktA G t k (Function.update FS s X₁) x
          + f₂ x * cktA G t k (Function.update FS s X₂) x := by
    intro X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂
    have h2 := congrFun ((ka_all hLC G t k FS hFS).2.1 s X₁ X₂ f₁ f₂ hX₁ hX₂ hf₁ hf₂) x
    simpa only [Pi.add_apply, Pi.mul_apply, smul_eq_mul] using h2
  have h3 : ∀ (X Y : TfA (I := I) (M := M)), SmA (I := I) (M := M) X →
      SmA (I := I) (M := M) Y → X =ᶠ[𝓝 x] Y →
      cktA G t k (Function.update FS s X) x = cktA G t k (Function.update FS s Y) x := by
    intro X Y hX hY heq
    have h4 : ∀ q : Fin (k + 3), EvEqF (I := I) (M := M) x
        (Function.update FS s X q) (Function.update FS s Y q) := by
      intro q
      rcases eq_or_ne q s with hq | hq
      · rw [hq, Function.update_self, Function.update_self]
        exact heq
      · rw [Function.update_of_ne hq, Function.update_of_ne hq]
        try rfl
    exact (((ka_all hLC G t k (Function.update FS s X) (smA_update hFS hX)).2.2 x
      (Function.update FS s Y) (smA_update hFS hY) h4)).eq_of_nhds
  exact Work.Diff.GE.field_value_dep_of_linear x h1 h3 hX hX' h

/-- Value dependence of the iteration in all slots at once. -/
theorem ka_val_dep_all (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M)
    (t : ℝ) (k : ℕ) (x : M) {F F' : Fin (k + 3) → TfA (I := I) (M := M)}
    (hF : ∀ s, SmA (I := I) (M := M) (F s))
    (hF' : ∀ s, SmA (I := I) (M := M) (F' s))
    (h : ∀ s, F s x = F' s x) :
    cktA G t k F x = cktA G t k F' x := by
  set H : Finset (Fin (k + 3)) → (Fin (k + 3) → TfA (I := I) (M := M)) :=
    fun u s => if s ∈ u then F' s else F s with hHdef
  have hH : ∀ u s, SmA (I := I) (M := M) (H u s) := by
    intro u s
    rw [hHdef]
    by_cases hs : s ∈ u
    · simp only [if_pos hs]; exact hF' s
    · simp only [if_neg hs]; exact hF s
  have hHself : ∀ u s, s ∉ u → H u s = F s := by
    intro u s hs
    rw [hHdef]
    simp only [if_neg hs]
  have hstep : ∀ (u : Finset (Fin (k + 3))) (s : Fin (k + 3)), s ∉ u →
      cktA G t k (H u) x = cktA G t k (H (insert s u)) x := by
    intro u s hs
    have hupd : H (insert s u) = Function.update (H u) s (F' s) := by
      funext v
      rw [hHdef, Function.update_apply]
      by_cases hv : v = s
      · subst hv; simp
      · rw [if_neg hv]
        simp only [Finset.mem_insert, hv, false_or]
    rw [hupd]
    have hsd := ka_val_dep hLC G t k x (hH u) s (hF s) (hF' s) (h s)
    have hsame : Function.update (H u) s (F s) = H u := by
      funext v
      by_cases hv : v = s
      · rw [hv, Function.update_self, hHself u s hs]
      · rw [Function.update_of_ne hv]
    rwa [hsame] at hsd
  have hchain : cktA G t k (H ∅) x = cktA G t k (H Finset.univ) x :=
    Finset.induction_on (motive := fun u => cktA G t k (H ∅) x = cktA G t k (H u) x)
      (Finset.univ : Finset (Fin (k + 3))) rfl
      (fun a u ha ih => by rw [ih, hstep u a ha])
  have h0 : H ∅ = F := by funext s; simp [hHdef]
  have h1 : H Finset.univ = F' := by funext s; simp [hHdef]
  rwa [h0, h1] at hchain

theorem covKAExt_frame_eq_smoothExt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (v : Fin k → Fin (Module.finrank ℝ E)) (i j l : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.covKAExt G t k (fun s : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (v s))
        (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
        (Work.Diff.GE.cFrame (I := I) x₀ l) (Work.Diff.EXT.pt (I := I) x₀ y)
      = Work.Diff.EXT.covKAExt G t k
          (fun s : Fin k => Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.GE.cFrame (I := I) x₀ (v s) (Work.Diff.EXT.pt (I := I) x₀ y)))
          (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.GE.cFrame (I := I) x₀ i (Work.Diff.EXT.pt (I := I) x₀ y)))
          (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.GE.cFrame (I := I) x₀ j (Work.Diff.EXT.pt (I := I) x₀ y)))
          (Submission.Diff.smoothExt (Work.Diff.EXT.pt (I := I) x₀ y)
            (Work.Diff.GE.cFrame (I := I) x₀ l (Work.Diff.EXT.pt (I := I) x₀ y)))
          (Work.Diff.EXT.pt (I := I) x₀ y) := by
  set x : M := Work.Diff.EXT.pt (I := I) x₀ y with hx
  have hxval : x = (extChartAt I x₀).symm y := hx
  have hpsrc : x ∈ (chartAt H x₀).source := by
    have h1 : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source := by
      have hmem : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).symm '' (extChartAt I x₀).target :=
        Set.mem_image_of_mem _ hy
      rwa [PartialEquiv.symm_image_target_eq_source] at hmem
    have h2 : (extChartAt I x₀).source = (chartAt H x₀).source := extChartAt_source I x₀
    rw [hxval, ← h2]
    exact h1
  have hY : ∀ a : Fin (Module.finrank ℝ E),
      ∃ Z : TfA (I := I) (M := M), SmA (I := I) (M := M) Z ∧
        EvEqF (I := I) (M := M) x Z (Work.Diff.GE.cFrame (I := I) x₀ a) := by
    intro a
    obtain ⟨Z, hZsm, hZeq⟩ :=
      Work.Diff.T.exists_global_eventuallyEq_symmL (I := I) x₀
        (Work.Diff.GE.cBasis (E := E) a) hpsrc
    exact ⟨Z, hZsm, hZeq⟩
  choose Y hYsm hYeq using hY
  have hSL1 : ∀ q, SmLoc (I := I) (M := M)
      ((mkT3 (fun s : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (v s))
        (trip3 (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
          (Work.Diff.GE.cFrame (I := I) x₀ l))) q) x :=
    smLoc_mkT3 (fun s => smLoc_cFrame (I := I) x₀ hpsrc (v s))
      (fun p => by
        fin_cases p
        · exact smLoc_cFrame (I := I) x₀ hpsrc i
        · exact smLoc_cFrame (I := I) x₀ hpsrc j
        · exact smLoc_cFrame (I := I) x₀ hpsrc l)
  have hSM2 : ∀ q, SmA (I := I) (M := M)
      ((mkT3 (fun s : Fin k => Y (v s)) (trip3 (Y i) (Y j) (Y l))) q) :=
    smA_mkT3 (fun s => hYsm (v s))
      (fun p => by
        fin_cases p
        · exact hYsm i
        · exact hYsm j
        · exact hYsm l)
  have hSM3 : ∀ q, SmA (I := I) (M := M)
      ((mkT3 (fun s : Fin k =>
          Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ (v s) x))
        (trip3 (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ i x))
          (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ j x))
          (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ l x)))) q) :=
    smA_mkT3 (fun s => Work.Diff.GE.smoothExt_cmdiff x _)
      (fun p => by
        fin_cases p
        · exact Work.Diff.GE.smoothExt_cmdiff x _
        · exact Work.Diff.GE.smoothExt_cmdiff x _
        · exact Work.Diff.GE.smoothExt_cmdiff x _)
  have hEQ12 : ∀ q, EvEqF (I := I) (M := M) x
      ((mkT3 (fun s : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (v s))
        (trip3 (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
          (Work.Diff.GE.cFrame (I := I) x₀ l))) q)
      ((mkT3 (fun s : Fin k => Y (v s)) (trip3 (Y i) (Y j) (Y l))) q) :=
    evEqF_mkT3 (fun s => (hYeq (v s)).symm)
      (fun p => by
        fin_cases p
        · exact (hYeq i).symm
        · exact (hYeq j).symm
        · exact (hYeq l).symm)
  have hVAL23 : ∀ q,
      ((mkT3 (fun s : Fin k => Y (v s)) (trip3 (Y i) (Y j) (Y l))) q) x
      = ((mkT3 (fun s : Fin k =>
            Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ (v s) x))
          (trip3 (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ i x))
            (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ j x))
            (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ l x)))) q) x :=
    val_mkT3 (fun s => (hYeq (v s)).eq_of_nhds.trans (Work.Diff.GE.smoothExt_apply x _).symm)
      (fun p => by
        fin_cases p
        · exact (hYeq i).eq_of_nhds.trans (Work.Diff.GE.smoothExt_apply x _).symm
        · exact (hYeq j).eq_of_nhds.trans (Work.Diff.GE.smoothExt_apply x _).symm
        · exact (hYeq l).eq_of_nhds.trans (Work.Diff.GE.smoothExt_apply x _).symm)
  have hbr1 : Work.Diff.EXT.covKAExt G t k (fun s : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (v s))
      (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
      (Work.Diff.GE.cFrame (I := I) x₀ l) x
      = cktA G t k (mkT3 (fun s : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (v s))
          (trip3 (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
            (Work.Diff.GE.cFrame (I := I) x₀ l))) x :=
    (Work.Diff.EXT.cktA_mkT3_eq G t k (fun s : Fin k => Work.Diff.GE.cFrame (I := I) x₀ (v s))
      (trip3 (Work.Diff.GE.cFrame (I := I) x₀ i) (Work.Diff.GE.cFrame (I := I) x₀ j)
        (Work.Diff.GE.cFrame (I := I) x₀ l)) x).symm
  have hbr2 : Work.Diff.EXT.covKAExt G t k
      (fun s : Fin k => Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ (v s) x))
      (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ i x))
      (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ j x))
      (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ l x)) x
      = cktA G t k (mkT3 (fun s : Fin k =>
            Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ (v s) x))
          (trip3 (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ i x))
            (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ j x))
            (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ l x)))) x :=
    (Work.Diff.EXT.cktA_mkT3_eq G t k
      (fun s : Fin k => Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ (v s) x))
      (trip3 (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ i x))
        (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ j x))
        (Submission.Diff.smoothExt x (Work.Diff.GE.cFrame (I := I) x₀ l x))) x).symm
  rw [hbr1, hbr2]
  exact ((ka_locAt (I := I) (M := M) hLC G t k (x := x) hSL1 hSM2 hEQ12).eq_of_nhds).trans
    (ka_val_dep_all hLC G t k x hSM2 hSM3 hVAL23)

end Work.Diff.EXT
