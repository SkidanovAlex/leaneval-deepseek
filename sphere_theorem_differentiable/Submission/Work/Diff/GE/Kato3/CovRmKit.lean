import Mathlib
import Submission.Work.Diff.GE.dRmPhi
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.Frame
import Submission.Diff.Evol
import Submission.Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Kato3.CovRmKit`: first-order tensor calculus of `∇Rm`

Toolkit for the field form of `∇³Rm` (`Work.Diff.GE.cov3RmExt`).  The frozen `covRm = ∇Rm` is
defined with `Classical.epsilon`-chosen extensions `smoothExt x ·`; here we collect the facts that
make `∇Rm` an honest `(0,5)`-tensor:

* `dRmPhi_skew_last` : `dRmPhi` (the section-level form of `∇Rm`, `= covRm` on the chosen
  extensions) is antisymmetric in its last two field arguments.  This is the missing piece for the
  *fourth* field slot of `dRmPhi`: all its consequences (linearity, binding) are immediate.
* `dRmPhi_linear_slotD`, `dRmPhi_bind_slotD` : the fourth field slot is linear, resp. depends only
  on the value at the base point.
* `covRm_field_form` : `covRm` evaluated on arbitrary smooth fields, which is the form in which one
  computes with it.
* `covRm_linear_fith` : `covRm` is linear in its fifth argument (via antisymmetry in the last two
  arguments and the known linearity in the fourth).
* `covRm_field_smooth` : `y ↦ covRm g y (V y) (A y) (B y) (C y) (D y)` is `C^∞` for smooth fields.
* the toolbox `mvfderiv_sum`, `lcOf_sum`, `lcOf_congr_eventuallyEq`.

Everything rests on the existing modules `dRmPhi`, `dRmPhi_slotA`, `covRm_linear_thd`,
`covRm_linear_fth`, `Frame` (`rmP_skew`) and `mvfderiv_apply_contMDiff`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.Kato3

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Toolbox: `mvfderiv` and the connection on finite sums -/

/-- `mvfderiv` of a finite sum of smooth functions. -/
theorem mvfderiv_sum {ι : Type*} (t : Finset ι) (F : ι → M → ℝ)
    (hF : ∀ i, CMDiff ∞ (F i)) (x : M) (v : TangentSpace I x) :
    mvfderiv I (fun y : M => ∑ i ∈ t, F i y) x v = ∑ i ∈ t, mvfderiv I (F i) x v := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, mvfderiv_const, zero_apply]
  | insert i t hi ih =>
      have ht : CMDiff ∞ (fun y : M => ∑ j ∈ t, F j y) :=
        ContMDiff.sum (fun j _ => hF j)
      have h1 : mvfderiv I (fun y : M => F i y + ∑ j ∈ t, F j y) x v
          = mvfderiv I (F i) x v + mvfderiv I (fun y : M => ∑ j ∈ t, F j y) x v := by
        rw [show (fun y : M => F i y + ∑ j ∈ t, F j y)
            = F i + (fun y : M => ∑ j ∈ t, F j y) from rfl]
        have h := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
          (mvfderiv_add (x := x) (g := F i) (g' := fun y : M => ∑ j ∈ t, F j y)
            ((hF i).mdifferentiableAt (by simp)) (ht.mdifferentiableAt (by simp)))
        simpa only [add_apply] using h
      rw [Finset.sum_insert hi]
      simp only [Finset.sum_insert hi, h1, ih]

/-- The Levi-Civita connection on a finite sum of scaled smooth fields:
`∇ (∑ᵢ fᵢ • Yᵢ) = ∑ᵢ (fᵢ • ∇ Yᵢ + (dfᵢ) ⊗ Yᵢ)`. -/
theorem lcOf_sum (g : SMet I M) {ι : Type*} (t : Finset ι) (f : ι → M → ℝ)
    (Y : ι → Π y : M, TangentSpace I y)
    (hf : ∀ i, CMDiff ∞ (f i)) (hY : ∀ i, CMDiff ∞ (T% (Y i))) (x : M) :
    lcOf g (∑ i ∈ t, f i • Y i) x
      = ∑ i ∈ t, (f i x • lcOf g (Y i) x + (mvfderiv I (f i) x).smulRight (Y i x)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have hσ : MDiffAt (T% (0 : Π y : M, TangentSpace I y)) x :=
        (cmDiff_zeroField (I := I) (M := M)).mdifferentiableAt (by simp)
      have h2 : lcOf g (0 : Π y : M, TangentSpace I y) x
          = lcOf g (0 : Π y : M, TangentSpace I y) x + lcOf g 0 x := by
        have h := (lcOf g).isCovariantDerivativeOn.add (s := Set.univ)
          (σ := (0 : Π y : M, TangentSpace I y)) (σ' := 0) hσ hσ
        simpa using h
      have h3 : lcOf g (0 : Π y : M, TangentSpace I y) x = 0 := by
        have h4 : lcOf g (0 : Π y : M, TangentSpace I y) x + lcOf g 0 x
            = 0 + lcOf g (0 : Π y : M, TangentSpace I y) x := by
          rw [zero_add]
          exact h2.symm
        exact add_right_cancel h4
      simpa using h3
  | insert i t hi ih =>
      have hsingle : CMDiff ∞ (T% (f i • Y i)) := (hf i).smul_section (hY i)
      have hsums : CMDiff ∞ (T% (∑ j ∈ t, f j • Y j)) := cmDiff_sum_smul (I := I) t f Y hf hY
      have hm1 : MDiffAt (T% (f i • Y i)) x := hsingle.mdifferentiableAt (by simp)
      have hm2 : MDiffAt (T% (∑ j ∈ t, f j • Y j)) x := hsums.mdifferentiableAt (by simp)
      have hm3 : MDiffAt (T% (Y i)) x := (hY i).mdifferentiableAt (by simp)
      have hm4 : MDiffAt (f i) x := (hf i).mdifferentiableAt (by simp)
      have hadd := (lcOf g).isCovariantDerivativeOn.add (s := Set.univ) (σ := f i • Y i)
        (σ' := ∑ j ∈ t, f j • Y j) hm1 hm2
      have hlei := (lcOf g).isCovariantDerivativeOn.leibniz (s := Set.univ) (σ := Y i) (g := f i)
        hm3 hm4
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      rw [hadd, hlei, ih]

/-- The connection depends on the germ at the base point. -/
theorem lcOf_congr_eventuallyEq (g : SMet I M) {X X' : Π y : M, TangentSpace I y} {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (heq : X =ᶠ[𝓝 x] X') :
    lcOf g X x = lcOf g X' x := by
  exact (lcOf g).isCovariantDerivativeOn.congr_of_eventuallyEq (s := Set.univ) hX hX'
    Filter.univ_mem heq

/-! ## The fourth field slot of `dRmPhi` -/

/-- `dRmPhi` is antisymmetric in its last two field arguments. -/
theorem dRmPhi_skew_last (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    {A B C D : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (hD : CMDiff ∞ (T% D)) :
    dRmPhi g x v A B C D = -dRmPhi g x v A B D C := by
  have hf : CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (C y) (D y)) :=
    rmP_fields_smooth hLC g hA hB hC hD
  have hgg : CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (D y) (C y)) :=
    rmP_fields_smooth hLC g hA hB hD hC
  have hfun : (fun y : M => rmP g y (A y) (B y) (C y) (D y))
      + (fun y : M => rmP g y (A y) (B y) (D y) (C y)) = fun _ : M => (0 : ℝ) := by
    funext y
    rw [Pi.add_apply, rmP_skew hLC g y (A y) (B y) (C y) (D y)]
    ring
  have hderiv : mvfderiv I (fun y : M => rmP g y (A y) (B y) (C y) (D y)) x v
      = -mvfderiv I (fun y : M => rmP g y (A y) (B y) (D y) (C y)) x v := by
    have h := congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
      (mvfderiv_add (x := x) (hf.mdifferentiableAt (by simp)) (hgg.mdifferentiableAt (by simp)))
    rw [hfun, mvfderiv_const] at h
    simp only [zero_apply, add_apply] at h
    linarith
  have hc1 : rmP g x ((lcOf g) A x v) (B x) (C x) (D x)
      = -rmP g x ((lcOf g) A x v) (B x) (D x) (C x) := rmP_skew hLC g x _ (B x) (C x) (D x)
  have hc2 : rmP g x (A x) ((lcOf g) B x v) (C x) (D x)
      = -rmP g x (A x) ((lcOf g) B x v) (D x) (C x) := rmP_skew hLC g x _ _ (C x) (D x)
  have hc3 : rmP g x (A x) (B x) ((lcOf g) C x v) (D x)
      = -rmP g x (A x) (B x) (D x) ((lcOf g) C x v) := rmP_skew hLC g x _ _ _ (D x)
  have hc4 : rmP g x (A x) (B x) (C x) ((lcOf g) D x v)
      = -rmP g x (A x) (B x) ((lcOf g) D x v) (C x) := rmP_skew hLC g x _ _ _ _
  simp only [dRmPhi]
  rw [hderiv, hc1, hc2, hc3, hc4]
  ring

/-- The fourth field slot of `dRmPhi` is `C^∞(M)`-linear. -/
theorem dRmPhi_linear_slotD (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    {A B C D₁ D₂ : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (hD₁ : CMDiff ∞ (T% D₁)) (hD₂ : CMDiff ∞ (T% D₂)) {f₁ f₂ : M → ℝ}
    (hf₁ : CMDiff ∞ f₁) (hf₂ : CMDiff ∞ f₂) :
    dRmPhi g x v A B C (f₁ • D₁ + f₂ • D₂)
      = f₁ x * dRmPhi g x v A B C D₁ + f₂ x * dRmPhi g x v A B C D₂ := by
  have hD : CMDiff ∞ (T% (f₁ • D₁ + f₂ • D₂)) :=
    ((hf₁).smul_section hD₁).add_section ((hf₂).smul_section hD₂)
  calc dRmPhi g x v A B C (f₁ • D₁ + f₂ • D₂)
      = -dRmPhi g x v A B (f₁ • D₁ + f₂ • D₂) C := dRmPhi_skew_last hLC g x v hA hB hC hD
    _ = -(f₁ x * dRmPhi g x v A B D₁ C + f₂ x * dRmPhi g x v A B D₂ C) := by
          rw [fth_dRmPhi_linear hLC hA hB hD₁ hD₂ hC hf₁ hf₂]
    _ = f₁ x * dRmPhi g x v A B C D₁ + f₂ x * dRmPhi g x v A B C D₂ := by
          rw [dRmPhi_skew_last hLC g x v hA hB hC hD₁,
            dRmPhi_skew_last hLC g x v hA hB hC hD₂]
          ring

/-- The fourth field slot of `dRmPhi` depends only on the value of the field at the base point. -/
theorem dRmPhi_bind_slotD (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    {A B C D D' : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C))
    (hD : CMDiff ∞ (T% D)) (hD' : CMDiff ∞ (T% D')) (h : D x = D' x) :
    dRmPhi g x v A B C D = dRmPhi g x v A B C D' := by
  calc dRmPhi g x v A B C D = -dRmPhi g x v A B D C := dRmPhi_skew_last hLC g x v hA hB hC hD
    _ = -dRmPhi g x v A B D' C := by rw [fth_dRmPhi_bind hLC hA hB hD hD' hC h]
    _ = dRmPhi g x v A B C D' := by rw [dRmPhi_skew_last hLC g x v hA hB hC hD']

/-! ## `covRm` as a function of fields -/

/-- `∇Rm` is antisymmetric in its last two arguments. -/
theorem covRm_skew_last (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    (a b c d : TangentSpace I x) :
    covRm g x v a b c d = -covRm g x v a b d c := by
  rw [covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := b) (c := c) (d := d),
    covRm_eq_dRmPhi (g := g) (x := x) (v := v) (a := a) (b := b) (c := d) (d := c)]
  exact dRmPhi_skew_last hLC g x v (smoothExt_cmdiff x a) (smoothExt_cmdiff x b)
    (smoothExt_cmdiff x c) (smoothExt_cmdiff x d)

/-- **The field form of `∇Rm`**: evaluating `covRm` on arbitrary smooth fields. -/
theorem covRm_field_form (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v : TangentSpace I x)
    {X₁ X₂ X₃ X₄ : Π y : M, TangentSpace I y}
    (h₁ : CMDiff ∞ (T% X₁)) (h₂ : CMDiff ∞ (T% X₂)) (h₃ : CMDiff ∞ (T% X₃))
    (h₄ : CMDiff ∞ (T% X₄)) :
    covRm g x v (X₁ x) (X₂ x) (X₃ x) (X₄ x) = dRmPhi g x v X₁ X₂ X₃ X₄ := by
  rw [covRm_eq_dRmPhi]
  rw [dRmPhi_bind_fst hLC (smoothExt_cmdiff x (X₁ x)) h₁ (smoothExt_cmdiff x (X₂ x))
      (smoothExt_cmdiff x (X₃ x)) (smoothExt_cmdiff x (X₄ x)) (smoothExt_apply x (X₁ x)),
    dRmPhi_bind_slotB hLC h₁ (smoothExt_cmdiff x (X₂ x)) h₂ (smoothExt_cmdiff x (X₃ x))
      (smoothExt_cmdiff x (X₄ x)) (smoothExt_apply x (X₂ x)),
    fth_dRmPhi_bind hLC h₁ h₂ (smoothExt_cmdiff x (X₃ x)) h₃ (smoothExt_cmdiff x (X₄ x))
      (smoothExt_apply x (X₃ x)),
    dRmPhi_bind_slotD hLC g x v h₁ h₂ h₃ (smoothExt_cmdiff x (X₄ x)) h₄
      (smoothExt_apply x (X₄ x))]

/-- `∇Rm` is linear in its fifth argument. -/
theorem covRm_linear_fith (hLC : LCSmooth I M) (g : SMet I M) (x : M) (v a b c : TangentSpace I x)
    (r s : ℝ) (d₁ d₂ : TangentSpace I x) :
    covRm g x v a b c (r • d₁ + s • d₂)
      = r * covRm g x v a b c d₁ + s * covRm g x v a b c d₂ := by
  rw [covRm_skew_last hLC g x v a b c (r • d₁ + s • d₂),
    covRm_linear_fth hLC g x v a b r s d₁ d₂]
  rw [covRm_skew_last hLC g x v a b d₁ c, covRm_skew_last hLC g x v a b d₂ c]
  ring

/-- **Smoothness of `∇Rm` on smooth fields.** -/
theorem covRm_field_smooth (hLC : LCSmooth I M) (g : SMet I M)
    {V A B C D : Π y : M, TangentSpace I y}
    (hV : CMDiff ∞ (T% V)) (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B))
    (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
    CMDiff ∞ (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y)) := by
  have hfun : (fun y : M => covRm g y (V y) (A y) (B y) (C y) (D y))
      = fun y : M => dRmPhi g y (V y) A B C D := by
    funext y
    exact covRm_field_form hLC g y (V y) hA hB hC hD
  rw [hfun]
  obtain ⟨hcov⟩ := (hLC g).1
  have hF : CMDiff ∞ (fun z : M => rmP g z (A z) (B z) (C z) (D z)) :=
    rmP_fields_smooth hLC g hA hB hC hD
  have hlcA : CMDiff ∞ (T% (fun y : M => lcOf g A y (V y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hA hV
  have hlcB : CMDiff ∞ (T% (fun y : M => lcOf g B y (V y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hB hV
  have hlcC : CMDiff ∞ (T% (fun y : M => lcOf g C y (V y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hC hV
  have hlcD : CMDiff ∞ (T% (fun y : M => lcOf g D y (V y))) :=
    Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiff_cov_apply
      (lcOf g) hcov hD hV
  have t1 : CMDiff ∞ (fun y : M => mvfderiv I (fun z : M => rmP g z (A z) (B z) (C z) (D z)) y (V y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hF hV
  have t2 : CMDiff ∞ (fun y : M => rmP g y (lcOf g A y (V y)) (B y) (C y) (D y)) :=
    rmP_fields_smooth hLC g hlcA hB hC hD
  have t3 : CMDiff ∞ (fun y : M => rmP g y (A y) (lcOf g B y (V y)) (C y) (D y)) :=
    rmP_fields_smooth hLC g hA hlcB hC hD
  have t4 : CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (lcOf g C y (V y)) (D y)) :=
    rmP_fields_smooth hLC g hA hB hlcC hD
  have t5 : CMDiff ∞ (fun y : M => rmP g y (A y) (B y) (C y) (lcOf g D y (V y))) :=
    rmP_fields_smooth hLC g hA hB hC hlcD
  simp only [dRmPhi]
  exact (((t1.sub t2).sub t3).sub t4).sub t5

end Work.Diff.GE.Kato3
