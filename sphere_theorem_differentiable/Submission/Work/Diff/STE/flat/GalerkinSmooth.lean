/-
# The explicit jet: differentiability and smoothness

This module collects the calculus facts about the explicit jet of a box-supported coefficient
family (`Work.Diff.STE.Flat.Galerkin.jetExp`): the closed-form directional derivatives of the
characters `dExp`/`d2Exp`, and the joint smoothness in `(a, x)` of `valExp`, `linExp`, `secExp` and
of the assembled jet.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.GalerkinDefs
import Submission.Work.Diff.STE.pd_fourierExp
import Submission.Work.Diff.STE.contDiff_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

namespace Flat

namespace Galerkin

noncomputable section

open scoped BigOperators

/-! ## The directional derivatives of a character -/

/-- The directional derivative of `fourierExp m` along `e_c` is `dExp m c`. -/
lemma fderiv_fourierExp_apply_single {n : ℕ} (m : Fin n → ℤ) (c : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (Work.Diff.STE.fourierExp m) x (Pi.single c 1) = dExp m c x := by
  simpa [dExp, Work.Diff.STE.pd] using Work.Diff.STE.pd_fourierExp m c x

/-- The directional derivative of `dExp m d` along `e_c` is `d2Exp m d c`. -/
lemma fderiv_dExp_apply_single {n : ℕ} (m : Fin n → ℤ) (d c : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (fun y => dExp m d y) x (Pi.single c 1) = d2Exp m d c x := by
  have h1 : (fun y => dExp m d y)
      = (2 * Real.pi * Complex.I * (m d : ℂ)) • (Work.Diff.STE.fourierExp m) := by
    funext y
    simp [dExp, smul_eq_mul]
  have hd : DifferentiableAt ℝ (Work.Diff.STE.fourierExp m) x :=
    (Work.Diff.STE.contDiff_fourierExp_top m).differentiable (by simp) x
  rw [h1, fderiv_const_smul hd, smul_apply, smul_eq_mul]
  rw [fderiv_fourierExp_apply_single m c x]
  rfl

/-! ## Smoothness in `(a, x)` -/

/-- Smoothness of the coefficient application in the state variable. -/
lemma contDiff_coeff_apply {n N : ℕ} (m : box n N) (i j : Fin n) :
    ContDiff ℝ ⊤ (fun p : Coeff n N × (Fin n → ℝ) => p.1 m i j) :=
  ContinuousLinearMap.contDiff
    ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj i).comp
      ((ContinuousLinearMap.proj m).comp
        (ContinuousLinearMap.fst ℝ (Coeff n N) (Fin n → ℝ)))))

/-- The character `x ↦ fourierExp m x` is smooth as a function of the second variable. -/
lemma contDiff_fourierExp_snd {n N : ℕ} (m : Fin n → ℤ) :
    ContDiff ℝ ⊤ (fun p : Coeff n N × (Fin n → ℝ) => Work.Diff.STE.fourierExp m p.2) :=
  (Work.Diff.STE.contDiff_fourierExp_top m).comp contDiff_snd

lemma contDiff_dExp_snd {n N : ℕ} (m : Fin n → ℤ) (c : Fin n) :
    ContDiff ℝ ⊤ (fun p : Coeff n N × (Fin n → ℝ) => dExp m c p.2) := by
  have h : (fun p : Coeff n N × (Fin n → ℝ) => dExp m c p.2)
      = fun p => (2 * Real.pi * Complex.I * (m c : ℂ)) * Work.Diff.STE.fourierExp m p.2 := rfl
  rw [h]
  exact (contDiff_const (c := 2 * Real.pi * Complex.I * (m c : ℂ))).mul
    (contDiff_fourierExp_snd (N := N) m)

lemma contDiff_d2Exp_snd {n N : ℕ} (m : Fin n → ℤ) (d c : Fin n) :
    ContDiff ℝ ⊤ (fun p : Coeff n N × (Fin n → ℝ) => d2Exp m d c p.2) := by
  have h : (fun p : Coeff n N × (Fin n → ℝ) => d2Exp m d c p.2)
      = fun p => (2 * Real.pi * Complex.I * (m d : ℂ)) *
          ((2 * Real.pi * Complex.I * (m c : ℂ)) * Work.Diff.STE.fourierExp m p.2) := rfl
  rw [h]
  exact (contDiff_const (c := 2 * Real.pi * Complex.I * (m d : ℂ))).mul
    ((contDiff_const (c := 2 * Real.pi * Complex.I * (m c : ℂ))).mul
      (contDiff_fourierExp_snd (N := N) m))

/-- The directional derivative of a character is smooth in `x`. -/
lemma contDiff_dExp_single {n : ℕ} (m : Fin n → ℤ) (c : Fin n) :
    ContDiff ℝ ⊤ (fun y : Fin n → ℝ => dExp m c y) :=
  contDiff_const.mul (Work.Diff.STE.contDiff_fourierExp_top m)

/-- The second directional derivative of a character is smooth in `x`. -/
lemma contDiff_d2Exp_single {n : ℕ} (m : Fin n → ℤ) (d c : Fin n) :
    ContDiff ℝ ⊤ (fun y : Fin n → ℝ => d2Exp m d c y) :=
  contDiff_const.mul (contDiff_dExp_single m c)

/-- The value component of the explicit jet is smooth in `(a, x)`. -/
lemma contDiff_valExp {n N : ℕ} :
    ContDiff ℝ ⊤ (fun p : Coeff n N × (Fin n → ℝ) => valExp p.1 p.2) := by
  refine contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => ?_))
  refine ContDiff.sum (fun m _ => ?_)
  exact (contDiff_coeff_apply m i j).mul (contDiff_fourierExp_snd (N := N) m.1)

/-- The first-derivative component of the explicit jet is smooth in `(a, x)`. -/
lemma contDiff_linExp {n N : ℕ} :
    ContDiff ℝ ⊤ (fun p : Coeff n N × (Fin n → ℝ) => linExp p.1 p.2) := by
  refine contDiff_pi.mpr (fun c => contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => ?_)))
  refine ContDiff.sum (fun m _ => ?_)
  exact (contDiff_coeff_apply m i j).mul (contDiff_dExp_snd (N := N) m.1 c)

/-- The second-derivative component of the explicit jet is smooth in `(a, x)`. -/
lemma contDiff_secExp {n N : ℕ} :
    ContDiff ℝ ⊤ (fun p : Coeff n N × (Fin n → ℝ) => secExp p.1 p.2) := by
  refine contDiff_pi.mpr (fun c => contDiff_pi.mpr
    (fun d => contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => ?_))))
  refine ContDiff.sum (fun m _ => ?_)
  exact (contDiff_coeff_apply m i j).mul (contDiff_d2Exp_snd (N := N) m.1 d c)

/-- The explicit jet is smooth in `(a, x)`. -/
lemma contDiff_jetExp {n N : ℕ} :
    ContDiff ℝ ⊤ (fun p : Coeff n N × (Fin n → ℝ) => jetExp p.1 p.2) := by
  have h : (fun p : Coeff n N × (Fin n → ℝ) => jetExp p.1 p.2)
      = fun p => (valExp p.1 p.2, linExp p.1 p.2, secExp p.1 p.2) := rfl
  rw [h, contDiff_prod_iff]
  refine ⟨?_, ?_⟩
  · simpa [Function.comp_def] using contDiff_valExp (n := n) (N := N)
  · rw [contDiff_prod_iff]
    exact ⟨by simpa [Function.comp_def] using contDiff_linExp (n := n) (N := N),
      by simpa [Function.comp_def] using contDiff_secExp (n := n) (N := N)⟩

/-- The explicit jet at a fixed coefficient family is a smooth function of `x`. -/
lemma contDiff_jetExp_fixed {n N : ℕ} (a : Coeff n N) :
    ContDiff ℝ ⊤ (fun x : Fin n → ℝ => jetExp a x) :=
  contDiff_jetExp.comp (by
    show ContDiff ℝ ⊤ (fun x : Fin n → ℝ => (a, x))
    fun_prop)

/-- The explicit jet at a fixed coefficient family is continuous in `x`. -/
lemma continuous_jetExp_fixed {n N : ℕ} (a : Coeff n N) :
    Continuous (fun x : Fin n → ℝ => jetExp a x) :=
  (contDiff_jetExp_fixed a).continuous

end

end Galerkin

end Flat

end Work.Diff.STE
