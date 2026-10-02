/-
# `Work.FQCInputs.continuous_iteratedDeriv_two_F`

The map `(c, z) ↦ iteratedDeriv 2 (F c) z` is continuous, where
`F c = (Tsq c)^[5] = (T_c)^{10}` is the holomorphic second return map of the tricorn at the
parameter `c` (`Work.EL.F`, `F c z = ((z² + c̄)² + c)^[5] z`).

This is the smooth-dependence-on-the-parameter input consumed by the FQC area: the second
derivative `iteratedDeriv 2 (F c) z` enters the simplicity condition of the transported parabolic
point (`Work.FQC.SimpleTransfer`), which is read off along the continuous family
`c ↦ principal (muQC …)`.

The proof is a direct induction on the number of iterates.  `Tsq c z = (z² + c̄)² + c` is a
polynomial, so `(c, z) ↦ Tsq c z` and its first two `z`-derivatives are continuous (explicit
formulae below), and the chain rules for `deriv` and for the second derivative
(`iteratedDeriv_comp_two`) propagate this to every iterate.
-/
import Mathlib
import Submission.Work.FQCInputs.Defs
import Submission.Work.FQC.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.FQCInputs

/-! ## 1. The first two `z`-derivatives of `Tsq c = (z² + c̄)² + c` -/

private lemma contDiff_tsq (c : ℂ) : ContDiff ℂ ⊤ (Work.Landing.Tsq c) := by
  unfold Work.Landing.Tsq
  fun_prop

private lemma contDiff_tsq_iter (c : ℂ) (n : ℕ) : ContDiff ℂ ⊤ ((Work.Landing.Tsq c)^[n]) := by
  induction n with
  | zero => simpa using contDiff_id
  | succ n ih =>
      rw [Function.iterate_succ']
      exact (contDiff_tsq c).comp ih

/-- The derivative of the polynomial `Tsq c`. -/
private lemma tsq_deriv_formula (c w : ℂ) :
    deriv (Work.Landing.Tsq c) w = 4 * w * (w ^ 2 + star c) := by
  have hpoly : Work.Landing.Tsq c =
      (fun z : ℂ => Polynomial.eval z (Polynomial.C (2 * star c) * Polynomial.X ^ 2 +
        Polynomial.X ^ 4 + Polynomial.C (star c ^ 2 + c))) := by
    funext z
    unfold Work.Landing.Tsq
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  rw [hpoly, Polynomial.deriv]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C_mul_X_pow,
    Polynomial.derivative_X_pow, Polynomial.derivative_C, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_zero]
  ring

/-- The second derivative of the polynomial `Tsq c`. -/
private lemma tsq_iteratedDeriv2_formula (c w : ℂ) :
    iteratedDeriv 2 (Work.Landing.Tsq c) w = 12 * w ^ 2 + 4 * star c := by
  have hd1 : deriv (Work.Landing.Tsq c) = fun z => 4 * z * (z ^ 2 + star c) := by
    funext u
    exact tsq_deriv_formula c u
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, hd1]
  have hpoly : (fun z : ℂ => 4 * z * (z ^ 2 + star c)) =
      fun z => Polynomial.eval z (Polynomial.C (4 * star c) * Polynomial.X +
        Polynomial.C 4 * Polynomial.X ^ 3) := by
    funext z
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    ring
  rw [hpoly, Polynomial.deriv]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C_mul_X,
    Polynomial.derivative_C_mul_X_pow, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  ring

/-! ## 2. The iterate of `Tsq`, together with its first two `z`-derivatives -/

/-- The `n`-th iterate of `Tsq c`, as a function of `(c, z)`. -/
def TsqA (n : ℕ) : ℂ × ℂ → ℂ := fun p => (Work.Landing.Tsq p.1)^[n] p.2

/-- The `z`-derivative of the `n`-th iterate of `Tsq c`. -/
def TsqD (n : ℕ) : ℂ × ℂ → ℂ := fun p => deriv ((Work.Landing.Tsq p.1)^[n]) p.2

/-- The second `z`-derivative of the `n`-th iterate of `Tsq c`. -/
def TsqE (n : ℕ) : ℂ × ℂ → ℂ := fun p => iteratedDeriv 2 ((Work.Landing.Tsq p.1)^[n]) p.2

private lemma TsqA_succ (n : ℕ) :
    TsqA (n + 1) = fun p => Work.Landing.Tsq p.1 (TsqA n p) := by
  funext p
  unfold TsqA
  rw [Function.iterate_succ_apply']

private lemma TsqD_succ (n : ℕ) :
    TsqD (n + 1) = fun p => deriv (Work.Landing.Tsq p.1) (TsqA n p) * TsqD n p := by
  funext p
  have h : (Work.Landing.Tsq p.1)^[n + 1] =
      Work.Landing.Tsq p.1 ∘ (Work.Landing.Tsq p.1)^[n] := Function.iterate_succ' _ _
  have hd1 : DifferentiableAt ℂ (Work.Landing.Tsq p.1) ((Work.Landing.Tsq p.1)^[n] p.2) :=
    ((contDiff_tsq p.1).differentiable (by simp)).differentiableAt
  have hd2 : DifferentiableAt ℂ ((Work.Landing.Tsq p.1)^[n]) p.2 :=
    ((contDiff_tsq_iter p.1 n).differentiable (by simp)).differentiableAt
  unfold TsqD TsqA
  rw [h, deriv_comp p.2 hd1 hd2]

private lemma TsqE_succ (n : ℕ) :
    TsqE (n + 1) = fun p =>
      iteratedDeriv 2 (Work.Landing.Tsq p.1) (TsqA n p) * (TsqD n p) ^ 2 +
        deriv (Work.Landing.Tsq p.1) (TsqA n p) * TsqE n p := by
  funext p
  have h : (Work.Landing.Tsq p.1)^[n + 1] =
      Work.Landing.Tsq p.1 ∘ (Work.Landing.Tsq p.1)^[n] := Function.iterate_succ' _ _
  have hg : ContDiffAt ℂ 2 (Work.Landing.Tsq p.1) ((Work.Landing.Tsq p.1)^[n] p.2) :=
    ((contDiff_tsq p.1).contDiffAt).of_le le_top
  have hf : ContDiffAt ℂ 2 ((Work.Landing.Tsq p.1)^[n]) p.2 :=
    ((contDiff_tsq_iter p.1 n).contDiffAt).of_le le_top
  unfold TsqE TsqA TsqD
  rw [h, iteratedDeriv_comp_two hg hf]

/-! ## 3. Continuity of the three families -/

private lemma cont_TsqA_zero : Continuous (TsqA 0) := by
  unfold TsqA
  simp only [Function.iterate_zero_apply]
  exact continuous_snd

private lemma cont_TsqD_zero : Continuous (TsqD 0) := by
  have h : TsqD 0 = fun _ => (1 : ℂ) := by
    funext p
    unfold TsqD
    rw [Function.iterate_zero]
    exact deriv_id p.2
  rw [h]
  exact continuous_const

private lemma cont_TsqE_zero : Continuous (TsqE 0) := by
  have h : TsqE 0 = fun _ => (0 : ℂ) := by
    funext p
    unfold TsqE
    rw [Function.iterate_zero]
    have hd : deriv (id : ℂ → ℂ) = fun _ => (1 : ℂ) := deriv_id'
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, hd]
    exact deriv_const _ _
  rw [h]
  exact continuous_const

private lemma cont_tsq_two : Continuous (fun p : ℂ × ℂ => Work.Landing.Tsq p.1 p.2) := by
  unfold Work.Landing.Tsq
  fun_prop

private lemma cont_tsqD_two :
    Continuous (fun p : ℂ × ℂ => deriv (Work.Landing.Tsq p.1) p.2) := by
  have h : (fun p : ℂ × ℂ => deriv (Work.Landing.Tsq p.1) p.2) =
      fun p => 4 * p.2 * (p.2 ^ 2 + star p.1) := by
    funext p
    exact tsq_deriv_formula p.1 p.2
  rw [h]
  fun_prop

private lemma cont_tsqE_two :
    Continuous (fun p : ℂ × ℂ => iteratedDeriv 2 (Work.Landing.Tsq p.1) p.2) := by
  have h : (fun p : ℂ × ℂ => iteratedDeriv 2 (Work.Landing.Tsq p.1) p.2) =
      fun p => 12 * p.2 ^ 2 + 4 * star p.1 := by
    funext p
    exact tsq_iteratedDeriv2_formula p.1 p.2
  rw [h]
  fun_prop

private lemma cont_TsqA_succ (n : ℕ) (hA : Continuous (TsqA n)) :
    Continuous (fun p : ℂ × ℂ => Work.Landing.Tsq p.1 (TsqA n p)) :=
  (cont_tsq_two.comp (continuous_fst.prodMk hA)).congr (fun p => rfl)

private lemma cont_TsqD_succ (n : ℕ) (hA : Continuous (TsqA n)) (hD : Continuous (TsqD n)) :
    Continuous (fun p : ℂ × ℂ => deriv (Work.Landing.Tsq p.1) (TsqA n p) * TsqD n p) :=
  ((cont_tsqD_two.comp (continuous_fst.prodMk hA)).mul hD).congr (fun p => rfl)

private lemma cont_TsqE_succ (n : ℕ) (hA : Continuous (TsqA n)) (hD : Continuous (TsqD n))
    (hE : Continuous (TsqE n)) :
    Continuous (fun p : ℂ × ℂ =>
      iteratedDeriv 2 (Work.Landing.Tsq p.1) (TsqA n p) * (TsqD n p) ^ 2 +
        deriv (Work.Landing.Tsq p.1) (TsqA n p) * TsqE n p) :=
  (((cont_tsqE_two.comp (continuous_fst.prodMk hA)).mul (hD.pow 2)).add
    ((cont_tsqD_two.comp (continuous_fst.prodMk hA)).mul hE)).congr (fun p => rfl)

private lemma cont_all (n : ℕ) :
    Continuous (TsqA n) ∧ Continuous (TsqD n) ∧ Continuous (TsqE n) := by
  induction n with
  | zero => exact ⟨cont_TsqA_zero, cont_TsqD_zero, cont_TsqE_zero⟩
  | succ n ih =>
      obtain ⟨hA, hD, hE⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · rw [TsqA_succ]
        exact cont_TsqA_succ n hA
      · rw [TsqD_succ]
        exact cont_TsqD_succ n hA hD
      · rw [TsqE_succ]
        exact cont_TsqE_succ n hA hD hE

/-! ## 4. The target -/

theorem continuous_iteratedDeriv_two_F :
    Continuous fun q : ℂ × ℂ => iteratedDeriv 2 (Work.EL.F q.1) q.2 := by
  have hE : Continuous (TsqE 5) := (cont_all 5).2.2
  exact hE

end Work.FQCInputs

end
