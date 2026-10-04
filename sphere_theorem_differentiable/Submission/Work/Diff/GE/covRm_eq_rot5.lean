import Mathlib
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.GE.rot5_eq_rotA
import Submission.Work.Diff.GE.norms_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Frame change of the `(0,5)`-tensor `∇Rm`, and its multilinear expansion

`Submission.Diff.covRm g x v a b c d = (∇_v Rm)(a,b,c,d)` is `ℝ`-multilinear in its five arguments,
so it is a tensor.  This file records the two consequences used by
`Work.Diff.GE.dRmNormSq_eq_N5_of_basis`:

* `covRm_sum_expand_smooth`: the multilinear expansion on finite linear combinations,
  `∇Rm (∑ c₀•a) … (∑ c₄•a) = ∑_{r : Fin 5 → ι} (∏_p c_p (r p)) · ∇Rm (a r₀) … (a r₄)`
  (this is `Work.Diff.GE.covRm_sum_expand` with the hypothesis weakened from `C^ω` to `C^∞`);
* `covRm_eq_rot5`: if the new frame is `e' i = ∑ j, A i j • f j`, then the components of `∇Rm`
  in `e'` are the `rot5 A`-rotation of the components in `f`.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-! ## Finite-sum expansions in the five arguments -/

/-- A map `V → ℝ` that is additive and homogeneous is linear on finite sums. -/
private lemma lin_of_binary {V : Type*} [AddCommMonoid V] [Module ℝ V] (F : V → ℝ)
    (hadd : ∀ x y : V, F (x + y) = F x + F y)
    (hsmul : ∀ (r : ℝ) (x : V), F (r • x) = r * F x)
    {ι : Type*} (s : Finset ι) (r : ι → ℝ) (z : ι → V) :
    F (∑ i ∈ s, r i • z i) = ∑ i ∈ s, r i * F (z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hsmul 0 (0 : V)
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, hsmul, ih]

/-- Finite-sum form of the linearity of `covRm` in its first (direction) argument `v`. -/
private lemma covRm_sum_fst
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (v : ι → TangentSpace I x) (a b c d : TangentSpace I x) :
    covRm g x (∑ i ∈ s, r i • v i) a b c d
      = ∑ i ∈ s, r i * covRm g x (v i) a b c d :=
  lin_of_binary (fun w : TangentSpace I x => covRm g x w a b c d)
    (fun u w => by
      simpa only [one_smul, one_mul] using covRm_linear_fst hLC g x 1 1 u w a b c d)
    (fun ρ w => by
      simpa only [zero_smul, add_zero, zero_mul] using
        covRm_linear_fst hLC g x ρ 0 w 0 a b c d) s r v

/-- Finite-sum form of the linearity of `covRm` in its second argument `a`. -/
private lemma covRm_sum_snd
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (a : ι → TangentSpace I x) (v b c d : TangentSpace I x) :
    covRm g x v (∑ i ∈ s, r i • a i) b c d
      = ∑ i ∈ s, r i * covRm g x v (a i) b c d :=
  lin_of_binary (fun w : TangentSpace I x => covRm g x v w b c d)
    (fun u w => by
      simpa only [one_smul, one_mul] using covRm_linear_snd hLC g x v 1 1 u w b c d)
    (fun ρ w => by
      simpa only [zero_smul, add_zero, zero_mul] using
        covRm_linear_snd hLC g x v ρ 0 w 0 b c d) s r a

/-- Finite-sum form of the linearity of `covRm` in its third argument `b`. -/
private lemma covRm_sum_thd
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (b : ι → TangentSpace I x) (v a c d : TangentSpace I x) :
    covRm g x v a (∑ i ∈ s, r i • b i) c d
      = ∑ i ∈ s, r i * covRm g x v a (b i) c d :=
  lin_of_binary (fun w : TangentSpace I x => covRm g x v a w c d)
    (fun u w => by
      simpa only [one_smul, one_mul] using covRm_linear_thd hLC g x v a 1 1 u w c d)
    (fun ρ w => by
      simpa only [zero_smul, add_zero, zero_mul] using
        covRm_linear_thd hLC g x v a ρ 0 w 0 c d) s r b

/-- Finite-sum form of the linearity of `covRm` in its fourth argument `c`. -/
private lemma covRm_sum_fth
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (c : ι → TangentSpace I x) (v a b d : TangentSpace I x) :
    covRm g x v a b (∑ i ∈ s, r i • c i) d
      = ∑ i ∈ s, r i * covRm g x v a b (c i) d :=
  lin_of_binary (fun w : TangentSpace I x => covRm g x v a b w d)
    (fun u w => by
      simpa only [one_smul, one_mul] using covRm_linear_fth hLC g x v a b 1 1 u w d)
    (fun ρ w => by
      simpa only [zero_smul, add_zero, zero_mul] using
        covRm_linear_fth hLC g x v a b ρ 0 w 0 d) s r c

/-- Finite-sum form of the linearity of `covRm` in its fifth argument `d`. -/
private lemma covRm_sum_fith
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (d : ι → TangentSpace I x) (v a b c : TangentSpace I x) :
    covRm g x v a b c (∑ i ∈ s, r i • d i)
      = ∑ i ∈ s, r i * covRm g x v a b c (d i) :=
  lin_of_binary (fun w : TangentSpace I x => covRm g x v a b c w)
    (fun u w => by
      simpa only [one_smul, one_mul] using
        Work.Diff.GE.Kato3.covRm_linear_fith hLC g x v a b c 1 1 u w)
    (fun ρ w => by
      simpa only [zero_smul, add_zero, zero_mul] using
        Work.Diff.GE.Kato3.covRm_linear_fith hLC g x v a b c ρ 0 w 0) s r d

/-- **Multilinear expansion of `∇Rm`.**  For a family `a : Fin n → TₓM` and coefficients
`c : Fin 5 → Fin n → ℝ`,
`∇Rm (∑_k c₀ k • a k) … (∑_k c₄ k • a k) = ∑_{r : Fin 5 → Fin n} (∏_p c_p (r p)) · ∇Rm (a (r₀)) … (a (r₄))`.

This is `Work.Diff.GE.covRm_sum_expand` with the `C^ω` hypothesis weakened to `C^∞`. -/
theorem covRm_sum_expand_smooth
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) {n : ℕ}
    (a : Fin n → TangentSpace I x) (c : Fin 5 → Fin n → ℝ) :
    covRm g x (∑ k, c 0 k • a k) (∑ k, c 1 k • a k) (∑ k, c 2 k • a k)
        (∑ k, c 3 k • a k) (∑ k, c 4 k • a k)
      = ∑ r : Fin 5 → Fin n, (∏ p : Fin 5, c p (r p)) *
          covRm g x (a (r 0)) (a (r 1)) (a (r 2)) (a (r 3)) (a (r 4)) := by
  rw [sum_pi_five (F := fun r : Fin 5 → Fin n => (∏ p : Fin 5, c p (r p)) *
        covRm g x (a (r 0)) (a (r 1)) (a (r 2)) (a (r 3)) (a (r 4)))]
  simp only [Fin.prod_univ_five, Matrix.cons_val]
  rw [covRm_sum_fst hLC g x Finset.univ (c 0) a _ _ _ _]
  refine Finset.sum_congr rfl (fun k0 _ => ?_)
  rw [covRm_sum_snd hLC g x Finset.univ (c 1) a (a k0) _ _ _]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k1 _ => ?_)
  rw [covRm_sum_thd hLC g x Finset.univ (c 2) a (a k0) (a k1) _ _]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k2 _ => ?_)
  rw [covRm_sum_fth hLC g x Finset.univ (c 3) a (a k0) (a k1) (a k2) _]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k3 _ => ?_)
  rw [covRm_sum_fith hLC g x Finset.univ (c 4) a (a k0) (a k1) (a k2) (a k3)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k4 _ => ?_)
  ring

/-! ## The frame change -/

/-- **Frame change of `∇Rm`.**  If `e' i = ∑ j, A i j • f j`, then the components of the
`(0,5)`-tensor `∇Rm` in the frame `e'` are the `rot5 A`-rotation of its components in `f`. -/
theorem covRm_eq_rot5
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (f e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hA : ∀ i, e' i = ∑ j, A i j • f j) :
    (fun m i j k l => covRm g x (e' m) (e' i) (e' j) (e' k) (e' l))
      = rot5 A (fun m i j k l => covRm g x (f m) (f i) (f j) (f k) (f l)) := by
  funext m i j k l
  rw [hA m, hA i, hA j, hA k, hA l]
  have hexp := covRm_sum_expand_smooth (n := Module.finrank ℝ E) hLC g x f
      ![A m, A i, A j, A k, A l]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.prod_univ_five] at hexp
  rw [hexp]
  clear hexp
  rw [rot5]
  rw [sum_pi_five (F := fun y : Fin 5 → Fin (Module.finrank ℝ E) =>
        (A m (y 0) * A i (y 1) * A j (y 2) * A k (y 3) * A l (y 4)) *
          covRm g x (f (y 0)) (f (y 1)) (f (y 2)) (f (y 3)) (f (y 4)))]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]

end Work.Diff.GE
