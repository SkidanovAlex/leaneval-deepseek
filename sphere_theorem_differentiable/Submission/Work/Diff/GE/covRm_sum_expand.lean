import Mathlib
import Submission.Work.Diff.GE.kato_covRm_multilinear
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multilinear expansion of `∇Rm` on finite linear combinations

`covRm g x v a b c d = (∇_v Rm)(a,b,c,d)` is the `(0,5)`-tensor `∇Rm` evaluated on five tangent
vectors, hence `ℝ`-multilinear in its five arguments.  This module records the resulting expansion
of `∇Rm` when each of its five arguments is a finite linear combination `∑ k, c p k • a k` of a
family `a : Fin n → TangentSpace I x`:

`∇Rm (∑ c₀ • a) (∑ c₁ • a) (∑ c₂ • a) (∑ c₃ • a) (∑ c₄ • a)
   = ∑ r : Fin 5 → Fin n, (∏ p, c p (r p)) * ∇Rm (a (r 0)) … (a (r 4))`.

The proof expands the multilinear form slot by slot.  The per-slot linearity of `covRm` in its
second/third/fourth argument is `covRm_linear_snd/thd/fth`; the fifth is
`Work.Diff.GE.Kato3.covRm_linear_fith`; the first is the additivity/homogeneity of the defining
`mvfderiv`/connection, reproduced here (`covRm_add_fst_local`, `covRm_smul_fst_local`).  The passage
from the five-fold iterated sum to the sum over the function type `Fin 5 → Fin n` is the
re-indexing `sum_pi_five`, and the product over `Fin 5` is `Fin.prod_univ_five`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-! ## Re-indexing of a sum over the function type `Fin 5 → Fin n` -/

/-- Re-indexing a function `Fin 5 → Fin n` as a nested `5`-tuple of its five coordinates. -/
private def tupleEquiv (n : ℕ) : (Fin 5 → Fin n) ≃ Fin n × Fin n × Fin n × Fin n × Fin n where
  toFun y := (y 0, y 1, y 2, y 3, y 4)
  invFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]
  left_inv y := by funext i; fin_cases i <;> rfl
  right_inv p := by rfl

/-- Every element of `Fin 5 → Fin n` is the vector of its five coordinates. -/
private theorem fun_eq_vec5 {n : ℕ} (y : Fin 5 → Fin n) : y = ![y 0, y 1, y 2, y 3, y 4] := by
  funext i; fin_cases i <;> rfl

/-- A sum over the function type `Fin 5 → Fin n` is the corresponding five-fold iterated sum. -/
private theorem sum_pi_five {n : ℕ} {β : Type*} [AddCommMonoid β] (F : (Fin 5 → Fin n) → β) :
    ∑ y : Fin 5 → Fin n, F y = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, F ![a,b,c,d,e] := by
  refine (Fintype.sum_equiv (tupleEquiv n) F
      (fun p : Fin n × Fin n × Fin n × Fin n × Fin n =>
        F ![p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2]) ?_).trans ?_
  · intro y
    rw [fun_eq_vec5 y]
    rfl
  · simp only [Fintype.sum_prod_type]

/-! ## Linearity of `covRm` in its first (direction) argument -/

/-- `covRm` is additive in its first (direction) argument. -/
private lemma covRm_add_fst_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (v₁ v₂ a b c d : TangentSpace I x) :
    covRm g x (v₁ + v₂) a b c d = covRm g x v₁ a b c d + covRm g x v₂ a b c d := by
  rw [covRm_eq_dRmPhi, covRm_eq_dRmPhi, covRm_eq_dRmPhi]
  simp only [dRmPhi]
  rw [map_add (mvfderiv I (fun y : M => rmP g y (smoothExt x a y) (smoothExt x b y)
        (smoothExt x c y) (smoothExt x d y)) x)]
  simp only [map_add, rmP_add_fst g hLC, rmP_add_snd g hLC, rmP_add_thd g hLC, rmP_add_fth g hLC]
  ring

/-- `covRm` is homogeneous in its first (direction) argument. -/
private lemma covRm_smul_fst_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M)
    (ρ : ℝ) (v a b c d : TangentSpace I x) :
    covRm g x (ρ • v) a b c d = ρ * covRm g x v a b c d := by
  rw [covRm_eq_dRmPhi, covRm_eq_dRmPhi]
  simp only [dRmPhi]
  rw [map_smul (mvfderiv I (fun y : M => rmP g y (smoothExt x a y) (smoothExt x b y)
        (smoothExt x c y) (smoothExt x d y)) x)]
  simp only [map_smul, smul_eq_mul, rmP_smul_fst g hLC, rmP_smul_snd g hLC, rmP_smul_thd g hLC,
    rmP_smul_fth g hLC]
  ring

/-! ## Finite-sum expansion in each of the five arguments -/

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
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) {ι : Type*}
    (s : Finset ι) (r : ι → ℝ) (v : ι → TangentSpace I x) (a b c d : TangentSpace I x) :
    covRm g x (∑ i ∈ s, r i • v i) a b c d
      = ∑ i ∈ s, r i * covRm g x (v i) a b c d :=
  lin_of_binary (fun w : TangentSpace I x => covRm g x w a b c d)
    (fun u w => covRm_add_fst_local hLC g x u w a b c d)
    (fun ρ w => covRm_smul_fst_local hLC g x ρ w a b c d) s r v

/-- Finite-sum form of the linearity of `covRm` in its second argument `a`. -/
private lemma covRm_sum_snd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
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
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
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
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
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
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
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

/-! ## The requested expansion -/

theorem covRm_sum_expand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) {n : ℕ}
    (a : Fin n → TangentSpace I x) (c : Fin 5 → Fin n → ℝ) :
    Submission.Diff.covRm g x (∑ k, c 0 k • a k) (∑ k, c 1 k • a k) (∑ k, c 2 k • a k)
        (∑ k, c 3 k • a k) (∑ k, c 4 k • a k)
      = ∑ r : Fin 5 → Fin n, (∏ p : Fin 5, c p (r p)) *
          Submission.Diff.covRm g x (a (r 0)) (a (r 1)) (a (r 2)) (a (r 3)) (a (r 4)) := by
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

end Work.Diff.GE
