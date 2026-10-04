import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.cov2RmExt_prelim
import Submission.Work.Diff.GE.dRmPhi_slotA
import Submission.Work.Diff.GE.covRm_linear_thd
import Submission.Work.Diff.GE.covRm_linear_fth
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Expansion of `∇Rm` on finite linear combinations (four slots)

`covRm g x v a b c d = (∇_v Rm)(a,b,c,d)` is `ℝ`-multilinear in its five arguments.  This file
records the specialisation needed by the gradient-estimate computation: expand slots `1, 2, 3, 5`
in a family `e : Fin n → TangentSpace I x` while slot `4` is kept fixed at the single vector `e k`.

The per-slot linearity is supplied by `covRm_linear_fst` (`cov2RmExt_prelim`), `covRm_linear_snd`
(`dRmPhi_slotA`), `covRm_linear_thd`, `covRm_linear_fth` and `Work.Diff.GE.Kato3.covRm_linear_fith`;
the passage from the two-term form to finite sums is `lin_of_binary`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.Diff.GE

open Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

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

/-- Finite-sum linearity of `covRm` in its first (direction) argument `v`. -/
private lemma covRm_sum_fst
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
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

/-- Finite-sum linearity of `covRm` in its second argument `a`. -/
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

/-- Finite-sum linearity of `covRm` in its third argument `b`. -/
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

/-- Finite-sum linearity of `covRm` in its fifth argument `d`. -/
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

/-- Expansion of `∇Rm` on finite linear combinations in slots `1, 2, 3, 5`, slot `4` fixed. -/
theorem covRm_expand_four
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) {n : ℕ}
    (e : Fin n → TangentSpace I x) (a b c d : Fin n → ℝ) (k : Fin n) :
    Submission.Diff.covRm g x (∑ i, a i • e i) (∑ j, b j • e j) (∑ l, c l • e l) (e k)
        (∑ m, d m • e m)
      = ∑ i, ∑ j, ∑ l, ∑ m,
          (a i * b j * c l * d m) *
            Submission.Diff.covRm g x (e i) (e j) (e l) (e k) (e m) := by
  rw [covRm_sum_fst hLC g x Finset.univ a e _ _ _ _]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [covRm_sum_snd hLC g x Finset.univ b e (e i) _ _ _]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [covRm_sum_thd hLC g x Finset.univ c e (e i) (e j) _ _]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [covRm_sum_fith hLC g x Finset.univ d e (e i) (e j) (e l) (e k)]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  ring

end Work.Diff.GE
