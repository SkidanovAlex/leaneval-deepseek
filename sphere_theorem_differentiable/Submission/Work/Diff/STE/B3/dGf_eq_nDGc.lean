/-
# The honest first jet of the coordinate-frame chart matrix

`Work.Diff.STE.B3.dGf D h j z c i k` is the honest first partial derivative
`∂_c (Gf · i k)` of the coordinate-frame chart matrix of the section `h`, while
`Work.Diff.STE.B3.nDGc D j z V dV` is the *nominal* first jet of the frame-change formula
`Gf = Finvf · V · Finvfᵀ` with the orthonormal-frame chart matrix and its jet as variables.

This module proves that the two agree when `V` and `dV` are the orthonormal-frame chart matrix
`Mf` of the section and its first jet `dMf`:

`dGf D h j z c i k = nDGc D j z (Mf z) (dMf z) c i k`.

The proof is the product rule: near `z` the frame-change identity
`Gf y i k = Σ_{ab} Finvf y i a · Mf y a b · Finvf y k b` holds (`tmNom_Gf_eventuallyEq`), so the
left-hand side depends only on the germ at `z` (`pdR_congr`), the derivative is pulled into the two
finite sums (`pdR_fun_sum_at`), and each of the three factors is differentiated by the Leibniz rule
(`pdR_mul_at`).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.LowJetDefs
import Submission.Work.Diff.STE.B3.tmNom_aux
import Submission.Work.Diff.STE.B3.transport_tame_leibniz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Matrix ContDiff
open LeanEval.Geometry.SphereTheorem Submission.Diff

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1600000

theorem dGf_eq_nDGc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j)
    (c i k : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.B3.dGf (I := I) (M := M) D h j z c i k
      = Work.Diff.STE.B3.nDGc (I := I) (M := M) D j z
          (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)
          (Work.Diff.STE.B3.dMf (I := I) (M := M) D h j z) c i k := by
  classical
  unfold Work.Diff.STE.B3.dGf
  -- the flat coordinate lies in the chart target at `z`
  have hzt : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
    D.htarget j z hz
  -- smoothness of the two factors of the frame-change identity at `z`
  have hFf : ∀ p q : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun y => Finvf (I := I) (M := M) D j y p q) z :=
    fun p q => tmNom_Finvf_ContDiffAt (I := I) (M := M) D j p q hz
  have hMf : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun y => Mf (I := I) (M := M) D h j y a b) z := by
    intro a b
    have hU := tmNom_eventually_mem_target (I := I) (M := M) D j hzt
    have hsum : ContDiffAt ℝ ∞ (fun y => ∑ p, ∑ q,
        Ff (I := I) (M := M) D j y a p * Gf (I := I) (M := M) D h j y p q
          * Ff (I := I) (M := M) D j y b q) z :=
      ContDiffAt.sum (fun p _ => ContDiffAt.sum (fun q _ =>
        ((Ff_contDiffAt (I := I) (M := M) D j a p hzt).mul
          (Gf_contDiffAt (I := I) (M := M) D h hsmooth j p q hzt)).mul
          (Ff_contDiffAt (I := I) (M := M) D j b q hzt)))
    refine hsum.congr_of_eventuallyEq ?_
    filter_upwards [hU] with y hy
    exact Mf_eq_of_target (I := I) (M := M) D h j a b hy
  -- replace `Gf` by the frame-change expression in a neighbourhood of `z`
  rw [pdR_congr (tmNom_Gf_eventuallyEq (I := I) (M := M) D h j hz i k) c]
  -- differentiability of the summands
  have hdiffa : ∀ a : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun y => ∑ b, Finvf (I := I) (M := M) D j y i a
        * Mf (I := I) (M := M) D h j y a b
        * Finvf (I := I) (M := M) D j y k b) z := by
    intro a
    have hc : ContDiffAt ℝ ∞ (fun y => ∑ b, Finvf (I := I) (M := M) D j y i a
        * Mf (I := I) (M := M) D h j y a b
        * Finvf (I := I) (M := M) D j y k b) z :=
      ContDiffAt.sum (fun b _ => ((hFf i a).mul (hMf a b)).mul (hFf k b))
    exact hc.differentiableAt (by simp)
  have hdiffb : ∀ a b : Fin (Module.finrank ℝ E), DifferentiableAt ℝ
      (fun y => Finvf (I := I) (M := M) D j y i a
        * Mf (I := I) (M := M) D h j y a b
        * Finvf (I := I) (M := M) D j y k b) z :=
    fun a b => (((hFf i a).mul (hMf a b)).mul (hFf k b)).differentiableAt (by simp)
  -- pull the derivative into the two finite sums
  have step1 : Work.Diff.STE.pdR c
        (fun y => ∑ a, ∑ b, Finvf (I := I) (M := M) D j y i a
          * Mf (I := I) (M := M) D h j y a b
          * Finvf (I := I) (M := M) D j y k b) z
      = ∑ a, ∑ b, Work.Diff.STE.pdR c
          (fun y => Finvf (I := I) (M := M) D j y i a
            * Mf (I := I) (M := M) D h j y a b
            * Finvf (I := I) (M := M) D j y k b) z := by
    rw [pdR_fun_sum_at c hdiffa]
    exact Finset.sum_congr rfl (fun a _ => pdR_fun_sum_at c (fun b => hdiffb a b))
  rw [step1]
  -- unfold the nominal jet
  simp only [nDGc, dMf]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  -- the Leibniz rule for the triple product `Finvf · Mf · Finvf`
  have hf1 : DifferentiableAt ℝ
      (fun y => Finvf (I := I) (M := M) D j y i a) z := (hFf i a).differentiableAt (by simp)
  have hf2 : DifferentiableAt ℝ
      (fun y => Mf (I := I) (M := M) D h j y a b) z := (hMf a b).differentiableAt (by simp)
  have hf3 : DifferentiableAt ℝ
      (fun y => Finvf (I := I) (M := M) D j y k b) z := (hFf k b).differentiableAt (by simp)
  rw [pdR_mul_at (f := fun y => Finvf (I := I) (M := M) D j y i a
          * Mf (I := I) (M := M) D h j y a b)
        (g := fun y => Finvf (I := I) (M := M) D j y k b) c (hf1.mul hf2) hf3,
      pdR_mul_at (f := fun y => Finvf (I := I) (M := M) D j y i a)
        (g := fun y => Mf (I := I) (M := M) D h j y a b) c hf1 hf2]
  ring

end Work.Diff.STE.B3
