import Mathlib
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.koszul
import Submission.Work.Diff.GE.cGram_eq_sum_gramInv
import Submission.Work.Diff.GE.cGram_chrB_eq_koszulPair

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- **Symmetry of the Koszul pairing in its first two (lowered) slots.**

`koszulPair a b c = ½(∂_a G_{bc} + ∂_b G_{ac} - ∂_c G_{ab})` is symmetric under `a ↔ b`: the two
first derivative terms are exchanged, and the third is unchanged because the first derivative
`mvfderiv` only sees the *function* `y' ↦ (G t).inner y' (σ_a y') (σ_b y')`, which is pointwise
symmetric in `a, b` by `(G t).symm`. -/
private lemma koszulPair_comm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (y : M)
    (a b c : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.koszulPair (I := I) G x₀ a b c t y
      = Work.Diff.GE.koszulPair (I := I) G x₀ b a c t y := by
  unfold Work.Diff.GE.koszulPair
  have h1 : (fun y' : M => (G t).inner y'
        (Work.Diff.GE.cFrame (I := I) x₀ b y') (Work.Diff.GE.cFrame (I := I) x₀ c y'))
      = (fun y' : M => (G t).inner y'
        (Work.Diff.GE.cFrame (I := I) x₀ c y') (Work.Diff.GE.cFrame (I := I) x₀ b y')) := by
    funext y'; exact (G t).symm y' _ _
  have h2 : (fun y' : M => (G t).inner y'
        (Work.Diff.GE.cFrame (I := I) x₀ c y') (Work.Diff.GE.cFrame (I := I) x₀ a y'))
      = (fun y' : M => (G t).inner y'
        (Work.Diff.GE.cFrame (I := I) x₀ a y') (Work.Diff.GE.cFrame (I := I) x₀ c y')) := by
    funext y'; exact (G t).symm y' _ _
  have h3 : (fun y' : M => (G t).inner y'
        (Work.Diff.GE.cFrame (I := I) x₀ a y') (Work.Diff.GE.cFrame (I := I) x₀ b y'))
      = (fun y' : M => (G t).inner y'
        (Work.Diff.GE.cFrame (I := I) x₀ b y') (Work.Diff.GE.cFrame (I := I) x₀ a y')) := by
    funext y'; exact (G t).symm y' _ _
  rw [h2.symm, h1.symm, h3.symm]
  ring

/-- The `ΓΓ` term of the chart curvature: the metric pairing of the two Christoffel vectors
`chrB (l) (j) = ∇_{σ_j}σ_l` and `chrB (k) (i) = ∇_{σ_i}σ_k`, expanded in the inverse Gram matrix,
with the pairing `cGram (chrB l j) (cBasis m) = koszulPair l j m` of
`Work.Diff.GE.cGram_chrB_eq_koszulPair` and the symmetry `koszulPair l j m = koszulPair j l m`
(of the first two slots) used to reach the stated order of indices.

Intended route: `Work.Diff.GE.cGram_eq_sum_gramInv` with `V = chrB (cBasis l) (cBasis j)` and
`W = chrB (cBasis k) (cBasis i)`, then `Work.Diff.GE.cGram_chrB_eq_koszulPair` twice, then the
first-slot symmetry of `koszulPair`. The symmetry is proved from `koszulPair a b c =
(1/2)*(∂_a G_{bc} + ∂_b G_{ac} - ∂_c G_{ab})`, by replacing the function
`fun y' => (G t).inner y' (σ_b y') (σ_a y')` with `fun y' => (G t).inner y' (σ_a y') (σ_b y')`
(pointwise `(G t).symm`) inside `mvfderiv`. -/
theorem cGram_chrB_chrB_eq_sum_koszul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    {y : M} (hy : y ∈ (chartAt H x₀).source) (j l i k : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.cGram (G t) x₀ y
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) j))
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) k) (Work.Diff.GE.cBasis (E := E) i))
      = ∑ m, ∑ n, Work.Diff.GE.GramInv (I := I) G x₀ t y m n
          * Work.Diff.GE.koszulPair (I := I) G x₀ j l m t y
          * Work.Diff.GE.koszulPair (I := I) G x₀ i k n t y := by
  rw [Work.Diff.GE.cGram_eq_sum_gramInv (I := I) G x₀ hy t
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) l) (Work.Diff.GE.cBasis (E := E) j))
        (Submission.ChartCurv.chrB (Submission.Diff.lcOf (G t)) x₀ y
          (Work.Diff.GE.cBasis (E := E) k) (Work.Diff.GE.cBasis (E := E) i))]
  refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => ?_))
  rw [Work.Diff.GE.cGram_chrB_eq_koszulPair (I := I) G x₀ hy t l j m,
      Work.Diff.GE.cGram_chrB_eq_koszulPair (I := I) G x₀ hy t k i n]
  rw [koszulPair_comm (I := I) G x₀ t y l j m, koszulPair_comm (I := I) G x₀ t y k i n]

end Work.Diff.EXT
