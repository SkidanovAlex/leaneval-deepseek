import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.EXT.christoffel_bounds_of_core
import Submission.Work.Diff.GE.chrB_eq_sum_gramInv
import Submission.Work.Diff.GE.cGram_chrB_eq_koszulPair
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.EXT.chartData_step_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart components of the lowered connection difference

The chart component `aComp` of the *lowered* connection difference `g_t(∇^{g_t} - ∇^{g_0})` is, by
definition, the inverse-Gram contraction of the difference of the Christoffel symbols.  The point of
this file is the *exact* algebraic identity

  `aComp G x₀ t y i j l = koszulPair G x₀ j i l t (pt x₀ y)
      - ∑ p, GramM G x₀ t (pt x₀ y) l p · cGam (G 0) x₀ (pt x₀ y) p i j`,

i.e. the lowering of the *time-`t`* Christoffel symbol `Γ(g_t)^p_{ij}` against the time-`t` Gram
matrix reproduces the Koszul pairing `⟨∇_{σ_i}σ_j, σ_l⟩ = koszulPair j i l`, the only remaining
term being the lowering of the *initial* Christoffel symbol.

The two ingredients are

* `Work.Diff.GE.chrB_eq_sum_gramInv`: the coordinate vector of `∇_{σ_i}σ_j` in the chart at `x₀` is
  the inverse Gram matrix applied to the Koszul pairings, whence the chart Christoffel symbol
  `cGam (G t) x₀ y q i j` is the `q`-th entry of that (inverse-Gram) vector;
* `GramM * GramInv = 1` (the inverse of the Gram matrix of a basis), which undoes the lowering.

The whole content is therefore matrix algebra; `koszulPair` only enters through the pairings.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

/-- The `l`-th coordinate functional against a finite linear combination over a basis. -/
lemma coord_sum_smul {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis ι ℝ V) (v : ι → ℝ) (l : ι) :
    b.coord l (∑ k, v k • b k) = v l := by
  rw [← Module.Basis.equivFun_symm_apply b v]
  exact Module.Basis.coord_equivFun_symm b l v

/-- The chart Christoffel symbol `Γ(g_t)^q_{ij}` is the `q`-th component of the inverse Gram matrix
applied to the Koszul pairings `⟨∇_{σ_i}σ_j, σ_m⟩ = koszulPair j i m`. -/
lemma cGam_eq_mulVec_koszulPair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (q i j : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) q i j
      = (Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).mulVec
          (fun m => Work.Diff.GE.koszulPair G x₀ j i m t
            (Work.Diff.EXT.pt (I := I) x₀ y)) q := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨(G t).toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hsrc : Work.Diff.EXT.pt (I := I) x₀ y ∈ (chartAt H x₀).source := by
    rw [← extChartAt_source (I := I) (x := x₀)]
    exact (extChartAt I x₀).map_target hy
  have hchr := Work.Diff.GE.chrB_eq_sum_gramInv (I := I) (M := M) G x₀ t hsrc j i
  rw [Work.Diff.GE.cGam]
  rw [hchr]
  exact coord_sum_smul (Module.finBasis ℝ E) _ q

/-- The Gram matrix of the chart frame is invertible at every chart coordinate in the target. -/
lemma gramM_mul_gramInv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)
        * Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) = 1 := by
  have hdet := Work.Diff.EXT.gramM_det_ne_zero_target (I := I) (M := M) G x₀ t hy
  rw [Work.Diff.GE.GramInv]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)

/-- **Lowering the time-`t` Christoffel symbol against the time-`t` metric gives the Koszul
pairing.**  This is the only non-trivial algebraic ingredient of `aComp_eq_koszulPair_sub`. -/
lemma gramM_mul_cGam_eq_koszulPair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j l : Fin (Module.finrank ℝ E)) :
    (∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) l p
          * Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      = Work.Diff.GE.koszulPair G x₀ j i l t (Work.Diff.EXT.pt (I := I) x₀ y) := by
  classical
  have hcgam : ∀ q, Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) q i j
      = (Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).mulVec
          (fun m => Work.Diff.GE.koszulPair G x₀ j i m t
            (Work.Diff.EXT.pt (I := I) x₀ y)) q :=
    fun q => cGam_eq_mulVec_koszulPair (I := I) (M := M) G x₀ t hy q i j
  have hright := gramM_mul_gramInv (I := I) (M := M) G x₀ t hy
  have hmain : (Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).mulVec
        ((Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).mulVec
          (fun m => Work.Diff.GE.koszulPair G x₀ j i m t
            (Work.Diff.EXT.pt (I := I) x₀ y))) l
      = Work.Diff.GE.koszulPair G x₀ j i l t (Work.Diff.EXT.pt (I := I) x₀ y) := by
    rw [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
  calc (∑ p : Fin (Module.finrank ℝ E),
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) l p
          * Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j)
      = ∑ p : Fin (Module.finrank ℝ E),
          Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) l p
            * (Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).mulVec
                (fun m => Work.Diff.GE.koszulPair G x₀ j i m t
                  (Work.Diff.EXT.pt (I := I) x₀ y)) p :=
        Finset.sum_congr rfl (fun p _ => by rw [hcgam p])
    _ = (Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).mulVec
          ((Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).mulVec
            (fun m => Work.Diff.GE.koszulPair G x₀ j i m t
              (Work.Diff.EXT.pt (I := I) x₀ y))) l := by
        simp only [Matrix.mulVec_apply, Matrix.row, dotProduct]
    _ = Work.Diff.GE.koszulPair G x₀ j i l t (Work.Diff.EXT.pt (I := I) x₀ y) := hmain

theorem aComp_eq_koszulPair_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (i j l : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.aComp G x₀ t y i j l
      = Work.Diff.GE.koszulPair G x₀ j i l t (Work.Diff.EXT.pt (I := I) x₀ y)
        - ∑ p : Fin (Module.finrank ℝ E),
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) l p
              * Work.Diff.GE.cGam (G 0) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p i j := by
  classical
  have hkey := gramM_mul_cGam_eq_koszulPair (I := I) (M := M) G x₀ t hy i j l
  rw [Work.Diff.EXT.aComp]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib, hkey]

end Work.Diff.EXT.ConnCov
