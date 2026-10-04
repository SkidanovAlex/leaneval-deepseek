import Mathlib
import Submission.Work.Diff.EXT.ConnCov.dAOfTowerBoundShiAux
import Submission.Work.Diff.EXT.ConnCov.aComp_jets_of_aOfTower
import Submission.Work.Diff.EXT.ConnCov.aComp_jets_of_chartMat_jets
import Submission.Work.Diff.EXT.ConnCov.aCompCoefDef
import Submission.Work.Diff.EXT.ConnCov.aCompCoef_succ_bound
import Submission.Work.Diff.EXT.ConnCov.chartMat_self_bound_of_hmet
import Submission.Work.Diff.EXT.ConnCov.fderiv_chartMat_eq_aComp_coef
import Submission.Work.Diff.EXT.chartMat_fderiv_basis
import Submission.Work.Diff.EXT.chartMat_bounds_of_christoffel_bounds
import Submission.Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Chart jets of the metric from chart jets of the connection difference

Target: `Work.Diff.EXT.ConnCov.chartMat_jets_of_aComp_jets`.

The chart matrix `y ↦ chartMat G x₀ t y` of `G t` is the matrix of the metric `G t` in the
coordinate frame of the chart at `x₀`.  The hypothesis bounds the chart jets of `aComp`, i.e. of the
chart array of the *lowered* connection difference `g_t(∇^{g_t} − ∇^{g_0})`, up to order `K` on the
slab `[T/2,T) × K'`; the conclusion bounds all chart jets of `chartMat` up to order `K+1` there.

## Route

The point of the statement is that the *inverse* metric is never used, so no ellipticity of the
chart matrix is needed.  The metric-compatibility identity in the coordinate frame
(`Work.Diff.EXT.chartMat_fderiv_basis`)

`∂_m g_{ij} = Σ_p (Γ^p_{mi} g_{pj} + Γ^p_{mj} g_{ip})`

together with the definition of `aComp` (i.e. `Γ_{lij}(t) = aComp_{ijl} + Σ_p g_{lp}(t)Γ0^p_{ij}`,
`Work.Diff.EXT.ConnCov.aComp_eq_sKz_sub`) gives the *explicit* formula

`∂_m g_{ij} = aComp_{mij} + aComp_{mji} + Σ_p (g_{ip}Γ0^p_{mj} + g_{jp}Γ0^p_{mi})`,

in which the Christoffel symbols `Γ` of `G t` have been eliminated in favour of `aComp` and the
*fixed* Christoffel symbols `Γ0` of `G 0`; the right hand side is `aCompCoef G x₀ t i j m y` below.
Both the summands `aComp` and the *products* `g·Γ0` are differentiated by the Leibniz rule; this
gives, by induction on the order, a bound for the jets of `chartMat` assuming a bound for its value
together with uniform bounds for the jets of `aComp` of the same order and for those of `Γ0` at
every order (`cGam_zero_iteratedFDeriv_bound`, which needs no hypothesis).  The value bound comes
from the two-sided metric equivalence `hmet`.

The induction is carried out exactly as in `Work.Diff.EXT.chartMat_bounds_of_christoffel_bounds`
(whose auxiliary lemmas `norm_iteratedFDerivWithin_sum_two_mul_le'`, `sum_choose_mul_le`,
`fderiv_cmMatEntry_eq` are reused verbatim), with the Christoffel coefficient `chartCoef` replaced
by `aCompCoef`.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1500000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The core induction** of `chartMat_jets_of_aComp_jets`.

The three analytic inputs are separated out as hypotheses, so that the bookkeeping of the induction
on the order `k` (which is all that is left here) can be read on its own:

* `hbase` bounds the chart matrix itself on the slab (this is where the two-sided metric
  equivalence `hmet` is used, and it is the only place where the value of the metric matters);
* `hderiv` is the pointwise identity for the coefficient `aCompCoef` of the first derivative of the
  chart matrix (the metric-compatibility identity combined with the definition of `aComp`);
* `hstep` is the induction step: bounds of order `≤ k` for the chart matrix, for the Christoffel
  entries of the *fixed* metric `G 0` and for `aComp` give a bound of order `k+1` for the chart
  matrix (the Leibniz rule applied to `aCompCoef`).

The Christoffel jets of `G 0` are the unconditional `cGam_zero_iteratedFDeriv_bound` (no
ellipticity), and the `aComp` jets are the hypothesis `hcomp` of the target. -/
theorem chartMat_jets_of_aComp_jets_core
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T : ℝ) (hT : 0 < T)
    (x₀ : M) (K' : Set E) (hK'c : IsCompact K') (hK't : K' ⊆ (extChartAt I x₀).target)
    (K : ℕ)
    (hbase : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ t ∈ Set.Ico (T / 2) T,
      ∀ (i j : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
      |Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i j| ≤ C0)
    (hderiv : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ (extChartAt I x₀).target,
      ∀ (i j m : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
          (Module.finBasis ℝ E m)
        = aCompCoef (I := I) (M := M) G x₀ t i j m y)
    (hstep : ∀ (k : ℕ), k ≤ K → ∀ (C P Ac : ℝ), 0 ≤ C → 0 ≤ P → 0 ≤ Ac →
      (∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ k' ≤ k,
        ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k' (fun y' : E =>
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C) →
      (∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ k' ≤ k,
        ∀ (l i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k' (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y‖ ≤ P) →
      (∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ k' ≤ k,
        ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k' (fun y' : E =>
          Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ Ac) →
      ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K',
        ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ (k + 1) (fun y' : E =>
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C')
    (hcomp : ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ K →
      ∀ (i j l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ m
          (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ Cc) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ K + 1 →
      ∀ (i j : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ m
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C' := by
  classical
  obtain ⟨Cc, hCc0, hCc⟩ := hcomp
  choose Pg hPg using
    Work.Diff.EXT.cGam_zero_iteratedFDeriv_bound (I := I) (M := M) G x₀ K' hK'c hK't
  have key : ∀ k : ℕ, k ≤ K + 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K',
      ∀ k' ≤ k, ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k' (fun y' : E =>
          Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C := by
    intro k
    induction k with
    | zero =>
        intro _
        obtain ⟨C0, hC00, hC0⟩ := hbase
        refine ⟨C0, hC00, ?_⟩
        intro t ht y hy k' hk' i j
        rw [show k' = 0 from Nat.le_zero.mp hk', norm_iteratedFDeriv_zero]
        exact le_trans (le_of_eq (by rw [Real.norm_eq_abs])) (hC0 t ht i j y hy)
    | succ k ih =>
        intro hk
        have hkK : k ≤ K := by omega
        obtain ⟨C, hC0, hCb⟩ := ih (by omega)
        set P : ℝ := ∑ k' ∈ Finset.range (k + 1), Pg k' with hPdef
        have hP0 : 0 ≤ P := by
          rw [hPdef]
          exact Finset.sum_nonneg (fun i _ => (hPg i).1)
        have hPb : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ k' ≤ k,
            ∀ (l i j : Fin (Module.finrank ℝ E)),
            ‖iteratedFDeriv ℝ k' (fun y' : E => Work.Diff.GE.cGam (G 0) x₀
              (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y‖ ≤ P := by
          intro t ht y hy k' hk' l i j
          refine le_trans ((hPg k').2 y hy i j l) ?_
          rw [hPdef]
          exact Finset.single_le_sum (fun i _ => (hPg i).1)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hk'))
        have hAcb : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ k' ≤ k,
            ∀ (i j l : Fin (Module.finrank ℝ E)),
            ‖iteratedFDeriv ℝ k' (fun y' : E =>
              Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ Cc :=
          fun t ht y hy k' hk' i j l => hCc t ht k' (le_trans hk' hkK) i j l y hy
        obtain ⟨C', hC'0, hC'b⟩ := hstep k hkK C P Cc hC0 hP0 hCc0 hCb hPb hAcb
        refine ⟨max C C', le_trans hC0 (le_max_left _ _), ?_⟩
        intro t ht y hy k' hk' i j
        rcases Nat.lt_or_eq_of_le hk' with hlt | heq
        · exact le_trans (hCb t ht y hy k' (Nat.lt_succ_iff.mp hlt) i j) (le_max_left _ _)
        · subst heq
          exact le_trans (hC'b t ht y hy i j) (le_max_right _ _)
  obtain ⟨C, hC0, hC⟩ := key (K + 1) le_rfl
  exact ⟨C, hC0, fun t ht m hm i j y hy => hC t ht y hy m hm i j⟩

theorem chartMat_jets_of_aComp_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (x₀ : M) (K' : Set E) (hK'c : IsCompact K') (hK't : K' ⊆ (extChartAt I x₀).target)
    (K : ℕ)
    (hcomp : ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ K →
      ∀ (i j l : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ m
          (fun y' : E => Work.Diff.EXT.aComp (I := I) (M := M) G x₀ t y' i j l) y‖ ≤ Cc) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ K + 1 →
      ∀ (i j : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ m
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C' := by
  -- The three analytic inputs are the bound on the values of the chart matrix
  -- (`Work.Diff.EXT.ConnCov.chartMat_self_bound_of_hmet`), the identity for the coefficient of its
  -- first derivative (`Work.Diff.EXT.ConnCov.fderiv_chartMat_eq_aComp_coef`) and the induction step
  -- (`Work.Diff.EXT.ConnCov.aCompCoef_succ_bound`).
  refine chartMat_jets_of_aComp_jets_core (I := I) (M := M) G T hT x₀ K' hK'c hK't K ?_ ?_ ?_ hcomp
  · exact Work.Diff.EXT.ConnCov.chartMat_self_bound_of_hmet (I := I) (M := M) G T C hT hC hmet
      x₀ K' hK'c hK't
  · intro t ht y hy i j m
    rw [aCompCoef_eq_sum]
    exact Work.Diff.EXT.ConnCov.fderiv_chartMat_eq_aComp_coef (I := I) (M := M) G x₀ t hy i j m
  · intro k hk C P Ac hC' hP' hAc' hCb hPb hAcb
    refine Work.Diff.EXT.ConnCov.aCompCoef_succ_bound (I := I) (M := M) G (T / 2) T x₀ K' hK't
      (fun t ht y hy i j m => ?_) k C P Ac hC' hP' hAc' hCb hPb hAcb
    rw [aCompCoef_eq_sum]
    exact Work.Diff.EXT.ConnCov.fderiv_chartMat_eq_aComp_coef (I := I) (M := M) G x₀ t hy i j m

end Work.Diff.EXT.ConnCov
