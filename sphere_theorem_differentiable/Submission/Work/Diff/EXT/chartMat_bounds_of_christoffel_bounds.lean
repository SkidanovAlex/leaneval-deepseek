import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.chartData_contDiffOn
import Submission.Work.Diff.EXT.chartMatBoundsDefs
import Submission.Work.Diff.EXT.chartMatBoundsAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.EXT.chartMat_bounds_of_christoffel_bounds`

The chart matrix `y ↦ chartMat G x₀ t y` of a family of metrics satisfies the metric-compatibility
identity

`∂_m g_{ij} = Σ_p (Γ^p_{mi} g_{pj} + Γ^p_{mj} g_{ip})`

in the chart at `x₀` (`Work.Diff.EXT.chartMat_fderiv_basis`).  Differentiating this identity `k`
times expresses the `(k+1)`-st spatial derivative of `g_{ij}` in terms of the `k`-jets of the
Christoffel entries `Γ` and of the `k`-jets of the components `g_{ij}` themselves; the Leibniz rule
then gives, by induction on `k`, a uniform bound for every iterated spatial derivative of the chart
matrix, assuming only a uniform bound on `g` itself together with uniform bounds for the jets of
`Γ`.  This is the lemma proved here.

The induction is carried out in `Submission.Work.Diff.EXT.chartMatBoundsAux`; the present file
supplies the bookkeeping (the uniform bounds for `Γ` at every order and the induction on `k`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace Work.Diff.EXT

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- The coefficient function `chartCoef` written with the Gram matrix instead of the chart matrix
(they are the same function of the chart coordinate). -/
lemma chartCoef_eq_GramM_sum (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j m : Fin (Module.finrank ℝ E)) (y : E) :
    chartCoef (I := I) (M := M) G x₀ t i j m y
      = ∑ p : Fin (Module.finrank ℝ E),
          (Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i
              * Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) p j
            + Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j
              * Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i p) := by
  unfold chartCoef
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [show cmMatEntry (I := I) (M := M) G x₀ t p j y
        = Work.Diff.GE.GramM (I := I) G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) p j from rfl,
      show cmMatEntry (I := I) (M := M) G x₀ t i p y
        = Work.Diff.GE.GramM (I := I) G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i p from rfl,
      show cGamEntry (I := I) (M := M) G x₀ t p m i y
        = Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i from rfl,
      show cGamEntry (I := I) (M := M) G x₀ t p m j y
        = Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j from rfl]

theorem chartMat_bounds_of_christoffel_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target) (hU : UniqueDiffOn ℝ K)
    (hGam : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j l : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.cGam (G t) x₀
          (Work.Diff.EXT.pt (I := I) x₀ y') l i j) y‖ ≤ C)
    (hU0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (i j : Fin (Module.finrank ℝ E)),
      |Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i j| ≤ C)
    (hderiv : ∀ t ∈ Set.Ico σ T, ∀ y ∈ (extChartAt I x₀).target,
      ∀ (i j m : Fin (Module.finrank ℝ E)),
      fderiv ℝ (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y
          (Module.finBasis ℝ E m)
        = ∑ p : Fin (Module.finrank ℝ E),
            (Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m i
                * Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) p j
              + Work.Diff.GE.cGam (G t) x₀ (Work.Diff.EXT.pt (I := I) x₀ y) p m j
                * Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i p))
    (hsm : ∀ t ∈ Set.Ico σ T, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) K)
    (hsmG : ∀ t ∈ Set.Ico σ T, ∀ (i j l : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.cGam (G t) x₀
        (Work.Diff.EXT.pt (I := I) x₀ y') l i j) K) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j)
          y‖ ≤ C := by
  classical
  -- uniform bounds for the Christoffel entries at every order
  choose Pg hPg using hGam
  -- the metric-compatibility identity in the vocabulary of `chartCoef`
  have hderiv' : ∀ t ∈ Set.Ico σ T, ∀ y ∈ (extChartAt I x₀).target,
      ∀ (i j m : Fin (Module.finrank ℝ E)),
      fderiv ℝ (cmMatEntry (I := I) (M := M) G x₀ t i j) y (Module.finBasis ℝ E m)
        = chartCoef (I := I) (M := M) G x₀ t i j m y := by
    intro t ht y hy i j m
    have h := hderiv t ht y hy i j m
    rw [chartCoef_eq_GramM_sum]
    exact h
  -- the induction: uniform bounds up to order `k`
  have key : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k' (cmMatEntry (I := I) (M := M) G x₀ t i j) y‖ ≤ C := by
    intro k
    induction k with
    | zero =>
        obtain ⟨C0, hC00, hC0⟩ := hU0
        refine ⟨C0, hC00, ?_⟩
        intro t ht y hy k' hk' i j
        rw [show k' = 0 from Nat.le_zero.mp hk', norm_iteratedFDeriv_zero]
        exact le_trans (le_of_eq (by simp [cmMatEntry, Real.norm_eq_abs])) (hC0 t ht y hy i j)
    | succ k ih =>
        obtain ⟨C, hC0, hCb⟩ := ih
        -- a single uniform bound for the Christoffel entries of order `≤ k`
        set P : ℝ := ∑ k' ∈ Finset.range (k + 1), Pg k' with hPdef
        have hP0 : 0 ≤ P := by
          rw [hPdef]
          exact Finset.sum_nonneg (fun i _ => (hPg i).1)
        have hPb : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ k' ≤ k,
            ∀ (l i j : Fin (Module.finrank ℝ E)),
            ‖iteratedFDeriv ℝ k' (cGamEntry (I := I) (M := M) G x₀ t l i j) y‖ ≤ P := by
          intro t ht y hy k' hk' l i j
          have h1 : ‖iteratedFDeriv ℝ k' (cGamEntry (I := I) (M := M) G x₀ t l i j) y‖
              ≤ Pg k' := (hPg k').2 t ht y hy i j l
          have h2 : Pg k' ≤ P := by
            rw [hPdef]
            exact Finset.single_le_sum (fun i _ => (hPg i).1)
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hk'))
          exact le_trans h1 h2
        obtain ⟨C', hC'0, hC'b⟩ :=
          cmMatEntry_succ_bound (I := I) (M := M) G σ T x₀ K hKt hderiv' k C P hC0 hP0 hCb hPb
        refine ⟨max C C', le_trans hC0 (le_max_left _ _), ?_⟩
        intro t ht y hy k' hk' i j
        rcases Nat.lt_or_eq_of_le hk' with hlt | heq
        · exact le_trans (hCb t ht y hy k' (Nat.lt_succ_iff.mp hlt) i j) (le_max_left _ _)
        · subst heq
          exact le_trans (hC'b t ht y hy i j) (le_max_right _ _)
  intro k
  obtain ⟨C, hC0, hC⟩ := key k
  exact ⟨C, hC0, fun t ht y hy i j => by
    simpa only [cmMatEntry] using hC t ht y hy k le_rfl i j⟩

end Work.Diff.EXT
