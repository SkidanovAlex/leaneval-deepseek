import Mathlib
import Submission.Work.Diff.EXT.ConnCov.ChartTowerDefs
import Submission.Work.Diff.EXT.ConnCov.reactJetsKit
import Submission.Work.Diff.EXT.ConnCov.rmChartTower_jets
import Submission.Work.Diff.EXT.gramInv_jets
import Submission.Work.Diff.EXT.gramInv_bounds_of_gram_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform jet bounds for the chart Christoffel symbols

`Work.Diff.GE.chrCoord G x₀ n a b t y` is the chart Christoffel symbol `Γ^n_{ab}` of the metric
`G t` in the coordinate frame of the chart at `x₀`, i.e. the inverse-Gram contraction
`∑_p γ^{np} koszulPair_{abp}` of the Koszul pairings.

The target `Work.Diff.EXT.ConnCov.chrCoord_jets_bound` shows that the chart jets of `chrCoord` of
order `≤ L` are uniformly bounded on a compact `K'` inside the chart target and on
`[T/2, T)`, as soon as the chart jets of the *chart matrix* `chartMat` of order `≤ L + 1` are, and
the metrics `G t` are quadratically comparable with the initial metric `G 0` (`hmet`).

The two factors of the contraction are handled separately:

* the *Koszul* factor `sKz (dJet1 (G t) x₀ ·) a b r` is a linear combination of first chart
  derivatives of the chart matrix, so its jets of order `≤ L` are controlled by the jets of the
  chart matrix of order `≤ L + 1` (this is the finitary `JBu` statement
  `Work.Diff.EXT.ConnCov.sKz_dJet1_jBu`);
* the *inverse Gram* factor `γ^{pr}`: the comparison `hmet` bounds the Gram matrix below on the
  compact `K'` (`Work.Diff.EXT.gram_det_bound`), whence `Work.Diff.EXT.gramInv_jets` bounds all
  jets of `GramInv` of order `≤ L` by a single constant.

Products and finite sums of `JBu` families are again `JBu` families
(`Work.Diff.EXT.CBound.JBu.mul`, `JBu.sum`), the pointwise identity
`∑_r γ^{pr} koszulPair_{abr} = chrCoord` holds on the chart target
(`Work.Diff.EXT.koszulPair_eq_sKz`), and `JBu.congrOn` transports the result to `chrCoord`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Work.Diff.EXT.CBound

namespace Work.Diff.EXT.ConnCov

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-! ## The chart matrix in the coordinate frame is the Gram matrix on the chart -/

/-- The chart matrix of `G t` at the chart coordinate `y` is the Gram matrix of the coordinate
frame of the chart at `x₀` at the point `pt x₀ y`. -/
lemma chartMat_eq_GramM_pt
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (y : E)
    (i j : Fin (Module.finrank ℝ E)) :
    Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y i j
      = Work.Diff.GE.GramM (I := I) G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) i j :=
  rfl

/-! ## Two `JBu` families

`Work.Diff.EXT.CBound.JBu σ T K k A` bundles the smoothness of `A t` at the points of `K` with
uniform bounds for all iterated Fréchet derivatives of order `≤ k`.  We build the two factors of
the Christoffel symbol as `JBu` families of order `L` (resp. `L + 1`). -/

/-- A component of the chart matrix, as a `JBu` family of order `k`, from a common bound for the
chart jets of order `≤ k`. -/
lemma chartMat_jBu_le
    (G : ℝ → Submission.Diff.SMet I M) (T Cg : ℝ) (x₀ : M) (K : Set E) (k : ℕ)
    (hCg0 : 0 ≤ Cg) (hKt : K ⊆ (extChartAt I x₀).target)
    (hbd : ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ k →
      ∀ (i j : Fin (Module.finrank ℝ E)), ∀ y ∈ K,
        ‖iteratedFDeriv ℝ m
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ Cg)
    (a b : Fin (Module.finrank ℝ E)) :
    JBu (T / 2) T K k (fun t y => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y a b) := by
  refine ⟨fun t ht y hy => contDiffAt_component_of_chartMat (I := I) (M := M) G x₀ t ?_ a b,
    fun _ => Cg, fun _ => hCg0, ?_⟩
  · exact Work.Diff.EXT.contDiffAt_chartMatFun (I := I) (M := M) (G t) x₀ (hKt hy)
  · intro t ht y hy m hm
    exact hbd t ht m hm a b y hy

/-- A component of the inverse chart Gram matrix, as a `JBu` family of order `k`, from a common
bound `B` for its jets of order `≤ k`. -/
lemma gramInv_jBu_const
    (G : ℝ → Submission.Diff.SMet I M) (σ T B : ℝ) (x₀ : M) (K : Set E) (k : ℕ)
    (hB0 : 0 ≤ B) (hKt : K ⊆ (extChartAt I x₀).target)
    (hbd : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ m ≤ k,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.GramInv (I := I) G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j) y‖ ≤ B)
    (i j : Fin (Module.finrank ℝ E)) :
    JBu σ T K k (fun t y => Work.Diff.GE.GramInv (I := I) G x₀ t
      (Work.Diff.EXT.pt (I := I) x₀ y) i j) := by
  exact ⟨fun t ht y hy => GramInv_contDiffAt_of_target (I := I) (M := M) G x₀ t (hKt hy) i j,
    fun _ => B, fun _ => hB0, fun t ht y hy m hm => hbd t ht y hy m hm i j⟩

/-! ## The Christoffel symbol is the inverse-Gram contraction of the Koszul pairings -/

/-- **The pointwise identity**: on the chart target, the chart Christoffel symbol
`chrCoord G x₀ p a b t (pt x₀ y)` is the contraction `∑_r γ^{pr} koszulPair_{abr}` of the inverse
Gram matrix with the Koszul pairings, and the Koszul pairing is the scalar expression
`sKz (dJet1 (G t) x₀ y)` in the first chart jets of the metric. -/
lemma chrCoord_eq_sum_gramInv_sKz
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (p a b : Fin (Module.finrank ℝ E)) :
    (∑ r : Fin (Module.finrank ℝ E), Work.Diff.GE.GramInv (I := I) G x₀ t
        (Work.Diff.EXT.pt (I := I) x₀ y) p r
      * Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) a b r)
      = Work.Diff.GE.chrCoord (I := I) G x₀ p a b t (Work.Diff.EXT.pt (I := I) x₀ y) := by
  rw [Work.Diff.GE.chrCoord]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [show Work.Diff.GE.koszulPair (I := I) G x₀ a b r t (Work.Diff.EXT.pt (I := I) x₀ y)
      = Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) a b r from
    Work.Diff.EXT.koszulPair_eq_sKz (I := I) (M := M) (G t) x₀ hy a b r]

/-! ## The target theorem -/

theorem chrCoord_jets_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (L : ℕ) (x₀ : M) (K' : Set E) (hK'c : IsCompact K') (hK't : K' ⊆ (extChartAt I x₀).target)
    (hjet : ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ m : ℕ, m ≤ L + 1 →
      ∀ (i j : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ m
          (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ Cg) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ J : ℕ, J ≤ L →
      ∀ (p a b : Fin (Module.finrank ℝ E)), ∀ y ∈ K',
        ‖iteratedFDeriv ℝ J (fun y' : E => Work.Diff.GE.chrCoord (I := I) G x₀ p a b t
            (Work.Diff.EXT.pt (I := I) x₀ y')) y‖ ≤ Cc := by
  classical
  obtain ⟨Cg, hCg0, hCg⟩ := hjet
  -- ### the determinant of the Gram matrix is bounded below on `K'`
  obtain ⟨c, hcpos, hcdet⟩ :=
    Work.Diff.EXT.gram_det_bound (I := I) (M := M) G T C hT hC hmet x₀ K' hK'c hK't
  -- ### jet bounds for the Gram matrix of order `≤ L`, from the chart jets of `chartMat`
  have hG : ∀ m ≤ L, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K',
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ m (fun y' : E => Work.Diff.GE.GramM (I := I) G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j) y‖ ≤ C := by
    intro m hm
    refine ⟨Cg, hCg0, fun t ht y hy i j => ?_⟩
    have heq : (fun y' : E => Work.Diff.GE.GramM (I := I) G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j)
        = (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) := by
      funext y'
      exact (chartMat_eq_GramM_pt (I := I) (M := M) G x₀ t y' i j).symm
    rw [heq]
    exact hCg t ht m (by omega) i j y hy
  -- ### smoothness of the Gram matrix entries in the chart coordinate
  have hsmG : ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K', ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramM (I := I) G x₀ t
        (Work.Diff.EXT.pt (I := I) x₀ y') i j) y :=
    fun t _ht y hy i j => GramM_contDiffAt_of_target (I := I) (M := M) G x₀ t (hK't hy) i j
  -- ### a single constant bounding all jets of `GramInv` of order `≤ L`
  obtain ⟨Bgi, hBgi0, hBgi⟩ :=
    Work.Diff.EXT.gramInv_jets (I := I) (M := M) G (T / 2) T x₀ K' L hK't
      ⟨c, hcpos, hcdet⟩ hsmG hG
  have hInvJ : ∀ (i j : Fin (Module.finrank ℝ E)),
      JBu (T / 2) T K' L (fun t y => Work.Diff.GE.GramInv (I := I) G x₀ t
        (Work.Diff.EXT.pt (I := I) x₀ y) i j) :=
    fun i j => gramInv_jBu_const (I := I) (M := M) G (T / 2) T Bgi x₀ K' L hBgi0 hK't
      (fun t ht y hy m hm i' j' => hBgi t ht y hy m hm i' j') i j
  -- ### the Koszul factor, a `JBu` family of order `L`, from chart jets of order `≤ L + 1`
  have hMatJ : ∀ (a b : Fin (Module.finrank ℝ E)),
      JBu (T / 2) T K' (L + 1)
        (fun t y => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y a b) :=
    fun a b => chartMat_jBu_le (I := I) (M := M) G T Cg x₀ K' (L + 1) hCg0 hK't
      (fun t ht m hm i j y hy => hCg t ht m hm i j y hy) a b
  have hKzJ : ∀ (a b r : Fin (Module.finrank ℝ E)),
      JBu (T / 2) T K' L
        (fun t y => Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 (G t) x₀ y) a b r) :=
    fun a b r => sKz_dJet1_jBu (I := I) (M := M) G T x₀ K' L hK't hMatJ a b r
  -- ### the Christoffel symbol itself, as a `JBu` family of order `L`
  have hMain : ∀ (p a b : Fin (Module.finrank ℝ E)),
      JBu (T / 2) T K' L
        (fun t y => Work.Diff.GE.chrCoord (I := I) G x₀ p a b t
          (Work.Diff.EXT.pt (I := I) x₀ y)) := by
    intro p a b
    refine (JBu.sum (fun r => (hInvJ p r).mul (hKzJ a b r))).congrOn hK't ?_
    intro t y hy
    exact chrCoord_eq_sum_gramInv_sKz (I := I) (M := M) G x₀ t hy p a b
  choose B hB0 hB using fun q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
      × Fin (Module.finrank ℝ E) => (hMain q.1 q.2.1 q.2.2).2
  refine ⟨∑ q : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
    ∑ j ∈ Finset.range (L + 1), B q j, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun q _ => Finset.sum_nonneg (fun j _ => hB0 q j))
  · intro t ht J hJ p a b y hy
    refine le_trans (hB (p, a, b) t ht y hy J hJ) ?_
    refine le_trans (Finset.single_le_sum (fun j _ => hB0 (p, a, b) j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hJ))) ?_
    exact Finset.single_le_sum (fun q _ => Finset.sum_nonneg (fun j _ => hB0 q j))
      (Finset.mem_univ (p, a, b))

end Work.Diff.EXT.ConnCov
