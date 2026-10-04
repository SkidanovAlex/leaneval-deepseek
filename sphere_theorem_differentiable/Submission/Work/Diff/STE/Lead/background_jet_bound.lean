import Mathlib
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.D.psi.abs_coord_factor_le
import Submission.Work.Diff.EXT.chartRic_partial_jet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

/-
ROUTE (a compactness statement, no Sobolev input).

The chart matrix of the FIXED background metric `g₀` in the chart at `D.x₀ i`,
`y ↦ Work.Diff.STE.D.chartMatOf g₀.inner (D.x₀ i) y`, is `C^∞` on the chart target (for the metric
`g₀`: `Work.Diff.EXT.chartMatFun` smoothness `Work.Diff.EXT.contDiffAt_chartMatFun`, or
`Work.Diff.STE.B3.frameMat_contMDiffAt_of_chartData` with
`Work.Diff.STE.D.chartData_metric` for `g₀`), so its value, its first `fderiv` and its second
`fderiv` are continuous there.

On the closed flat ball `‖z‖ ≤ D.σ i` (compact, finite-dimensional) the three continuous functions
`z ↦ |chartMat ... z a b|`, `z ↦ |(fderiv ... ) (bB p)|`, `z ↦ |(fderiv (fderiv ...)) (bB p)(bB q)|`
are bounded by a single constant independent of `i`, `a`, `b`, `p`, `q`, `z` — because `ι₀` and
`Fin (Module.finrank ℝ E)` are finite (finite supremum over indices, then the supremum over the
compact ball: the `IsCompact.exists_bound_of_continuousOn` / `exists_isMinOn` idiom, as in
`Work.Diff.STE.B3.dens_lower_bound_chart` and `Work.Diff.STE.D.psi.abs_coord_factor_le`; the flat
ball is contained in the chart target by `D.htarget` since `σ i ≤ 2 σ i`).

### Implementation notes

The whole content is packaged into the private helper `jet_bound_compact`, which is stated for an
arbitrary smooth-on-a-compact-set matrix-valued function `Φ : E → MatE` and an arbitrary compact set
`K ⊆ E`; the target theorem is then the finite supremum over `i : ι₀` of the resulting constants.

Inside `jet_bound_compact` the bound is read off from the single continuous function
`z ↦ ‖Φ z‖ + ∑_{a b} ( ∑_p |∂_{bB p}(Φ · a b)| + ∑_{p q} |∂_{bB p} ∂_{bB q}(Φ · a b)| )`,
whose compactness bound dominates every one of the three families of quantities (each term of the
sum is nonnegative, and the first family is controlled by the first summand together with the
sup-norm inequalities `|Φ z a b| ≤ ‖Φ z a‖ ≤ ‖Φ z‖`).  The second and third families are precisely
the terms appearing in the sum, so no identification of iterated `fderiv`s is needed.
-/

private lemma le_sum_sum₂ {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ → ℝ)
    (hf : ∀ i j, 0 ≤ f i j) (i : ι) (j : κ) : f i j ≤ ∑ a, ∑ b, f a b := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b, f a b)
    (fun a _ => Finset.sum_nonneg (fun b _ => hf a b)) (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun b => f i b) (fun b _ => hf i b) (Finset.mem_univ j)

/-- **The uniform jet bound on a compact set, for a function that is smooth on that set.**

For a compact `K`, a function `Φ : E → MatE` that is `C^∞` at every point of `K`, there is a
constant `B ≥ 0` bounding, uniformly on `K`, the entries of `Φ`, its first coordinate derivatives
and its second coordinate derivatives (in the directions of the basis `bB`). -/
private theorem jet_bound_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {Φ : E → Work.Diff.EXT.MatE (E := E)} {K : Set E} (hK : IsCompact K)
    (hΦ : ∀ y ∈ K, ContDiffAt ℝ (⊤ : ℕ∞) Φ y) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ K,
      (∀ a b : Fin (Module.finrank ℝ E), |Φ z a b| ≤ B) ∧
      (∀ (a b p : Fin (Module.finrank ℝ E)),
        |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p)| ≤ B) ∧
      (∀ (a b p q : Fin (Module.finrank ℝ E)),
        |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
          (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)| ≤ B) := by
  classical
  have hc0 : ContinuousOn (fun z => Φ z) K :=
    fun z hz => ((hΦ z hz).continuousAt).continuousWithinAt
  have hc1 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun z => fderiv ℝ (fun y : E => Φ y a b) z) K := by
    intro a b z hz
    have hF : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => Φ y a b) z :=
      contDiffAt_pi.mp (contDiffAt_pi.mp (hΦ z hz) a) b
    have h2 : ContDiffAt ℝ (2 : ℕ∞) (fun y : E => Φ y a b) z :=
      hF.of_le (WithTop.coe_le_coe.mpr le_top)
    exact ((h2.fderiv_right (m := 1) (by norm_num)).continuousAt).continuousWithinAt
  have hc2 : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun z => fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z) K := by
    intro a b z hz
    have hF : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : E => Φ y a b) z :=
      contDiffAt_pi.mp (contDiffAt_pi.mp (hΦ z hz) a) b
    have h3 : ContDiffAt ℝ (3 : ℕ∞) (fun y : E => Φ y a b) z :=
      hF.of_le (WithTop.coe_le_coe.mpr le_top)
    exact (((h3.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).continuousAt).continuousWithinAt
  have hs2 : ∀ a b p : Fin (Module.finrank ℝ E),
      ContinuousOn (fun z => |(fderiv ℝ (fun y : E => Φ y a b) z)
        (Work.Diff.EXT.bB (E := E) p)|) K := by
    intro a b p
    show ContinuousOn ((fun r : ℝ => |r|) ∘
      ((ContinuousLinearMap.apply ℝ ℝ (Work.Diff.EXT.bB (E := E) p)) ∘
        (fun z => fderiv ℝ (fun y : E => Φ y a b) z))) K
    exact continuous_abs.comp_continuousOn
      ((ContinuousLinearMap.apply ℝ ℝ (Work.Diff.EXT.bB (E := E) p)).continuous.comp_continuousOn
        (hc1 a b))
  have hs3 : ∀ a b p q : Fin (Module.finrank ℝ E),
      ContinuousOn (fun z => |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
        (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|) K := by
    intro a b p q
    show ContinuousOn ((fun r : ℝ => |r|) ∘
      (((ContinuousLinearMap.apply ℝ ℝ (Work.Diff.EXT.bB (E := E) q)).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (Work.Diff.EXT.bB (E := E) p))) ∘
        (fun z => fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z))) K
    exact continuous_abs.comp_continuousOn
      (((ContinuousLinearMap.apply ℝ ℝ (Work.Diff.EXT.bB (E := E) q)).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (Work.Diff.EXT.bB (E := E) p))).continuous.comp_continuousOn
        (hc2 a b))
  have hΓ : ContinuousOn (fun z => ‖Φ z‖ + ∑ a, ∑ b,
      ((∑ p, |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p)|)
       + (∑ p, ∑ q, |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
            (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|))) K := by
    refine hc0.norm.add ?_
    refine continuousOn_finsetSum _ (fun a _ => ?_)
    refine continuousOn_finsetSum _ (fun b _ => ?_)
    exact (continuousOn_finsetSum _ (fun p _ => hs2 a b p)).add
      (continuousOn_finsetSum _ (fun p _ => continuousOn_finsetSum _ (fun q _ => hs3 a b p q)))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΓ
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro z hz
  have hΓz : ‖Φ z‖ + ∑ a, ∑ b,
      ((∑ p, |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p)|)
       + (∑ p, ∑ q, |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
            (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|)) ≤ max C 0 := by
    have h1 := hC z hz
    have h2 : 0 ≤ ‖Φ z‖ + ∑ a, ∑ b,
      ((∑ p, |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p)|)
       + (∑ p, ∑ q, |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
            (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|)) := by positivity
    rw [Real.norm_of_nonneg h2] at h1
    exact le_trans h1 (le_max_left C 0)
  have hsub : (∑ a, ∑ b,
      ((∑ p, |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p)|)
       + (∑ p, ∑ q, |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
            (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|))) ≤ max C 0 :=
    le_trans (le_add_of_nonneg_left (norm_nonneg _)) hΓz
  have h0le : ‖Φ z‖ ≤ max C 0 :=
    le_trans (le_add_of_nonneg_right (by positivity)) hΓz
  refine ⟨?_, ?_, ?_⟩
  · intro a b
    rw [← Real.norm_eq_abs]
    exact le_trans (le_trans (norm_le_pi_norm (Φ z a) b) (norm_le_pi_norm (Φ z) a)) h0le
  · intro a b p
    have hA : (∑ p', |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p')|)
        ≤ (∑ p', |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p')|)
          + (∑ p', ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
              (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')|) :=
      le_add_of_nonneg_right (by positivity)
    have hT : (∑ p', |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p')|)
          + (∑ p', ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
              (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')|)
        ≤ ∑ a', ∑ b', ((∑ p', |(fderiv ℝ (fun y : E => Φ y a' b') z) (Work.Diff.EXT.bB (E := E) p')|)
          + (∑ p', ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a' b') y) z)
              (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')|)) :=
      le_sum_sum₂ (f := fun a' b' =>
          (∑ p', |(fderiv ℝ (fun y : E => Φ y a' b') z) (Work.Diff.EXT.bB (E := E) p')|)
          + (∑ p', ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a' b') y) z)
              (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')|))
        (fun a' b' => by positivity) a b
    calc |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p)|
        ≤ ∑ p', |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p')| :=
          Finset.single_le_sum
            (f := fun p' => |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p')|)
            (fun p' _ => abs_nonneg _) (Finset.mem_univ p)
      _ ≤ _ := hA
      _ ≤ _ := hT
      _ ≤ max C 0 := hsub
  · intro a b p q
    have hA : (∑ p', ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
            (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')|)
        ≤ (∑ p', |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p')|)
          + (∑ p', ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
              (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')|) :=
      le_add_of_nonneg_left (by positivity)
    have hT : (∑ p', |(fderiv ℝ (fun y : E => Φ y a b) z) (Work.Diff.EXT.bB (E := E) p')|)
          + (∑ p', ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
              (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')|)
        ≤ ∑ a', ∑ b', ((∑ p', |(fderiv ℝ (fun y : E => Φ y a' b') z) (Work.Diff.EXT.bB (E := E) p')|)
          + (∑ p', ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a' b') y) z)
              (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')|)) :=
      le_sum_sum₂ (f := fun a' b' =>
          (∑ p', |(fderiv ℝ (fun y : E => Φ y a' b') z) (Work.Diff.EXT.bB (E := E) p')|)
          + (∑ p', ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a' b') y) z)
              (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')|))
        (fun a' b' => by positivity) a b
    calc |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
          (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)|
        ≤ ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
            (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q')| :=
          Finset.single_le_sum
            (f := fun q' => |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
              (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q')|)
            (fun q' _ => abs_nonneg _) (Finset.mem_univ q)
      _ ≤ ∑ p', ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
            (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')| :=
          Finset.single_le_sum
            (f := fun p' => ∑ q', |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E => Φ y' a b) y) z)
              (Work.Diff.EXT.bB (E := E) p') (Work.Diff.EXT.bB (E := E) q')|)
            (fun p' _ => by positivity) (Finset.mem_univ p)
      _ ≤ _ := hA
      _ ≤ _ := hT
      _ ≤ max C 0 := hsub

theorem background_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) :
    ∃ Mbg : ℝ, 0 ≤ Mbg ∧ ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i →
      (|Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i)
          (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z) a b| ≤ Mbg)
    ∧ (∀ p : Fin (Module.finrank ℝ E),
        |(fderiv ℝ (fun y : E => (Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner
              (D.x₀ i) y) a b) (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
            (Work.Diff.EXT.bB (E := E) p)| ≤ Mbg)
    ∧ (∀ p q : Fin (Module.finrank ℝ E),
        |(fderiv ℝ (fun y : E => (fderiv ℝ (fun y' : E =>
              (Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i) y') a b) y))
              (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z))
              (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)| ≤ Mbg) := by
  classical
  -- For each chart index `i`, the compactness bound on the flat `σ i`-ball.
  have key : ∀ i : ι₀, ∃ B : ℝ, 0 ≤ B ∧
      ∀ y ∈ (Work.Diff.STE.flatToE (I := I) (D.x₀ i) ''
        Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i)),
      (∀ a b : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i) y a b| ≤ B)
      ∧ (∀ (a b p : Fin (Module.finrank ℝ E)),
        |(fderiv ℝ (fun y : E => Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner
              (D.x₀ i) y a b) y) (Work.Diff.EXT.bB (E := E) p)| ≤ B)
      ∧ (∀ (a b p q : Fin (Module.finrank ℝ E)),
        |(fderiv ℝ (fun y : E => fderiv ℝ (fun y' : E =>
              Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i) y' a b) y) y)
              (Work.Diff.EXT.bB (E := E) p) (Work.Diff.EXT.bB (E := E) q)| ≤ B) := by
    intro i
    refine jet_bound_compact (Φ := Work.Diff.STE.D.chartMatOf (I := I) (M := M) g₀.inner (D.x₀ i))
      (K := Work.Diff.STE.flatToE (I := I) (D.x₀ i) ''
        Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i))
      ((isCompact_closedBall _ _).image
        (Work.Diff.STE.B3.flatToE_contDiff (I := I) (D.x₀ i)).continuous) ?_
    rintro y ⟨z, hz, rfl⟩
    have hz1 : ‖z‖ ≤ D.σ i := by
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      exact hz
    have hz2 : ‖z‖ ≤ 2 * D.σ i := by
      have := D.hσ i
      linarith
    have hy : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target :=
      D.htarget i z hz2
    have h := Work.Diff.EXT.contDiffAt_chartMatFun (I := I) (M := M) g₀ (D.x₀ i) hy
    simpa only [Work.Diff.STE.D.chartMatOf_inner] using h
  choose Bf hBfnn hBf using key
  refine ⟨∑ i, Bf i, Finset.sum_nonneg (fun i _ => hBfnn i), ?_⟩
  intro i a b z hz
  have hmem : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz
  have hle : Bf i ≤ ∑ j, Bf j :=
    Finset.single_le_sum (f := Bf) (fun j _ => hBfnn j) (Finset.mem_univ i)
  obtain ⟨h1, h2, h3⟩ := hBf i (Work.Diff.STE.flatToE (I := I) (D.x₀ i) z)
    ⟨z, hmem, rfl⟩
  exact ⟨le_trans (h1 a b) hle, fun p => le_trans (h2 a b p) hle,
    fun p q => le_trans (h3 a b p q) hle⟩

end Work.Diff.STE.Lead
