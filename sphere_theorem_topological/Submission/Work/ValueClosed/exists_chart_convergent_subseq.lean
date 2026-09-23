import Mathlib
import Submission.Work.ValueClosed.Defs

namespace Work.ValueClosed

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic Submission.GlobalExp Submission.InjRadius Submission.GExpJointPt
open Submission.ChartConnection Submission.ChartBounds Submission.GExpFlow

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Extraction of a convergent subsequence of tangent data.**  For any sequence of points `p n` of
the compact manifold `M` and unit tangent vectors `ξ n ∈ T_{p n}M`, there are a chart centre `z₀`, a
strictly monotone `φ`, a limit point `pstar` in that chart, chart coordinates `y : ℕ → E` and a limit
`y₀ : E` such that `p (φ k) → pstar`, `y k → y₀`, the vectors are the coordinates of the `ξ`'s,
`ξ (φ k) = frameVector z₀ (p (φ k)) (y k)`, and the limit vector is again unit,
`‖frameVector z₀ pstar y₀‖ = 1`.

Route: a finite cover of `M` by compact pieces contained in chart sources
(`Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt`, which needs
`LocallyCompactSpace M` — derivable in this context), a pigeonhole to land infinitely often in one
piece, then `IsCompact.tendsto_subseq` **on the chart coordinates in the model space `E`** (not on
`M`: the project has no `FirstCountableTopology` instance on `M`): once for the coordinates of the
points (in the compact image of the piece) and once for the coordinates `y k` of the tangent vectors
(which are bounded because `‖ξ n‖ = 1` and `exists_chartGram_bounds` bounds the chart Gram form from
below on the compact piece, `chartGram z₀ (p k) (y k) (y k) = ‖ξ k‖² = 1` via
`GExpFlow.norm_frameVector`); the unit norm in the limit follows from `GExpFlow.norm_frameVector` plus
`ChartBounds.continuousAt_chartGram_prod` (no `hmet` needed). -/
theorem exists_chart_convergent_subseq
    (p : ℕ → M) (ξ : (n : ℕ) → TangentSpace I (p n)) (hunit : ∀ n, ‖ξ n‖ = 1) :
    ∃ (z₀ : M) (pstar : M) (y₀ : E) (φ : ℕ → ℕ),
      StrictMono φ ∧ pstar ∈ (chartAt H z₀).source ∧
      Tendsto (fun k => p (φ k)) atTop (𝓝 pstar) ∧
      ∃ y : ℕ → E, Tendsto y atTop (𝓝 y₀) ∧
        (∀ k, ξ (φ k) = frameVector (I := I) z₀ (p (φ k)) (y k)) ∧
        ‖frameVector (I := I) z₀ pstar y₀‖ = 1 := by
  classical
  haveI : LocallyCompactSpace M := inferInstance
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  -- ### Step 1: a finite cover of `M` by compact pieces inside chart sources
  obtain ⟨n, zc, Z, hZc, hZsrc, hcover⟩ :=
    Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt (I := I) (M := M)
  -- ### Step 2: the pigeonhole
  have hmem : ∀ k : ℕ, p k ∈ ⋃ i : Fin n, Z i := fun k => hcover (mem_univ k)
  have hpigeon : ∃ i : Fin n, ∀ N : ℕ, ∃ k > N, p k ∈ Z i := by
    by_contra hcon
    push Not at hcon
    choose N hN using hcon
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hmem (Finset.univ.sup N + 1))
    exact hN i (Finset.univ.sup N + 1)
      (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))) hi
  obtain ⟨i₀, hi₀⟩ := hpigeon
  obtain ⟨φ, hφ, hφmem⟩ := Nat.exists_strictMono_subsequence (P := fun k => p k ∈ Z i₀) hi₀
  -- ### Step 3: the chart and its compact piece
  have hKc : IsCompact (Z i₀) := hZc i₀
  have hKsrc : Z i₀ ⊆ (chartAt H (zc i₀)).source := hZsrc i₀
  have hsub : Z i₀ ⊆ (extChartAt I (zc i₀)).source := fun q hq => by simpa using hKsrc hq
  have hsubT : ∀ q ∈ Z i₀, (extChartAt I (zc i₀)) q ∈ (extChartAt I (zc i₀)).target :=
    fun q hq => PartialEquiv.map_source _ (hsub hq)
  have hsymm : ContinuousOn (fun x : E => (extChartAt I (zc i₀)).symm x)
      (extChartAt I (zc i₀)).target :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) (zc i₀)).continuousOn
  -- ### Step 4: the chart Gram form is bounded below on the piece
  have hKne : (Z i₀).Nonempty := ⟨p (φ 0), hφmem 0⟩
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ :=
    exists_chartGram_bounds (I := I) (zc i₀) hKc hKne hKsrc
  -- ### Step 5: the coordinate vectors of the unit vectors are bounded
  have hgram1 : ∀ k : ℕ, chartGram (I := I) (zc i₀) (p (φ k))
      ((trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ (p (φ k)) (ξ (φ k)))
      ((trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ (p (φ k)) (ξ (φ k)))
      = 1 := by
    intro k
    rw [chartGram_clm (I := I) (hsub (hφmem k)) (ξ (φ k)) (ξ (φ k)),
      real_inner_self_eq_norm_sq, hunit (φ k)]
    norm_num
  have hyB : ∀ k : ℕ,
      ‖(trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
        (p (φ k)) (ξ (φ k))‖ ≤ Real.sqrt (1 / lam) := by
    intro k
    have h := (hbnd (p (φ k)) (hφmem k)
      ((trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
        (p (φ k)) (ξ (φ k)))).1
    rw [hgram1 k] at h
    have h2 : ‖(trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
        (p (φ k)) (ξ (φ k))‖ ^ 2 ≤ 1 / lam := by
      rw [le_div_iff₀ hlam, mul_comm]
      exact h
    calc ‖(trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
          (p (φ k)) (ξ (φ k))‖
        = Real.sqrt (‖(trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
          (p (φ k)) (ξ (φ k))‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (1 / lam) := Real.sqrt_le_sqrt h2
  -- ### Step 6: compactness extraction in the chart coordinates
  have hKEc : IsCompact ((extChartAt I (zc i₀)) '' Z i₀) :=
    hKc.image_of_continuousOn ((continuousOn_extChartAt (I := I) (zc i₀)).mono hsub)
  have hmemK : ∀ k : ℕ, ((extChartAt I (zc i₀)) (p (φ k)),
      (trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ (p (φ k)) (ξ (φ k)))
      ∈ ((extChartAt I (zc i₀)) '' Z i₀) ×ˢ
        Metric.closedBall (0 : E) (Real.sqrt (1 / lam)) :=
    fun k => ⟨⟨p (φ k), hφmem k, rfl⟩, by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hyB k⟩
  obtain ⟨⟨x₀, y₀⟩, hzy, ψ, hψ, hlim⟩ := IsCompact.tendsto_subseq
    (hKEc.prod (isCompact_closedBall (0 : E) (Real.sqrt (1 / lam))))
    (x := fun k => ((extChartAt I (zc i₀)) (p (φ k)),
      (trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ (p (φ k)) (ξ (φ k))))
    hmemK
  obtain ⟨q₀, hq₀K, hq₀eq⟩ := hzy.1
  have hq₀src : q₀ ∈ (extChartAt I (zc i₀)).source := hsub hq₀K
  -- componentwise convergence of the chart coordinates
  have hxc : Tendsto (fun k => (extChartAt I (zc i₀)) (p (φ (ψ k)))) atTop (𝓝 x₀) :=
    (continuous_fst.tendsto (x₀, y₀)).comp hlim
  have hyc : Tendsto (fun k => (trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
      (p (φ (ψ k))) (ξ (φ (ψ k)))) atTop (𝓝 y₀) :=
    (continuous_snd.tendsto (x₀, y₀)).comp hlim
  -- the base points converge in `M`
  have hqc : Tendsto (fun k => p (φ (ψ k))) atTop (𝓝 q₀) := by
    have hxc' : Tendsto (fun k => (extChartAt I (zc i₀)) (p (φ (ψ k)))) atTop
        (𝓝 ((extChartAt I (zc i₀)) q₀)) := by rw [hq₀eq]; exact hxc
    have htend : Tendsto (fun k => (extChartAt I (zc i₀)) (p (φ (ψ k)))) atTop
        (𝓝[(extChartAt I (zc i₀)).target] ((extChartAt I (zc i₀)) q₀)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hxc', Filter.Eventually.of_forall fun k =>
        hsubT _ (hφmem (ψ k))⟩
    have h1 : Tendsto (fun k => (extChartAt I (zc i₀)).symm
        ((extChartAt I (zc i₀)) (p (φ (ψ k))))) atTop
        (𝓝 ((extChartAt I (zc i₀)).symm ((extChartAt I (zc i₀)) q₀))) :=
      (hsymm.continuousWithinAt (hsubT q₀ hq₀K)).tendsto.comp htend
    have h1' : Tendsto (fun k => (extChartAt I (zc i₀)).symm
        ((extChartAt I (zc i₀)) (p (φ (ψ k))))) atTop (𝓝 q₀) := by
      rwa [PartialEquiv.left_inv _ hq₀src] at h1
    exact Tendsto.congr' (Filter.Eventually.of_forall fun k =>
      PartialEquiv.left_inv _ (hsub (hφmem (ψ k)))) h1'
  -- ### Step 7: the limiting coordinate vector is again unit
  have hgramlim : Tendsto (fun k => chartGram (I := I) (zc i₀) (p (φ (ψ k)))
      ((trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
        (p (φ (ψ k))) (ξ (φ (ψ k))))
      ((trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
        (p (φ (ψ k))) (ξ (φ (ψ k))))) atTop
      (𝓝 (chartGram (I := I) (zc i₀) q₀ y₀ y₀)) := by
    have hcont := continuousAt_chartGram_prod (I := I) (zc i₀) (hKsrc hq₀K) y₀
    have hpair : Tendsto (fun k => (p (φ (ψ k)),
        (trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
          (p (φ (ψ k))) (ξ (φ (ψ k))))) atTop (𝓝 (q₀, y₀)) :=
      (Prod.tendsto_iff (fun k => (p (φ (ψ k)),
        (trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
          (p (φ (ψ k))) (ξ (φ (ψ k))))) (q₀, y₀)).mpr ⟨hqc, hyc⟩
    exact hcont.tendsto.comp hpair
  have hgrameq : chartGram (I := I) (zc i₀) q₀ y₀ y₀ = 1 := by
    refine tendsto_nhds_unique hgramlim ?_
    have hfun : (fun k => chartGram (I := I) (zc i₀) (p (φ (ψ k)))
        ((trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
          (p (φ (ψ k))) (ξ (φ (ψ k))))
        ((trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
          (p (φ (ψ k))) (ξ (φ (ψ k))))) = fun _ => (1 : ℝ) := by
      funext k
      exact hgram1 (ψ k)
    rw [hfun]
    exact tendsto_const_nhds
  have hnormlim : ‖frameVector (I := I) (zc i₀) q₀ y₀‖ = 1 := by
    rw [norm_frameVector, hgrameq, Real.sqrt_one]
  -- ### Step 8: the tangent vectors are the coordinates of the `ξ`'s
  have hframe : ∀ k : ℕ, ξ (φ (ψ k)) = frameVector (I := I) (zc i₀) (p (φ (ψ k)))
      ((trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
        (p (φ (ψ k))) (ξ (φ (ψ k)))) := by
    intro k
    exact (Trivialization.symmL_continuousLinearMapAt
      (e := trivializationAt E (TangentSpace I) (zc i₀)) (R := ℝ)
      (by simpa using hsub (hφmem (ψ k))) (ξ (φ (ψ k)))).symm
  -- ### Assembly
  exact ⟨zc i₀, q₀, y₀, fun k => φ (ψ k), hφ.comp hψ, hKsrc hq₀K, hqc,
    (fun k => (trivializationAt E (TangentSpace I) (zc i₀)).continuousLinearMapAt ℝ
      (p (φ (ψ k))) (ξ (φ (ψ k)))), hyc, hframe, hnormlim⟩

end Work.ValueClosed
