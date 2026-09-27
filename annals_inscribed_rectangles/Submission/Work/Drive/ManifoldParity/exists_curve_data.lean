import Mathlib
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.ManifoldParity.InterSetDefs
import Submission.Work.Drive.ManifoldParity.TangentialDefs
import Submission.Work.Drive.ManifoldParity.exists_local_graph
import Submission.Work.Drive.ManifoldParity.InterSetFlowDefs

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


namespace Work.Drive.ManifoldParity

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option backward.isDefEq.respectTransparency false

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Work.Drive.Ctop M]

/-- At a point of the intersection set, the chart at the common image point contains both images. -/
theorem exists_curve_data_chartRegion_self (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) {x : Work.Drive.Amb 4}
    (heq : D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x)) :
    x ∈ Work.Drive.chartRegion (D (Work.Drive.sqPart x)) D N := by
  rw [Work.Drive.mem_chartRegion]
  have hmem : ∀ y : M, y ∈ (Work.Drive.chr y).source := fun y => by
    rw [Work.Drive.chr, ← extChartAt_source (I := 𝓡 4) y]
    exact mem_extChartAt_source _
  exact ⟨hmem _, by rw [heq]; exact hmem _⟩

omit [T2Space M] [IsManifold (𝓡 4) Work.Drive.Ctop M] in
/-- A point of a chart region has its image in the source of the chart at the centre. -/
theorem exists_curve_data_extChartAt_source (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M) {p : M} {x : Work.Drive.Amb 4}
    (hx : x ∈ Work.Drive.chartRegion p D N) :
    D (Work.Drive.sqPart x) ∈ (extChartAt (𝓡 4) p).source := by
  have h := hx.1
  rwa [Work.Drive.chr, ← extChartAt_source (I := 𝓡 4) p] at h

/-- **The derivative of the charted difference map through `Lfun`.**  At a meeting point the two
change-of-coordinates maps coincide, so the derivative of `chartDiff` is the (fixed, invertible)
change of coordinates applied to the chart-independent difference of the two manifold derivatives. -/
theorem exists_curve_data_fderiv_chartDiff (p : M) (D : EuclideanSpace ℝ (Fin 2) → M)
    (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop D)
    (hN : ContMDiff (𝓡 3) (𝓡 4) Work.Drive.Ctop N)
    {x : Work.Drive.Amb 4} (hx : x ∈ Work.Drive.chartRegion p D N)
    (heq : D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x)) (v : Work.Drive.Amb 4) :
    fderiv ℝ (Work.Drive.chartDiff p D N) x v =
      tangentCoordChange (𝓡 4) (D (Work.Drive.sqPart x)) p (D (Work.Drive.sqPart x))
        (Work.Drive.Lfun D N x v) := by
  rw [Work.Drive.fderiv_chartDiff_apply p D N hD hN hx]
  have htc : tangentCoordChange (𝓡 4) (D (Work.Drive.sqPart x)) p (D (Work.Drive.sqPart x)) =
      tangentCoordChange (𝓡 4) (N (Work.Drive.cbPart x)) p (N (Work.Drive.cbPart x)) := by
    rw [← heq]
  rw [htc, ← map_sub, ← Work.Drive.Lfun_apply]

theorem exists_curve_data {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Work.Drive.Ctop M]
    (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Work.Drive.Ctop D)
    (hN : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Work.Drive.Ctop N)
    (htrans : ∀ x : Work.Drive.Amb 4, x ∈ Submission.Drive.unitBox 4 →
      D (Work.Drive.sqPart x) = N (Work.Drive.cbPart x) →
      LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) D (Work.Drive.sqPart x)).toLinearMap ⊔
        LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) N (Work.Drive.cbPart x)).toLinearMap = ⊤)
    {x : Work.Drive.Amb 4} (hx : x ∈ Work.Drive.interSet D N) :
    ∃ (i : Fin 5) (γ : ℝ → Work.Drive.Amb 4) (R : Set (Work.Drive.Amb 4)),
      IsOpen R ∧ x ∈ R ∧ ContDiff ℝ Work.Drive.Ctop γ ∧ (∀ t, (γ t) i = t) ∧ γ (x i) = x ∧
      (∀ y ∈ R, (D (Work.Drive.sqPart y) = N (Work.Drive.cbPart y) ↔ y = γ (y i))) ∧
      (∀ y ∈ R, D (Work.Drive.sqPart y) = N (Work.Drive.cbPart y) →
        Work.Drive.Lfun D N y (fderiv ℝ γ (y i) 1) = 0) := by
  obtain ⟨hbox, heq⟩ := hx
  have hxreg : x ∈ Work.Drive.chartRegion (D (Work.Drive.sqPart x)) D N :=
    exists_curve_data_chartRegion_self D N heq
  have hsurj : Function.Surjective
      (fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N) x) :=
    Work.Drive.chartDiff_surjective_of_transverse (D (Work.Drive.sqPart x)) D N hD hN hxreg heq
      (htrans x hbox heq)
  obtain ⟨i, hi⟩ := Work.Drive.exists_domRestrict_surjective hsurj
  obtain ⟨δ, ρ, η, hδ, hρ, hηcd, hηi, hηx, hchar⟩ :=
    Work.Drive.exists_local_graph (D (Work.Drive.sqPart x)) D N hD hN hxreg heq i hi
  let γ : ℝ → Work.Drive.Amb 4 := fun t => t • EuclideanSpace.single i 1 + η t
  have hγ : γ = fun t : ℝ => t • EuclideanSpace.single i 1 + η t := rfl
  let R : Set (Work.Drive.Amb 4) :=
    {y | |y i - x i| < δ ∧ ‖y - y i • EuclideanSpace.single i 1 - η (y i)‖ < ρ}
  have hR : R = {y : Work.Drive.Amb 4 |
      |y i - x i| < δ ∧ ‖y - y i • EuclideanSpace.single i 1 - η (y i)‖ < ρ} := rfl
  refine ⟨i, γ, R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR]
    refine IsOpen.inter ?_ ?_
    · have hcont : Continuous fun y : Work.Drive.Amb 4 => |y i - x i| := by
        have h3 : (fun y : Work.Drive.Amb 4 => y i - x i) =
            ⇑(Work.Drive.coordL i) - (fun _ => x i) := by
          funext y; simp
        have h4 : Continuous fun y : Work.Drive.Amb 4 => y i - x i := by
          rw [h3]
          exact (Work.Drive.coordL i).continuous.sub continuous_const
        exact h4.abs
      exact isOpen_lt hcont continuous_const
    · have hcont : Continuous fun y : Work.Drive.Amb 4 =>
          ‖y - y i • EuclideanSpace.single i 1 - η (y i)‖ := by
        refine Continuous.norm ?_
        refine Continuous.sub ?_ ?_
        · refine Continuous.sub continuous_id ?_
          have h3 : (fun y : Work.Drive.Amb 4 => y i • EuclideanSpace.single i 1) =
              ⇑(Work.Drive.coordL i) • (fun _ => EuclideanSpace.single i (1:ℝ)) := by
            funext y; simp
          rw [h3]
          exact (Work.Drive.coordL i).continuous.smul continuous_const
        · have h3 : (fun y : Work.Drive.Amb 4 => η (y i)) =
              η ∘ ⇑(Work.Drive.coordL i) := by funext y; simp
          rw [h3]
          exact hηcd.continuous.comp (Work.Drive.coordL i).continuous
      exact isOpen_lt hcont continuous_const
  · rw [hR]
    refine ⟨?_, ?_⟩
    · rw [sub_self, abs_zero]; exact hδ
    · have h0 : x - x i • EuclideanSpace.single i 1 - η (x i) = 0 := by
        rw [hηx, sub_self]
      rw [h0, norm_zero]; exact hρ
  · rw [hγ]
    exact (contDiff_id.smul contDiff_const).add hηcd
  · intro t
    rw [hγ]
    simp [hηi]
  · rw [hγ]
    show x i • EuclideanSpace.single i 1 + η (x i) = x
    rw [hηx]
    abel
  · intro y hy
    rw [hR] at hy
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨-, hiff⟩ := hchar y hy1 hy2
    rw [hγ]
    exact hiff
  · intro y hy hyeq
    rw [hR] at hy
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨hyreg, hiff⟩ := hchar y hy1 hy2
    have hyγ : y = y i • EuclideanSpace.single i 1 + η (y i) := hiff.mp hyeq
    have hγy : γ (y i) = y := by rw [hγ]; exact hyγ.symm
    have hε : 0 < δ - |y i - x i| := by linarith [hy1]
    have hev : (fun t : ℝ => Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N (γ t))
        =ᶠ[𝓝 (y i)] (fun _ : ℝ => (0 : Work.Drive.Tgt 4)) := by
      show ∀ᶠ t in 𝓝 (y i), Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N (γ t) = 0
      rw [Metric.eventually_nhds_iff]
      refine ⟨δ - |y i - x i|, hε, ?_⟩
      intro t ht
      rw [Real.dist_eq] at ht
      have htδ : |t - x i| < δ := by
        have h1 : |t - x i| ≤ |t - y i| + |y i - x i| := by
          have h2 := abs_add_le (t - y i) (y i - x i)
          rwa [show t - y i + (y i - x i) = t - x i by ring] at h2
        linarith
      have hc : (γ t) i = t := by rw [hγ]; simp [hηi]
      have hz : ‖γ t - γ t i • EuclideanSpace.single i 1 - η (γ t i)‖ < ρ := by
        rw [hc]
        have h0 : γ t - t • EuclideanSpace.single i 1 - η t = 0 := by
          have hγt : γ t = t • EuclideanSpace.single i 1 + η t := rfl
          rw [hγt, add_sub_cancel_left, sub_self]
        rw [h0, norm_zero]; exact hρ
      obtain ⟨hreg, hiff'⟩ := hchar (γ t) (by rw [hc]; exact htδ) hz
      have hcoord : γ t = γ t i • EuclideanSpace.single i 1 + η (γ t i) := by
        rw [hc, hγ]
      exact (Work.Drive.chartDiff_eq_zero_iff hreg).mpr (hiff'.mpr hcoord)
    have hfd : fderiv ℝ (fun t : ℝ =>
        Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N (γ t)) (y i) = 0 := by
      have h0 : fderiv ℝ (fun _ : ℝ => (0 : Work.Drive.Tgt 4)) (y i) = 0 := by simp
      exact (Filter.EventuallyEq.fderiv_eq hev).trans h0
    have hγcd : ContDiff ℝ Work.Drive.Ctop γ := by
      rw [hγ]; exact (contDiff_id.smul contDiff_const).add hηcd
    have hγdiff : DifferentiableAt ℝ γ (y i) := (hγcd.differentiable (by simp)).differentiableAt
    have hcda : DifferentiableAt ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N) y := by
      have hopen : IsOpen (Work.Drive.chartRegion (D (Work.Drive.sqPart x)) D N) :=
        Work.Drive.isOpen_chartRegion _ D N hD.continuous hN.continuous
      have hcd : ContDiffOn ℝ Work.Drive.Ctop
          (Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N)
          (Work.Drive.chartRegion (D (Work.Drive.sqPart x)) D N) :=
        Work.Drive.contDiffOn_chartDiff _ D N hD hN
      exact (hcd.contDiffAt (hopen.mem_nhds hyreg)).differentiableAt (by simp)
    have hcda' : DifferentiableAt ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N)
        (γ (y i)) := hγy.symm ▸ hcda
    have hcomp : fderiv ℝ (fun t : ℝ =>
        Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N (γ t)) (y i)
        = (fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N) (γ (y i))).comp
          (fderiv ℝ γ (y i)) := by
      have h := fderiv_comp (𝕜 := ℝ) (f := γ) (x := y i)
        (g := Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N) hcda' hγdiff
      simpa only [Function.comp_def] using h
    have h2 : (fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N) (γ (y i)))
        (fderiv ℝ γ (y i) 1) = 0 := by
      have h1 : (fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N) (γ (y i))).comp
          (fderiv ℝ γ (y i)) = 0 := by
        rw [← hcomp]; exact hfd
      have hh := congrArg (fun L : ℝ →L[ℝ] Work.Drive.Tgt 4 => L 1) h1
      simpa using hh
    have hfdEq : fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N) (γ (y i))
        = fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N) y := by rw [hγy]
    have hzero' : fderiv ℝ (Work.Drive.chartDiff (D (Work.Drive.sqPart x)) D N) y
        (fderiv ℝ γ (y i) 1) = 0 := by
      rw [← hfdEq]; exact h2
    have hTeq := exists_curve_data_fderiv_chartDiff (D (Work.Drive.sqPart x)) D N hD hN hyreg hyeq
      (fderiv ℝ γ (y i) 1)
    rw [hzero'] at hTeq
    have hsrc : D (Work.Drive.sqPart y) ∈
        (extChartAt (𝓡 4) (D (Work.Drive.sqPart x))).source :=
      exists_curve_data_extChartAt_source D N hyreg
    have hinj : Function.Injective (tangentCoordChange (𝓡 4) (D (Work.Drive.sqPart y))
        (D (Work.Drive.sqPart x)) (D (Work.Drive.sqPart y))) :=
      Work.Drive.tangentCoordChange_injective
        ⟨mem_extChartAt_source (I := 𝓡 4) (D (Work.Drive.sqPart y)), hsrc⟩
    exact hinj (by rw [hTeq.symm, map_zero])

end Work.Drive.ManifoldParity
