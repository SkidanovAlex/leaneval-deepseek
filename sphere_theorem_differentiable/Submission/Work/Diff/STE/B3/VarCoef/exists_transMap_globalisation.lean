import Mathlib
import Submission.Work.Diff.STE.D.bump_smul_smooth
import Submission.Work.Diff.STE.D.transMap_interior_contDiffAt
import Submission.Work.Diff.STE.B3.VarCoef.exists_contDiff_tsupport_eq_one_nhds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Diff.STE.B3.VarCoef

/-! ## Globalisation of a locally smooth function, preserving its first jet on a compact set

The two results of this file are the analytic engine of the chart-transition globalisation
`Work.Diff.STE.B3.VarCoef.exists_transMap_globalisation`.

`exists_contDiff_fderiv_eqOn` is the abstract statement: a function which is `C^∞` on an *open*
set `U` and whose domain of interest `K ⊆ U` is *compact* agrees on `K`, together with its first
derivative, with a *globally* `C^∞` function.  The point is that the naive device (`multiply by a
smooth bump which is `1` on `K` and supported in `U`) loses the derivative information at the
boundary `∂K` of `K`: the factor `fderiv φ` need not vanish there.  The cure is to use a bump
which is `1` on a whole *neighbourhood* of `K`, which is exactly what
`Work.Diff.STE.B3.VarCoef.exists_contDiff_tsupport_eq_one_nhds` (a strengthening of the bump of a
compact subset of an open set) provides. -/

/-- **Globalisation of a function smooth on a neighbourhood of a compact set, with its first jet.**

If `f` is `C^∞` on the open set `U`, the compact set `K` is contained in `U`, then `f` agrees on
`K` with a globally `C^∞` function `T`, and moreover `T` and `f` have the same derivative at every
point of `K`.

Proof: let `φ` be a bump which is `1` on a neighbourhood of `K` and has `tsupport φ ⊆ U`
(`Work.Diff.STE.B3.VarCoef.exists_contDiff_tsupport_eq_one_nhds`), and set `T := φ • f`.  The
product is `C^∞`: at a point of `U` it is the product of two smooth germs, at a point outside `U`
the first factor vanishes on a neighbourhood.  On `K` the equation `T = f` is immediate, and for
the derivative the Leibniz rule (`fderiv_fun_smul`) gives
`fderiv T = φ · fderiv f + (fderiv φ).smulRight (f)`, whose second term vanishes because
`fderiv φ = 0` on `K`. -/
theorem exists_contDiff_fderiv_eqOn
    {ι : Type*} [Fintype ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K U : Set (ι → ℝ)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : (ι → ℝ) → F) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) :
    ∃ T : (ι → ℝ) → F,
      ContDiff ℝ (⊤ : ℕ∞) T ∧
      (∀ y ∈ K, T y = f y) ∧
      (∀ y ∈ K, fderiv ℝ T y = fderiv ℝ f y) := by
  classical
  obtain ⟨φ, hφsm, hφtsup, hφ1, hφ0⟩ :=
    exists_contDiff_tsupport_eq_one_nhds (E := ι → ℝ) hK hU hKU
  refine ⟨fun y => φ y • f y, ?_, ?_, ?_⟩
  · -- `φ • f` is globally `C^∞`
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ U
    · exact hφsm.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hy))
    · -- outside `U` the bump vanishes on a neighbourhood
      have hny : y ∉ tsupport φ := fun h => hy (hφtsup h)
      have hev : φ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hny
      have hev2 : (fun z => φ z • f z) =ᶠ[𝓝 y] (fun _ => (0 : F)) :=
        hev.mono (fun z hz => by simp [hz])
      exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hev2
  · -- the values agree on `K`
    intro y hy
    show φ y • f y = f y
    rw [hφ1 y hy, one_smul]
  · -- the derivatives agree on `K`
    intro y hy
    have hyU : y ∈ U := hKU hy
    have hφd : DifferentiableAt ℝ φ y := (hφsm.contDiffAt (x := y)).differentiableAt (by simp)
    have hfd : DifferentiableAt ℝ f y :=
      (hf.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
    rw [fderiv_fun_smul hφd hfd, hφ1 y hy, hφ0 y hy]
    simp

/-- **The chart transition `z ↦ coord_i (pt_l z)` globalises with its first jet**.

This is the form of `Work.Diff.STE.B3.VarCoef.exists_contDiff_eqOn_tMapFun_swap` in which the set on
which the globalisation is required is the support of a compactly supported coefficient `c` (rather
than a weight-defined region `Ω`), and in which the *first derivative* is required to match as
well.

`z ↦ coord (x₀ i) (pt l z)` is `C^∞` at every point of the open set
`U := {z | flatToE (x₀ l) z ∈ interior (chart-l target) ∧ pt_l z ∈ chart-i source}`
(`Work.Diff.STE.D.transMap_interior_contDiffAt`), and `U` is open because `flatToE (x₀ l)` is
continuous (so the first condition is open) and `pt_l` is smooth, hence continuous, on the
interior of the chart-`l` target.  The hypotheses say that `tsupport c` is compact and contained in
`U`, so `Work.Diff.STE.B3.VarCoef.exists_contDiff_fderiv_eqOn` applies. -/
theorem exists_transMap_globalisation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l i : ι₀)
    {c : (Fin (Module.finrank ℝ E) → ℝ) → ℝ}
    (hcK : IsCompact (tsupport c))
    (hcU : tsupport c ⊆ {z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈ interior ((extChartAt I (D.x₀ l)).target) ∧
        D.pt l z ∈ (extChartAt I (D.x₀ i)).source}) :
    ∃ T : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) T ∧
      (∀ z ∈ tsupport c, T z = Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l z)) ∧
      (∀ z ∈ tsupport c, fderiv ℝ T z =
        fderiv ℝ (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)) z) := by
  classical
  -- The transition map whose globalisation is required.
  let f : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ) :=
    fun w => Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)
  -- The open set on which it is smooth.
  let U : Set (Fin (Module.finrank ℝ E) → ℝ) :=
    {z | Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈ interior ((extChartAt I (D.x₀ l)).target) ∧
      D.pt l z ∈ (extChartAt I (D.x₀ i)).source}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    -- the chart-`l` condition is open: `flatToE (x₀ l)` is continuous
    have h1 : (Work.Diff.STE.flatToE (I := I) (D.x₀ l)) ⁻¹'
        interior ((extChartAt I (D.x₀ l)).target) ∈ 𝓝 z :=
      (isOpen_interior.preimage
        (Work.Diff.STE.D.contDiff_flatToE (I := I) (M := M) (D.x₀ l)).continuous).mem_nhds hz.1
    -- the chart-`i` condition is open: `pt l` is continuous on the interior of the chart-`l` target
    have h2 : (D.pt l) ⁻¹' ((extChartAt I (D.x₀ i)).source) ∈ 𝓝 z :=
      ((Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) (M := M) D l z
          hz.1).continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_source (I := I) (D.x₀ i)).mem_nhds hz.2)
    exact Filter.inter_mem h1 h2
  -- smoothness of the transition on `U`
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f U := by
    intro z hz
    exact (Work.Diff.STE.D.transMap_interior_contDiffAt (I := I) D i l z hz.1 hz.2).contDiffWithinAt
  obtain ⟨T, hTsm, hTval, hTder⟩ :=
    exists_contDiff_fderiv_eqOn (ι := Fin (Module.finrank ℝ E)) hcK hU hcU f hf
  exact ⟨T, hTsm, fun z hz => hTval z hz, fun z hz => hTder z hz⟩

end Work.Diff.STE.B3.VarCoef
