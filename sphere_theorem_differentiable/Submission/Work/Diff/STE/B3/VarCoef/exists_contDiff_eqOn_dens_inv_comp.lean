import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.B3.closure_Omega_goodSet
import Submission.Work.Diff.STE.B3.VarCoef.exists_contDiff_eqOn_dens_comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

/-- **The inverse chart density composed with the transition extends globally.**

Same setting as `Work.Diff.STE.B3.VarCoef.exists_contDiff_eqOn_dens_comp`, but for the *reciprocal*:
the function `y ↦ (√(dens_i (coord_i (pt_l y))))⁻¹` agrees on the open set
`Ω := {y | D.psi l y ≠ 0 ∧ D.ζ i (D.pt l y) ≠ 0}` with a globally `C^∞` function.

Needed for the coefficient `co` in `Work.Diff.STE.B3.VarCoef.R_Qk_chartExpr`: on `Ω`, `co` must
equal `ζ_i (pt_l y) · χ_i (coord_i (pt_l y)) · (√dens_i (coord_i (pt_l y)))⁻¹ · (frame pairings)(y)`.

Route: identical to the proved sibling — `haveI := Work.Diff.STE.B3.t2Space_of_B3Data D`,
`closure Ω ⊆ goodSet D i l`, `goodSet` is open, `closure Ω` is compact, and on `goodSet` the
composite `y ↦ √(dens i (coord i (pt l y)))` is `C^∞` and strictly positive
(`Work.Diff.STE.B3.VarCoef.dens_comp_contDiffOn` gives the smoothness,
`Work.Diff.STE.B3.dens_pos_of_mem_target` the positivity), so its reciprocal is `C^∞` there
(`ContDiffOn.inv`); conclude with `Work.Diff.STE.D.bump_smul_smooth`. -/
theorem exists_contDiff_eqOn_dens_inv_comp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l i : ι₀) :
    ∃ G : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) G ∧
      ∀ y : Fin (Module.finrank ℝ E) → ℝ,
        D.psi l y ≠ 0 → D.ζ i (D.pt l y) ≠ 0 →
        G y = (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l y))))⁻¹ := by
  classical
  -- The `B3Data` weights force `M` to be Hausdorff, so the Layer-D lemmas become available.
  haveI hT2 : T2Space M := Work.Diff.STE.B3.t2Space_of_B3Data (I := I) (M := M) D
  -- the function whose reciprocal we want to globalise
  let g : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun y =>
    Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l y)))
  -- it is `C^∞` on the good set (the proved sibling)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Work.Diff.STE.D.goodSet (I := I) (M := M) D i l) :=
    dens_comp_contDiffOn (I := I) (M := M) D l i
  -- and strictly positive there, because `dens i` is positive on the chart-`i` target
  have hne : ∀ y ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i l, g y ≠ 0 := by
    intro y hy
    have hflat : Work.Diff.STE.flatToE (I := I) (D.x₀ i)
        (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l y))
        = (extChartAt I (D.x₀ i)) (D.pt l y) :=
      Work.Diff.STE.D.flatToE_coord (I := I) (M := M) D i hy.2.1
    have hpos : 0 < D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l y)) :=
      Work.Diff.STE.B3.dens_pos_of_mem_target (I := I) D i
        (by rw [hflat]; exact interior_subset hy.2.2)
    exact (Real.sqrt_pos.mpr hpos).ne'
  -- hence so is its reciprocal
  have hginv : ContDiffOn ℝ (⊤ : ℕ∞) g⁻¹ (Work.Diff.STE.D.goodSet (I := I) (M := M) D i l) :=
    hg.inv hne
  -- the bump: `closure Ω` is compact, `goodSet` is open and contains it
  have hK : IsCompact (closure (Work.Diff.STE.D.Omega (I := I) (M := M) D i l)) :=
    Work.Diff.STE.D.isCompact_closure_Omega (I := I) (M := M) D i l
  have hU : IsOpen (Work.Diff.STE.D.goodSet (I := I) (M := M) D i l) :=
    Work.Diff.STE.D.isOpen_goodSet (I := I) (M := M) D i l
  have hKU : closure (Work.Diff.STE.D.Omega (I := I) (M := M) D i l) ⊆
      Work.Diff.STE.D.goodSet (I := I) (M := M) D i l :=
    Work.Diff.STE.B3.closure_Omega_goodSet (I := I) (M := M) D i l
  obtain ⟨φ, _hφ, hone, _hsupp, hsm⟩ :=
    Work.Diff.STE.D.bump_smul_smooth (closure (Work.Diff.STE.D.Omega (I := I) (M := M) D i l))
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i l) hK hU hKU g⁻¹ hginv
  refine ⟨fun y => φ y • g⁻¹ y, hsm, fun y hy1 hy2 => ?_⟩
  have hyO : y ∈ Work.Diff.STE.D.Omega (I := I) (M := M) D i l := ⟨hy1, hy2⟩
  have h1 : φ y = 1 := hone y (subset_closure hyO)
  show φ y • g⁻¹ y = g⁻¹ y
  simp [h1]

end Work.Diff.STE.B3.VarCoef
