import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.B3.closure_Omega_goodSet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

open scoped Topology

/-- **Smoothness of the chart density composed with the transition map, on the good set.**

On the good set `goodSet D i l` the point `pt_l z` lies in the source of the chart `i` and its
chart-`i` flat coordinate `coord_i (pt_l z)` lies in the *interior* of the chart-`i` target.  Hence

* `z ↦ coord_i (pt_l z)` is `C^∞` at such a point (`Work.Diff.STE.D.transMap_interior_contDiffAt`),
* `dens i` is `C^∞` (and positive) at `coord_i (pt_l z)`
  (`Work.Diff.STE.D.dens_interior_contDiffAt`, `Work.Diff.STE.B3.dens_pos_of_mem_target`),

and `Real.sqrt` is `C^∞` at a positive real, so the composite `z ↦ √(dens i (coord_i (pt_l z)))` is
`C^∞` there. -/
lemma dens_comp_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l i : ι₀) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l y))))
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i l) := by
  intro z hz
  -- `z ↦ coord_i (pt_l z)` is smooth at `z`
  have hT : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l w)) z :=
    Work.Diff.STE.D.transMap_interior_contDiffAt (I := I) D i l z hz.1 hz.2.1
  -- the flat coordinate of `pt_l z` is the chart-`i` image of `pt_l z`
  have hflat : Work.Diff.STE.flatToE (I := I) (D.x₀ i)
      (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l z))
      = (extChartAt I (D.x₀ i)) (D.pt l z) :=
    Work.Diff.STE.D.flatToE_coord (I := I) (M := M) D i hz.2.1
  -- `dens i` is smooth at that flat coordinate
  have hdi : ContDiffAt ℝ (⊤ : ℕ∞) (D.dens i)
      (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l z)) :=
    Work.Diff.STE.D.dens_interior_contDiffAt (I := I) D i _
      (by rw [hflat]; exact hz.2.2)
  -- and strictly positive there, so `Real.sqrt` is smooth at its value
  have hpos : 0 < D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l z)) :=
    Work.Diff.STE.B3.dens_pos_of_mem_target (I := I) D i
      (by rw [hflat]; exact interior_subset hz.2.2)
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : Fin (Module.finrank ℝ E) → ℝ =>
      Real.sqrt (D.dens i w)) (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l z)) :=
    (Real.contDiffAt_sqrt hpos.ne').comp _ hdi
  exact (hsqrt.comp z hT).contDiffWithinAt

/-- **The chart-density composition with the transition map is globally smooth.**

Setting `Ω := {y | D.psi l y ≠ 0 ∧ D.ζ i (D.pt l y) ≠ 0}`, the function
`y ↦ √(dens_i (coord_i (pt_l y)))` — the square root of the chart-`i` volume density at the point of
`M` whose chart-`l` flat coordinate is `y` — agrees on `Ω` with a *globally* `C^∞` function of `y`.

This is the analytic crux of the "chart expression of `Q_k`" lemma
(`Work.Diff.STE.B3.VarCoef.R_Qk_chartExpr`): the identity `R_l(Q_k h) = φ_l·Σ_iΣ_{cd} co·P_i(...)`
forces the coefficient `ci` to equal `ζ_i(pt_l y)·√(dens_i(coord_i(pt_l y)))·(frame pairings)(y)` on
the open set `Ω`, while the statement demands `ci` to be `C^∞` on all of `Fin n → ℝ`.

Suggested route (pointed out by the reviewers): the `B3Data` weights force `M` to be Hausdorff —
`Work.Diff.STE.B3.t2Space_of_B3Data` in
`Submission/Work/Diff/STE/B3/closure_Omega_goodSet.lean` (sorry-free) — so with
`haveI := Work.Diff.STE.B3.t2Space_of_B3Data D` one may use the Layer-D lemmas under `[T2Space M]`.
Then `closure Ω ⊆ goodSet D i l` (`Work.Diff.STE.D.closure_Omega_subset_goodSet`, `Omega` there is
exactly the set above), `goodSet` is open, `closure Ω` is compact
(`Work.Diff.STE.B3.isCompact_closure_Omega`), and the composite is `C^∞` on `goodSet` because there
`pt_l y ∈ (chart-i source)` and `flatToE (x₀ i) (coord_i (pt_l y)) = extChartAt I (x₀ i) (pt_l y)`
lies in the *interior* of the chart-`i` target, so `dens i` is `C^∞` there
(`Work.Diff.STE.D.dens_interior_contDiffAt`), `pt_l` is `C^∞` there
(`Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior`) and `coord_i` is `C^∞` on the chart-`i` source.
Finally apply `Work.Diff.STE.D.bump_smul_smooth` with `K := closure Ω` and `U := goodSet D i l`. -/
theorem exists_contDiff_eqOn_dens_comp
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
        G y = Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l y))) := by
  classical
  -- The `B3Data` weights force `M` to be Hausdorff, so the Layer-D lemmas become available.
  haveI hT2 : T2Space M := Work.Diff.STE.B3.t2Space_of_B3Data (I := I) (M := M) D
  -- the function whose smoothness we want to globalise
  let g : (Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun y =>
    Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l y)))
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g (Work.Diff.STE.D.goodSet (I := I) (M := M) D i l) :=
    dens_comp_contDiffOn (I := I) (M := M) D l i
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
      (Work.Diff.STE.D.goodSet (I := I) (M := M) D i l) hK hU hKU g hg
  refine ⟨fun y => φ y • g y, hsm, fun y hy1 hy2 => ?_⟩
  have hyO : y ∈ Work.Diff.STE.D.Omega (I := I) (M := M) D i l := ⟨hy1, hy2⟩
  have h1 : φ y = 1 := hone y (subset_closure hyO)
  show φ y • g y = Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt l y)))
  rw [h1, one_smul]

end Work.Diff.STE.B3.VarCoef
