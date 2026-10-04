import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.perMatDefs
import Submission.Work.Diff.STE.B3.VarCoef.contDiffOn_mat_of_goodSet
import Submission.Work.Diff.STE.B3.SymCalcStep8.contDiff_mul_of_contDiffOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

/-!
# Smoothness of the periodised cut-off chart matrix

`perMat D η l h a b` is the periodisation of `z ↦ η z · D.mat l h a b z`.  Since
`tsupport η` lies in the open unit cube (hypothesis `hηt`) and inside the chart target of `x₀ l`
(hypothesis `hηt2`), the periodisation is smooth:

* the *cut-off* `η` is smooth by `hηsm`, and the *chart matrix* is smooth on
  `goodSet D l l = {z | flatToE (x₀ l) z ∈ interior (extChartAt I (x₀ l)).target}` by
  `contDiffOn_mat_of_goodSet` (which reconstructs `mat l` from the smooth components `R j`
  through the partition of unity `Σ_j ζ_j² = 1`);
* so the product `z ↦ η z · D.mat l h a b z` is globally smooth by
  `contDiff_mul_of_contDiffOn`, and it is supported in the open unit cube;
* its periodisation is therefore smooth by `periodization_contDiff_periodic`.

Note that the set occurring in `hηt2` is `goodSet D l l` up to the two automatic conditions of
`goodSet`: for `z` with `flatToE (x₀ l) z ∈ interior target`, the point `D.pt l z` lies in the
chart source and its chart image lies in the target interior
(`PartialEquiv.map_target` / `PartialEquiv.right_inv` for the extended chart).  In particular no
`[T2Space M]` is needed. -/

/-- The set of flat coordinates whose image lies in the interior of the chart target is open. -/
lemma isOpen_interiorTarget_preimage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (x₀ : M) :
    IsOpen {z : Fin (Module.finrank ℝ E) → ℝ |
      Work.Diff.STE.flatToE (I := I) x₀ z ∈ interior ((extChartAt I x₀).target)} :=
  isOpen_interior.preimage
    (Work.Diff.STE.B3.flatToE_contDiff (I := I) x₀).continuous

/-- The set above is contained in `goodSet D l l`: the remaining two conditions of `goodSet` are
automatic because the extended chart is a partial homeomorphism. -/
lemma interiorTarget_subset_goodSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (l : ι₀) :
    {z : Fin (Module.finrank ℝ E) → ℝ |
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z
        ∈ interior ((extChartAt I (D.x₀ l)).target)}
      ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D l l := by
  intro z hz
  refine ⟨hz, (extChartAt I (D.x₀ l)).map_target (interior_subset hz), ?_⟩
  rw [show D.pt l z = (extChartAt I (D.x₀ l)).symm
      (Work.Diff.STE.flatToE (I := I) (D.x₀ l) z) from rfl,
    (extChartAt I (D.x₀ l)).right_inv (interior_subset hz)]
  exact hz

/-- The topological support of the `ℂ`-lift of `η` is the topological support of `η`. -/
lemma tsupport_ofReal_eq
    {n : ℕ} (η : (Fin n → ℝ) → ℝ) :
    tsupport (fun z : Fin n → ℝ => ((η z : ℝ) : ℂ)) = tsupport η := by
  unfold tsupport
  congr 1
  ext z
  simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]

theorem perMat_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (η : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hηsm : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηt : tsupport η ⊆ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (l : ι₀)
    (hηt2 : ∀ z : Fin (Module.finrank ℝ E) → ℝ, z ∈ tsupport η →
      Work.Diff.STE.flatToE (I := I) (D.x₀ l) z ∈
        interior ((extChartAt I (D.x₀ l)).target))
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ (j : ι₀) (a' b' : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R j h a' b'))
    (a b : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.perMat (I := I) (M := M) D η l h a b) := by
  classical
  -- the chart matrix is `C^∞` on the open set of flat coordinates interior to the chart target
  have hmatsm : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => D.mat l h a b z)
      {z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ l) z
          ∈ interior ((extChartAt I (D.x₀ l)).target)} :=
    (contDiffOn_mat_of_goodSet (I := I) (M := M) D l h a b hsm).mono
      (interiorTarget_subset_goodSet (I := I) (M := M) D l)
  -- its `ℂ`-lift
  have hf : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => ((D.mat l h a b z : ℝ) : ℂ))
      {z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ l) z
          ∈ interior ((extChartAt I (D.x₀ l)).target)} :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hmatsm
  -- the `ℂ`-lift of the cut-off
  have hφ : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => ((η z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hηsm
  -- its topological support is contained in the set above
  have hsup : tsupport (fun z : Fin (Module.finrank ℝ E) → ℝ => ((η z : ℝ) : ℂ)) ⊆
      {z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ l) z
          ∈ interior ((extChartAt I (D.x₀ l)).target)} := by
    intro z hz
    exact hηt2 z ((tsupport_ofReal_eq η) ▸ hz)
  -- hence the product is globally smooth
  have hmul : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ((η z : ℝ) : ℂ) * ((D.mat l h a b z : ℝ) : ℂ)) :=
    Work.Diff.STE.B3.SymCalcStep8.contDiff_mul_of_contDiffOn
      {z : Fin (Module.finrank ℝ E) → ℝ |
        Work.Diff.STE.flatToE (I := I) (D.x₀ l) z
          ∈ interior ((extChartAt I (D.x₀ l)).target)}
      (isOpen_interiorTarget_preimage (I := I) (D.x₀ l))
      (fun z : Fin (Module.finrank ℝ E) → ℝ => ((D.mat l h a b z : ℝ) : ℂ)) hf
      (fun z : Fin (Module.finrank ℝ E) → ℝ => ((η z : ℝ) : ℂ)) hφ hsup
  have hg : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => ((η z * D.mat l h a b z : ℝ) : ℂ)) := by
    simpa only [← Complex.ofReal_mul] using hmul
  -- the product is supported in the open unit cube
  have hsupp : Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((η z * D.mat l h a b z : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    rw [Function.mem_support] at hz
    refine hηt (subset_tsupport η (Function.mem_support.mpr ?_))
    intro h0
    exact hz (by simp [h0])
  -- the periodisation of a smooth function supported in the open unit cube is smooth
  exact (Work.Diff.STE.periodization_contDiff_periodic
    (fun z : Fin (Module.finrank ℝ E) → ℝ => ((η z * D.mat l h a b z : ℝ) : ℂ)) hg hsupp).1

end Work.Diff.STE.B3.VarCoef
