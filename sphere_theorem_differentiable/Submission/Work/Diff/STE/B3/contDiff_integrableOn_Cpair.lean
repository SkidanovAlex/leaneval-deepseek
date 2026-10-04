import Mathlib
import Submission.Work.Diff.STE.B3.integrableOn_Cpair_term

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- **Layer B3: the component integrand `u ab · R i k a b` is integrable on the centred cube.**

Both factors are assumed *continuous* (on the whole flat coordinate space
`Fin (Module.finrank ℝ E) → ℝ`), so the integrand is continuous; the centred cube `(-1/2,1/2]^n` is
contained in the compact closed cube `[-1/2,1/2]^n`, and a continuous function is integrable on a
compact set.  Nothing about the geometry of `M` enters: the localisation data `D` is used only
through the values `D.R i k a b`, whose continuity is the hypothesis `hk`. -/
theorem contDiff_integrableOn_Cpair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)), Continuous (D.R j k a b))
    (a b : Fin (Module.finrank ℝ E)) :
    MeasureTheory.IntegrableOn (fun y => u a b y * D.R i k a b y)
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume := by
  -- The integrand is continuous, being a product of continuous functions.
  have hf : Continuous fun y : Fin (Module.finrank ℝ E) → ℝ => u a b y * D.R i k a b y :=
    (hu a b).mul (hk i a b)
  -- The centred cube sits inside the compact closed cube `[-1/2,1/2]^n`.
  have hsub : Work.Diff.STE.B3Data.centreCube (E := E) ⊆
      Set.univ.pi (fun _ : Fin (Module.finrank ℝ E) => Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    rw [Work.Diff.STE.B3Data.centreCube, Set.mem_pi] at hz
    rw [Set.mem_pi]
    intro j _
    exact Set.Ioc_subset_Icc_self (hz j (Set.mem_univ j))
  -- A continuous function is integrable on a compact set; restrict to the centred cube.
  exact (hf.continuousOn.integrableOn_compact
    (isCompact_univ_pi fun _ : Fin (Module.finrank ℝ E) => isCompact_Icc)).mono_set hsub

end Work.Diff.STE.B3
