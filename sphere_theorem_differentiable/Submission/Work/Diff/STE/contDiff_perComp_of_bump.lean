import Mathlib
import Submission.Work.Diff.STE.SNorm
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.contDiffOn_locComp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE

/-- The affine change of coordinates from the chart of `x₀ i` to the flat coordinates centred at
the chart centre. -/
noncomputable def aff (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {ι₀ : Type*} (x₀ : ι₀ → M) (i : ι₀) :
    (Fin (Module.finrank ℝ E) → ℝ) → E :=
  fun z => (Module.finBasis ℝ E).equivFun.symm
    ((Module.finBasis ℝ E).equivFun ((extChartAt I (x₀ i)) (x₀ i)) + z)

/-- **The localised, bumped, periodised chart component is smooth and periodic.**

Let `χ` be a smooth bump which is `1` on the support of the flat representative
`flatRep θ x₀ g i a b` of the `(a,b)`-component of the metric `g` in the chart of `x₀ i`, whose
closed support is mapped by `aff` into the chart target, and such that `χ · flatRep` is supported
in the open unit cube `(-1/2,1/2)ⁿ`.  Then the periodisation of `χ · flatRep` is `C^∞` and
`1`-periodic.  This is what makes the norm `SNorm` of Layer B a well-formed `Hᵏ`-norm (the Layer A
Fourier theory applies to it).

The statement is phrased with the `ℂ`-valued product `↑χ · ↑flatRep` (rather than the coercion of
the real product) so that it matches `periodization_contDiff_periodic` definitionally; the real
product occurs only in the (unused for smoothness, but recorded) identity hypothesis `hχ1`. -/
theorem contDiff_perComp_of_bump
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    {ι₀ : Type*} (θ : SmoothPartitionOfUnity ι₀ I M) (x₀ : ι₀ → M)
    (g : Submission.Diff.SMet I M) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
    (χ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχ1 : ∀ x : Fin (Module.finrank ℝ E) → ℝ,
      Work.Diff.STE.flatRep θ x₀ g i a b x ≠ 0 → χ x = 1)
    (hχt : ∀ x ∈ tsupport χ,
      Work.Diff.STE.aff (H := H) (I := I) E x₀ i x ∈ (extChartAt I (x₀ i)).target)
    (hsmall : Function.support (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ((χ x : ℝ) : ℂ) * ((Work.Diff.STE.flatRep θ x₀ g i a b x : ℝ) : ℂ))
      ⊆ Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ∑' m : Fin (Module.finrank ℝ E) → ℤ,
          ((χ (x + fun j => (m j : ℝ)) : ℝ) : ℂ) *
            ((Work.Diff.STE.flatRep θ x₀ g i a b (x + fun j => (m j : ℝ)) : ℝ) : ℂ)) ∧
      Work.Diff.STE.Periodic1 (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ∑' m : Fin (Module.finrank ℝ E) → ℤ,
          ((χ (x + fun j => (m j : ℝ)) : ℝ) : ℂ) *
            ((Work.Diff.STE.flatRep θ x₀ g i a b (x + fun j => (m j : ℝ)) : ℝ) : ℂ)) := by
  have haff : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.aff (H := H) (I := I) E x₀ i) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun ((extChartAt I (x₀ i)) (x₀ i)) + z) :=
      contDiff_const.add contDiff_id
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        (Module.finBasis ℝ E).equivFun.symm w) :=
      (((Module.finBasis ℝ E).equivFun.symm :
          (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E) :
          (Fin (Module.finrank ℝ E) → ℝ) →ₗ[ℝ] E).toContinuousLinearMap.contDiff
    exact h2.comp h1
  have hΨ : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => χ x * Work.Diff.STE.flatRep θ x₀ g i a b x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · have htarget : Work.Diff.STE.aff (H := H) (I := I) E x₀ i x
          ∈ (extChartAt I (x₀ i)).target := hχt x hx
      have houter : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.locComp (I := I) θ x₀ g i a b)
          (Work.Diff.STE.aff (H := H) (I := I) E x₀ i x) :=
        (contDiffOn_locComp (I := I) θ x₀ g i a b).contDiffAt
          ((isOpen_extChartAt_target (I := I) (x₀ i)).mem_nhds htarget)
      have hfl : ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.flatRep θ x₀ g i a b) x :=
        houter.comp x haff.contDiffAt
      exact hχ.contDiffAt.mul hfl
    · have hz : ∀ᶠ y in 𝓝 x, y ∉ tsupport χ :=
        (isClosed_tsupport χ).isOpen_compl.mem_nhds hx
      have h0 : (fun y => χ y * Work.Diff.STE.flatRep θ x₀ g i a b y)
          =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hz] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h0
  have hΨc : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ((χ x : ℝ) : ℂ) * ((Work.Diff.STE.flatRep θ x₀ g i a b x : ℝ) : ℂ)) := by
    have h := Complex.ofRealCLM.contDiff.comp hΨ
    have h' : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ((χ x * Work.Diff.STE.flatRep θ x₀ g i a b x : ℝ) : ℂ)) := h
    have heq : (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ((χ x * Work.Diff.STE.flatRep θ x₀ g i a b x : ℝ) : ℂ))
        = (fun x : Fin (Module.finrank ℝ E) → ℝ =>
          ((χ x : ℝ) : ℂ) * ((Work.Diff.STE.flatRep θ x₀ g i a b x : ℝ) : ℂ)) :=
      funext fun x => Complex.ofReal_mul _ _
    rwa [heq] at h'
  exact ⟨(periodization_contDiff_periodic (ι := Fin (Module.finrank ℝ E))
      (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ((χ x : ℝ) : ℂ) * ((Work.Diff.STE.flatRep θ x₀ g i a b x : ℝ) : ℂ)) hΨc hsmall).1,
    (periodization_contDiff_periodic (ι := Fin (Module.finrank ℝ E))
      (fun x : Fin (Module.finrank ℝ E) → ℝ =>
        ((χ x : ℝ) : ℂ) * ((Work.Diff.STE.flatRep θ x₀ g i a b x : ℝ) : ℂ)) hΨc hsmall).2.1⟩

end Work.Diff.STE
