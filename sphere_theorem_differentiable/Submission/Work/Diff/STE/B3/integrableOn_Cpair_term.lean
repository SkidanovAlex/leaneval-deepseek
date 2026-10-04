import Mathlib
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.Diff.STE.B3.integrable_of_continuousOn_of_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: integrability of the term `u ab · R i k a b`

The component integrand of the adjunction `BPair (Rstar i u) k = CPair i u (R i k)` is

`u a b z * D.R i k a b z = u a b z * ψ i z * √(dens i z) * mat i k a b z`,

a product of four factors: the coefficient family `u a b` (continuous, by hypothesis), the
localised weight `ψ i = χ i · ζ i ∘ pt i`, the square root of the volume density, and the chart
matrix `mat i k a b = k (pt i z) (eᵢa) (eᵢb)` (continuous on `{χ i ≠ 0}`, by hypothesis).

The only place where the *junk* values of the chart maps could enter is `√(dens i z)`, and there
they are harmless: `dens i` is `√det` of the Gram matrix of the coordinate frame, evaluated at the
point `pt i z = (extChartAt I (x₀ i)).symm (flatToE (x₀ i) z)` of `M`.  On the flat ball
`‖z‖ ≤ σ i` the flat coordinate lies in the chart target (`B3Data.htarget`), so `pt i` is
continuous there and `(chartMatFun g₀ (x₀ i))` is `C^∞` at the corresponding point of the chart
source (`Work.Diff.STE.B3.contMDiffAt_gmat_coeff'`, composed with the chart inverse and the affine
flat coordinate) — hence `dens i` is continuous on the flat `σ i`-ball, without the
`I.Boundaryless` / `T2Space M` hypotheses of `B3/densGood.lean`.

The integrand therefore is *continuous* on the open ball `‖z‖ < σ i`, it vanishes identically
outside that ball (where `ψ i = 0`), and it is globally bounded: the density is bounded above by
`hdens`, while `|u ab| · |ψ i| · |mat i k a b|` is bounded on the compact closed `σ i`-ball, on
which `mat i k a b` is continuous and `χ i ≠ 0`.  `integrable_of_continuousOn_of_bound` then gives
integrability on the whole space, hence on the centred cube.
-/

set_option linter.unusedSectionVars false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ### The flat balls -/

/-- The affine identification `flatToE x₀` of the flat coordinates with the model space is
continuous. -/
lemma continuous_flatToE (x₀ : M) : Continuous (flatToE (I := I) x₀) := by
  have h1 : Continuous fun z : Fin (Module.finrank ℝ E) → ℝ =>
      (Module.finBasis ℝ E).equivFun ((extChartAt I x₀) x₀) + z :=
    continuous_const.add continuous_id
  have h2 : Continuous fun w : Fin (Module.finrank ℝ E) → ℝ =>
      (Module.finBasis ℝ E).equivFun.symm w :=
    (((Module.finBasis ℝ E).equivFun.symm :
      (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E).toContinuousLinearMap).continuous
  exact h2.comp h1

/-- The open flat ball of radius `σ i` is the metric ball of that radius. -/
lemma sigmaBall_eq_ball (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    sigmaBall D i = Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) := by
  ext z
  simp only [mem_sigmaBall, Metric.mem_ball, dist_zero_right]

/-- The closed flat ball of radius `σ i` is the metric closed ball of that radius. -/
lemma sigmaClosedBall_eq_closedBall (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    sigmaClosedBall D i = Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) := by
  ext z
  simp only [mem_sigmaClosedBall, Metric.mem_closedBall, dist_zero_right]

lemma isOpen_sigmaBall' (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    IsOpen (sigmaBall D i) := by
  rw [sigmaBall_eq_ball D i]
  exact Metric.isOpen_ball

lemma isBounded_sigmaBall' (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    Bornology.IsBounded (sigmaBall D i) := by
  rw [sigmaBall_eq_ball D i]
  exact Metric.isBounded_ball

lemma isCompact_sigmaClosedBall' (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    IsCompact (sigmaClosedBall D i) := by
  rw [sigmaClosedBall_eq_closedBall D i]
  exact isCompact_closedBall _ _

lemma nonempty_sigmaClosedBall' (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    (sigmaClosedBall D i).Nonempty :=
  ⟨0, by simp only [mem_sigmaClosedBall, norm_zero]; exact le_of_lt (D.hσ i)⟩

/-! ### Continuity of `pt i`, of the weight `ψ i` and of the volume density

Everything is proved on the *closed* flat `σ i`-ball, which still lies well inside the `2σ i`-ball
on which the chart is genuine (`B3Data.htarget`). -/

/-- The parametrisation `z ↦ pt i z` is continuous on the flat `σ i`-ball. -/
lemma continuousOn_pt_sigmaClosedBall' (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    ContinuousOn (D.pt i) (sigmaClosedBall D i) := by
  have hsym : ContinuousOn (fun z : E => (extChartAt I (D.x₀ i)).symm z)
      (extChartAt I (D.x₀ i)).target :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ((⊤ : ENat) : WithTop ENat))
      (D.x₀ i)).continuousOn
  have hmaps : MapsTo (flatToE (I := I) (D.x₀ i)) (sigmaClosedBall D i)
      (extChartAt I (D.x₀ i)).target := by
    intro z hz
    refine D.htarget i z ?_
    have hz' : ‖z‖ ≤ D.σ i := hz
    have := D.hσ i
    linarith
  exact ContinuousOn.comp hsym (continuous_flatToE (I := I) (D.x₀ i)).continuousOn hmaps

/-- The localised weight `ψ i = χ i · ζ i ∘ pt i` is continuous on the flat `σ i`-ball. -/
lemma continuousOn_psi_sigmaClosedBall' (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    ContinuousOn (fun z => D.psi i z) (sigmaClosedBall D i) := by
  have hχ : Continuous (fun z => D.χ i z) := (D.hχsm i).continuous
  have hζ : ContinuousOn (fun z => D.ζ i (D.pt i z)) (sigmaClosedBall D i) :=
    (D.hζsm i).continuous.comp_continuousOn (continuousOn_pt_sigmaClosedBall' D i)
  refine ContinuousOn.congr (hχ.continuousOn.mul hζ) (fun z hz => ?_)
  simp only [B3Data.psi, Pi.mul_apply]

/-- Every value of the normalised weight family is bounded by one, because the squares sum to
one. -/
lemma abs_zeta_le_one (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) (p : M) :
    |D.ζ i p| ≤ 1 := by
  have hterm : (D.ζ i p) ^ 2 ≤ ∑ j : ι₀, (D.ζ j p) ^ 2 :=
    Finset.single_le_sum (f := fun j : ι₀ => (D.ζ j p) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [D.hζsq] at hterm
  calc |D.ζ i p| = Real.sqrt ((D.ζ i p) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hterm
    _ = 1 := Real.sqrt_one

/-- **The volume density of the chart is continuous on the flat `σ i`-ball.**  It is `√det` of the
Gram matrix of the coordinate frame, evaluated along `pt i`; on that ball `pt i` is continuous and
the Gram matrix entries are `C^∞` as functions on the chart source. -/
lemma continuousOn_dens_closed (D : B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀) :
    ContinuousOn (D.dens i) (sigmaClosedBall D i) := by
  have hcoeff : ∀ a b : Fin (Module.finrank ℝ E),
      ContinuousOn (fun p : M =>
        (g₀.inner p (Submission.Geodesic.frameVector (I := I) (D.x₀ i) p
          (Module.finBasis ℝ E a)))
        (Submission.Geodesic.frameVector (I := I) (D.x₀ i) p (Module.finBasis ℝ E b)))
        (chartAt H (D.x₀ i)).source :=
    fun a b p hp =>
      ((Work.Diff.STE.B3.contMDiffAt_gmat_coeff' (I := I) g₀ (D.x₀ i) hp a b).continuousAt)
        |>.continuousWithinAt
  have hpt := continuousOn_pt_sigmaClosedBall' D i
  have hmaps : MapsTo (D.pt i) (sigmaClosedBall D i) (chartAt H (D.x₀ i)).source := by
    intro z hz
    rw [← extChartAt_source (I := I) (D.x₀ i)]
    refine PartialEquiv.map_target (extChartAt I (D.x₀ i)) (D.htarget i z ?_)
    have hz' : ‖z‖ ≤ D.σ i := hz
    have := D.hσ i
    linarith
  have hmat : ContinuousOn (fun z => (fun a b =>
      Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
        (flatToE (I := I) (D.x₀ i) z) a b)) (sigmaClosedBall D i) := by
    rw [continuousOn_pi]
    intro a
    rw [continuousOn_pi]
    intro b
    have h := ContinuousOn.comp (hcoeff a b) hpt hmaps
    refine h.congr (fun z hz => ?_)
    simp only [Function.comp_apply, Work.Diff.EXT.chartMatFun, B3Data.pt, Work.Diff.EXT.bB]
    try rfl
  have hdet : ContinuousOn (fun z => (Matrix.of (Work.Diff.EXT.chartMatFun (I := I) g₀ (D.x₀ i)
      (flatToE (I := I) (D.x₀ i) z))).det) (sigmaClosedBall D i) :=
    (continuous_id.matrix_det).comp_continuousOn hmat
  exact (Real.continuous_sqrt.comp_continuousOn hdet).congr (fun z hz => rfl)

/-! ### The integrand -/

theorem integrableOn_Cpair_term
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (k : Work.Diff.STE.Bil (I := I) (M := M))
    (hu : ∀ a b : Fin (Module.finrank ℝ E), Continuous (u a b))
    (hk : ∀ (j : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContinuousOn (D.mat j k a b) {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0})
    (hdens : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (i : ι₀)
      (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → c ≤ D.dens i z ∧ D.dens i z ≤ C)
    (a b : Fin (Module.finrank ℝ E)) :
    MeasureTheory.IntegrableOn (fun y => u a b y * D.R i k a b y)
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume := by
  classical
  obtain ⟨c, C₀, hcpos, hC₀pos, hdensb⟩ := hdens
  -- On the closed flat ball, `χ i` does not vanish, so the chart matrix is continuous there.
  have hmatK : ContinuousOn (fun z => D.mat i k a b z) (sigmaClosedBall D i) :=
    (hk i a b).mono (fun z hz => by
      have hz' : ‖z‖ ≤ D.σ i := hz
      exact chi_ne_zero_of_norm_le_sigma D hz')
  -- The comparison function whose supremum bounds the integrand outside the density.
  have hAK : ContinuousOn
      (fun z => |u a b z| * |D.psi i z| * |D.mat i k a b z|) (sigmaClosedBall D i) := by
    refine ContinuousOn.congr (((hu a b).abs.continuousOn.mul
      (continuousOn_psi_sigmaClosedBall' D i).abs).mul hmatK.abs) (fun z hz => ?_)
    simp only [Pi.mul_apply]
  obtain ⟨z₀, hz₀K, hz₀max⟩ :=
    (isCompact_sigmaClosedBall' D i).exists_isMaxOn (nonempty_sigmaClosedBall' D i) hAK
  set M : ℝ := |u a b z₀| * |D.psi i z₀| * |D.mat i k a b z₀| with hM
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hmax : ∀ z ∈ sigmaClosedBall D i,
      |u a b z| * |D.psi i z| * |D.mat i k a b z| ≤ M := fun z hz => by
    simpa only [hM, Set.mem_ofPred_eq] using hz₀max hz
  -- The integrand vanishes outside the open `σ i`-ball.
  have hzero : ∀ z ∉ sigmaBall D i, u a b z * D.R i k a b z = 0 := by
    intro z hz
    have hψ : D.psi i z = 0 := by
      by_contra h
      exact hz (norm_lt_sigma_of_psi_ne_zero D h)
    simp only [B3Data.R, hψ, zero_mul, mul_zero]
  -- The integrand is continuous on the open `σ i`-ball.
  have hcont : ContinuousOn (fun z => u a b z * D.R i k a b z) (sigmaBall D i) := by
    have h1 : ContinuousOn (fun z => u a b z) (sigmaBall D i) := (hu a b).continuousOn
    have h2 : ContinuousOn (fun z => D.psi i z) (sigmaBall D i) :=
      (continuousOn_psi_sigmaClosedBall' D i).mono (fun z hz => by
        have hz' : ‖z‖ < D.σ i := hz
        exact le_of_lt hz')
    have h3 : ContinuousOn (fun z => Real.sqrt (D.dens i z)) (sigmaBall D i) :=
      Real.continuous_sqrt.comp_continuousOn ((continuousOn_dens_closed D i).mono (fun z hz => by
        have hz' : ‖z‖ < D.σ i := hz
        exact le_of_lt hz'))
    have h4 : ContinuousOn (fun z => D.mat i k a b z) (sigmaBall D i) :=
      (hk i a b).mono (fun z hz => by
        have hz' : ‖z‖ < D.σ i := hz
        exact chi_ne_zero_of_norm_le_sigma D (le_of_lt hz'))
    refine (h1.mul (h2.mul (h3.mul h4))).congr (fun z hz => ?_)
    simp only [B3Data.R, Pi.mul_apply]
    ring
  -- The global bound.
  have hbound : ∀ z, ‖u a b z * D.R i k a b z‖ ≤ M * Real.sqrt C₀ := by
    intro z
    by_cases hψ : D.psi i z = 0
    · rw [show D.R i k a b z = 0 by simp only [B3Data.R, hψ, zero_mul]]
      simp only [mul_zero, norm_zero]
      exact mul_nonneg hMnn (Real.sqrt_nonneg _)
    · have hlt : ‖z‖ < D.σ i := norm_lt_sigma_of_psi_ne_zero D hψ
      have hzK : z ∈ sigmaClosedBall D i := by
        simp only [mem_sigmaClosedBall]; exact le_of_lt hlt
      have hdensle : Real.sqrt (D.dens i z) ≤ Real.sqrt C₀ :=
        Real.sqrt_le_sqrt (hdensb i z (le_of_lt hlt)).2
      have hle : |u a b z| * |D.psi i z| * Real.sqrt (D.dens i z) * |D.mat i k a b z|
          ≤ M * Real.sqrt C₀ := by
        have hstep : |u a b z| * |D.psi i z| * Real.sqrt (D.dens i z) * |D.mat i k a b z|
            ≤ |u a b z| * |D.psi i z| * Real.sqrt C₀ * |D.mat i k a b z| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left hdensle (by positivity)
        have hstep2 : |u a b z| * |D.psi i z| * Real.sqrt C₀ * |D.mat i k a b z|
            = (|u a b z| * |D.psi i z| * |D.mat i k a b z|) * Real.sqrt C₀ := by ring
        rw [hstep2] at hstep
        exact hstep.trans (mul_le_mul_of_nonneg_right (hmax z hzK) (Real.sqrt_nonneg _))
      refine le_trans ?_ hle
      exact le_of_eq (by
        rw [B3Data.R, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (Real.sqrt_nonneg (D.dens i z))]
        ring)
  exact (integrable_of_continuousOn_of_bound (isOpen_sigmaBall' D i) (isBounded_sigmaBall' D i)
    hcont hzero hbound).integrableOn

end Work.Diff.STE.B3
