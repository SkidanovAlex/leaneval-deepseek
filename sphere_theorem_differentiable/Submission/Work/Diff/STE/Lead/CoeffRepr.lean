import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.Lead.coeffFun_lipschitz_of_ode

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The coefficient functional of a periodised localised component, on the unit cube

This file collects the elementary representation lemmas for the Fourier coefficients of the
periodised localised components `D.Rper i h a b` of Layer B3 which are shared by the
`ε → 0`-limit argument (`Work.Diff.STE.Lead.limit_coeff_hasDerivWithinAt`).

The main point is that the lattice sum defining `D.Rper i h a b` collapses to the *finite* sum
over the multi-indices `{0,-1}^n` as soon as one evaluates it on the half open unit cube
`unitCube = (0,1]^n`, because the localised component `D.R i h a b` is supported in the open
centred cube `(-1/2,1/2)^n`:

  `D.Rper i h a b z = ∑ m ∈ cubeIdx E, R i h a b (z + m)`,   `z ∈ (0,1]^n`.

This holds for **every** section `h` (no smoothness hypothesis) and is what makes the coefficient
functional

  `ĉ_μ(h) = fourierCoeff (D.Rper i h a b) μ = ∫_{cube} e_{-μ} z · ∑_{m ∈ cubeIdx} R i h a b (z+m) dz`

an integral of an *explicit finite* sum over the cube — the form in which both the parametric
differentiation in `t` and the linearity of the coefficient functional are read off.

The other ingredients here are the two closure properties of the chart-smoothness hypothesis
`Work.Diff.STE.D.ChartData` that the limit argument needs: subtraction, and the resulting
measurability/boundedness of the localised components.
-/

noncomputable section

open MeasureTheory BigOperators
open scoped Manifold ContDiff Bundle Topology

namespace Work.Diff.STE.Lead

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## The support of a localised component -/

/-- The localised component `D.R i h a b` is supported in the open centred cube `(-1/2,1/2)^n`,
for an arbitrary section `h`: this is the support of the localised weight `D.psi i`. -/
lemma R_support_pi (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    Function.support (D.R i h a b) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
  fun _ hz => D.psi_supp i (fun h0 => hz (by
    simp only [Work.Diff.STE.B3Data.R, h0, zero_mul, mul_zero]))

/-! ## The periodisation on the unit cube is the finite sum over `{0,-1}^n` -/

/-- **On the unit cube the periodisation of a localised component is the finite sum over
`{0,-1}^n`.**  For `z ∈ (0,1]^n` every lattice translate `z + m` with `R i h a b (z+m) ≠ 0` lies in
the open centred cube, which forces `m ∈ {0,-1}^n`. -/
lemma Rper_eq_finset_sum_of_mem_unitCube
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ)
    (hz : z ∈ Work.Diff.STE.unitCube) :
    D.Rper i h a b z =
      ∑ m ∈ cubeIdx E, ((D.R i h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) := by
  rw [Work.Diff.STE.B3Data.Rper]
  refine tsum_eq_sum (s := cubeIdx E) fun m hm => ?_
  by_contra hc
  have hne : D.R i h a b (z + Work.Diff.STE.iVec m) ≠ 0 :=
    fun h0 => hc (by rw [h0, Complex.ofReal_zero])
  have hmem : z + Work.Diff.STE.iVec m ∈ Function.support (D.R i h a b) := by
    rwa [Function.mem_support]
  have hpi := R_support_pi (I := I) (M := M) D h i a b hmem
  have hnot : ¬∀ j, m j ∈ Finset.Icc (-1 : ℤ) 0 :=
    fun hall => hm ((Fintype.mem_piFinset).mpr hall)
  obtain ⟨j, hj⟩ := not_forall.mp hnot
  have hj' : ¬((-1 : ℤ) ≤ m j ∧ m j ≤ 0) := fun hh' => hj (Finset.mem_Icc.mpr hh')
  have hbad : m j ≤ -2 ∨ 1 ≤ m j := by
    push_neg at hj'
    omega
  have hcoord := Set.mem_pi.mp hpi j (Set.mem_univ j)
  rw [Set.mem_Ioo] at hcoord
  simp only [Pi.add_apply, Work.Diff.STE.iVec_apply] at hcoord
  have hzc : z j ∈ Set.Ioc (0 : ℝ) 1 := Set.mem_pi.mp hz j (Set.mem_univ j)
  rw [Set.mem_Ioc] at hzc
  rcases hbad with hle | hge
  · have hcast : ((m j : ℤ) : ℝ) ≤ -2 := by exact_mod_cast hle
    linarith [hcoord.1, hzc.2]
  · have hcast : (1 : ℝ) ≤ ((m j : ℤ) : ℝ) := by exact_mod_cast hge
    linarith [hcoord.2, hzc.1]

/-- **The coefficient functional as an integral of the finite sum over `{0,-1}^n`.**  For an
arbitrary section `h`,

  `ĉ_μ(h) = ∫_{cube} e_{-μ}(z) · ∑_{m ∈ cubeIdx} R i h a b (z + m) dz`.

No smoothness of `h` is required — this is the identity in which the *pointwise* differentiability
of `h ↦ R i h a b` (which the ODE hypothesis provides) can be integrated. -/
theorem fourierCoeff_Rper_eq_sum_integral
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ) :
    Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ
      = ∫ z in Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)),
          Work.Diff.STE.fourierExp (-μ) z *
            ∑ m ∈ cubeIdx E, ((D.R i h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) := by
  rw [Work.Diff.STE.fourierCoeff]
  exact setIntegral_congr_fun BesselCont.measSet_unitCube
    (fun z hz => by rw [Rper_eq_finset_sum_of_mem_unitCube (I := I) (M := M) D h i a b z hz])

/-! ## The chart-smoothness hypothesis is closed under subtraction -/

omit [T2Space M] [I.Boundaryless] in
/-- **The chart-smoothness hypothesis is closed under subtraction.** -/
lemma ChartData_sub (X Y : Work.Diff.STE.Bil (I := I) (M := M))
    (hX : Work.Diff.STE.D.ChartData (I := I) (M := M) X)
    (hY : Work.Diff.STE.D.ChartData (I := I) (M := M) Y) :
    Work.Diff.STE.D.ChartData (I := I) (M := M) (X - Y) := by
  intro x₀
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => fun i j : Fin (Module.finrank ℝ E) =>
        X ((extChartAt I x₀).symm y)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) j)))
      (extChartAt I x₀).target := hX x₀
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => fun i j : Fin (Module.finrank ℝ E) =>
        Y ((extChartAt I x₀).symm y)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) j)))
      (extChartAt I x₀).target := hY x₀
  refine (h1.sub h2).congr ?_
  intro y hy
  funext i j
  simp only [Pi.sub_apply, ContinuousLinearMap.sub_apply]

/-! ## Measurability and boundedness of a localised component with chart-smooth data -/

/-- **A localised component with chart-smooth data is measurable** (it is `C^∞` with compact
support). -/
lemma measurable_R_of_chartData (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    Measurable (fun z : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b z : ℝ) : ℂ)) :=
  (Complex.continuous_ofReal.measurable).comp
    (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hh i a b).continuous.measurable

/-- **A localised component with chart-smooth data is bounded**: it is continuous and supported in
the closed centred cube, which is compact. -/
lemma exists_abs_R_le_of_chartData (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, |D.R i h a b w| ≤ C := by
  have hcont : Continuous (D.R i h a b) :=
    (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hh i a b).continuous
  have hK : IsCompact (Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Icc (-(1 / 2 : ℝ)) (1 / 2))) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun w => ?_⟩
  by_cases hw : w ∈ Set.pi Set.univ
      (fun _ : Fin (Module.finrank ℝ E) => Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
  · exact le_trans (by simpa only [Real.norm_eq_abs] using hC w hw) (le_max_left _ _)
  · have hzero : D.R i h a b w = 0 := by
      by_contra hne
      exact hw (Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self)
        (R_support_pi (I := I) (M := M) D h i a b (Function.mem_support.mpr hne)))
    rw [hzero, abs_zero]
    exact le_max_right _ _

end Work.Diff.STE.Lead
