import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Lead.continuous_deTurckSec_R
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.Lead.R_abs_le
import Submission.Work.Diff.STE.Lead.transfer_tendsto

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the Fourier coefficients of the DeTurck components

The localised component `D.R i (deTurckSec hLC g₀ (U σ) …) a b` of the DeTurck section is smooth
(`Work.Diff.STE.B3.chartData_deTurckSec` + `Work.Diff.STE.B3.R_contDiff_of_chartData`) and its
periodisation `D.Rper i …` has Fourier coefficients given by the integral of the (compactly
supported) flat component against the character
(`Work.Diff.STE.Lead.Rper_fourierCoeff_eq_integral`).

Two facts then give the continuity in `σ` of the coefficient functional:

* the *pointwise* continuity of `σ ↦ D.R i (deTurckSec (U σ) …) a b z` for every flat point `z`
  (`Work.Diff.STE.Lead.continuous_deTurckSec_R`);
* the *uniform* bound `|D.R i (deTurckSec (U σ) …) a b z| ≤ √(dens bound) · K`, valid for every `z`
  and every `σ ∈ [0,τ₀)`, supplied by `Work.Diff.STE.Lead.R_abs_le` from the pointwise DeTurck
  bound `hbd` and the uniform two-sided density bound `Work.Diff.STE.B3.dens_bound_sigma`.

Dominated convergence on the centred fundamental cube then applies (the dominating function is the
constant `√(dens bound) · K`, integrable because the cube has finite measure).
-/

namespace Work.Diff.STE.Lead

open MeasureTheory Filter
open scoped Topology

/-- **The Fourier coefficient of a periodised localised component as an integral over the centred
cube.**  For a section `Z` whose flat localised component `D.R j Z a b` is `C^∞` (hence compactly
supported in the open centred cube), the `m`-th Fourier coefficient of the periodisation is the
integral of the component against the character `e_{-m}` over the centred cube
`(-1/2,1/2]^n`. -/
lemma Rper_fourierCoeff_eq_integral_centre
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (Z : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (a b : Fin (Module.finrank ℝ E))
    (m : Fin (Module.finrank ℝ E) → ℤ) (hZ : ContDiff ℝ (⊤ : ℕ∞) (D.R j Z a b)) :
    Work.Diff.STE.fourierCoeff (D.Rper j Z a b) m
      = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ) := by
  rw [Rper_fourierCoeff_eq_integral (I := I) (M := M) D Z j a b m hZ]
  exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Work.Diff.STE.B3Data.centreCube (E := E))
    (f := fun z : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.fourierExp (-m) z * ((D.R j Z a b z : ℝ) : ℂ)) (fun z hz => by
      have hz0 : D.R j Z a b z = 0 := by
        by_contra h0
        exact hz (Set.pi_mono (fun _ _ => Set.Ioo_subset_Ioc_self)
          (D.R_support j Z a b (Function.mem_support.mpr h0)))
      rw [hz0, Complex.ofReal_zero, mul_zero])).symm

theorem continuous_fourierCoeff_deTurckSec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (τ₀ : ℝ) (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k) (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (hsym : ∀ (t : ℝ) (x : M) (u v : TangentSpace I x), (U t) x u v = (U t) x v u)
    (hpos : ∀ (t : ℝ) (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < (U t) x v v)
    (hUB : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k)
    (hell : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (U t) x v v)
    (hub : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      (U t) x v v ≤ K * g₀.inner x v v)
    (hbd : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (u v : TangentSpace I x),
      |Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U t) (hsym t) (hpos t) (hsm t) x u v|
        ≤ K * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v))
    (hcont : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun σ : ℝ => D.BNorm k (U σ - U t))
        (nhdsWithin t (Set.Ico (0 : ℝ) τ₀)) (nhds 0))
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ) :
    ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ContinuousWithinAt
      (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U σ) (hsym σ) (hpos σ) (hsm σ)) a b) μ)
      (Set.Ico (0 : ℝ) τ₀) t := by
  classical
  -- a uniform upper bound for the volume density on the `σ i`-ball
  obtain ⟨cdens, Cdens, hcdens, hCdens, hdensbd⟩ :=
    Work.Diff.STE.B3.dens_bound_sigma (I := I) (M := M) D
  -- smoothness of the flat localised components of the DeTurck family
  have hsmR : ∀ σ : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U σ) (hsym σ) (hpos σ) (hsm σ)) a b) :=
    fun σ => Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _
      (Work.Diff.STE.B3.chartData_deTurckSec (I := I) (M := M) (g₀ := g₀) hLC (U σ)
        (hsym σ) (hpos σ) (hsm σ)) i a b
  -- the uniform pointwise bound on those components
  have hRbd : ∀ σ ∈ Set.Ico (0 : ℝ) τ₀, ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      |D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U σ) (hsym σ) (hpos σ) (hsm σ)) a b z|
        ≤ Real.sqrt Cdens * K := by
    intro σ hσ
    exact Work.Diff.STE.Lead.R_abs_le (I := I) (M := M) D
      (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U σ) (hsym σ) (hpos σ) (hsm σ)) K Cdens
      (le_of_lt hK) hCdens (fun j z hz => (hdensbd j z hz).2)
      (fun y u' v' => hbd σ hσ y u' v') i a b
  -- the coefficient as an integral over the centred cube
  have hcoeff : ∀ σ : ℝ, Work.Diff.STE.fourierCoeff (D.Rper i
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U σ) (hsym σ) (hpos σ) (hsm σ)) a b) μ
      = ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          Work.Diff.STE.fourierExp (-μ) z
            * ((D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U σ) (hsym σ) (hpos σ)
                (hsm σ)) a b z : ℝ) : ℂ) :=
    fun σ => Rper_fourierCoeff_eq_integral_centre (I := I) (M := M) D _ i a b μ (hsmR σ)
  intro t ht
  -- the centred cube has finite measure
  have hvol : (volume : Measure (Fin (Module.finrank ℝ E) → ℝ))
      (Work.Diff.STE.B3Data.centreCube (E := E)) < ⊤ := by
    have hKc : IsCompact (Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2))) :=
      isCompact_univ_pi (fun _ : Fin (Module.finrank ℝ E) => isCompact_Icc)
    exact lt_of_le_of_lt (measure_mono (Set.pi_mono (fun _ _ => Set.Ioc_subset_Icc_self)))
      hKc.measure_lt_top
  -- dominated convergence for the integral representation
  have hInt : Filter.Tendsto (fun σ : ℝ =>
        ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          Work.Diff.STE.fourierExp (-μ) z
            * ((D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U σ) (hsym σ) (hpos σ)
                (hsm σ)) a b z : ℝ) : ℂ))
      (nhdsWithin t (Set.Ico (0 : ℝ) τ₀))
      (nhds (∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          Work.Diff.STE.fourierExp (-μ) z
            * ((D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U t) (hsym t) (hpos t)
                (hsm t)) a b z : ℝ) : ℂ))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (Fin (Module.finrank ℝ E) → ℝ)).restrict
        (Work.Diff.STE.B3Data.centreCube (E := E)))
      (l := nhdsWithin t (Set.Ico (0 : ℝ) τ₀))
      (F := fun σ : ℝ => fun z : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.fourierExp (-μ) z
          * ((D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U σ) (hsym σ) (hpos σ)
              (hsm σ)) a b z : ℝ) : ℂ))
      (f := fun z : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.fourierExp (-μ) z
          * ((D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U t) (hsym t) (hpos t)
              (hsm t)) a b z : ℝ) : ℂ))
      (bound := fun _ : Fin (Module.finrank ℝ E) → ℝ => Real.sqrt Cdens * K) ?_ ?_ ?_ ?_
    · -- strong measurability of every integrand
      refine Filter.Eventually.of_forall fun σ => ?_
      exact ((BesselCont.continuous_fourierExp_char (-μ)).mul
        (Complex.continuous_ofReal.comp (hsmR σ).continuous)).aestronglyMeasurable
    · -- domination by the constant `√Cdens * K`
      refine Filter.eventually_of_mem self_mem_nhdsWithin fun σ hσ => ?_
      refine Filter.Eventually.of_forall fun z => ?_
      simpa only [Complex.norm_mul, BesselCont.norm_fourierExp_char, one_mul, Complex.norm_real,
        Real.norm_eq_abs] using hRbd σ hσ z
    · -- the constant is integrable on the centred cube
      refine MeasureTheory.IntegrableOn.of_bound hvol
        (MeasureTheory.aestronglyMeasurable_const) (Real.sqrt Cdens * K)
        (Filter.Eventually.of_forall fun z => le_of_eq (Real.norm_of_nonneg ?_))
      exact mul_nonneg (Real.sqrt_nonneg Cdens) (le_of_lt hK)
    · -- pointwise convergence, from the continuity of the flat components
      refine Filter.Eventually.of_forall fun z => ?_
      exact ((continuous_const.mul Complex.continuous_ofReal).tendsto _).comp
        (Work.Diff.STE.Lead.continuous_deTurckSec_R (I := I) (M := M) D hLC τ₀ B hB lam K hlam
          hK U hsm hsym hpos hUB hell hub hcont i a b z t ht)
  -- assemble
  have hlim : Filter.Tendsto (fun σ : ℝ =>
        ∫ z in Work.Diff.STE.B3Data.centreCube (E := E),
          Work.Diff.STE.fourierExp (-μ) z
            * ((D.R i (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U σ) (hsym σ) (hpos σ)
                (hsm σ)) a b z : ℝ) : ℂ))
      (nhdsWithin t (Set.Ico (0 : ℝ) τ₀))
      (nhds (Work.Diff.STE.fourierCoeff (D.Rper i
        (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (U t) (hsym t) (hpos t) (hsm t)) a b) μ)) := by
    rw [hcoeff t]
    exact hInt
  refine hlim.congr' (Filter.Eventually.of_forall fun σ => ?_)
  exact (hcoeff σ).symm

end Work.Diff.STE.Lead
