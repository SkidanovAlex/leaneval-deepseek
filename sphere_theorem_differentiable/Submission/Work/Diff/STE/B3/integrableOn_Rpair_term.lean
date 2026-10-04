import Mathlib
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.Diff.STE.B3.integrable_of_continuousOn_of_bound
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.integrableOn_Cpair_term
import Submission.Work.Diff.STE.B3.continuousAt_mat_Rstar
import Submission.Work.Diff.STE.B3.mat_Rstar_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: integrability of the term `R j (Rstar i u) a b · R j k a b`

The first of the three integrability inputs of the adjunction
`BPair (Rstar i u) k = CPair i u (R i k)` (`B3/BPair_Rstar.lean`) is the term

`z ↦ D.R j (D.Rstar i u) a b z · D.R j k a b z`

on the centred fundamental cube, i.e. the product of the localised component of the
*reconstruction* `Rstar i u` in the chart `j` with the localised component of the section `k` in the
same chart.

The proof is the same shape as the one used for the sibling `integrableOn_Cpair_term`:

* the integrand is a product of `ψ j · √(dens j)` with the two chart matrices
  `mat j (Rstar i u) a b` and `mat j k a b`; on the region `‖z‖ < σ j` the weight is
  `ψ j z = ζ j (pt j z)` (`hχ1`) and the density satisfies the two-sided bound `hdens`;
* the reconstruction factor `mat j (Rstar i u) a b` is **bounded on the closed `σ j`-ball**
  (`Work.Diff.STE.B3.mat_Rstar_bound`) and **continuous on the genuine set**
  `{z | ‖z‖ < σ j ∧ ζ i (pt j z) ≠ 0}` (`Work.Diff.STE.B3.continuousAt_mat_Rstar`);
* the `k`-factor is continuous on `{χ j ≠ 0} ⊇ σ j`-ball (`hk`) hence bounded there (compactness);
* off the genuine set the integrand vanishes: either `‖z‖ ≥ σ j`, where `ψ j z = 0`, or
  `ζ i (pt j z) = 0`, where `Rstar i u (pt j z) = 0` by
  `Work.Diff.STE.B3.Rstar_eq_zero_of_zeta_eq_zero`.

Hence the integrand is continuous on the open set `genuineSet D i j`, vanishes outside it and is
globally bounded, so `integrable_of_continuousOn_of_bound` applies; integrability on the centred
cube follows by monotonicity of the measure.

Note that everything here works **without** `I.Boundaryless` and without `T2Space M`, matching the
statement: the only continuity input about the charts is `continuousAt_extChartAt_symm''` (through
`dens_bound_sigma` and `continuousAt_mat_Rstar`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- `(ψ · √d · X) * (ψ · √d · Y) = ψ ^ 2 * d * (X * Y)` for `d ≥ 0`. -/
private lemma psi_sqrt_fac (d ψ X Y : ℝ) (hd : 0 ≤ d) :
    (ψ * Real.sqrt d * X) * (ψ * Real.sqrt d * Y) = ψ ^ 2 * d * (X * Y) := by
  conv_rhs => rw [show d = (Real.sqrt d) ^ 2 from (Real.sq_sqrt hd).symm]
  ring

/-- The elementary estimate on the product of the localised weight and the density. -/
private lemma abs_bound_fac {ψ d X Y CX Mk C₀ : ℝ} (hψ : |ψ| ≤ 1) (hd0 : 0 ≤ d) (hd : d ≤ C₀)
    (_hC₀ : 0 ≤ C₀) (hX : |X| ≤ CX) (hCX : 0 ≤ CX) (hY : |Y| ≤ Mk) (_hMk : 0 ≤ Mk) :
    |ψ ^ 2 * d * (X * Y)| ≤ C₀ * (CX * Mk) := by
  have hψ2 : |ψ| ^ 2 ≤ 1 := by nlinarith [hψ, abs_nonneg ψ]
  have hkey : |ψ ^ 2 * d * (X * Y)| = |ψ| ^ 2 * d * (|X| * |Y|) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hd0, abs_of_nonneg (sq_nonneg ψ), sq_abs]
  rw [hkey]
  calc |ψ| ^ 2 * d * (|X| * |Y|)
      ≤ 1 * C₀ * (CX * Mk) := by
        refine mul_le_mul (mul_le_mul hψ2 hd hd0 (by norm_num))
          (mul_le_mul hX hY (abs_nonneg Y) hCX)
          (mul_nonneg (abs_nonneg X) (abs_nonneg Y)) (by positivity)
    _ = C₀ * (CX * Mk) := by ring

/-- The set of flat coordinates on which the chart `j` is genuine (`‖z‖ < σ j`) **and** the
reconstruction `Rstar i u` does not vanish (`ζ i (pt j z) ≠ 0`).  This is the open region on which
the integrand is written in terms of genuine values only. -/
private def genuineSet (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | ‖z‖ < D.σ j ∧ D.ζ i (D.pt j z) ≠ 0}

private lemma mem_genuineSet (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    z ∈ genuineSet D i j ↔ ‖z‖ < D.σ j ∧ D.ζ i (D.pt j z) ≠ 0 := Iff.rfl

private lemma isOpen_genuineSet (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    IsOpen (genuineSet D i j) := by
  have hcontζ : ContinuousOn (fun z => D.ζ i (D.pt j z)) (sigmaBall D j) :=
    (D.hζsm i).continuous.comp_continuousOn
      ((continuousOn_pt_sigmaClosedBall' D j).mono (fun z hz => by
        have hz' : ‖z‖ < D.σ j := hz
        exact le_of_lt hz'))
  have h := ContinuousOn.isOpen_inter_preimage hcontζ (isOpen_sigmaBall' D j)
    (isOpen_ne (x := (0 : ℝ)))
  have hset : sigmaBall D j ∩ (fun z => D.ζ i (D.pt j z)) ⁻¹' {y : ℝ | y ≠ 0}
      = genuineSet D i j := by
    ext z
    simp only [genuineSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, mem_sigmaBall]
  rw [hset] at h
  exact h

private lemma isBounded_genuineSet (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Bornology.IsBounded (genuineSet D i j) :=
  (isBounded_sigmaBall' D j).subset (fun z hz => by
    rw [mem_sigmaBall]
    exact ((mem_genuineSet D i j z).mp hz).1)

theorem integrableOn_Rpair_term
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
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    MeasureTheory.IntegrableOn
      (fun z => D.R j (D.Rstar i u) a b z * D.R j k a b z)
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume := by
  classical
  -- bound of the reconstruction factor on the closed `σ j`-ball
  obtain ⟨CX, hCXnn, hCX⟩ := mat_Rstar_bound D i j u hu hdens a b
  obtain ⟨c, C₀, hcpos, hC₀pos, hdensb⟩ := hdens
  -- bound of the `k`-factor on the closed `σ j`-ball
  have hmatK : ContinuousOn (fun z => D.mat j k a b z) (sigmaClosedBall D j) :=
    (hk j a b).mono (fun z hz => chi_ne_zero_of_norm_le_sigma D hz)
  obtain ⟨z₀, -, hz₀max⟩ := (isCompact_sigmaClosedBall' D j).exists_isMaxOn
    (nonempty_sigmaClosedBall' D j) hmatK.abs
  have hMk : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ j →
      |D.mat j k a b z| ≤ |D.mat j k a b z₀| := fun z hz =>
    hz₀max (by rw [mem_sigmaClosedBall]; exact hz)
  have hMknn : 0 ≤ |D.mat j k a b z₀| := abs_nonneg _
  -- the integrand vanishes off the genuine set
  have hzero : ∀ z ∉ genuineSet D i j,
      D.R j (D.Rstar i u) a b z * D.R j k a b z = 0 := by
    intro z hz
    rcases not_and_or.mp ((mem_genuineSet D i j z).not.mp hz) with h1 | h2
    · have hψ : D.psi j z = 0 := by
        by_contra hc
        exact h1 (norm_lt_sigma_of_psi_ne_zero D hc)
      simp only [B3Data.R, hψ, zero_mul, mul_zero]
    · have hζ0 : D.ζ i (D.pt j z) = 0 := not_not.mp h2
      have hR : D.Rstar i u (D.pt j z) = 0 := Rstar_eq_zero_of_zeta_eq_zero D u hζ0
      have hmat : D.mat j (D.Rstar i u) a b z = 0 := by
        simp only [B3Data.mat, hR]
        simp
      rw [B3Data.R, hmat]
      ring
  -- the integrand is continuous on the genuine set
  have hcont : ContinuousOn (fun z => D.R j (D.Rstar i u) a b z * D.R j k a b z)
      (genuineSet D i j) := by
    intro z hz
    obtain ⟨hzlt, hζ⟩ := (mem_genuineSet D i j z).mp hz
    have hzle : ‖z‖ ≤ D.σ j := le_of_lt hzlt
    have hz2 : ‖z‖ ≤ 2 * D.σ j := by have := D.hσ j; linarith
    have hnhds : sigmaClosedBall D j ∈ 𝓝 z :=
      Filter.mem_of_superset ((isOpen_sigmaBall' D j).mem_nhds hzlt) (fun w hw => by
        have hw' : ‖w‖ < D.σ j := hw
        exact le_of_lt hw')
    have hpt : ContinuousAt (D.pt j) z :=
      (continuousOn_pt_sigmaClosedBall' D j).continuousAt hnhds
    have hpsi : ContinuousAt (fun z => D.psi j z) z :=
      (((D.hχsm j).continuous.continuousAt).mul
        (((D.hζsm j).continuous.continuousAt).comp hpt)).congr
        (Filter.Eventually.of_forall (fun w => by simp only [B3Data.psi]; rfl))
    have hsqrt : ContinuousAt (fun z => Real.sqrt (D.dens j z)) z :=
      Real.continuous_sqrt.continuousAt.comp
        (dens_continuousAt_of_mem_target D j (D.htarget j z hz2))
    have hchiOpen : IsOpen {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0} :=
      IsOpen.preimage (D.hχsm j).continuous isOpen_ne
    have hmemchi : z ∈ {z : Fin (Module.finrank ℝ E) → ℝ | D.χ j z ≠ 0} := by
      rw [Set.mem_setOf_eq, D.hχ1 j z hzle]
      exact one_ne_zero
    have hmatk : ContinuousAt (D.mat j k a b) z :=
      (hk j a b).continuousAt (hchiOpen.mem_nhds hmemchi)
    have hX : ContinuousAt (D.mat j (D.Rstar i u) a b) z :=
      continuousAt_mat_Rstar D i j u hu a b hzlt hζ
    have h1 : ContinuousAt (fun z => D.R j (D.Rstar i u) a b z) z := by
      refine ((hpsi.mul hsqrt).mul hX).congr (Filter.Eventually.of_forall (fun w => ?_))
      simp only [B3Data.R, Pi.mul_apply]
    have h2 : ContinuousAt (fun z => D.R j k a b z) z := by
      refine ((hpsi.mul hsqrt).mul hmatk).congr (Filter.Eventually.of_forall (fun w => ?_))
      simp only [B3Data.R, Pi.mul_apply]
    exact (h1.mul h2).continuousWithinAt
  -- the global bound
  have hbound : ∀ z, ‖D.R j (D.Rstar i u) a b z * D.R j k a b z‖
      ≤ C₀ * (CX * |D.mat j k a b z₀|) := by
    intro z
    by_cases hz : z ∈ genuineSet D i j
    · obtain ⟨hzlt, -⟩ := (mem_genuineSet D i j z).mp hz
      have hzle : ‖z‖ ≤ D.σ j := le_of_lt hzlt
      have hdnn : 0 ≤ D.dens j z := by
        rw [B3Data.dens]; exact Real.sqrt_nonneg _
      have hdeq : D.R j (D.Rstar i u) a b z * D.R j k a b z
          = (D.psi j z) ^ 2 * D.dens j z
            * (D.mat j (D.Rstar i u) a b z * D.mat j k a b z) := by
        simp only [B3Data.R]
        exact psi_sqrt_fac (D.dens j z) (D.psi j z) _ _ hdnn
      have hpsi1 : |D.psi j z| ≤ 1 := by
        rw [B3Data.psi, D.hχ1 j z hzle, one_mul]
        exact abs_zeta_le_one D j (D.pt j z)
      rw [hdeq, Real.norm_eq_abs]
      exact abs_bound_fac hpsi1 hdnn (hdensb j z hzle).2 (le_of_lt hC₀pos)
        (hCX z hzle) hCXnn (hMk z hzle) hMknn
    · rw [hzero z hz, norm_zero]
      positivity
  -- assemble
  have hInt : Integrable (fun z => D.R j (D.Rstar i u) a b z * D.R j k a b z) volume :=
    integrable_of_continuousOn_of_bound (isOpen_genuineSet D i j) (isBounded_genuineSet D i j)
      hcont hzero hbound
  exact hInt.mono_measure Measure.restrict_le_self

end Work.Diff.STE.B3
