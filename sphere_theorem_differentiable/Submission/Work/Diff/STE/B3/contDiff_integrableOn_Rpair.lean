import Mathlib
import Submission.Work.Diff.STE.B3.integrableOn_Rpair_term

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: integrability of the term `R j (Rstar i u) a b · R j k a b`

The term is

`z ↦ D.R j (D.Rstar i u) a b z * D.R j k a b z`

on the centred fundamental cube, i.e. the product of the localised component of the
*reconstruction* `Rstar i u` in the chart `j` with the localised component of the section `k` in the
same chart.

The hypothesis on the second factor is here **global continuity** of the localised component
`D.R j k a b` (rather than continuity of the bare chart matrix `D.mat j k a b` on `{χ j ≠ 0}`,
which is what the sibling `integrableOn_Rpair_term` assumes).  That is the shape in which the
hypothesis is available when `k` is a Galerkin (Fourier) truncation: the localised component
`R j k a b = ψ j · √(dens j) · mat j k a b` is then a finite linear combination of smooth functions.

The proof is otherwise the one of `integrableOn_Rpair_term`:

* the integrand is written in terms of the weight `ψ j`, the density `√(dens j)` and the two
  chart matrices; it vanishes off the set `genuineSet` where `‖z‖ < σ j` and `ζ i (pt j z) ≠ 0`
  (either `ψ j z = 0`, or the reconstruction `Rstar i u` vanishes at `pt j z`);
* on `genuineSet` it is continuous: the reconstruction factor is continuous by
  `continuousAt_mat_Rstar`, and the `k`-factor by hypothesis;
* it is globally bounded: the reconstruction factor is bounded by `mat_Rstar_bound` together with
  the two-sided density bound `dens_bound_sigma`, and the `k`-factor by compactness of the closed
  `σ j`-ball (on which `genuineSet` lies).

Integrability then follows from `integrable_of_continuousOn_of_bound`, and restriction to the
centred cube from monotonicity of the measure.
-/

set_option linter.unusedSectionVars false

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

/-! ## An elementary estimate

The absolute value of a product of four factors, the second of which is nonnegative. -/

private lemma abs_mul4_le {p q r s P Q R S : ℝ}
    (hp : |p| ≤ P) (hq : q ≤ Q) (hr : |r| ≤ R) (hs : |s| ≤ S)
    (hq0 : 0 ≤ q) (hP0 : 0 ≤ P) (hQ0 : 0 ≤ Q) (hR0 : 0 ≤ R) (_hS0 : 0 ≤ S) :
    |p * q * r * s| ≤ P * Q * R * S := by
  have hfac : |p * q * r * s| = |p| * q * |r| * |s| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hq0]
  have h1 : |p| * q ≤ P * Q := mul_le_mul hp hq hq0 hP0
  have h2 : |r| * |s| ≤ R * S := mul_le_mul hr hs (abs_nonneg s) hR0
  calc |p * q * r * s| = (|p| * q) * (|r| * |s|) := by rw [hfac]; ring
    _ ≤ (P * Q) * (R * S) :=
        mul_le_mul h1 h2 (mul_nonneg (abs_nonneg r) (abs_nonneg s)) (mul_nonneg hP0 hQ0)
    _ = P * Q * R * S := by ring

/-! ## The genuine set -/

/-- The set of flat coordinates on which the chart `j` is genuine (`‖z‖ < σ j`) and the
reconstruction `Rstar i u` does not vanish (`ζ i (pt j z) ≠ 0`). -/
private def cgenuineSet (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | ‖z‖ < D.σ j ∧ D.ζ i (D.pt j z) ≠ 0}

private lemma cgenuineSet_mem (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    z ∈ cgenuineSet D i j ↔ ‖z‖ < D.σ j ∧ D.ζ i (D.pt j z) ≠ 0 := Iff.rfl

private lemma isOpen_cgenuineSet (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    IsOpen (cgenuineSet D i j) := by
  have hcontζ : ContinuousOn (fun z => D.ζ i (D.pt j z)) (sigmaBall D j) :=
    (D.hζsm i).continuous.comp_continuousOn
      ((continuousOn_pt_sigmaClosedBall' D j).mono (fun z hz => by
        have hz' : ‖z‖ < D.σ j := hz
        exact le_of_lt hz'))
  have h := ContinuousOn.isOpen_inter_preimage hcontζ (isOpen_sigmaBall' D j)
    (isOpen_ne (x := (0 : ℝ)))
  have hset : sigmaBall D j ∩ (fun z => D.ζ i (D.pt j z)) ⁻¹' {y : ℝ | y ≠ 0}
      = cgenuineSet D i j := by
    ext z
    simp only [cgenuineSet, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, mem_sigmaBall]
  rw [hset] at h
  exact h

private lemma isBounded_cgenuineSet (D : B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Bornology.IsBounded (cgenuineSet D i j) :=
  (isBounded_sigmaBall' D j).subset (fun z hz => by
    rw [mem_sigmaBall]
    exact ((cgenuineSet_mem D i j z).mp hz).1)

/-! ## The target -/

theorem contDiff_integrableOn_Rpair
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
    (j : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    MeasureTheory.IntegrableOn
      (fun z => D.R j (D.Rstar i u) a b z * D.R j k a b z)
      (Work.Diff.STE.B3Data.centreCube (E := E)) MeasureTheory.volume := by
  classical
  -- the two-sided density bound and the bound of the reconstruction chart matrix
  obtain ⟨c, C₀, hcpos, hC₀pos, hdensb⟩ := dens_bound_sigma D
  have hdens : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (i : ι₀)
      (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → c ≤ D.dens i z ∧ D.dens i z ≤ C :=
    ⟨c, C₀, hcpos, hC₀pos, hdensb⟩
  obtain ⟨CX, hCXnn, hCX⟩ := mat_Rstar_bound D i j u hu hdens a b
  -- bound of the `k`-factor on the closed `σ j`-ball
  obtain ⟨z₀, -, hz₀max⟩ := (isCompact_sigmaClosedBall' D j).exists_isMaxOn
    (nonempty_sigmaClosedBall' D j) ((hk j a b).continuousOn.abs)
  have hMk : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ j →
      |D.R j k a b z| ≤ |D.R j k a b z₀| := fun z hz =>
    hz₀max (by rw [mem_sigmaClosedBall]; exact hz)
  have hMknn : 0 ≤ |D.R j k a b z₀| := abs_nonneg _
  -- the integrand vanishes off the genuine set
  have hzero : ∀ z ∉ cgenuineSet D i j,
      D.R j (D.Rstar i u) a b z * D.R j k a b z = 0 := by
    intro z hz
    rcases not_and_or.mp ((cgenuineSet_mem D i j z).not.mp hz) with h1 | h2
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
      (cgenuineSet D i j) := by
    intro z hz
    obtain ⟨hzlt, hζ⟩ := (cgenuineSet_mem D i j z).mp hz
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
    have hX : ContinuousAt (D.mat j (D.Rstar i u) a b) z :=
      continuousAt_mat_Rstar D i j u hu a b hzlt hζ
    have h1 : ContinuousAt (fun z => D.R j (D.Rstar i u) a b z) z := by
      refine ((hpsi.mul hsqrt).mul hX).congr (Filter.Eventually.of_forall (fun w => ?_))
      simp only [B3Data.R, Pi.mul_apply]
    have h2 : ContinuousAt (fun z => D.R j k a b z) z := (hk j a b).continuousAt
    exact (h1.mul h2).continuousWithinAt
  -- the global bound
  have hbound : ∀ z, ‖D.R j (D.Rstar i u) a b z * D.R j k a b z‖
      ≤ Real.sqrt C₀ * CX * |D.R j k a b z₀| := by
    intro z
    by_cases hz : z ∈ cgenuineSet D i j
    · obtain ⟨hzlt, -⟩ := (cgenuineSet_mem D i j z).mp hz
      have hzle : ‖z‖ ≤ D.σ j := le_of_lt hzlt
      have hdle : D.dens j z ≤ C₀ := (hdensb j z hzle).2
      have hpsi1 : |D.psi j z| ≤ 1 := by
        rw [B3Data.psi, D.hχ1 j z hzle, one_mul]
        exact abs_zeta_le_one D j (D.pt j z)
      have hsq : Real.sqrt (D.dens j z) ≤ Real.sqrt C₀ := Real.sqrt_le_sqrt hdle
      have hmat1 : |D.mat j (D.Rstar i u) a b z| ≤ CX := hCX z hzle
      have hR2 : |D.R j k a b z| ≤ |D.R j k a b z₀| := hMk z hzle
      have hdeq : D.R j (D.Rstar i u) a b z
          = D.psi j z * Real.sqrt (D.dens j z) * D.mat j (D.Rstar i u) a b z := rfl
      rw [Real.norm_eq_abs, hdeq]
      calc |D.psi j z * Real.sqrt (D.dens j z) * D.mat j (D.Rstar i u) a b z
              * D.R j k a b z|
          ≤ 1 * Real.sqrt C₀ * CX * |D.R j k a b z₀| :=
            abs_mul4_le hpsi1 hsq hmat1 hR2 (Real.sqrt_nonneg _) zero_le_one
              (Real.sqrt_nonneg _) hCXnn hMknn
        _ = Real.sqrt C₀ * CX * |D.R j k a b z₀| := by ring
    · rw [hzero z hz, norm_zero]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCXnn) hMknn
  -- assemble
  have hInt : Integrable (fun z => D.R j (D.Rstar i u) a b z * D.R j k a b z) volume :=
    integrable_of_continuousOn_of_bound (isOpen_cgenuineSet D i j) (isBounded_cgenuineSet D i j)
      hcont hzero hbound
  exact hInt.mono_measure Measure.restrict_le_self

end Work.Diff.STE.B3
