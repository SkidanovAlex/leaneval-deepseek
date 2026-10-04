import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.mat_jet_bound_of_energy
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.mat_jet_bound_global
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.iteratedFDeriv_le_of_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform (in the section) first-jet bound for the B3 chart matrices

`Work.Diff.STE.B3.mat_jet_bound_of_energy` bounds the `m`-th flat jet of the chart matrix
`D.mat i h c d` by `C (1 + √(D.ENormB k h))` for every section `h` with smooth chart data
`ChartData h` (and `2m + n < 2k`, `n = finrank ℝ E`), with a constant `C` that is *independent* of
`h`.  The pointwise jet bound requested here turns that into a bound in terms of the
Fourier-side energy, i.e. of the hypothesis `D.BNorm k h ≤ B`:

  `∃ K > 0, ∀ h, ChartData h → D.BNorm k h ≤ B → |∂_r (D.mat i h c d) z| ≤ K` for `‖z‖ ≤ 2 σ i`.

Three things are needed.

* **Uniformity of the two energies.**  `Work.Diff.STE.B3Data.ENormB_le_BNorm` controls `ENormB`
  by `BNorm`, but states its constant *after* the section `h`.  Its proof, however, produces a
  constant that only depends on `D` and `k` (it come from the general
  `Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic`), so we reprove it in the uniform form
  `ENormB_le_BNorm_uniform` (the localised components `D.R i h a b` are smooth by
  `Work.Diff.STE.B3.R_contDiff_of_chartData`, and their periodisations by
  `Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff`).
* **A single partial derivative is a first-order jet.**  `pdR r f z = fderiv ℝ f z (e_r)` is the
  first iterated derivative evaluated on a basis tuple, so it is dominated by the `m = 1` complex
  `pdVec` appearing in `mat_jet_bound_of_energy` (`pdR_le_pdVec_ofReal`, via the complexification
  dictionary `Work.Diff.STE.B3.pdVec_ofReal_eq` and `iteratedFDeriv_one_apply`).
* **Smoothness of `D.mat i h c d` at `z`**, from `ChartData`: this is the proved
  `Work.Diff.STE.B3.mat_contDiffAt_of_chartData` (which uses the `2σ`-ball hypothesis
  `D.htarget`).
-/

namespace Work.Diff.STE.Lead

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- **The physical energy is controlled by the Fourier-side norm, uniformly in the section.**
This is `Work.Diff.STE.B3Data.ENormB_le_BNorm` with the constant pulled out in front of the
section (its proof only uses the section through the smoothness of the localised components, which
`ChartData` provides, and the numerical constant of
`Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic`). -/
private theorem ENormB_le_BNorm_uniform
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.ENormB k h ≤ C * D.BNorm k h := by
  obtain ⟨C, hC, hmain⟩ :=
    Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic (ι := Fin (Module.finrank ℝ E)) k
  refine ⟨C, hC, fun h hh => ?_⟩
  have hRsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) :=
    Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hh
  have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.ENormSq k (D.Rper i h a b)
        ≤ C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) := by
    intro i a b
    obtain ⟨hcd, hper⟩ :=
      Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i h a b (hRsm i a b)
    exact hmain (D.Rper i h a b) hcd hper
  calc D.ENormB k h
      = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq k (D.Rper i h a b) := rfl
    _ ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => hterm i a b
    _ = C * D.BNorm k h := by
        simp only [Work.Diff.STE.B3Data.BNorm, Finset.mul_sum]

/-- **A single flat partial derivative is a first-order jet.**  The `r`-th partial derivative of a
real-valued `f` at `z` (which is *not* assumed differentiable away from `z`) is dominated by the
norm of the first complex iterated partial derivative appearing in
`Work.Diff.STE.B3.mat_jet_bound_of_energy`. -/
private lemma pdR_le_pdVec_ofReal {n : ℕ} {f : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (r : Fin n) :
    |Work.Diff.STE.pdR r f z|
      ≤ ‖Work.Diff.STE.pdVec 1 (fun _ : Fin 1 => r)
          (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) z‖ := by
  have hz : Work.Diff.STE.pdVec 1 (fun _ : Fin 1 => r)
      (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) z
      = ((Work.Diff.STE.pdR r f z : ℝ) : ℂ) := by
    rw [Work.Diff.STE.B3.pdVec_ofReal_eq hf 1 (fun _ : Fin 1 => r)]
    congr 1
    rw [iteratedFDeriv_one_apply]
    rfl
  rw [hz, Complex.norm_real, Real.norm_eq_abs]

end Helpers

theorem mat_jet_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (hk : Module.finrank ℝ E + 4 < 2 * k)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k h ≤ B →
      ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ 2 * D.σ i → |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K := by
  classical
  -- the section-independent energy bounds
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.B3.mat_jet_bound_of_energy (I := I) (M := M) D k
  obtain ⟨C₁, hC₁, hC₁b⟩ := ENormB_le_BNorm_uniform (I := I) (M := M) D k
  have hKpos : 0 < C * (1 + Real.sqrt (C₁ * B)) + 1 := by
    have h1 : 0 ≤ Real.sqrt (C₁ * B) := Real.sqrt_nonneg _
    have h2 : 0 ≤ C * (1 + Real.sqrt (C₁ * B)) := mul_nonneg hC (by linarith)
    linarith
  refine ⟨C * (1 + Real.sqrt (C₁ * B)) + 1, hKpos, ?_⟩
  intro h hh hBn i c d r z hz
  -- `ENormB k h` is bounded, uniformly in `h`, by `C₁ * B`
  have hEN : D.ENormB k h ≤ C₁ * B := by
    have h1 := hC₁b h hh
    have h2 : C₁ * D.BNorm k h ≤ C₁ * B := mul_le_mul_of_nonneg_left hBn hC₁
    linarith
  have hsqrt : Real.sqrt (D.ENormB k h) ≤ Real.sqrt (C₁ * B) := Real.sqrt_le_sqrt hEN
  -- the order-`1` jet bound of `mat_jet_bound_of_energy`
  have hjet := hCb h hh i c d 1 (by omega) (fun _ : Fin 1 => r) z hz
  have hjet' : ‖Work.Diff.STE.pdVec 1 (fun _ : Fin 1 => r)
        (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.mat i h c d y : ℝ) : ℂ)) z‖
      ≤ C * (1 + Real.sqrt (C₁ * B)) := by
    refine hjet.trans (mul_le_mul_of_nonneg_left ?_ hC)
    linarith
  -- convert the complex jet bound into the real partial derivative
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) (D.mat i h c d) z :=
    Work.Diff.STE.B3.mat_contDiffAt_of_chartData (I := I) (M := M) D h hh i c d z
      (D.htarget i z hz)
  have hconv := pdR_le_pdVec_ofReal (f := D.mat i h c d) (z := z) hf r
  linarith

end Work.Diff.STE.Lead
