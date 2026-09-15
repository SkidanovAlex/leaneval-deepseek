import Submission.FUP.HSHoles
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
import Submission.Commons.Analysis.Fourier.fourier_comp_smul
import Submission.Commons.MeasureTheory.Lp.memLp_comp_smul

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 4: the iterated cut-off and its function-theoretic properties

This module builds the *function-level* layer of the induction on scales of Han–Schlag's §5: the
iterated cut-off `W_m = ∏_{n<m} Ψ_{nT}`, the iteration `f_m = W_m · f`, and their `L¹`/`L²`
properties (which is what the Fourier support induction needs).
-/

namespace Submission.FUP

/-- `Ψ_n` as a complex-valued function. -/
noncomputable def psiC (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (n : ℕ) : ℝᵈ → ℂ :=
  fun z => ((Psi Φ L T X n z : ℝ) : ℂ)

lemma psiC_eq_PsiC {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) (X : Set ℝᵈ) :
    psiC Φ L T X n = PsiC Φ L T X n :=
  funext fun z => (PsiC_eq_ofReal hL Φ T n X z).symm

lemma integrable_psiC {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) : Integrable (psiC Φ L T X n) :=
  (integrable_PsiC hL Φ T n hX).congr
    (Filter.Eventually.of_forall fun z => (PsiC_eq_ofReal hL Φ T n X z))

lemma aestronglyMeasurable_psiC {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) : AEStronglyMeasurable (psiC Φ L T X n) volume :=
  (integrable_psiC hL Φ T n hX).aestronglyMeasurable

lemma norm_psiC_le_one {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) (X : Set ℝᵈ) :
    ∀ᵐ z ∂(volume : Measure ℝᵈ), ‖psiC Φ L T X n z‖ ≤ 1 :=
  Filter.Eventually.of_forall fun z => by
    rw [psiC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Psi_nonneg hL Φ T n X z)]
    exact Psi_le_one hL Φ T n X z

lemma memLp_psiC_one {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) : MemLp (psiC Φ L T X n) 1 volume :=
  memLp_one_iff_integrable.mpr (integrable_psiC hL Φ T n hX)

lemma memLp_psiC_top {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) : MemLp (psiC Φ L T X n) ⊤ volume :=
  memLp_top_of_bound (aestronglyMeasurable_psiC hL Φ T n hX) 1 (norm_psiC_le_one hL Φ T n X)

lemma memLp_psiC_two {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T n : ℕ) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) : MemLp (psiC Φ L T X n) 2 volume := by
  rw [memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_psiC hL Φ T n hX)]
  refine ((integrable_psiC hL Φ T n hX).norm).mono'
    ((aestronglyMeasurable_psiC hL Φ T n hX).norm.pow 2) ?_
  filter_upwards [norm_psiC_le_one hL Φ T n X] with z hz
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith [hz, norm_nonneg (psiC Φ L T X n z)]

/-! ## The iterated cut-off `W_m` -/

/-- Han–Schlag's `W_m = ∏_{n<m} Ψ_{nT}`. -/
noncomputable def cutFam (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (m : ℕ) : ℝᵈ → ℝ :=
  ∏ n ∈ Finset.range m, Psi Φ L T X (n * T)

lemma cutFam_apply (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (m : ℕ) (z : ℝᵈ) :
    cutFam Φ L T X m z = ∏ n ∈ Finset.range m, Psi Φ L T X (n * T) z := by
  rw [cutFam, Finset.prod_apply]

lemma cutFam_nonneg {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T m : ℕ) (X : Set ℝᵈ) :
    ∀ z, 0 ≤ cutFam Φ L T X m z := by
  intro z
  rw [cutFam_apply]
  exact Finset.prod_nonneg fun n _ => Psi_nonneg hL Φ T (n * T) X z

lemma cutFam_le_one {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T m : ℕ) (X : Set ℝᵈ) :
    ∀ z, cutFam Φ L T X m z ≤ 1 := by
  intro z
  rw [cutFam_apply]
  exact Finset.prod_le_one (fun n _ => Psi_nonneg hL Φ T (n * T) X z)
    (fun n _ => Psi_le_one hL Φ T (n * T) X z)

lemma cutFam_succ (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (m : ℕ) :
    cutFam Φ L T X (m + 1)
      = fun z => cutFam Φ L T X m z * Psi Φ L T X (m * T) z := by
  funext z
  rw [cutFam_apply, cutFam_apply, Finset.prod_range_succ]

/-- The complexified iterated cut-off, as a product of the `psiC`'s. -/
lemma cutFamC_eq_prod (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (m : ℕ) :
    (fun z => ((cutFam Φ L T X m z : ℝ) : ℂ))
      = ∏ n ∈ Finset.range m, psiC Φ L T X (n * T) := by
  funext z
  rw [Finset.prod_apply, cutFam_apply, Complex.ofReal_prod]
  rfl

lemma aestronglyMeasurable_cutFamC {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T m : ℕ)
    {X : Set ℝᵈ} (hX : X ⊆ cube (-1) 1) :
    AEStronglyMeasurable (fun z => ((cutFam Φ L T X m z : ℝ) : ℂ)) volume := by
  rw [cutFamC_eq_prod]
  exact Finset.aestronglyMeasurable_prod (Finset.range m)
    fun n _ => aestronglyMeasurable_psiC hL Φ T (n*T) hX

/-! ## The tail mass `c''` and the pointwise lower bound on `X` -/

/-- The tail mass `c'' = ∫_{L^{T-1}/10 ≤ ‖z‖} φ` of the cut-off. -/
noncomputable def tailMass (Φ : FupCutoff d) (L T : ℕ) : ℝ :=
  ∫ z in {z : ℝᵈ | (L : ℝ) ^ (T - 1) / 10 ≤ ‖z‖}, Φ.reFun z

lemma tailMass_nonneg (Φ : FupCutoff d) (L T : ℕ) : 0 ≤ tailMass Φ L T :=
  integral_nonneg_of_ae (Filter.Eventually.of_forall fun z => Φ.reFun_nonneg z)

lemma tailMass_le_one (Φ : FupCutoff d) (L T : ℕ) : tailMass Φ L T ≤ 1 := by
  have h := setIntegral_le_integral (μ := volume) Φ.integrable_reFun
    (Filter.Eventually.of_forall fun z => Φ.reFun_nonneg z)
    (s := {z : ℝᵈ | (L : ℝ) ^ (T - 1) / 10 ≤ ‖z‖})
  rw [Φ.integral_reFun] at h
  exact h

/-- `Ψ_n ≥ 1 - c''` on `X` (Han–Schlag (5-4), for points of `X`). -/
lemma Psi_lower_on_X {L T n : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) {x : ℝᵈ} (hx : x ∈ X) :
    1 - tailMass Φ L T ≤ Psi Φ L T X n x := by
  have h := Psi_lower hL hT Φ X (subset_Sset (n := n + 1) (by omega) hX hx)
  change 1 - (∫ z in {z : ℝᵈ | (L : ℝ) ^ (T - 1) / 10 ≤ ‖z‖}, Φ.reFun z) ≤ Psi Φ L T X n x
  exact h

/-- **The lower bound for the iterated cut-off**: `W_m ≥ (1-c'')^m` on `X`. -/
theorem cutFam_lower {L T : ℕ} (hL : 1 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) (m : ℕ) :
    ∀ x ∈ X, (1 - tailMass Φ L T) ^ m ≤ cutFam Φ L T X m x := by
  intro x hx
  have hc0 : 0 ≤ 1 - tailMass Φ L T := by linarith [tailMass_le_one Φ L T]
  have hprod : ∏ _n ∈ Finset.range m, (1 - tailMass Φ L T)
      = (1 - tailMass Φ L T) ^ m := by
    rw [Finset.prod_const, Finset.card_range]
  rw [cutFam_apply, ← hprod]
  refine Finset.prod_le_prod (fun n _ => hc0) (fun n _ => ?_)
  exact Psi_lower_on_X hL hT Φ hX hx

/-! ## The iterated functions `f_m = W_m · f` -/

/-- Han–Schlag's `f_m = (∏_{n<m} Ψ_{nT}) · f`. -/
noncomputable def indFun (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (m : ℕ)
    (f : ℝᵈ → ℂ) : ℝᵈ → ℂ :=
  fun z => ((cutFam Φ L T X m z : ℝ) : ℂ) * f z

lemma indFun_zero (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (f : ℝᵈ → ℂ) :
    indFun Φ L T X 0 f = f := by
  funext z
  rw [indFun, cutFam_apply]
  simp

lemma indFun_succ (Φ : FupCutoff d) (L T : ℕ) (X : Set ℝᵈ) (m : ℕ) (f : ℝᵈ → ℂ) :
    indFun Φ L T X (m + 1) f = psiC Φ L T X (m * T) * indFun Φ L T X m f := by
  funext z
  simp only [indFun, cutFam_succ, Pi.mul_apply, psiC]
  push_cast
  ring

lemma memLp_indFun_two {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T m : ℕ) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) {f : ℝᵈ → ℂ} (hf : MemLp f 2 volume) :
    MemLp (indFun Φ L T X m f) 2 volume := by
  show MemLp (fun z => ((cutFam Φ L T X m z : ℝ) : ℂ) * f z) 2 volume
  exact hf.of_le ((aestronglyMeasurable_cutFamC hL Φ T m hX).mul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (cutFam_nonneg hL Φ T m X z)]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutFam_le_one hL Φ T m X z))

lemma memLp_indFun_one {L : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) (T m : ℕ) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) {f : ℝᵈ → ℂ} (hf : MemLp f 2 volume) (hm : 1 ≤ m) :
    MemLp (indFun Φ L T X m f) 1 volume := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [indFun_succ]
  exact MemLp.mul (p := 2) (q := 2) (r := 1) (memLp_indFun_two hL Φ T k hX hf)
    (memLp_psiC_two hL Φ T (k*T) hX)

end Submission.FUP
