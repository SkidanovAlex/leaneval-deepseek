import Submission.FUP.HSSets
import Submission.FUP.Metric
import Submission.Commons.Analysis.Fourier.fourier_mul_support_of_integrable
import Submission.Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 2: the growth of the Fourier support in the induction on scales

The induction on scales of Han–Schlag's §5 multiplies a function with Fourier support in `Y`
successively by the cut-offs `Ψ_{nT}`, each of which has Fourier support in the ball of radius
`L^{(n+1)T}` (with the normalised cut-off of `HSSets.exists_fupCutoff_radius_le_one`).  This module
contains

* `ellSum L T m = ∑_{n<m} L^{(n+1)T}`, the (upper bound on the) radius of the Fourier support of
  `f_m = ∏_{n<m} Ψ_{nT} · f`, and the arithmetic bound
  `ellSum L T m * L^{-mT} ≤ 2` (`ellSum_mul_inv_pow_le`);
* the predicate `FourierSuppIn f S` ("the Fourier transform of `f` vanishes off `S`") for
  `f ∈ L¹ ∩ L²`, together with the transfer lemma
  `FourierSuppIn f S → (𝓕 g = 0` off `E`) → FourierSuppIn (g * f) (S + E)`
  (`fourierSuppIn_mul`), which is the induction step.
-/

namespace Submission.FUP

/-- `∑_{n<m} L^{(n+1)T}`: the radius of the Fourier support of `∏_{n<m} Ψ_{nT}`. -/
noncomputable def ellSum (L T : ℕ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.range m, (L : ℝ) ^ ((n + 1) * T)

lemma ellSum_succ (L T m : ℕ) :
    ellSum L T (m + 1) = ellSum L T m + (L : ℝ) ^ ((m + 1) * T) := by
  rw [ellSum, Finset.sum_range_succ, ← ellSum]

lemma ellSum_nonneg (L T m : ℕ) : 0 ≤ ellSum L T m :=
  Finset.sum_nonneg fun n _ => pow_nonneg (Nat.cast_nonneg L) _

/-- The geometric growth: `∑_{n<m} L^{(n+1)T} ≤ 2 L^{mT}` for `2 ≤ L`, `1 ≤ T`. -/
lemma ellSum_mul_inv_pow_le {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T) :
    ∀ m : ℕ, ellSum L T m * ((L : ℝ) ^ (m * T))⁻¹ ≤ 2 := by
  have hLr : (1:ℝ) < (L:ℝ) := by
    have h1 : (1:ℕ) < L := by omega
    exact_mod_cast h1
  have hLT : (2:ℝ) ≤ (L:ℝ) ^ T := by
    calc (2:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
      _ = (L:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (L:ℝ) ^ T := pow_le_pow_right₀ hLr.le hT
  have hLTpos : (0:ℝ) < (L:ℝ) ^ T := pow_pos (by linarith) _
  intro m
  induction m with
  | zero => simp [ellSum]
  | succ m ih =>
      rw [ellSum_succ]
      have hpow : (L : ℝ) ^ ((m + 1) * T) = (L : ℝ) ^ (m * T) * (L : ℝ) ^ T := by
        rw [← pow_add]; congr 1; ring
      have hmp : (0:ℝ) < (L : ℝ) ^ (m * T) := pow_pos (by linarith) _
      have hgoal : (ellSum L T m + (L : ℝ) ^ ((m + 1) * T)) * ((L : ℝ) ^ ((m + 1) * T))⁻¹
          = ellSum L T m * ((L : ℝ) ^ (m * T))⁻¹ * ((L : ℝ) ^ T)⁻¹ + 1 := by
        rw [hpow]
        field_simp
      rw [hgoal]
      have h1 : ellSum L T m * ((L : ℝ) ^ (m * T))⁻¹ * ((L : ℝ) ^ T)⁻¹ ≤ 2 * ((L : ℝ) ^ T)⁻¹ :=
        mul_le_mul_of_nonneg_right ih (inv_nonneg.mpr hLTpos.le)
      have h2 : 2 * ((L : ℝ) ^ T)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hLTpos]; exact hLT
      linarith

/-- `f` has Fourier support in `S`, for `f ∈ L¹ ∩ L²` (the function-level Fourier transform). -/
def FourierSuppIn (f : ℝᵈ → ℂ) (S : Set ℝᵈ) : Prop :=
  ∀ ξ : ℝᵈ, ξ ∉ S → 𝓕 f ξ = 0

lemma FourierSuppIn.mono {f : ℝᵈ → ℂ} {S T : Set ℝᵈ} (h : FourierSuppIn f S) (hST : S ⊆ T) :
    FourierSuppIn f T :=
  fun ξ hξ => h ξ (fun hS => hξ (hST hS))

/-- **The induction step**: multiplying by a function whose Fourier transform vanishes off `E`
adds `E` to the support. -/
theorem fourierSuppIn_mul {g f : ℝᵈ → ℂ} (hg1 : Integrable g (volume : Measure ℝᵈ))
    (hg2 : MemLp g 2 (volume : Measure ℝᵈ)) (hf1 : Integrable f (volume : Measure ℝᵈ))
    (hf2 : MemLp f 2 (volume : Measure ℝᵈ)) {S E : Set ℝᵈ} (hS : FourierSuppIn f S)
    (hE : ∀ ξ : ℝᵈ, ξ ∉ E → 𝓕 g ξ = 0) :
    FourierSuppIn (fun x => g x * f x) (addSet S E) := by
  intro ξ hξ
  refine Commons.Analysis.Fourier.fourier_mul_support_of_integrable g f hg1 hg2 hf1 hf2 E S
    hE (fun η hη => hS η hη) ξ ?_
  intro a ha b hb hab
  exact hξ ⟨b, hb, a, ha, by rw [hab, add_comm]⟩

end Submission.FUP
