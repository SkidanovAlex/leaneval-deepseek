import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.VocabO
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PggParts` — the parts of the `gg`-row estimate

The five `gg`-pieces of the §8 nonlinearity `N` are estimated in the angular norm

  `E(f) = ∫⁻ r in Ioi 0, r⁻¹ · (∫⁻ θ in Iθ, |K(θ) · f r θ|)`.

Every piece is a product `A·B` of an elliptic coefficient `A` (`Rop`, `Uop/sin2θ`,
`Vop`, or the angular moment `FK g`) and one of the three *slots* `g`, `D_θ g`, `D_z g`
of the datum.  The route is Cauchy–Schwarz in `θ`, then the weighted `H⁴`-energy bound
`∫ w·(slot)² ≤ HkSq α 4 g`, then Cauchy–Schwarz in `r` with `r⁻¹ = w^{1/2}/(1+r)`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)

/-! ## The angular energy functionals -/

/-- `Φ₀(G)(r) = ∫_θ (G r θ)²`: the angular `L²`-energy of the `(0,0)`-slot. -/
def Phi0 (G : ℝ → ℝ → ℝ) : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2

/-- `Φ₁(G)(r) = ∫_θ (D_θG r θ)²`: the angular `L²`-energy of the `(0,1)`-slot. -/
def Phi1 (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth G z θ) ^ 2

/-- `Φ₂(G)(r) = ∫_θ (D_zG r θ)²`: the angular `L²`-energy of the `(1,0)`-slot. -/
def Phi2 (G : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2

theorem Phi0_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Phi0 G z :=
  MeasureTheory.integral_nonneg fun θ => sq_nonneg _

theorem Phi1_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Phi1 G z :=
  MeasureTheory.integral_nonneg fun θ => sq_nonneg _

theorem Phi2_nonneg (G : ℝ → ℝ → ℝ) (z : ℝ) : 0 ≤ Phi2 G z :=
  MeasureTheory.integral_nonneg fun θ => sq_nonneg _

/-- The slice at `z = 0` of a function vanishing on the angular boundary is a.e. measurable. -/
theorem aesm_slice_zero_of_axis {G : ℝ → ℝ → ℝ}
    (h0 : ∀ θ ∈ Work.Spaces.Iθ, G 0 θ = 0) :
    MeasureTheory.AEStronglyMeasurable (fun θ => G 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine MeasureTheory.AEStronglyMeasurable.congr
    (f := fun _ : ℝ => (0 : ℝ)) aestronglyMeasurable_const ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
    measurableSet_Icc)] with θ hθ
  exact (h0 θ hθ).symm

/-- The same for the `(0,1)`-slot. -/
theorem aesm_slice_zero_Dth_of_axis {G : ℝ → ℝ → ℝ}
    (h0 : ∀ θ ∈ Work.Spaces.Iθ, G 0 θ = 0) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dth G 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  refine MeasureTheory.AEStronglyMeasurable.congr
    (f := fun _ : ℝ => (0 : ℝ)) aestronglyMeasurable_const ?_
  filter_upwards [ae_mem_Ioo_Iθ_aux] with θ hθ
  have hnb : (fun θ' => (0 : ℝ)) =ᶠ[𝓝 θ] (fun θ' => G 0 θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact (h0 θ' ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩).symm
  have hp : Work.Spaces.pth G 0 θ = 0 := by
    rw [Work.Spaces.pth, ← Filter.EventuallyEq.deriv_eq hnb]
    simp
  show (0 : ℝ) = Work.Spaces.Dth G 0 θ
  rw [Work.Spaces.Dth, hp, mul_zero]

/-- The `(1,0)`-slot at `z = 0` vanishes identically. -/
theorem aesm_slice_zero_Dz (G : ℝ → ℝ → ℝ) :
    MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dz G 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hzero : (fun θ => Work.Spaces.Dz G 0 θ) = fun _ => (0 : ℝ) := by
    funext θ
    simp [Work.Spaces.Dz]
  rw [hzero]
  exact aestronglyMeasurable_const

/-- The energy facts for the `(0,0)`-slot, from `angE_w_le_HkSq`. -/
theorem Phi0_props {α : ℝ} {G : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad G)
    (hmem : Work.Spaces.HkMem α 4 G)
    (hsl0 : MeasureTheory.AEStronglyMeasurable (fun θ => G 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∀ r, 0 ≤ Phi0 G r) ∧
    (∀ r, 0 < r → MeasureTheory.IntegrableOn (fun θ => (G r θ) ^ 2) Work.Spaces.Iθ) ∧
    AEMeasurable (Phi0 G) (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
    MeasureTheory.IntegrableOn (fun r => Work.Spaces.w r * Phi0 G r) (Set.Ioi 0) ∧
    (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Phi0 G r) ≤ Work.Spaces.HkSq α 4 G := by
  have hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ => G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
    · rw [← h]; exact hsl0
    · exact aesm_slice_of_smoothQuad hsq h
  obtain ⟨h1, h2, h3, h4⟩ :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.angE_w_le_HkSq (α := α) (k := 4) (f := G) (B := G)
      hmem hsl (aesm_uncurry_of_smoothQuad hsq)
      (fun z hz => ae_w_mul_sq_self_le_HkIntegrand α hz)
  exact ⟨fun r => Phi0_nonneg G r, h1, h2.aemeasurable, h3, h4⟩

/-- The energy facts for the `(0,1)`-slot, from `angE_w_le_HkSq`. -/
theorem Phi1_props {α : ℝ} {G : ℝ → ℝ → ℝ} (hα : 0 ≤ α)
    (hsq : Work.FTS.LocData.SmoothQuad G) (hmem : Work.Spaces.HkMem α 4 G)
    (hsl0 : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.Dth G 0 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∀ r, 0 ≤ Phi1 G r) ∧
    (∀ r, 0 < r → MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Dth G r θ) ^ 2)
      Work.Spaces.Iθ) ∧
    AEMeasurable (Phi1 G) (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
    MeasureTheory.IntegrableOn (fun r => Work.Spaces.w r * Phi1 G r) (Set.Ioi 0) ∧
    (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Phi1 G r) ≤ Work.Spaces.HkSq α 4 G := by
  have hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.Dth G z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
    · rw [← h]; exact hsl0
    · exact aesm_slice_Dth_of_smoothQuad hsq h
  obtain ⟨h1, h2, h3, h4⟩ :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.angE_w_le_HkSq (α := α) (k := 4) (f := G)
      (B := Work.Spaces.Dth G) hmem hsl (aesm_uncurry_Dth_of_smoothQuad hsq)
      (fun z hz => ae_w_mul_sq_Dth_le_HkIntegrand α hα hz)
  exact ⟨fun r => Phi1_nonneg G r, h1, h2.aemeasurable, h3, h4⟩

/-- The energy facts for the `(1,0)`-slot, from `angE_w_le_HkSq`. -/
theorem Phi2_props {α : ℝ} {G : ℝ → ℝ → ℝ} (hsq : Work.FTS.LocData.SmoothQuad G)
    (hmem : Work.Spaces.HkMem α 4 G) :
    (∀ r, 0 ≤ Phi2 G r) ∧
    (∀ r, 0 < r → MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.Dz G r θ) ^ 2)
      Work.Spaces.Iθ) ∧
    AEMeasurable (Phi2 G) (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
    MeasureTheory.IntegrableOn (fun r => Work.Spaces.w r * Phi2 G r) (Set.Ioi 0) ∧
    (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Phi2 G r) ≤ Work.Spaces.HkSq α 4 G := by
  have hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable
      (fun θ => Work.Spaces.Dz G z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h | h
    · rw [← h]; exact aesm_slice_zero_Dz G
    · exact aesm_slice_Dz_of_smoothQuad hsq h
  obtain ⟨h1, h2, h3, h4⟩ :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.angE_w_le_HkSq (α := α) (k := 4) (f := G)
      (B := Work.Spaces.Dz G) hmem hsl (aesm_uncurry_Dz_of_smoothQuad hsq)
      (fun z hz => ae_w_mul_sq_Dz_le_HkIntegrand α hz)
  exact ⟨fun r => Phi2_nonneg G r, h1, h2.aemeasurable, h3, h4⟩

/-! ## The two outer assembly lemmas -/

/-! The two-sqrt form of the outer Cauchy–Schwarz is proved here directly (the sibling
module `PggTools/outer_weight_sqrt_pair.lean` states it too, but its auxiliary names collide
with those of `PggTools/outer_weight_le.lean`, so the two modules cannot be imported
together; the single-sqrt tool is imported above, the pair form is proved below). -/










theorem continuous_K : Continuous Work.Spaces.K := by
  show Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2
  fun_prop

theorem abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have h1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  have h2 : Real.cos θ ^ 2 ≤ 1 := Real.cos_sq_le_one θ
  have h3 : (0 : ℝ) ≤ |Real.sin θ| := abs_nonneg _
  have h4 : (0 : ℝ) ≤ Real.cos θ ^ 2 := sq_nonneg _
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
    abs_of_nonneg h4]
  nlinarith


/-! ## The arithmetic of the constants -/





end Work.FTS.Nonlinear.Pieces.rl1Pieces
