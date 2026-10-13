import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.LocDataExt.Monotone
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggAux
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.angE_w_le_HkSq
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.inner_lintegral_le
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.outer_weight_le
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.FK_pointwise_le

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

theorem pgw_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem pgw_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)

theorem pgw_measurable : Measurable (fun z : ℝ => Work.Spaces.w z) := by
  unfold Work.Spaces.w
  fun_prop

theorem pgw_inv_le {z : ℝ} (hz : 0 < z) : z⁻¹ ≤ Work.Spaces.w z := by
  have hz2 : 0 < z ^ 2 := pow_pos hz 2
  rw [Work.Spaces.w, le_div_iff₀ hz2]
  have hzz : z⁻¹ * z ^ 2 = z := by
    rw [sq, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hz), one_mul]
  rw [hzz]
  nlinarith [sq_nonneg (z + 1 / 2)]

theorem pg_pair_pointwise {Φ Ψ : ℝ → ℝ}
    (hΦnn : ∀ z, 0 ≤ Φ z) (hΨnn : ∀ z, 0 ≤ Ψ z) (z : ℝ) :
    ENNReal.ofReal z⁻¹ * (ENNReal.ofReal (Φ z)) ^ (1 / 2 : ℝ)
        * (ENNReal.ofReal (Ψ z)) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z))
          * ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Ψ z)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (hΦnn z) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_rpow_of_nonneg (hΨnn z) (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  by_cases hz : 0 < z
  · have hinv : 0 ≤ z⁻¹ := le_of_lt (inv_pos.mpr hz)
    rw [← ENNReal.ofReal_mul hinv,
        ← ENNReal.ofReal_mul (mul_nonneg hinv (Real.sqrt_nonneg _)),
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hle : z⁻¹ ≤ Work.Spaces.w z := pgw_inv_le hz
    have hkey : Real.sqrt (Work.Spaces.w z * Φ z) * Real.sqrt (Work.Spaces.w z * Ψ z)
        = Work.Spaces.w z * (Real.sqrt (Φ z) * Real.sqrt (Ψ z)) := by
      rw [Real.sqrt_mul (pgw_nonneg z), Real.sqrt_mul (pgw_nonneg z)]
      conv_rhs => rw [← Real.mul_self_sqrt (pgw_nonneg z)]
      ring
    calc z⁻¹ * Real.sqrt (Φ z) * Real.sqrt (Ψ z)
        = z⁻¹ * (Real.sqrt (Φ z) * Real.sqrt (Ψ z)) := by ring
      _ ≤ Work.Spaces.w z * (Real.sqrt (Φ z) * Real.sqrt (Ψ z)) :=
          mul_le_mul_of_nonneg_right hle (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      _ = Real.sqrt (Work.Spaces.w z * Φ z) * Real.sqrt (Work.Spaces.w z * Ψ z) := hkey.symm
  · have hz' : z ≤ 0 := le_of_not_gt hz
    rw [ENNReal.ofReal_of_nonpos (inv_nonpos.mpr hz')]
    simp

/-- **The pair (`√Φ·√Ψ`) outer Cauchy–Schwarz.** -/
theorem pg_pairsqrt_le {Φ Ψ : ℝ → ℝ}
    (hΦnn : ∀ z, 0 ≤ Φ z) (hΨnn : ∀ z, 0 ≤ Ψ z)
    (hΦmeas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hΨmeas : AEMeasurable Ψ (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hΦint : MeasureTheory.IntegrableOn (fun z => Work.Spaces.w z * Φ z) (Set.Ioi 0))
    (hΨint : MeasureTheory.IntegrableOn (fun z => Work.Spaces.w z * Ψ z) (Set.Ioi 0)) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * (ENNReal.ofReal (Φ z)) ^ (1 / 2 : ℝ)
        * (ENNReal.ofReal (Ψ z)) ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z)
          * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Ψ z)) := by
  let F : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Φ z))
  let G : ℝ → ENNReal := fun z => ENNReal.ofReal (Real.sqrt (Work.Spaces.w z * Ψ z))
  have hFmeas : AEMeasurable F (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    ((pgw_measurable.aemeasurable.mul hΦmeas).sqrt).ennreal_ofReal
  have hGmeas : AEMeasurable G (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    ((pgw_measurable.aemeasurable.mul hΨmeas).sqrt).ennreal_ofReal
  have hpt : ∀ z, ENNReal.ofReal z⁻¹ * (ENNReal.ofReal (Φ z)) ^ (1 / 2 : ℝ)
        * (ENNReal.ofReal (Ψ z)) ^ (1 / 2 : ℝ) ≤ F z * G z :=
    fun z => pg_pair_pointwise hΦnn hΨnn z
  have h1 : (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * (ENNReal.ofReal (Φ z)) ^ (1 / 2 : ℝ)
        * (ENNReal.ofReal (Ψ z)) ^ (1 / 2 : ℝ))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ), F z * G z :=
    MeasureTheory.lintegral_mono hpt
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (MeasureTheory.volume.restrict (Set.Ioi 0))
      (p := 2) (q := 2) Real.HolderConjugate.two_two (f := F) (g := G) hFmeas hGmeas
  have hFsq : ∀ z, F z ^ (2 : ℝ) = ENNReal.ofReal (Work.Spaces.w z * Φ z) := by
    intro z
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
        Real.sq_sqrt (mul_nonneg (pgw_nonneg z) (hΦnn z))]
  have hGsq : ∀ z, G z ^ (2 : ℝ) = ENNReal.ofReal (Work.Spaces.w z * Ψ z) := by
    intro z
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
        Real.sq_sqrt (mul_nonneg (pgw_nonneg z) (hΨnn z))]
  have hnnΦ : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
      fun z => Work.Spaces.w z * Φ z :=
    Filter.Eventually.of_forall fun z => mul_nonneg (pgw_nonneg z) (hΦnn z)
  have hnnΨ : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi 0)]
      fun z => Work.Spaces.w z * Ψ z :=
    Filter.Eventually.of_forall fun z => mul_nonneg (pgw_nonneg z) (hΨnn z)
  have hF2 : (∫⁻ z in Set.Ioi (0 : ℝ), F z ^ (2 : ℝ))
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z) := by
    rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hFsq)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) hΦint hnnΦ]
  have hG2 : (∫⁻ z in Set.Ioi (0 : ℝ), G z ^ (2 : ℝ))
      = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Ψ z) := by
    rw [MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall hGsq)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) hΨint hnnΨ]
  have hnnintΦ : (0 : ℝ) ≤ ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z :=
    MeasureTheory.integral_nonneg fun z => mul_nonneg (pgw_nonneg z) (hΦnn z)
  have hnnintΨ : (0 : ℝ) ≤ ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Ψ z :=
    MeasureTheory.integral_nonneg fun z => mul_nonneg (pgw_nonneg z) (hΨnn z)
  have hF2' : (∫⁻ z in Set.Ioi (0 : ℝ), F z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z)) := by
    rw [hF2, ENNReal.ofReal_rpow_of_nonneg hnnintΦ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.sqrt_eq_rpow]
  have hG2' : (∫⁻ z in Set.Ioi (0 : ℝ), G z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Ψ z)) := by
    rw [hG2, ENNReal.ofReal_rpow_of_nonneg hnnintΨ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ← Real.sqrt_eq_rpow]
  calc (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * (ENNReal.ofReal (Φ z)) ^ (1 / 2 : ℝ)
        * (ENNReal.ofReal (Ψ z)) ^ (1 / 2 : ℝ))
      ≤ ∫⁻ z in Set.Ioi (0 : ℝ), F z * G z := h1
    _ ≤ (∫⁻ z in Set.Ioi (0 : ℝ), F z ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫⁻ z in Set.Ioi (0 : ℝ), G z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hHolder
    _ = ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z))
          * ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Ψ z)) := by
        rw [hF2', hG2']
    _ = ENNReal.ofReal (Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Φ z)
          * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * Ψ z)) := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

/-- `ofReal (c * √x) = ofReal c * (ofReal x)^{1/2}` for `c, x ≥ 0`. -/
theorem ofReal_mul_sqrt {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) :
    ENNReal.ofReal (c * Real.sqrt x) = ENNReal.ofReal c * (ENNReal.ofReal x) ^ (1 / 2 : ℝ) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hx (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Real.sqrt_eq_rpow x, ENNReal.ofReal_mul hc]

/-- **The outer step.**  An a.e. bound of the inner angular functional by
`ofReal c · (ofReal (Φ r))^{1/2}` integrates against `r⁻¹` with the Hardy weight `w`. -/
theorem outer_of_inner {c Xs : ℝ} (hc : 0 ≤ c) {A B : ℝ → ℝ → ℝ} {Φ : ℝ → ℝ}
    (hinn : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|)
        ≤ ENNReal.ofReal c * (ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ))
    (hΦnn : ∀ r, 0 ≤ Φ r)
    (hΦmeas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hΦint : MeasureTheory.IntegrableOn (fun r => Work.Spaces.w r * Φ r) (Set.Ioi 0))
    (hΦle : (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Φ r) ≤ Xs) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|))
      ≤ ENNReal.ofReal (c * (Real.sqrt 2 * Real.sqrt Xs)) := by
  have hstep : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal c * (ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [hinn] with r hr
    exact mul_le_mul_right hr _
  have hpull : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (ENNReal.ofReal c * (ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)))
      = ENNReal.ofReal c * (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)) := by
    rw [MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall (fun r => by ac_rfl))]
    exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|))
      ≤ _ := hstep
    _ = ENNReal.ofReal c * (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * (ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)) := hpull
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Real.sqrt 2
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Φ r)) :=
        mul_le_mul_right
          (Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.outer_weight_le hΦnn hΦmeas hΦint) _
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Real.sqrt 2 * Real.sqrt Xs) := by
        refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hΦle) (Real.sqrt_nonneg 2)
    _ = ENNReal.ofReal (c * (Real.sqrt 2 * Real.sqrt Xs)) := by
        rw [ENNReal.ofReal_mul hc]

/-- **The outer step, pair form**: both slots carry a square root. -/
theorem outer_of_inner_pair {c Xs Ys : ℝ} (hc : 0 ≤ c) {A B : ℝ → ℝ → ℝ} {Φ Ψ : ℝ → ℝ}
    (hinn : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|)
        ≤ ENNReal.ofReal c * ((ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal (Ψ r)) ^ (1 / 2 : ℝ)))
    (hΦnn : ∀ r, 0 ≤ Φ r) (hΨnn : ∀ r, 0 ≤ Ψ r)
    (hΦmeas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hΨmeas : AEMeasurable Ψ (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hΦint : MeasureTheory.IntegrableOn (fun r => Work.Spaces.w r * Φ r) (Set.Ioi 0))
    (hΨint : MeasureTheory.IntegrableOn (fun r => Work.Spaces.w r * Ψ r) (Set.Ioi 0))
    (hΦle : (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Φ r) ≤ Xs)
    (hΨle : (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Ψ r) ≤ Ys) :
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|))
      ≤ ENNReal.ofReal (c * (Real.sqrt Xs * Real.sqrt Ys)) := by
  have hstep : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|))
      ≤ ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (ENNReal.ofReal c
          * ((ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal (Ψ r)) ^ (1 / 2 : ℝ))) := by
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [hinn] with r hr
    exact mul_le_mul_right hr _
  have hpull : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (ENNReal.ofReal c
        * ((ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)
          * (ENNReal.ofReal (Ψ r)) ^ (1 / 2 : ℝ))))
      = ENNReal.ofReal c * (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * ((ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal (Ψ r)) ^ (1 / 2 : ℝ))) := by
    rw [MeasureTheory.lintegral_congr_ae
      (Filter.Eventually.of_forall (fun r => by ac_rfl))]
    exact MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|))
      ≤ _ := hstep
    _ = ENNReal.ofReal c * (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * ((ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)
            * (ENNReal.ofReal (Ψ r)) ^ (1 / 2 : ℝ))) := hpull
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Real.sqrt
          (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Φ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Ψ r)) := by
        have hcongr : (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
            * ((ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)
              * (ENNReal.ofReal (Ψ r)) ^ (1 / 2 : ℝ)))
            = ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (ENNReal.ofReal (Φ r)) ^ (1 / 2 : ℝ)
                * (ENNReal.ofReal (Ψ r)) ^ (1 / 2 : ℝ) :=
          MeasureTheory.lintegral_congr_ae (Filter.Eventually.of_forall (fun r => by ac_rfl))
        rw [hcongr]
        exact mul_le_mul_right (pg_pairsqrt_le
          hΦnn hΨnn hΦmeas hΨmeas hΦint hΨint) _
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Real.sqrt Xs * Real.sqrt Ys) := by
        refine mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
        exact mul_le_mul (Real.sqrt_le_sqrt hΦle) (Real.sqrt_le_sqrt hΨle)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = ENNReal.ofReal (c * (Real.sqrt Xs * Real.sqrt Ys)) := by
        rw [ENNReal.ofReal_mul hc]

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

/-- From the integrability of the square of the angular slice, the integrability of the
slice against the kernel `K`. -/
theorem integrableOn_mul_K_of_sq {G : ℝ → ℝ → ℝ} {r : ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => G r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (h2 : MeasureTheory.IntegrableOn (fun θ => (G r θ) ^ 2) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn (fun θ => G r θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
  have hconst : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.integrableOn_const
      (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by simp)
  have hmabs : MeasureTheory.AEStronglyMeasurable (fun θ => |G r θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hmeas.norm.congr (Filter.Eventually.of_forall (fun θ => by
      simp only [Real.norm_eq_abs]))
  have hmaj : MeasureTheory.IntegrableOn (fun θ => G r θ ^ 2 + 1) Work.Spaces.Iθ :=
    (h2.add hconst).congr (Filter.Eventually.of_forall (fun θ => by simp [Pi.add_apply]))
  have h1 : MeasureTheory.IntegrableOn (fun θ => |G r θ|) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono' hmaj hmabs ?_
    filter_upwards with θ
    have h4 : |G r θ| ≤ G r θ ^ 2 + 1 := by
      nlinarith [sq_nonneg (|G r θ| - 1), abs_nonneg (G r θ), sq_abs (G r θ)]
    calc ‖|G r θ|‖ = |G r θ| := by rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      _ ≤ G r θ ^ 2 + 1 := h4
  refine MeasureTheory.Integrable.mono' (h1.const_mul 3) (hmeas.mul continuous_K.aestronglyMeasurable) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_mul]
  calc |G r θ| * |Work.Spaces.K θ| ≤ |G r θ| * 3 :=
        mul_le_mul_of_nonneg_left (abs_K_le_three θ) (abs_nonneg _)
    _ = 3 * |G r θ| := by ring

/-! ## The arithmetic of the constants -/

theorem sqrt_pi_div_two_mul_sqrt_two :
    Real.sqrt (Real.pi / 2) * Real.sqrt 2 = Real.sqrt Real.pi := by
  rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ Real.pi / 2) 2]
  norm_num

theorem inv_sqrt_eq_rpow_neg {α : ℝ} (hα : 0 < α) :
    (Real.sqrt α)⁻¹ = α ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow α, ← Real.rpow_neg (le_of_lt hα) (1 / 2)]

theorem sqrt_ten_div_mul_sqrt_pi {α : ℝ} (hα : 0 < α) :
    Real.sqrt (10 / α) * Real.sqrt Real.pi
      = Real.sqrt (10 * Real.pi) * α ^ (-(1 / 2 : ℝ)) := by
  have h10 : (0 : ℝ) ≤ 10 := by norm_num
  have h1 : Real.sqrt (10 / α) = Real.sqrt 10 * (Real.sqrt α)⁻¹ := by
    rw [Real.sqrt_div h10 α, div_eq_mul_inv]
  have h2 := inv_sqrt_eq_rpow_neg hα
  calc Real.sqrt (10 / α) * Real.sqrt Real.pi
      = Real.sqrt 10 * (Real.sqrt α)⁻¹ * Real.sqrt Real.pi := by rw [h1]
    _ = (Real.sqrt 10 * Real.sqrt Real.pi) * (Real.sqrt α)⁻¹ := by ring
    _ = Real.sqrt (10 * Real.pi) * (Real.sqrt α)⁻¹ := by
        rw [← Real.sqrt_mul h10 Real.pi]
    _ = Real.sqrt (10 * Real.pi) * α ^ (-(1 / 2 : ℝ)) := by rw [h2]

theorem alpha_mul_sqrt_ten_div {α : ℝ} (hα : 0 < α) :
    α * Real.sqrt (10 / α) * Real.sqrt Real.pi
      = Real.sqrt (10 * Real.pi) * α ^ (1 / 2 : ℝ) := by
  have h10 : (0 : ℝ) ≤ 10 := by norm_num
  have h1 : Real.sqrt (10 / α) = Real.sqrt 10 * (Real.sqrt α)⁻¹ := by
    rw [Real.sqrt_div h10 α, div_eq_mul_inv]
  have h2 := inv_sqrt_eq_rpow_neg hα
  have h3 : α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 / 2 : ℝ) := by
    conv_rhs => rw [show (1 / 2 : ℝ) = 1 + -(1 / 2) by norm_num, Real.rpow_add hα,
      Real.rpow_one]
  calc α * Real.sqrt (10 / α) * Real.sqrt Real.pi
      = α * (Real.sqrt 10 * (Real.sqrt α)⁻¹) * Real.sqrt Real.pi := by rw [h1]
    _ = α * (Real.sqrt 10 * Real.sqrt Real.pi) * (Real.sqrt α)⁻¹ := by ring
    _ = α * Real.sqrt (10 * Real.pi) * (Real.sqrt α)⁻¹ := by
        rw [← Real.sqrt_mul h10 Real.pi]
    _ = Real.sqrt (10 * Real.pi) * (α * (Real.sqrt α)⁻¹) := by ring
    _ = Real.sqrt (10 * Real.pi) * α ^ (1 / 2 : ℝ) := by rw [h2, h3]

end Work.FTS.Nonlinear.Pieces.rl1Pieces
