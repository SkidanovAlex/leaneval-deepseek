/-
# `Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_sub_aux`

The linearity certificate for `L₁₂` used by the `Tlim_bounds` assembly, proved here from scratch
(so that the assembly does not depend on the outcome of a concurrent delivery at the same
interface).

`L₁₂ a(0) - L₁₂ b(0) = L₁₂ (a - b)(0)` for two profiles `a`, `b` which are
* continuous on the open quadrant `Q0 = (0,∞) × (0,π/2)`, and
* dominated by `A·Rwt·(1+·)⁻¹` resp. `B·Rwt·(1+·)⁻¹`, `Rwt z = z^{3/2}/(1+z)²`.

The route is the pre-existing `Work.FTS.StrongEps.EComparison.L12_sub_of_integrable`, whose four
integrability inputs are produced by

* **continuity on the open quadrant**: the slices `θ ↦ K(θ)·a(s,θ)/s` are a.e. strongly
  measurable for every `s > 0` (`Work.Spaces.aesm_slice_of_continuousOn_Qd`) and the density
  `s ↦ L₁₂dens a s` is a.e. strongly measurable on `(0,∞)`
  (`Work.Spaces.aesm_of_continuousOn_Qd` + `AEStronglyMeasurable.integral_prod_right'`);
* **the majorant**: `|K(θ)·a(s,θ)/s| ≤ 3·A·Rwt s/((1+s)s)`, and
  `Rwt s/((1+s)s) = s^{1/2}/(1+s)³ ≤ s^{1/2}/(1+s)²`, which is integrable on `(0,∞)`
  (`RXT.Sys.MajorantPieces.sqrt_div_sq_Ioi_integral_le`, integral `≤ 3`);
* the elementary `∫_{Iθ} c dθ = c·(π/2)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS_RegExport.RXT.L12Iter.Basic
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS_RegExport.RXT.Sys.MajorantPieces.sqrt_div_sq_Ioi_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXR5L.Auxiliary

set_option autoImplicit false

local notation "Rwt" => Work.FTS_RegExport.RXT.L12Iter.Rwt

/-- The integral of a constant over `Iθ = [0,π/2]` is the constant times `π/2`. -/
private theorem integral_Iθ_const (c : ℝ) :
    (∫ _θ in Work.Spaces.Iθ, c) = c * (Real.pi / 2) := by
  rw [Work.Elliptic.integral_Iθ_eq_interval, intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- The angular weight `K(θ) = 3 sin θ cos²θ` is continuous on the open quadrant. -/
private theorem continuousOn_K_Q0 :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2) Work.FTS.EllipticEst.Q0 := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.K p.2)
      = fun p : ℝ × ℝ => 3 * Real.sin p.2 * Real.cos p.2 ^ 2 := by
    funext p
    rw [Work.Spaces.K]
  rw [hfun]
  exact ((continuous_const.mul (Real.continuous_sin.comp continuous_snd)).mul
    ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn

/-- The joint integrand `(s,θ) ↦ K(θ)·a(s,θ)/s` is continuous on the open quadrant. -/
private theorem continuousOn_integrand {a : ℝ → ℝ → ℝ}
    (hca : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry a p / p.1)
      Work.FTS.EllipticEst.Q0 := by
  refine (continuousOn_K_Q0.mul hca).div continuous_fst.continuousOn ?_
  intro p hp
  exact ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1

/-- The pointwise domination of the angular integrand, including the two angular endpoints
(where `K` vanishes). -/
private theorem integrand_bound {a : ℝ → ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hba : ∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |a s θ| ≤ A * (Rwt s / (1 + s)))
    {s : ℝ} (hs : 0 < s) :
    ∀ θ ∈ Work.Spaces.Iθ,
      ‖Work.Spaces.K θ * a s θ / s‖ ≤ 3 * (A * (Rwt s / (1 + s))) / s := by
  intro θ hθ
  have hC : 0 ≤ 3 * (A * (Rwt s / (1 + s))) / s := by
    have h1 : 0 ≤ A * (Rwt s / (1 + s)) :=
      mul_nonneg hA (div_nonneg (Work.FTS_RegExport.RXT.L12Iter.Rwt_nonneg hs.le) (by linarith))
    positivity
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · subst h0
    rw [Work.Spaces.K]
    simp
    exact hC
  · rcases eq_or_lt_of_le hθ.2 with h1 | h1
    · subst h1
      have hK0 : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]
        norm_num
      rw [hK0, zero_mul, zero_div, norm_zero]
      exact hC
    · have h1' := hba s θ hs ⟨h0, h1⟩
      have hK : |Work.Spaces.K θ| ≤ 3 := by
        rw [← Work.Elliptic.Ktheta_eq_K]
        exact Work.FTS_RegExport.RXT.L12Iter.abs_Ktheta_le_three θ
      have hnum : |Work.Spaces.K θ| * |a s θ| ≤ 3 * (A * (Rwt s / (1 + s))) :=
        mul_le_mul hK h1' (abs_nonneg _) (by norm_num)
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hs]
      exact div_le_div_of_nonneg_right hnum hs.le

/-- **The angular slice of the datum is integrable.**  For `a` continuous on the open quadrant and
dominated by `A·Rwt·(1+·)⁻¹`, the slice `θ ↦ K(θ)·a(s,θ)/s` is integrable on `Iθ` for every
`s > 0`. -/
private theorem integrableOn_slice_of_bdd {a : ℝ → ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hca : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hba : ∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |a s θ| ≤ A * (Rwt s / (1 + s))) :
    ∀ s ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ => Work.Spaces.K θ * a s θ / s) Work.Spaces.Iθ := by
  intro s hs
  have hs0 : 0 < s := hs
  have haesm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ * a s θ / s)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry a p / p.1)
      (continuousOn_integrand hca) hs0
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const
    (3 * (A * (Rwt s / (1 + s))) / s)) haesm ?_
  rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall (integrand_bound hA hba hs0)

/-- **The `L₁₂`-density of the datum is integrable on `(0,∞)`.** -/
private theorem integrableOn_dens_of_bdd {a : ℝ → ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hca : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hba : ∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |a s θ| ≤ A * (Rwt s / (1 + s))) :
    IntegrableOn (Work.Construction.L12dens a) (Set.Ioi (0 : ℝ)) := by
  -- a.e. strong measurability of the density on `(0,∞)`
  have haesmIz : AEStronglyMeasurable
      (fun z => ∫ θ, Work.Spaces.K θ * Function.uncurry a (z, θ) / z
        ∂(volume.restrict Work.Spaces.Iθ)) (volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 * Function.uncurry a p / p.1)
      (continuousOn_integrand hca)).integral_prod_right'
  have haesm : AEStronglyMeasurable (Work.Construction.L12dens a)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    MeasureTheory.AEStronglyMeasurable.mono_set (fun z hz => (Set.mem_Ioi.mp hz).le) haesmIz
  -- the integrable majorant `3·(π/2)·A·Rwt s/s`
  obtain ⟨hint, -⟩ :=
    Work.FTS_RegExport.RXT.Sys.MajorantPieces.sqrt_div_sq_Ioi_integral_le (z := 0) le_rfl
  have hmaj : Integrable (fun s : ℝ => 3 * (Real.pi / 2) * A * (Rwt s / s))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    refine (hint.const_mul (3 * (Real.pi / 2) * A)).congr ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
    show 3 * (Real.pi / 2) * A * (s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2)
      = 3 * (Real.pi / 2) * A * (Rwt s / s)
    rw [Work.FTS_RegExport.RXT.L12Iter.Rwt_div s hs]
  refine MeasureTheory.Integrable.mono' hmaj haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 < s := hs
  have hR : 0 ≤ Rwt s := Work.FTS_RegExport.RXT.L12Iter.Rwt_nonneg hs0.le
  have hRs : 0 ≤ Rwt s / s := div_nonneg hR hs0.le
  have hs1 : (0 : ℝ) < 1 + s := by linarith
  -- the inner mean inequality
  have hmain := MeasureTheory.norm_integral_le_of_norm_le
    (μ := volume.restrict Work.Spaces.Iθ)
    (f := fun θ => Work.Spaces.K θ * a s θ / s)
    (g := fun _ : ℝ => 3 * (A * (Rwt s / (1 + s))) / s)
    (MeasureTheory.integrable_const (3 * (A * (Rwt s / (1 + s))) / s))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => integrand_bound hA hba hs0 θ hθ))
  have hval : (∫ _θ in Work.Spaces.Iθ, 3 * (A * (Rwt s / (1 + s))) / s)
      = 3 * (A * (Rwt s / (1 + s))) / s * (Real.pi / 2) := integral_Iθ_const _
  have hdens : ‖Work.Construction.L12dens a s‖
      ≤ 3 * (A * (Rwt s / (1 + s))) / s * (Real.pi / 2) := by
    rw [Work.Construction.L12dens, Work.FM.L12dens]
    exact le_trans hmain (le_of_eq hval)
  calc ‖Work.Construction.L12dens a s‖
      ≤ 3 * (A * (Rwt s / (1 + s))) / s * (Real.pi / 2) := hdens
    _ = 3 * (Real.pi / 2) * A * (Rwt s / s) / (1 + s) := by ring
    _ ≤ 3 * (Real.pi / 2) * A * (Rwt s / s) := by
        rw [div_le_iff₀ hs1]
        have hnn : 0 ≤ 3 * (Real.pi / 2) * A * (Rwt s / s) :=
          mul_nonneg (mul_nonneg (by positivity) hA) hRs
        nlinarith [hnn, hs0]

/-- **Linearity of `L₁₂` in its profile, for continuous boundedly-dominated data.** -/
theorem L12_sub_of_bdd_proved {a b : ℝ → ℝ → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hca : ContinuousOn (Function.uncurry a) Work.FTS.EllipticEst.Q0)
    (hcb : ContinuousOn (Function.uncurry b) Work.FTS.EllipticEst.Q0)
    (hba : ∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |a s θ| ≤ A * (Rwt s / (1 + s)))
    (hbb : ∀ s θ : ℝ, 0 < s → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |b s θ| ≤ B * (Rwt s / (1 + s))) :
    Work.Construction.L12 a 0 - Work.Construction.L12 b 0
      = Work.Construction.L12 (fun z θ => a z θ - b z θ) 0 :=
  (Work.FTS.StrongEps.EComparison.L12_sub_of_integrable (z := 0)
    (integrableOn_slice_of_bdd hA hca hba)
    (integrableOn_slice_of_bdd hB hcb hbb)
    (integrableOn_dens_of_bdd hA hca hba)
    (integrableOn_dens_of_bdd hB hcb hbb)).symm

end Work.FTS_RegExport.RXR5L.Auxiliary
