import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FzFacts
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SupAbsThOAesm
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.n5Bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.Rl1

set_option autoImplicit false
set_option linter.unusedVariables false


/-! ## Pointwise and integral bounds for the kernel `K(θ) = 3 sinθ cos²θ` -/

/-- `K` is nonnegative on `Iθ`. -/
lemma n5_K_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Spaces.K θ := by
  rw [Work.Spaces.K]
  have h1 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  nlinarith

/-- `K ≤ 3` on `Iθ`. -/
lemma n5_K_le_three {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : Work.Spaces.K θ ≤ 3 := by
  rw [Work.Spaces.K]
  have h1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc : Real.cos θ ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  have h2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
  nlinarith

/-- `K` is measurable. -/
lemma n5_measurable_K : Measurable Work.Spaces.K := by
  change Measurable (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2)
  fun_prop

/-- `K` is integrable on `Iθ`. -/
lemma n5_integrableOn_K : IntegrableOn Work.Spaces.K Work.Spaces.Iθ := by
  refine IntegrableOn.of_bound (μ := volume) ?_ ?_ 3 ?_
  · rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  · exact n5_measurable_K.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (n5_K_nonneg hθ)]
    exact n5_K_le_three hθ

/-- `∫_θ K(θ)² ≤ 3` (from `K² ≤ 3K` and `∫_θ K = 1`). -/
lemma n5_integral_K_sq_le : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) ≤ 3 := by
  have h3K : IntegrableOn (fun θ => 3 * Work.Spaces.K θ) Work.Spaces.Iθ :=
    n5_integrableOn_K.const_mul 3
  refine le_trans (integral_mono_of_nonneg ?_ h3K ?_) ?_
  · exact Eventually.of_forall fun θ => sq_nonneg _
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have h0 := n5_K_nonneg hθ
    have h3 := n5_K_le_three hθ
    have : Work.Spaces.K θ * Work.Spaces.K θ ≤ 3 * Work.Spaces.K θ := by
      nlinarith
    simpa only [pow_two] using this
  · rw [MeasureTheory.integral_const_mul, Work.Coercivity.integral_Itheta_K]
    norm_num

/-! ## The two slice factors -/

/-- **Cauchy–Schwarz slice bound for `g`.**  If the squared slice of `g` is integrable on `Iθ`,
then `∫_θ K(θ)|g(s,θ)| ≤ 4√(∫_θ g(s,θ)²)`; the constant is `√(∫_θK²) ≤ √3 ≤ 4`. -/
lemma n5_K_mul_abs_le {g : Work.FTS.Galerkin.Fn} {s : ℝ} (hs : 0 < s)
    (hg : IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ)
    (hgm : AEStronglyMeasurable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ)) :
    IntegrableOn (fun θ => Work.Spaces.K θ * |g s θ|) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |g s θ|)
        ≤ 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
  have hP0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 :=
    integral_nonneg_of_ae (Eventually.of_forall fun θ => sq_nonneg _)
  -- a.e. strong measurability of the two factors on `Iθ`
  have hg_meas : AEStronglyMeasurable (fun θ => |g s θ|) (volume.restrict Work.Spaces.Iθ) :=
    continuous_abs.comp_aestronglyMeasurable hgm
  have hK_meas : AEStronglyMeasurable Work.Spaces.K (volume.restrict Work.Spaces.Iθ) :=
    n5_measurable_K.aestronglyMeasurable
  have hK2_int : Integrable (fun θ => (Work.Spaces.K θ) ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    have h3K : Integrable (fun θ => 3 * Work.Spaces.K θ) (volume.restrict Work.Spaces.Iθ) :=
      n5_integrableOn_K.const_mul 3
    refine h3K.mono' (hK_meas.pow 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
    have h0 := n5_K_nonneg hθ
    have h3 := n5_K_le_three hθ
    nlinarith
  have hK_mem : MemLp Work.Spaces.K 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq hK_meas).mpr hK2_int
  have hg2_int : Integrable (fun θ => |g s θ| ^ 2) (volume.restrict Work.Spaces.Iθ) := by
    refine hg.congr ?_
    filter_upwards with θ
    rw [sq_abs]
  have hg_mem : MemLp (fun θ => |g s θ|) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq hg_meas).mpr hg2_int
  -- integrability of the product
  have hprod : Integrable (fun θ => Work.Spaces.K θ * |g s θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    have h3abs : Integrable (fun θ => 3 * |g s θ|) (volume.restrict Work.Spaces.Iθ) := by
      have h := hg_mem.const_mul (3 : ℝ)
      simpa only [Pi.mul_apply] using h.integrable (by norm_num)
    refine h3abs.mono' (hK_meas.mul hg_meas) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (n5_K_nonneg hθ) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_right (n5_K_le_three hθ) (abs_nonneg _)
  refine ⟨hprod, ?_⟩
  -- Cauchy–Schwarz in the square form
  have hcs := Work.Spaces.cs_integral (u := Work.Spaces.K) (v := fun θ => |g s θ|)
    (s := Work.Spaces.Iθ) hK_mem hg_mem
  have hle : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |g s θ|) ^ 2
      ≤ 3 * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, |g s θ| ^ 2) = ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 :=
      setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [sq_abs])
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |g s θ|) ^ 2
        ≤ (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, |g s θ| ^ 2) := hcs
      _ = (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2)
            * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by rw [h1]
      _ ≤ 3 * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) :=
          mul_le_mul_of_nonneg_right n5_integral_K_sq_le hP0
  have hX0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |g s θ| :=
    integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (n5_K_nonneg hθ) (abs_nonneg _))
  have h3 : Real.sqrt 3 ≤ 4 := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |g s θ|)
      = Real.sqrt ((∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |g s θ|) ^ 2) :=
        (Real.sqrt_sq hX0).symm
    _ ≤ Real.sqrt (3 * (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) :=
        Real.sqrt_mul (by norm_num) _
    _ ≤ 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) :=
        mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)

/-- **The angular moment of `g` is controlled by the angular energy:**
`|(g,K)_{L²_θ}(s)| ≤ 4√(∫_θ g(s,θ)²)`. -/
lemma n5_FK_abs_le {g : Work.FTS.Galerkin.Fn} {s : ℝ} (hs : 0 < s)
    (hg : IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ)
    (hgm : AEStronglyMeasurable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ)) :
    |Work.Construction.FK g s| ≤ 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) := by
  obtain ⟨hint, hbd⟩ := n5_K_mul_abs_le hs hg hgm
  rw [Work.Construction.FK]
  refine le_trans ?_ hbd
  refine MeasureTheory.norm_integral_le_of_norm_le (f := fun θ => g s θ * Work.Spaces.K θ)
    hint ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (n5_K_nonneg hθ), mul_comm]

/-- **The explicit `F_*` slice bound**: `|F_*(s,θ)| ≤ 20αs/(1+s)²` on `Iθ` for `0 < α ≤ 1`. -/
lemma n5_Fstar_abs_le {α s θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hs : 0 < s)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar α s θ| ≤ 20 * α * s / (1 + s) ^ 2 := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hG := Work.Spaces.Gam_bounds α θ hα hθ
  have hz0 : 0 ≤ 2 * s / (1 + s) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  unfold Work.Construction.Fstar Work.FM.Fstar
  rw [abs_mul, abs_mul, abs_of_nonneg hz0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ α)]
  have hcd : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
    rw [abs_of_nonneg (div_nonneg hG.1 hcpos.le)]
    rw [div_le_iff₀ hcpos]
    nlinarith [hG.2, hc]
  calc α * |Work.Spaces.Gam α θ / Work.Spaces.c α| * (2 * s / (1 + s) ^ 2)
      ≤ α * 10 * (2 * s / (1 + s) ^ 2) := by
        have := mul_le_mul_of_nonneg_right hcd hz0
        nlinarith [hα.le]
    _ = 20 * α * s / (1 + s) ^ 2 := by ring




/-! ## The radial endgame -/







end Work.FTS.Nonlinear.Pieces.Rl1
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FKgFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

/-- The angular interval `[0,1]` (of measure exactly `1`) is contained in `Iθ = [0,π/2]`. -/
theorem Icc01_subset_Iθ : Set.Icc (0 : ℝ) 1 ⊆ Work.Spaces.Iθ := fun θ hθ =>
  ⟨hθ.1, by linarith [hθ.2, Real.pi_gt_three]⟩

/-- The `z`-slice of the `ℋ^k`-integrand of a radial function:
`Phi α k ρ z = ∫_θ HkIntegrand α k (z,θ ↦ ρ z) (z,θ) dθ`.  Its integral over `Iz` is
`HkSq α k (z,θ ↦ ρ z)`. -/
def Phi (α : ℝ) (k : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z _ => ρ z) z θ

theorem Phi_nonneg (α : ℝ) (k : ℕ) (ρ : ℝ → ℝ) (z : ℝ) : 0 ≤ Phi α k ρ z :=
  integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k (fun z _ => ρ z) z θ

theorem Phi_integrable {α : ℝ} {k : ℕ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k (fun z _ => ρ z)) :
    IntegrableOn (Phi α k ρ) Work.Spaces.Iz := hmem.2

theorem Phi_integrable_Ioi {α : ℝ} {k : ℕ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k (fun z _ => ρ z)) :
    IntegrableOn (Phi α k ρ) (Set.Ioi (0 : ℝ)) :=
  (Phi_integrable hmem).mono_set Set.Ioi_subset_Ici_self

theorem Phi_integral_eq_HkSq (α : ℝ) (k : ℕ) (ρ : ℝ → ℝ) :
    ∫ z in Work.Spaces.Iz, Phi α k ρ z = Work.Spaces.HkSq α k (fun z _ => ρ z) := rfl

theorem Phi_integral_Ioi_eq_HkSq (α : ℝ) (k : ℕ) (ρ : ℝ → ℝ) :
    ∫ z in Set.Ioi (0 : ℝ), Phi α k ρ z = Work.Spaces.HkSq α k (fun z _ => ρ z) :=
  (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).trans
    (Phi_integral_eq_HkSq α k ρ)

/-- The pointwise domination on the open quadrant: the `w²`-weighted square of a radial
function is bounded by its `ℋ⁴`-integrand. -/
theorem radial_pointwise_le {α : ℝ} {ρ : ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (ρ z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 (fun z _ => ρ z) z θ := by
  have hw : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hs : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
    linarith [hθ.2]
  have hpow1 : Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    have hpos : (0 : ℝ) ≤ Work.Spaces.eta / 2 := by unfold Work.Spaces.eta; norm_num
    have h := Real.rpow_le_rpow (x := Real.sin (2 * θ)) (y := 1)
      (z := Work.Spaces.eta / 2) hs.le (Real.sin_le_one _) hpos
    simpa using h
  have hpowpos : 0 < Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := Real.rpow_pos_of_pos hs _
  have hle : Work.Spaces.w z
      ≤ Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) := by
    rw [le_div_iff₀ hpowpos]
    nlinarith [hw]
  have hsq : (Work.Spaces.w z) ^ 2
      ≤ (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    rw [sq_le_sq, abs_of_pos hw, abs_of_pos (div_pos hw hpowpos)]
    exact hle
  calc (ρ z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (ρ z) ^ 2 * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = ((fun z _ => ρ z) z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 (fun z _ => ρ z) z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 (fun z _ => ρ z) z θ 0 (by norm_num)

/-- The `z`-slice form of the pointwise domination: the `w²`-weighted square of a radial
function is bounded by the `θ`-integral `Φ` of its `ℋ⁴`-integrand. -/
theorem radial_slot_le_Phi {α : ℝ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 (fun z _ => ρ z)) {z : ℝ} (hz : 0 < z) :
    (ρ z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ Phi α 4 ρ z := by
  have hconst : (∫ θ in Set.Icc (0 : ℝ) 1, ((ρ z) ^ 2 * (Work.Spaces.w z) ^ 2 : ℝ))
      = (ρ z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 - 0)]
    simp
  have h1 : (∫ θ in Set.Icc (0 : ℝ) 1, ((ρ z) ^ 2 * (Work.Spaces.w z) ^ 2 : ℝ))
      ≤ ∫ θ in Set.Icc (0 : ℝ) 1,
          Work.Spaces.HkIntegrand α 4 (fun z _ => ρ z) z θ := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => ?_)
      ((hmem.1 z hz.le).mono_set Icc01_subset_Iθ) ?_
    · positivity
    · rw [MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)).symm]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
        (fun θ hθ => radial_pointwise_le hz
          ⟨hθ.1, by linarith [hθ.2, Real.pi_gt_three]⟩)
  have h2 : (∫ θ in Set.Icc (0 : ℝ) 1,
        Work.Spaces.HkIntegrand α 4 (fun z _ => ρ z) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (fun z _ => ρ z) z θ :=
    MeasureTheory.setIntegral_mono_set (hmem.1 z hz.le)
      (Filter.Eventually.of_forall fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 4 (fun z _ => ρ z) z θ)
      (Filter.Eventually.of_forall fun θ hθ => Icc01_subset_Iθ hθ)
  rw [← hconst]
  exact le_trans h1 h2



/-- `∫_{z>0} |ρ|/(1+z)² ≤ 2·|Rho|_{ℋ⁴}` for a radial function: Cauchy–Schwarz in `z` against
`z²/(1+z)⁴`, the `L²`-factor being `√Φ` (a.e. strongly measurable because `Φ` is integrable
by hypothesis). -/
theorem fk_radialL1_le {α : ℝ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 (fun z _ => ρ z)) :
    ∫ z in Set.Ioi (0 : ℝ), |ρ z| / (1 + z) ^ 2
      ≤ 2 * Work.Spaces.HkNorm α 4 (fun z _ => ρ z) := by
  have hΦi : IntegrableOn (Phi α 4 ρ) (Set.Ioi (0 : ℝ)) := Phi_integrable_Ioi hmem
  have hΦnn : ∀ z, 0 ≤ Phi α 4 ρ z := Phi_nonneg α 4 ρ
  -- `z ↦ √(Φ z)` is square integrable with `∫ (√Φ)² = HkSq`
  have hAesm : AEStronglyMeasurable (fun z => Real.sqrt (Phi α 4 ρ z))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hΦi.aestronglyMeasurable
  have hAint : Integrable (fun z => Real.sqrt (Phi α 4 ρ z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hΦi.congr (Filter.Eventually.of_forall fun z => (Real.sq_sqrt (hΦnn z)).symm)
  have hAmem : MemLp (fun z => Real.sqrt (Phi α 4 ρ z)) 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq hAesm).mpr hAint
  -- the comparison function `z ↦ z²/(1+z)⁴`
  have hBmem : MemLp (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) 2
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := BqSqIntegral.1
  have hBint : ∫ z in Set.Ioi (0 : ℝ), (z ^ 2 / (1 + z) ^ 4) ^ 2 ≤ 2 := BqSqIntegral.2
  -- Cauchy–Schwarz
  have hcs := Work.Spaces.cs_integral hAmem hBmem
  have hA2 : (∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Phi α 4 ρ z) ^ 2)
      = Work.Spaces.HkSq α 4 (fun z _ => ρ z) := by
    rw [← Phi_integral_Ioi_eq_HkSq α 4 ρ]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun z => Real.sq_sqrt (hΦnn z))
  rw [hA2] at hcs
  have hX0 : 0 ≤ Work.Spaces.HkSq α 4 (fun z _ => ρ z) :=
    Work.Spaces.HkSq_nonneg α 4 (fun z _ => ρ z)
  have hII : (∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Phi α 4 ρ z) * (z ^ 2 / (1 + z) ^ 4))
      ≤ 2 * Real.sqrt (Work.Spaces.HkSq α 4 (fun z _ => ρ z)) := by
    have hnn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ),
        Real.sqrt (Phi α 4 ρ z) * (z ^ 2 / (1 + z) ^ 4) :=
      integral_nonneg fun z => mul_nonneg (Real.sqrt_nonneg _) (by positivity)
    have h2 : (∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Phi α 4 ρ z) * (z ^ 2 / (1 + z) ^ 4)) ^ 2
        ≤ Work.Spaces.HkSq α 4 (fun z _ => ρ z) * 2 :=
      hcs.trans (mul_le_mul_of_nonneg_left hBint hX0)
    have h3 : (∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Phi α 4 ρ z) * (z ^ 2 / (1 + z) ^ 4))
        ≤ Real.sqrt (Work.Spaces.HkSq α 4 (fun z _ => ρ z) * 2) :=
      (Real.le_sqrt hnn (by positivity)).mpr h2
    have h4 : Real.sqrt (Work.Spaces.HkSq α 4 (fun z _ => ρ z) * 2)
        ≤ 2 * Real.sqrt (Work.Spaces.HkSq α 4 (fun z _ => ρ z)) := by
      rw [Real.sqrt_mul hX0 2]
      have h2le : Real.sqrt 2 ≤ 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      nlinarith [Real.sqrt_nonneg (Work.Spaces.HkSq α 4 (fun z _ => ρ z)), h2le]
    exact le_trans h3 h4
  refine le_trans ?_ hII
  -- `|ρ|/(1+z)² = (|ρ|·w)·(z²/(1+z)⁴)`
  refine MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => by positivity) ?_ ?_
  · exact memLp_one_iff_integrable.mp (hAmem.mul hBmem)
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    show |ρ z| / (1 + z) ^ 2 ≤ Real.sqrt (Phi α 4 ρ z) * (z ^ 2 / (1 + z) ^ 4)
    have hz' : (0 : ℝ) < z := hz
    have hz0 : z ≠ 0 := ne_of_gt hz'
    have h1z : (1 : ℝ) + z ≠ 0 := by
      have h : (0 : ℝ) < 1 + z := by linarith
      linarith
    have hw0 : 0 ≤ Work.Spaces.w z := by unfold Work.Spaces.w; positivity
    have hsq : (|ρ z| * Work.Spaces.w z) ^ 2 ≤ Phi α 4 ρ z := by
      rw [mul_pow, sq_abs]
      exact radial_slot_le_Phi hmem hz
    have hle : |ρ z| * Work.Spaces.w z ≤ Real.sqrt (Phi α 4 ρ z) :=
      (Real.le_sqrt (mul_nonneg (abs_nonneg _) hw0) (hΦnn z)).mpr hsq
    have hB0 : 0 ≤ z ^ 2 / (1 + z) ^ 4 := by positivity
    have hstep := mul_le_mul_of_nonneg_right hle hB0
    have hid : |ρ z| / (1 + z) ^ 2
        = |ρ z| * Work.Spaces.w z * (z ^ 2 / (1 + z) ^ 4) := by
      unfold Work.Spaces.w
      field_simp
    rw [hid]
    exact hstep


end Work.FTS.Nonlinear.Pieces.rl1Tools
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.Nsplit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

open scoped Real Topology
open MeasureTheory Set Filter

theorem Nsplit {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.LocData.SmoothQuad g) (hΦs : Work.FTS.LocData.SmoothQuad Φs)
    (hΦg : Work.FTS.LocData.SmoothQuad Φg)
    (hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z)
    (hFK : ∀ z : ℝ, 0 < z → Work.Construction.FK (Work.Construction.Ftot α g) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK g z)
    (hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
        = (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
            + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
          + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
            + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
          + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
            + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
          + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ
            + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)
          + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ
            + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ) := by
  intro z θ hq
  have hz : 0 < z := hq.1
  have hzI : z ∈ Set.Ioi (-1 : ℝ) := by rw [Set.mem_Ioi]; linarith
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hq.2
  have hF : Work.FTS.LocData.SmoothQuad (Work.Construction.Fstar α) :=
    Work.FTS.LocData.Fstar_smoothQuad α
  -- ## the identity of the straightened stream functions, near (in `z`) and at (in `θ`) the point
  have hsliceθ : (fun θ' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ')
      = (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ'
          + Work.Construction.PhiTil α g Φg z θ') := by
    funext θ'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z hz]
    ring
  have hslicez : (fun z' => Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z' θ)
      =ᶠ[𝓝 z] (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ
          + Work.Construction.PhiTil α g Φg z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hq.1] with z' hz'
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hL z' hz']
    ring
  have hval : Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
        + Work.Construction.PhiTil α g Φg z θ :=
    congrFun hsliceθ θ
  -- ## differentiability of the `z`- and `θ`-slices of the two pieces
  have hs2 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    have h : Work.Construction.s2 = fun θ' : ℝ => Real.sin (2 * θ') := rfl
    rw [h]
    exact Real.differentiableAt_sin.comp θ
      ((differentiableAt_const (2 : ℝ)).mul differentiableAt_id)
  have hPsi1 : Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs
      = fun z' θ' => Φs z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 (Work.Construction.Fstar α) z' := rfl
  have hPsi2 : Work.Construction.PhiTil α g Φg
      = fun z' θ' => Φg z' θ' - (1 / (4 * α)) * Work.Construction.s2 θ'
          * Work.Construction.L12 g z' := rfl
  have hzs1 : DifferentiableAt ℝ
      (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z' θ) z := by
    rw [hPsi1]
    exact (differentiableAt_slice_z hΦs hzI hθ).sub
      ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
        (differentiableAt_L12_Fstar hα hα1 hz))
  have hzs2 : DifferentiableAt ℝ
      (fun z' => Work.Construction.PhiTil α g Φg z' θ) z := by
    rw [hPsi2]
    exact (differentiableAt_slice_z hΦg hzI hθ).sub
      ((differentiableAt_const (((1 : ℝ) / (4 * α)) * Work.Construction.s2 θ)).mul
        (hL12 z hz))
  have hts1 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ') θ := by
    rw [hPsi1]
    exact (differentiableAt_slice_θ hΦs hzI hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul
        (differentiableAt_const _))
  have hts2 : DifferentiableAt ℝ
      (fun θ' => Work.Construction.PhiTil α g Φg z θ') θ := by
    rw [hPsi2]
    exact (differentiableAt_slice_θ hΦg hzI hθ).sub
      (((differentiableAt_const ((1 : ℝ) / (4 * α))).mul hs2).mul
        (differentiableAt_const _))
  -- ## additivity of `∂_z` and `∂_θ` at the point
  have hpzP : Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ := by
    have hderiv := hslicez.deriv_eq
    have hsum : Work.Spaces.pz (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α g Φg z θ) z θ
        = Work.Spaces.pz (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Spaces.pz (Work.Construction.PhiTil α g Φg) z θ :=
      pz_add_of_diff hzs1 hzs2
    simp only [Work.Spaces.pz] at hsum hderiv ⊢
    exact hderiv.trans hsum
  have hpthP : Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ := by
    have hderiv := congrArg (fun F : ℝ → ℝ => deriv F θ) hsliceθ
    have hsum : Work.Spaces.pth (fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
          + Work.Construction.PhiTil α g Φg z θ) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Spaces.pth (Work.Construction.PhiTil α g Φg) z θ :=
      pth_add_of_diff hts1 hts2
    simp only [Work.Spaces.pth] at hsum hderiv ⊢
    exact hderiv.trans hsum
  -- ## the additivity of the three operators
  have hRop : Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Rop α (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Rop]
    rw [hval, hpzP, hpthP]
    ring
  have hUop : Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Uop]
    rw [hval, hpzP]
    ring
  have hVop : Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α g Φg) z θ := by
    simp only [Work.Construction.Vop]
    rw [hval, hpthP]
    ring
  -- ## additivity of `∂_θ` and `D_z` on `F = F_* + g`
  have hpthF : Work.Spaces.pth (Work.Construction.Ftot α g) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth g z θ :=
    pth_add_of_smoothQuad hF hreg hzI hθ
  have hDzF : Work.Spaces.Dz (Work.Construction.Ftot α g) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz g z θ :=
    Dz_add_of_diff (pz_add_of_smoothQuad hF hreg hzI hθ)
  -- ## the five groups
  have hN1 : Work.Construction.N1 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
        + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ := by
    simp only [Work.Construction.N1, Work.FTS.Nonlin.N1gg, Work.FTS.Nonlin.N1gs,
      Work.FTS.Nonlin.N1sg, Work.FTS.Nonlin.N1ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs, Work.Construction.Ftot]
    rw [hRop]
    ring
  have hN2 : Work.Construction.N2 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
        + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ := by
    simp only [Work.Construction.N2, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.N2gs,
      Work.FTS.Nonlin.N2sg, Work.FTS.Nonlin.N2ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs]
    rw [hUop, hpthF]
    ring
  have hN3 : Work.Construction.N3 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
        + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ := by
    simp only [Work.Construction.N3, Work.FTS.Nonlin.N3gg, Work.FTS.Nonlin.N3gs,
      Work.FTS.Nonlin.N3sg, Work.FTS.Nonlin.N3ss, Work.FTS.Nonlin.PhiTg,
      Work.FTS.Nonlin.PhiTs]
    rw [hVop, hDzF]
    ring
  have hN4 : Work.Construction.N4 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ)
        + (Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ) := by
    simp only [Work.Construction.N4, Work.FTS.Nonlin.N4gg, Work.FTS.Nonlin.N4gs,
      Work.FTS.Nonlin.N4sg, Work.FTS.Nonlin.N4ss, Work.Construction.Ftot]
    simp only [Dth_eq_s2_mul]
    rw [hFK z hz, hpthF]
    ring
  have hN5 : Work.Construction.N5 α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
      = (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ)
        + (Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ) := by
    simp only [Work.Construction.N5, Work.FTS.Nonlin.N5gg, Work.FTS.Nonlin.N5gs,
      Work.FTS.Nonlin.N5sg, Work.FTS.Nonlin.N5ss, Work.Construction.Ftot]
    rw [hFK z hz]
    ring
  rw [Work.Construction.N_eq_sum]
  simp only [Pi.add_apply, hN1, hN2, hN3, hN4, hN5]
  ring

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.Row45gs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option maxHeartbeats 800000

/-!
# `Row45gs` — the `rl¹`-estimates of the `N₄^{gs}` and `N₅^{gs}` rows

The two degrees of freedom of `gRHS` that are `g`-linear and carry the *stationary* profile
`F_*` are

  `N₄^{gs}(z,θ) = -(1/2) sin(2θ) FK(g)(z) ∂_θF_*(z,θ)`,
  `N₅^{gs}(z,θ) = -sin²θ FK(g)(z) F_*(z,θ)`

(`Work.FTS.Nonlin.N4gs`, `Work.FTS.Nonlin.N5gs`), and the `rl¹`-norm of the row is

  `‖N‖_{rl¹} = ∫⁻_{r>0} r⁻¹ (∫⁻_{θ∈Iθ} |K θ · N(r,θ)|)`.

Both pieces are *radially factorised*: `F_*(z,θ) = α(Γ(θ)/c) F_*(z)` with `F_*(z) = 2z/(1+z)²`
and `∂_θF_* = α(Γ'(θ)/c) F_*(z)`, so every `θ`-integral is a numerical multiple of
`|FK(g)(r)| r/(1+r)²`, with the numerical factor bounded uniformly in `α ≤ 1` by
`Work.Spaces.Gam_bounds` (`Γ ≤ 1`), `Work.FTS.LocData.c_ge_three_fifths` (`c ≥ 3/5`) and
`abs_K_mul_deriv_Gam_le` (`|K·Γ'| ≤ 2α`).

The two measure-theoretic engines of `LintEngine` then finish: `inner_le_const` turns the
pointwise angular bound into the `θ`-lintegral, and `outer_le_radial` — with the row
hypothesis `∫ |FK(g)|/(1+z)² ≤ 2B` as its `L¹`-input — turns the radial profile
`C|FK(g)(r)|r/(1+r)²` against the weight `r⁻¹` into `ofReal (4CX)`.

The overall constant `K = 100` is generous: the sharp constants produced here are `80/3`
(for `N₄^{gs}`) and `80` (for `N₅^{gs}`), and the passage from `α` (resp. `α²`) to `α^{1/2}`
uses `α ≤ 1`.
-/

/-- **Pointwise angular bound for `N₅^{gs}`.**  For `θ ∈ Iθ`,
`|K θ · N₅^{gs}(α,g)(r,θ)| ≤ 10 α |FK(g)(r)| r/(1+r)²`, uniformly in `θ`:
`|K θ| sin²θ ≤ 3`, `Γ(θ)/c ≤ 5/3` and `F_*(r) = 2r/(1+r)²`. -/
lemma N5gs_ptwise_le {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|
      ≤ 10 * α * |Work.Construction.FK g r| * r / (1 + r) ^ 2 := by
  have hc : (0:ℝ) < Work.Spaces.c α := by
    have := Work.FTS.LocData.c_ge_three_fifths α hα hα1
    linarith
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  have hGc : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 5/3 := by
    rw [div_le_iff₀ hc]
    have := Work.FTS.LocData.c_ge_three_fifths α hα hα1
    linarith
  have hGcnn : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hG0 hc.le
  have hR : (0:ℝ) ≤ 2 * r / (1 + r) ^ 2 := by positivity
  have hK3 := abs_K_le_three θ
  have hsin : (Real.sin θ)^2 ≤ 1 := by
    nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ]
  have hsin0 : (0:ℝ) ≤ (Real.sin θ)^2 := sq_nonneg _
  have hKsin : |Work.Spaces.K θ| * (Real.sin θ)^2 ≤ 3 := by
    nlinarith [abs_nonneg (Work.Spaces.K θ)]
  have hkey : |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|
      = |Work.Spaces.K θ| * (Real.sin θ)^2 * |Work.Construction.FK g r|
          * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * (2 * r / (1 + r)^2) := by
    rw [Work.FTS.Nonlin.N5gs, Work.Construction.Fstar, Work.FM.Fstar]
    rw [show Work.Spaces.K θ * (-(Real.sin θ)^2 * Work.Construction.FK g r
          * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * r / (1 + r)^2)))
        = -(Work.Spaces.K θ * (Real.sin θ)^2 * Work.Construction.FK g r
            * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * (2 * r / (1 + r)^2)) from by ring]
    rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hsin0, abs_of_nonneg (mul_nonneg hα.le hGcnn), abs_of_nonneg hR]
  rw [hkey]
  have h1 : |Work.Spaces.K θ| * (Real.sin θ)^2 * |Work.Construction.FK g r|
      * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α)) * (2 * r / (1 + r)^2)
      ≤ 3 * |Work.Construction.FK g r| * (α * (5/3)) * (2 * r / (1 + r)^2) := by
    have hV : (0:ℝ) ≤ |Work.Construction.FK g r| := abs_nonneg _
    have h2 : |Work.Spaces.K θ| * (Real.sin θ)^2 * |Work.Construction.FK g r|
        ≤ 3 * |Work.Construction.FK g r| := by
      have := mul_le_mul_of_nonneg_right hKsin hV
      linarith [this]
    have h3 : α * (Work.Spaces.Gam α θ / Work.Spaces.c α) ≤ α * (5/3) :=
      mul_le_mul_of_nonneg_left hGc hα.le
    have h4 : 0 ≤ α * (Work.Spaces.Gam α θ / Work.Spaces.c α) := mul_nonneg hα.le hGcnn
    have h5 : 0 ≤ 3 * |Work.Construction.FK g r| := by positivity
    have h6 : |Work.Spaces.K θ| * (Real.sin θ)^2 * |Work.Construction.FK g r|
          * (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
        ≤ 3 * |Work.Construction.FK g r| * (α * (5/3)) :=
      mul_le_mul h2 h3 h4 h5
    exact mul_le_mul_of_nonneg_right h6 hR
  have h7 : 3 * |Work.Construction.FK g r| * (α * (5/3)) * (2 * r / (1 + r)^2)
      = 10 * α * |Work.Construction.FK g r| * r / (1 + r)^2 := by ring
  linarith [h7]

/-- **The `θ`-lintegral of `N₅^{gs}`**: the pointwise bound of `N5gs_ptwise_le` integrated
over `Iθ` (of measure `π/2 ≤ 2`) gives `ofReal (2·10 α |FK(g)(r)| r/(1+r)²)`. -/
lemma N5gs_angInt_le {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|)
      ≤ ENNReal.ofReal (20 * α * |Work.Construction.FK g r| * r / (1 + r) ^ 2) := by
  have hD : (0:ℝ) ≤ 10 * α * |Work.Construction.FK g r| * r / (1 + r) ^ 2 := by positivity
  have h := inner_le_const hD (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
    (fun θ hθ => N5gs_ptwise_le hα hα1 hr hθ))
  rwa [show 2 * (10 * α * |Work.Construction.FK g r| * r / (1 + r) ^ 2)
      = 20 * α * |Work.Construction.FK g r| * r / (1 + r) ^ 2 from by ring] at h

/-- **Pointwise angular bound for `N₄^{gs}`**, a.e. on `Iθ`.  On the open interval
`∂_θF_* = α(Γ'/c)F_*` (`FzShape`), and `|K θ Γ'(θ)| sin(2θ) ≤ 2α` by
`abs_K_mul_deriv_Gam_le`; the endpoints are null. -/
lemma N4gs_ptwise_le {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|
        ≤ (10 / 3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2 := by
  have hc : (0:ℝ) < Work.Spaces.c α := by
    have := Work.FTS.LocData.c_ge_three_fifths α hα hα1
    linarith
  have hR : (0:ℝ) ≤ Work.FM.Fstar r := by rw [Work.FM.Fstar]; positivity
  have hc5 : 1 / Work.Spaces.c α ≤ 5/3 := by
    rw [div_le_iff₀ hc]
    have := Work.FTS.LocData.c_ge_three_fifths α hα hα1
    linarith
  have hct0 : (0:ℝ) ≤ 1 / Work.Spaces.c α := by positivity
  rw [show MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)) from by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc.symm]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hshape := (FzShape α hα).1 r θ hθ.1 hθ.2
  have hKG : |Work.Spaces.K θ| * |Real.sin (2 * θ)|
      * |deriv (fun t => Work.Spaces.Gam α t) θ| ≤ 2 * α := by
    have h := abs_K_mul_deriv_Gam_le hα hθI
    rw [abs_mul] at h
    have hsin : |Real.sin (2 * θ)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    calc |Work.Spaces.K θ| * |Real.sin (2 * θ)| * |deriv (fun t => Work.Spaces.Gam α t) θ|
        = |Work.Spaces.K θ| * |deriv (fun t => Work.Spaces.Gam α t) θ|
            * |Real.sin (2 * θ)| := by ring
      _ ≤ (2 * α) * 1 := mul_le_mul h hsin (abs_nonneg _) (by positivity)
      _ = 2 * α := by ring
  have hkey : |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|
      = (1/2) * (|Work.Spaces.K θ| * |Real.sin (2 * θ)|
            * |deriv (fun t => Work.Spaces.Gam α t) θ|)
          * |Work.Construction.FK g r| * (α * (1 / Work.Spaces.c α)) * Work.FM.Fstar r := by
    rw [Work.FTS.Nonlin.N4gs, Work.Construction.s2, hshape]
    rw [show Work.Spaces.K θ * (-(1/2) * Real.sin (2 * θ) * Work.Construction.FK g r
          * (α * (deriv (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α)
              * Work.FM.Fstar r))
        = -((1/2) * Work.Spaces.K θ * Real.sin (2 * θ)
            * deriv (fun t => Work.Spaces.Gam α t) θ * Work.Construction.FK g r
            * α * (1 / Work.Spaces.c α) * Work.FM.Fstar r) from by
      rw [div_eq_mul_inv]; ring]
    rw [abs_neg]
    simp only [abs_mul]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/2), abs_of_pos hα,
      abs_of_pos (one_div_pos.mpr hc), abs_of_nonneg hR]
    ring
  rw [hkey]
  have hstep : (1/2) * (|Work.Spaces.K θ| * |Real.sin (2 * θ)|
        * |deriv (fun t => Work.Spaces.Gam α t) θ|)
      * |Work.Construction.FK g r| * (α * (1 / Work.Spaces.c α)) * Work.FM.Fstar r
      ≤ (1/2) * (2 * α) * |Work.Construction.FK g r|
          * (α * (1 / Work.Spaces.c α)) * Work.FM.Fstar r := by
    have h0 : (0:ℝ) ≤ |Work.Construction.FK g r| * (α * (1 / Work.Spaces.c α))
        * Work.FM.Fstar r := by
      have h1 : (0:ℝ) ≤ 1 / Work.Spaces.c α := hct0
      positivity
    have h2 := mul_le_mul_of_nonneg_right hKG h0
    have h3 : (0:ℝ) ≤ (1/2 : ℝ) := by norm_num
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    linarith [h4]
  have h5 : (1/2) * (2 * α) * |Work.Construction.FK g r|
      * (α * (1 / Work.Spaces.c α)) * Work.FM.Fstar r
      = α ^ 2 * |Work.Construction.FK g r| * (1 / Work.Spaces.c α) * Work.FM.Fstar r := by ring
  have hXR : (0:ℝ) ≤ α ^ 2 * |Work.Construction.FK g r| * Work.FM.Fstar r := by positivity
  have h6 : α ^ 2 * |Work.Construction.FK g r| * (1 / Work.Spaces.c α) * Work.FM.Fstar r
      ≤ α ^ 2 * |Work.Construction.FK g r| * (5/3) * Work.FM.Fstar r := by
    have := mul_nonpos_of_nonneg_of_nonpos hXR (by linarith : 1 / Work.Spaces.c α - 5/3 ≤ 0)
    linarith [this]
  have h7 : α ^ 2 * |Work.Construction.FK g r| * (5/3) * Work.FM.Fstar r
      = (10 / 3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2 := by
    rw [Work.FM.Fstar]; ring
  linarith [hstep, h5, h6, h7]

/-- **The `θ`-lintegral of `N₄^{gs}`**, from the a.e. pointwise bound of `N4gs_ptwise_le`. -/
lemma N4gs_angInt_le {α : ℝ} {g : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|)
      ≤ ENNReal.ofReal ((20 / 3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2) := by
  have hD : (0:ℝ) ≤ (10/3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2 := by positivity
  have h := inner_le_const hD (N4gs_ptwise_le hα hα1 hr)
  rwa [show 2 * ((10/3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2)
      = (20/3) * α ^ 2 * |Work.Construction.FK g r| * r / (1 + r) ^ 2 from by ring] at h

theorem Row45gs :
    ∃ K : ℝ, 0 < K ∧ ∀ {α B : ℝ} {g : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → 0 ≤ B → Work.FTS.Nonlin.GalClass α g →
      MeasureTheory.IntegrableOn (fun z => |Work.Construction.FK g z| / (1 + z) ^ 2)
        (Set.Ioi (0 : ℝ)) →
      (∫ z in Set.Ioi (0 : ℝ), |Work.Construction.FK g z| / (1 + z) ^ 2) ≤ 2 * B →
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|))
        ≤ ENNReal.ofReal (K * B * α ^ (1 / 2 : ℝ)) ∧
      (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|))
        ≤ ENNReal.ofReal (K * B * α ^ (1 / 2 : ℝ)) := by
  refine ⟨100, by norm_num, ?_⟩
  intro α B g hα hα1 hB hgal hint hle
  have hsnn : (0:ℝ) ≤ α ^ (1/2:ℝ) := Real.rpow_nonneg hα.le _
  have hα_le_sqrt : α ≤ α ^ (1/2:ℝ) := by
    have h1 : α ^ ((1:ℝ)/2 + 1/2) = α ^ (1/2:ℝ) * α ^ (1/2:ℝ) := Real.rpow_add hα _ _
    rw [show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one] at h1
    have h2 : α ^ (1/2:ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
    nlinarith [h1, h2, hsnn]
  have hα2_le_sqrt : α ^ 2 ≤ α ^ (1/2:ℝ) := by
    have h1 : α ^ ((3:ℝ)/2 + 1/2) = α ^ ((3:ℝ)/2) * α ^ (1/2:ℝ) := Real.rpow_add hα _ _
    rw [show (3:ℝ)/2 + 1/2 = 2 by norm_num, Real.rpow_two] at h1
    have h2 : α ^ ((3:ℝ)/2) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
    nlinarith [h1, h2, hsnn]
  have hsB : (0:ℝ) ≤ α ^ (1/2:ℝ) * B := mul_nonneg hsnn hB
  constructor
  · have hmono : (∫⁻ r in Set.Ioi (0:ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|))
        ≤ (∫⁻ r in Set.Ioi (0:ℝ), ENNReal.ofReal r⁻¹ *
            ENNReal.ofReal ((20/3) * α^2 * |Work.Construction.FK g r| * r/(1+r)^2)) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      exact mul_le_mul' le_rfl (N4gs_angInt_le hα hα1 hr)
    have hout := outer_le_radial (ρ := Work.Construction.FK g) (X := B) (C := (20/3)*α^2)
      (by positivity) hB hint hle
    have hfin : ENNReal.ofReal (4 * ((20/3) * α^2) * B)
        ≤ ENNReal.ofReal (100 * B * α ^ (1/2:ℝ)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hα2B : α^2 * B ≤ α ^ (1/2:ℝ) * B := mul_le_mul_of_nonneg_right hα2_le_sqrt hB
      nlinarith [hα2B, hsB]
    exact le_trans (le_trans hmono hout) hfin
  · have hmono : (∫⁻ r in Set.Ioi (0:ℝ), ENNReal.ofReal r⁻¹ *
        (∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|))
        ≤ (∫⁻ r in Set.Ioi (0:ℝ), ENNReal.ofReal r⁻¹ *
            ENNReal.ofReal (20 * α * |Work.Construction.FK g r| * r/(1+r)^2)) := by
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      exact mul_le_mul' le_rfl (N5gs_angInt_le hα hα1 hr)
    have hout := outer_le_radial (ρ := Work.Construction.FK g) (X := B) (C := 20*α)
      (by positivity) hB hint hle
    have hfin : ENNReal.ofReal (4 * (20 * α) * B)
        ≤ ENNReal.ofReal (100 * B * α ^ (1/2:ℝ)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have hαB : α * B ≤ α ^ (1/2:ℝ) * B := mul_le_mul_of_nonneg_right hα_le_sqrt hB
      nlinarith [hαB, hsB]
    exact le_trans (le_trans hmono hout) hfin

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option autoImplicit false

/-- The zeroth (radial) summand of `𝒲^{l,∞}` is the honest sup of `f` over the domain, so a
`WlInfMem`-bound bounds `f` pointwise.  This is the `k = 0`, `pzIter 0` instance of
`Work.Spaces.WlInf_z_bound`. -/
theorem abs_le_WlInf_of_mem {α B : ℝ} {l : ℕ} {f : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.WlInfMem α l f) (h : Work.Spaces.WlInf α l f ≤ B)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |f z θ| ≤ B := by
  have hb := Work.Spaces.WlInf_z_bound α l f hmem 0 (Nat.zero_le l) z θ hz hθ
  simpa using le_trans hb h

/-- `starPt`: the `Φ̃_*`-coefficients `ℛ(Φ̃_*), 𝒱(Φ̃_*)` and `∂_θ 𝒰(Φ̃_*)` of the nonlinear
terms are bounded by `max Cs 0 · α`.

This is an immediate consequence of the `𝒲^{l,∞}`-bounds recorded in `StarPkg`: each of the
three quantities is kept in `WlInf`, the `(z+1)/z`-weight between the two is `≥ 1` on `z > 0`,
and `Cs ≤ max Cs 0` with `α > 0`. -/
theorem starPt {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    (∀ z, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α) ∧
    (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α) ∧
    (∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.pth (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs)) z θ|
        ≤ max Cs 0 * α) := by
  have hle : Cs * α ≤ max Cs 0 * α :=
    mul_le_mul_of_nonneg_right (le_max_left Cs 0) hα.le
  have hRmem : Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        z θ) := hs.R.1
  have hRbnd : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
        z θ) ≤ max Cs 0 * α := le_trans hs.R.2 hle
  refine ⟨?_, ?_, ?_⟩
  · intro z hz θ hθ
    have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
    have hb : |(z + 1) / z * Work.Construction.Rop α
        (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ max Cs 0 * α := abs_le_WlInf_of_mem hRmem hRbnd hzI hθ
    have hge1 : (1 : ℝ) ≤ (z + 1) / z := by
      rw [le_div_iff₀ hz]; linarith
    have hpos : 0 < (z + 1) / z := lt_of_lt_of_le zero_lt_one hge1
    have h1 : |Work.Construction.Rop α (Work.Construction.PhiTil α
        (Work.Construction.Fstar α) Φs) z θ|
        ≤ |(z + 1) / z * Work.Construction.Rop α
          (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ| := by
      rw [abs_mul, abs_of_pos hpos]
      calc |Work.Construction.Rop α (Work.Construction.PhiTil α
              (Work.Construction.Fstar α) Φs) z θ|
          = 1 * |Work.Construction.Rop α (Work.Construction.PhiTil α
              (Work.Construction.Fstar α) Φs) z θ| := (one_mul _).symm
        _ ≤ (z + 1) / z * |Work.Construction.Rop α (Work.Construction.PhiTil α
              (Work.Construction.Fstar α) Φs) z θ| :=
            mul_le_mul_of_nonneg_right hge1 (abs_nonneg _)
    exact le_trans h1 hb
  · intro z hz θ hθ
    exact abs_le_WlInf_of_mem hs.V.1 (le_trans hs.V.2 hle) hz hθ
  · intro z hz θ hθ
    exact abs_le_WlInf_of_mem hs.dU.1 (le_trans hs.dU.2 hle) hz hθ

end Work.FTS.Nonlinear.Pieces.rl1Tools
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.splits_of_ctx =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces

set_option autoImplicit false

/-! ## Pointwise congruence of the operators `ℛ`, `U`, `V`

These are the elementary fact that the three operators depend on their argument only through the
value and the two first partials at the point.  They let one replace the argument by an
expression that agrees with it *at the point in question* for `ℛ, U, V` (the derivative
congruences are supplied by the caller). -/




/-! ## The straightened stream function of `F = F_* + g` splits, on `z ≥ 0` -/


/-! ## The three splits -/


end Work.FTS.Nonlinear.Pieces
end
end
-- ===== merged: Submission.Work.FTS.OpenPkg.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField coeffOf IsSolOn IsGalFam
  ConvLocUnif muDyn lamDyn dynLin dynRHS DenseSpan WeakDetermines IsDynWeakOn ProfileBdd
  EquicontSpace EquicontTau profileFam RegPkg prof Slab)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The norm-level interface in the open-quadrant class -/

/-- **The primed norm interface** (`FTS/ELL_H2_LEAD.md` §B1 "Downstream edits").

The fields are those of `Work.FTS.Nonlin.N4Norm`, with

* `RegQ` replaced by `VocabO.HQo` (interior `C^∞` + honesty; **no** `BdryTraces`);
* `Work.FTS.LocData.SmoothQuad` / `Work.Spaces.SmoothInt` replaced by
  `Work.FTS.EllipticEst.SmoothOpen`;
* `Work.Spaces.WlInf`/`WlInfMem` replaced by `VocabO.WDp`/`WDMem` (`WlInf` demands true
  `(z+1)^k ∂_z^k` suprema up to `z = 0`, which the remainder of the `Φ_*` decomposition does not
  have; `WDp ≤ C_l · WlInf` on the smooth class, so nothing is lost).

Every field is a true statement about the paper's function spaces; the inhabitation lemmas are in
`Submission/Work/FTS/OpenPkg/NormFields/`. -/
structure N4Norm' (Ci α₂ : ℝ) : Prop where
  pos : 0 < Ci ∧ 0 < α₂
  /-- `ℋ⁴` is closed under products, with the loss `√10 α^{-1/2}` (`HProdQ`, tex 1086). -/
  prod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Xn α (fun z θ => f z θ * g z θ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g
  /-- Multiplication by a `𝒲^{4,∞}`-function (`WProdQ`, tex 1096).

  **This clause must be priced by the `𝒲`-norm, not by `WDp`.**  Independent refutations
  (`Work.FTS.OpenPkg.wprod_field`, declared false by its prover, and the review of
  `Work.FTS.OpenPkg.wtoh_field`) show that a `D`-sup bound on the coefficient is *not* enough: a
  coefficient which is `C^∞` on the open quadrant, has bounded `D`-derivatives, but whose angular
  derivatives do not decay at `θ = 0, π/2` (`f z θ = sin (log (1/θ))`, or the spike family
  `f_s = (z²/(1+z)³)·sin(2θ)^s` with `s ↓ (γ-1)/2`) violates the conclusion: the mixed slots of
  the product are weighted by `sin(2θ)^{-γ}` with `γ = 1 + α/10 > 1`, so the `ℋ⁴`-integral sees
  the angular decay while the plain `D`-sup does not.  The `𝒲^{4,∞}`-norm of the coefficient is
  exactly the missing information (its weight `sin(2θ)^{-α/5}/(α+sin 2θ)` is comparable to
  `sin(2θ)^{-γ}` in the slots with `j ≥ 1`).

  For the rows this is also the only usable form for coefficients which are not in `ℋ⁴`
  (`F_*`, `D_θF_*`, `D_zF_*`: the `i = 4` angular slot of `F_*` is not integrable). -/
  wprod : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.WlInfMem α 4 f → HQo α 4 g →
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
    Xn α (fun z θ => f z θ * g z θ)
      ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Xn α g
  /-- `𝒲^{4,∞}` controls `ℋ⁴` through the weight `(z+1)³/z²` (`WtoHQ`, tex 1160).

  As for `wprod`, the hypothesis must be the `𝒲`-membership of the *weighted* function: the
  `D`-sup form is refuted (review of `Work.FTS.OpenPkg.wtoh_field`; spike family
  `f_s = (z²/(1+z)³)ψ(z)·sin(2θ)^s` has `WDp 4 ((z+1)³/z²·f_s) = O(1)` while `Xn α f_s → ∞`). -/
  wtoh : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, Work.FTS.EllipticEst.SmoothOpen f →
    Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) →
    Xn α f ≤ Ci * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)
  /-- `L₁₂` maps the `ℋ⁴`-class into itself, losslessly (`L12HQ`, tex 1119). -/
  l12H : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → Work.Construction.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
    Xn α (fun z θ => Work.Construction.L12 g z) ≤ Ci * Xn α g
  /-- The zero mode of `L₁₂` is controlled by the `ℋ⁴`-norm (`L12ZeroQ`, tex 1519). -/
  l12zero : ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn, HQo α 4 f →
    |Work.Construction.L12 f 0| ≤ Ci * Xn α f
  /-- The angular moment `FK g = ∫_θ K(θ) g(z,θ) dθ` is an `ℋ⁴`-function controlled by `Xn α g`. -/
  fkH : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → Work.Construction.L12 g 0 = 0 →
    Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
    Xn α (fun z _ => Work.Construction.FK g z) ≤ Ci * Xn α g
  /-- `z ↦ L₁₂(g)(z)` is differentiable on `(0,∞)` in the interior class. -/
  l12diff : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → ∀ z ∈ Set.Ioi (0 : ℝ),
    DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z
  /-- Multiplication by a function of `z` alone is lossless in `α` (`radial_prod`). -/
  radialMul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (r : ℝ → ℝ) (g : Fn),
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) → Work.FTS.EllipticEst.SmoothOpen g →
    Work.Spaces.HkMem α 4 (fun z _ => r z) → Work.Spaces.HkMem α 4 g →
    (∀ b : ℕ, b ≤ 4 → Filter.Tendsto
      (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => r z) z 0) Filter.atTop (nhds 0)) →
    (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
    Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
    Xn α (fun z θ => r z * g z θ) ≤ Ci * Xn α (fun z _ => r z) * Xn α g
  /-- Multiplication by an angular profile is lossless in `α`
  (`HkIntegrand_mul_angular_le`).  `a` must be bounded and its `D_θ`-iterates must vanish at
  least like `sin(2θ)`. -/
  angmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (f : Fn),
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
    (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 4 (fun z θ => a θ * f z θ) ∧
    Xn α (fun z θ => a θ * f z θ) ≤ Ci * Ci * Xn α f
  /-- Multiplication by an angular profile in the `D`-sup norm. -/
  wang : ∀ α ∈ Set.Ioc 0 α₂, ∀ (a : ℝ → ℝ) (h : Fn),
    Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => a θ) →
    Work.FTS.EllipticEst.SmoothOpen h →
    (∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ Ci) →
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ Ci * Real.sin (2 * θ)) →
    WDMem 4 h →
    WDMem 4 (fun z θ => a θ * h z θ) ∧
    WDp 4 (fun z θ => a θ * h z θ) ≤ Ci * Ci * WDp 4 h
  /-- Multiplication by a `z`-profile in the `D`-sup norm. -/
  wrad : ∀ α ∈ Set.Ioc 0 α₂, ∀ (φ : ℝ → ℝ) (h : Fn),
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => φ z) →
    Work.FTS.EllipticEst.SmoothOpen h →
    WDMem 4 (fun z _ => φ z) → WDMem 4 h →
    WDMem 4 (fun z θ => φ z * h z θ) ∧
    WDp 4 (fun z θ => φ z * h z θ) ≤ Ci * WDp 4 (fun z _ => φ z) * WDp 4 h
  /-- **The `D`-sup product rule**, with the flat vanishing of one factor on the two angular
  boundary lines which makes the boundary values of `pzIter k` harmless. -/
  wmul : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.EllipticEst.SmoothOpen g →
    WDMem 4 f → WDMem 4 g →
    (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ,
      Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) →
    WDMem 4 (fun z θ => f z θ * g z θ) ∧
    WDp 4 (fun z θ => f z θ * g z θ) ≤ Ci * WDp 4 f * WDp 4 g

/-! ## The `IP`-level contract in the open-quadrant class -/

/-- **The primed `IP`-level facts consumed by N4.**

`IP` is the paper's concrete `ℋ⁴` inner product (`IP₄`).  Compared with
`Work.FTS.Nonlin.N4Extra`:

* **every clause carries the honesty hypothesis `HkMem α 4 f` on the first argument(s) it
  quantifies over** (and `SmoothOpen f` where the proof needs differentiability of `f`).  This is
  what makes the structure *jointly satisfiable with `UnifIP`*: for `f ∉ ℋ⁴` the norm `Xn α f` is
  the junk value `0` while `IP α f g` can be an honest non-zero number, so the un-primed clauses
  `cs`, `add`, `smul`, `neg`, `congr`, `t1`, `t4`, `st` are false for the concrete `IP₄`
  (`FTS/ELL_H2_LEAD.md` §B3, "faithfulness defect of the current `N4Extra`");
* the transport clauses `t2`/`t3` are *replaced* by `VocabO.T2Clause`/`VocabO.T3Clause`: the
  angular liveness of the coefficient is measured by the flat norm `CoefTh` (so that a spike
  family is excluded by hypothesis rather than by a false bound) and the `g`-side carries order-5
  honesty, which removes the `z`-outer junk-integral obstruction;
* the `𝒲^{4,∞}`-clauses `t3`/`t4`/`st` are stated in `WDp`/`WDMem`.

`satisfiable` is *not* asserted here: the inhabitation for the concrete `IP₄` is the row side's
obligation (`FTS/NonlinRows`); this structure is the contract. -/
structure N4Extra' (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct : ℝ) : Prop where
  pos : 0 < Ct ∧ 0 < α₂
  /-- Cauchy–Schwarz against the `ℋ⁴`-norm, on honest first arguments. -/
  cs : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.HkMem α 4 f → RegQ α 4 g →
    |IP α f g| ≤ Ct * Xn α f * Xn α g
  /-- Additivity in the first argument. -/
  add : ∀ α ∈ Set.Ioc 0 α₂, ∀ f₁ f₂ g : Fn, Work.Spaces.HkMem α 4 f₁ →
    Work.Spaces.HkMem α 4 f₂ → RegQ α 4 g →
    IP α (f₁ + f₂) g = IP α f₁ g + IP α f₂ g
  /-- Homogeneity in the first argument. -/
  smul : ∀ α ∈ Set.Ioc 0 α₂, ∀ (c : ℝ) (f g : Fn), Work.Spaces.HkMem α 4 f → RegQ α 4 g →
    IP α (fun z θ => c * f z θ) g = c * IP α f g
  /-- Negation in the first argument. -/
  neg : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.HkMem α 4 f → RegQ α 4 g →
    IP α (fun z θ => -f z θ) g = -IP α f g
  /-- `IP` only depends on the first argument through its values on the open quadrant `Qd`. -/
  congr : ∀ α ∈ Set.Ioc 0 α₂, ∀ f f' g : Fn, Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkMem α 4 f' → RegQ α 4 g →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) → IP α f g = IP α f' g
  /-- The `D_z`-self-pairing, lossless (design §5 T5). -/
  dz : ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, HQo α 4 g → |IP α (Work.Spaces.Dz g) g| ≤ Ct * Xn α g ^ 2
  /-- `T1Q`: transport with `D_θ` and an `ℋ⁴`-coefficient (tex 1119). -/
  t1 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, HQo α 4 f → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Xn α f * Xn α g ^ 2
  /-- `T2S`: transport with `D_z` and a flat angular coefficient (`VocabO.T2Clause`). -/
  t2 : T2Clause IP α₂ Ct
  /-- `T3S`: transport with `D_z` and a `𝒲^{4,∞}`-coefficient (`VocabO.T3Clause`). -/
  t3 : T3Clause IP α₂ Ct
  /-- `T3Q` with `D_θ` and a `𝒲^{4,∞}`-coefficient, in the `D`-sup norm. -/
  t4 : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, WDMem 4 f → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * WDp 4 f * Xn α g ^ 2
  /-- `STQ`: `SpecialTransport` (tex 1258), the derivative falling on a coefficient which
  vanishes at the angular ends. -/
  st : ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn, Work.Spaces.VanishTheta f →
    WDMem 4 (Work.Spaces.pth f) → RegQ α 4 g →
    |IP α (fun z θ => f z θ * Work.Spaces.pth g z θ) g|
      ≤ Ct * α ^ (-(1 / 2 : ℝ)) * WDp 4 (Work.Spaces.pth f) * Xn α g ^ 2

/-! ## The per-piece rows of the §8 estimate in the primed vocabulary -/

/-- **The context of the per-piece estimates** (the primed `Work.FTS.Nonlin.RowCtx`): the two
primed interfaces, the two open-quadrant elliptic packages, the Galerkin class of the
perturbation and the ranges of `α`. -/
structure RowCtx' (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs α : ℝ) (g Φs Φg : Fn) : Prop where
  hCi : 0 < Ci
  hN : N4Norm' Ci α₂
  hE : N4Extra' IP α₂ Ct
  hα : 0 < α
  hαα₂ : α ≤ α₂
  hα1 : α ≤ 1
  hg : GalClass α g
  hs : StarPkgo α Cs Φs
  hell : EllPkgGo α Ce g Φg

variable {IP : ℝ → Fn → Fn → ℝ} {α₂ Ci Ct Ce Cs α : ℝ} {g Φs Φg : Fn}

theorem RowCtx'.reg4 (h : RowCtx' IP α₂ Ci Ct Ce Cs α g Φs Φg) : RegQ α 4 g :=
  Work.FTS.Nonlin.galClass_regQ4 h.hg

theorem RowCtx'.hαIoc (h : RowCtx' IP α₂ Ci Ct Ce Cs α g Φs Φg) : α ∈ Set.Ioc 0 α₂ :=
  ⟨h.hα, h.hαα₂⟩


/-- **The per-piece table of §8 in the primed vocabulary.**

The fields are those of `Work.FTS.Nonlin.RowInputs` — the concrete inequalities of design §3.4 —
**with the `ℋ⁴`-honesty conjunct of the piece added to every norm bound**.  That conjunct is
exactly what `N4Extra'`'s clauses consume (they take `HkMem α 4 f` as a hypothesis), and it is
what the row proofs produce anyway (`HProdQ`, `L12HQ`, `WtoHQ`, … all conclude
`HkMem α 4 (piece) ∧ bound`).

The four fields `hkN0`, `hkN`, `hkAK`, `hkDz` are the honesty of the three blocks into which
`gRHS` is split, plus that of `D_z g`; they are the ones the *assembly* (`pairing_bound'`) needs in
addition to the per-piece rows. -/
structure RowInputs' (IP : ℝ → Fn → Fn → ℝ) (α C : ℝ) (g Φs Φg : Fn) : Prop where
  reg4 : RegQ α 4 g
  /-- row 1: `|N₀₁+N₀₂|_{ℋ⁴} ≤ Cα²` -/
  r1 : Work.Spaces.HkMem α 4 (N0fix α) ∧ Xn α (N0fix α) ≤ C * α ^ 2
  /-- row 2: `|N₀₃|_{ℋ⁴} ≤ Cα^{-1}X²` -/
  r2 : Work.Spaces.HkMem α 4 (N03g α g) ∧
    Xn α (N03g α g) ≤ C * (α ^ (-(1 : ℝ)) * Xn α g ^ 2)
  /-- row 3: `|N₀₄ᵃ|_{ℋ⁴} ≤ C√α X` -/
  r3 : Work.Spaces.HkMem α 4 (N04aF α g) ∧
    Xn α (N04aF α g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 4: `|(N₀₄ᵇ, g)| ≤ Cα^{-3/2}X³` -/
  r4 : Work.Spaces.HkMem α 4 (N04bF α g) ∧
    |IP α (N04bF α g) g| ≤ C * (α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 5: `|N₀₅ᵃ|_{ℋ⁴} ≤ C√α X` -/
  r5 : Work.Spaces.HkMem α 4 (N05aF α g) ∧
    Xn α (N05aF α g) ≤ C * (Real.sqrt α * Xn α g)
  /-- row 6: `|(N₀₅ᵇ, g)| ≤ Cα^{-1/2}X³` -/
  r6 : Work.Spaces.HkMem α 4 (N05bF α g) ∧
    |IP α (N05bF α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  /-- row 7: `|(N₀₆, g)| ≤ C√α X²` -/
  r7 : Work.Spaces.HkMem α 4 (N06F α g) ∧
    |IP α (N06F α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r8 : Work.Spaces.HkMem α 4 (N1gg α g Φg) ∧
    Xn α (N1gg α g Φg) ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 2)
  r9 : Work.Spaces.HkMem α 4 (N1gs α g Φg) ∧
    Xn α (N1gs α g Φg) ≤ C * (Real.sqrt α * Xn α g)
  r10 : Work.Spaces.HkMem α 4 (N1sg α Φs g) ∧
    Xn α (N1sg α Φs g) ≤ C * (Real.sqrt α * Xn α g)
  r11 : Work.Spaces.HkMem α 4 (N1ss α Φs) ∧ Xn α (N1ss α Φs) ≤ C * α ^ 2
  r12 : Work.Spaces.HkMem α 4 (N2gg α g Φg) ∧
    |IP α (N2gg α g Φg) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r13 : Work.Spaces.HkMem α 4 (N2gs α g Φg) ∧
    Xn α (N2gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r14 : Work.Spaces.HkMem α 4 (N2sg α Φs g) ∧
    |IP α (N2sg α Φs g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r15 : Work.Spaces.HkMem α 4 (N2ss α Φs) ∧ Xn α (N2ss α Φs) ≤ C * α ^ 2
  r16 : Work.Spaces.HkMem α 4 (N3gg α g Φg) ∧
    |IP α (N3gg α g Φg) g| ≤ C * (Real.sqrt α * Xn α g ^ 3)
  r17 : Work.Spaces.HkMem α 4 (N3gs α g Φg) ∧
    Xn α (N3gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r18 : Work.Spaces.HkMem α 4 (N3sg α Φs g) ∧
    |IP α (N3sg α Φs g) g| ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g ^ 2)
  r19 : Work.Spaces.HkMem α 4 (N3ss α Φs) ∧ Xn α (N3ss α Φs) ≤ C * α ^ 3
  r20 : Work.Spaces.HkMem α 4 (N4gg α g) ∧
    |IP α (N4gg α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r21 : Work.Spaces.HkMem α 4 (N4gs α g) ∧
    Xn α (N4gs α g) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r22 : Work.Spaces.HkMem α 4 (N4sg α g) ∧
    |IP α (N4sg α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r23 : Work.Spaces.HkMem α 4 (N4ss α) ∧ Xn α (N4ss α) ≤ C * α ^ 3
  r24 : Work.Spaces.HkMem α 4 (N5gg g) ∧ Xn α (N5gg g) ≤ C * Xn α g ^ 2
  r25 : Work.Spaces.HkMem α 4 (N5gs α g) ∧ Work.Spaces.HkMem α 4 (N5sg α g) ∧
    Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * Xn α g)
  r26 : Work.Spaces.HkMem α 4 (N5ss α) ∧ Xn α (N5ss α) ≤ C * α ^ 2
  /-- the `ℋ⁴`-bound of `AK` (design §3.2) -/
  rak : Work.Spaces.HkMem α 4 (Work.Construction.AK α) ∧ Xn α (Work.Construction.AK α) ≤ C
  rl0 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl1 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ C * Xn α g
  hN0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
      = N0fix α z θ + (N03g α g z θ + N04aF α g z θ + N04bF α g z θ
          + N05aF α g z θ + N05bF α g z θ + N06F α g z θ)
  hN : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      = (N1gg α g Φg z θ + N1gs α g Φg z θ + N1sg α Φs g z θ + N1ss α Φs z θ)
        + (N2gg α g Φg z θ + N2gs α g Φg z θ + N2sg α Φs g z θ + N2ss α Φs z θ)
        + (N3gg α g Φg z θ + N3gs α g Φg z θ + N3sg α Φs g z θ + N3ss α Φs z θ)
        + (N4gg α g z θ + N4gs α g z θ + N4sg α g z θ + N4ss α z θ)
        + (N5gg g z θ + N5gs α g z θ + N5sg α g z θ + N5ss α z θ)
  hNs : ∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = NstarLam μ g z θ
  /-- honesty of the `N₀`-block (`N0 α (F_*+g) g`) -/
  hkN0 : Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
  /-- honesty of the `N`-block (`N α (F_*+g) (Φ_*+Φ_g)`) -/
  hkN : Work.Spaces.HkMem α 4
    (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
  /-- honesty of `D_z g` -/
  hkDz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g)

/-! ## The row groups as an interface -/

/-- **The `ℋ⁴`-honesty of every piece entering the assembly of `pairing_bound'`.**  These are the
hypotheses that the primed clauses of `N4Extra'` consume; each is produced by the row proof of the
corresponding piece. -/
structure PiecesHk (α : ℝ) (g Φs Φg : Fn) : Prop where
  p1 : Work.Spaces.HkMem α 4 (N0fix α)
  p2 : Work.Spaces.HkMem α 4 (N03g α g)
  p3 : Work.Spaces.HkMem α 4 (N04aF α g)
  p4 : Work.Spaces.HkMem α 4 (N04bF α g)
  p5 : Work.Spaces.HkMem α 4 (N05aF α g)
  p6 : Work.Spaces.HkMem α 4 (N05bF α g)
  p7 : Work.Spaces.HkMem α 4 (N06F α g)
  p8 : Work.Spaces.HkMem α 4 (N1gg α g Φg)
  p9 : Work.Spaces.HkMem α 4 (N1gs α g Φg)
  p10 : Work.Spaces.HkMem α 4 (N1sg α Φs g)
  p11 : Work.Spaces.HkMem α 4 (N1ss α Φs)
  p12 : Work.Spaces.HkMem α 4 (N2gg α g Φg)
  p13 : Work.Spaces.HkMem α 4 (N2gs α g Φg)
  p14 : Work.Spaces.HkMem α 4 (N2sg α Φs g)
  p15 : Work.Spaces.HkMem α 4 (N2ss α Φs)
  p16 : Work.Spaces.HkMem α 4 (N3gg α g Φg)
  p17 : Work.Spaces.HkMem α 4 (N3gs α g Φg)
  p18 : Work.Spaces.HkMem α 4 (N3sg α Φs g)
  p19 : Work.Spaces.HkMem α 4 (N3ss α Φs)
  p20 : Work.Spaces.HkMem α 4 (N4gg α g)
  p21 : Work.Spaces.HkMem α 4 (N4gs α g)
  p22 : Work.Spaces.HkMem α 4 (N4sg α g)
  p23 : Work.Spaces.HkMem α 4 (N4ss α)
  p24 : Work.Spaces.HkMem α 4 (N5gg g)
  p25 : Work.Spaces.HkMem α 4 (N5gs α g)
  p26 : Work.Spaces.HkMem α 4 (N5sg α g)
  p27 : Work.Spaces.HkMem α 4 (N5ss α)
  pAK : Work.Spaces.HkMem α 4 (Work.Construction.AK α)
  pN0 : Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
  pN : Work.Spaces.HkMem α 4
    (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
  pDz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz g)

/-! ## The row groups as an interface -/

/-- **The three row groups of design §3.4, in the primed context**, bundled with the two exact
splits and the `N_*`-collapse of `RowInputs'`.

This is the *statement* that `FTS/NonlinRows` inhabits (rows 6, 7, 16, 18 consume
`VocabO.T2Clause`/`T3Clause`; rows 10, 11, 14, 15, 18, 19 consume `StarPkgo`); the assembly
`pairing_bound'` below is proved from it. -/
structure N4Rows' (IP : ℝ → Fn → Fn → ℝ) (α₂ Ci Ct Ce Cs : ℝ) where
  K₁ : ℝ
  K₂ : ℝ
  K₃ : ℝ
  hK₁ : 0 < K₁
  hK₂ : 0 < K₂
  hK₃ : 0 < K₃
  /-- rows 1--7 -/
  rowsN0 : ∀ {α : ℝ} {g Φs Φg : Fn}, 0 < α → α ≤ 1 → α ≤ α₂ → GalClass α g →
    StarPkgo α Cs Φs → EllPkgGo α Ce g Φg →
    Work.FTS.Nonlinear.Pieces.N0Rows IP α K₁ g Φs Φg
  /-- rows 8--26 -/
  rowsN : ∀ {α : ℝ} {g Φs Φg : Fn}, 0 < α → α ≤ 1 → α ≤ α₂ → GalClass α g →
    StarPkgo α Cs Φs → EllPkgGo α Ce g Φg →
    Work.FTS.Nonlinear.Pieces.NRows IP α K₂ g Φs Φg
  /-- the auxiliary rows (`AK` and the three zero modes) -/
  rowsAux : ∀ {α : ℝ} {g Φs Φg : Fn}, 0 < α → α ≤ 1 → α ≤ α₂ → GalClass α g →
    StarPkgo α Cs Φs → EllPkgGo α Ce g Φg →
    Work.FTS.Nonlinear.Pieces.AuxRows IP α K₃ g Φs Φg
  /-- the three exact splits of `N₀`, `N` and `N_*` -/
  splits : ∀ {α : ℝ} {g Φs Φg : Fn}, 0 < α → α ≤ 1 → α ≤ α₂ → GalClass α g →
    StarPkgo α Cs Φs → EllPkgGo α Ce g Φg →
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
        = N0fix α z θ + (N03g α g z θ + N04aF α g z θ + N04bF α g z θ
            + N05aF α g z θ + N05bF α g z θ + N06F α g z θ)) ∧
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
        = (N1gg α g Φg z θ + N1gs α g Φg z θ + N1sg α Φs g z θ + N1ss α Φs z θ)
          + (N2gg α g Φg z θ + N2gs α g Φg z θ + N2sg α Φs g z θ + N2ss α Φs z θ)
          + (N3gg α g Φg z θ + N3gs α g Φg z θ + N3sg α Φs g z θ + N3ss α Φs z θ)
          + (N4gg α g z θ + N4gs α g z θ + N4sg α g z θ + N4ss α z θ)
          + (N5gg g z θ + N5gs α g z θ + N5sg α g z θ + N5ss α z θ)) ∧
    (∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
      Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = NstarLam μ g z θ)
  /-- the honesty conjuncts of the pieces (`FTS/NonlinRows` produces them together with the rows) -/
  hkmem : ∀ {α : ℝ} {g Φs Φg : Fn}, 0 < α → α ≤ 1 → α ≤ α₂ → GalClass α g →
    StarPkgo α Cs Φs → EllPkgGo α Ce g Φg → PiecesHk α g Φs Φg

/-! ## The output of the primed pairing estimate -/

/-- **The output of `pairing_bound'`**, with `StarPkgo`/`EllPkgGo` (the primed analogue of
`Work.FTS.Apriori.PairData`). -/
structure PairData' (IP : ℝ → Fn → Fn → ℝ) (CcN Ce Cs α₄ : ℝ) : Prop where
  hCcN : 0 < CcN
  hα₄ : 0 < α₄
  bound : ∀ α : ℝ, 0 < α → α ≤ α₄ → ∀ g Φs Φg : Fn,
    GalClass α g → StarPkgo α Cs Φs → EllPkgGo α Ce g Φg → Xn α g ≤ α ^ (7 / 4 : ℝ) →
    |Work.FTS.Apriori.muOf α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * (α + α ^ (-(1 : ℝ)) * Xn α g + α ^ (-(5 / 2 : ℝ)) * Xn α g ^ 2)
      ∧ |Work.FTS.Apriori.muOf α g (fun z θ => Φs z θ + Φg z θ)| ≤ 1 / 2
      ∧ |Work.FTS.Apriori.rhsPair IP α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * Pbd α (Xn α g)

/-! ## The a-priori (N5) interface, open-quadrant form -/

/-- **The a-priori fields of N6, in the primed vocabulary.**  Field for field those of
`Work.FTS.Apriori.AprioriFields`, with the primed packages and the open-quadrant limit bound. -/
structure AprioriFields' (IP : ℝ → Fn → Fn → ℝ) (α C₀ clo cc CcN Ce Cs : ℝ) (φ : ℕ → Fn)
    (Φs : Fn) (EllSol : Fn → Fn) (g₀ : Fn) : Prop where
  /-- **`hInit`**: the projected datum lies in the a-priori ball. -/
  hInit : ∀ n : ℕ, ∑ k : Fin n,
    (coeffOf (IP α) g₀ φ n k) ^ 2 ≤ (Work.FTS.Apriori.Rstar clo C₀ α) ^ 2
  /-- **`hCoeffBound`**: every Galerkin solution stays in the a-priori ball. -/
  hCoeffBound : ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
    IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, ∑ k : Fin n, (c τ k) ^ 2 ≤ (Work.FTS.Apriori.Rstar clo C₀ α) ^ 2
  /-- **`hProfileBdd`**: uniform local bounds on the Galerkin profiles. -/
  hProfileBdd : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Work.FTS.Apriori.Rstar clo C₀ α) c →
    ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.Galerkin.Slab →
      ∃ Cb : ℝ, ∀ n : ℕ, ∀ p ∈ K, |Work.FTS.Galerkin.prof φ c n p| ≤ Cb
  /-- **`hLimBound`**: the limit of a convergent subsequence obeys the a-priori bound.  The
  slices of the limit are required to be `SmoothOpen` — which `RegPkg.smooth` supplies — not
  `SmoothQuad`. -/
  hLimBound : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) (Work.FTS.Apriori.Rstar clo C₀ α) c →
    ∀ (ψ : ℕ → ℕ) (g : Fam), StrictMono ψ →
    ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    (∀ τ : ℝ, 0 ≤ τ → Work.FTS.EllipticEst.SmoothOpen (slice g τ)) →
    ∀ τ : ℝ, 0 ≤ τ → Xn α (slice g τ) ≤ C₀ * α ^ 2

/-! ## The Galerkin (N6) bundle, open-quadrant form -/

/-- **The part of the Galerkin a-priori bundle that the ODE/existence layer uses.**

This is the projection of `Work.FTS.Galerkin.DynInputs` onto the fields that are actually consumed
by `galerkin_coeff_exists` and `exists_dynGSol_of_ode`: the inner product and its constants, the
basis and its density, the two stream functions (as *data* — their packages are **not** part of
this structure), the a-priori radius, the field constants, the compactness/limit inputs and the
limit bound.

Separating it is what allows the migration: the frozen packages `StarPkg`/`EllPkgG` occur only in
the three fields of `DynInputs` that this structure drops (`hΦs`, `hEllSol` and their constants). -/
structure DynCore (Law : Fn → Fn → Prop) (α : ℝ) (g₀ : Fn) (C₀ : ℝ) where
  IP : ℝ → Fn → Fn → ℝ
  α₂ : ℝ
  cc : ℝ
  clo : ℝ
  Cup : ℝ
  Ccs : ℝ
  hIP : UnifIP IP α₂ cc clo Cup Ccs
  φ : ℕ → Fn
  hφ : GalBasis α IP φ
  hφ_dense : DenseSpan α IP φ
  Φs : Fn
  EllSol : Fn → Fn
  hPsi : ∀ G : Fam, (∀ τ : ℝ, 0 ≤ τ → GalClass α (slice G τ)) → ∀ τ : ℝ, 0 ≤ τ →
    Law (Work.Construction.Ftau α G τ) (slice (PsiCan Φs EllSol G) τ)
  R : ℝ
  hR : 0 < R
  L : ℕ → ℝ
  hL : ∀ n : ℕ, 0 < L n
  K : ℕ → ℝ
  hK : ∀ n : ℕ, 0 ≤ K n
  hField_lip : ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
    LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ)
      (Metric.closedBall 0 (2 * R))
  hField_bound : ∀ (n : ℕ) (τ : ℝ) (c : Fin n → ℝ), 0 ≤ τ →
    c ∈ Metric.closedBall 0 (2 * R) → ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n
  hField_cont : ∀ (n : ℕ) (c : Fin n → ℝ), c ∈ Metric.closedBall 0 (2 * R) →
    ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0)
  hInit : ∀ n : ℕ, ∑ k : Fin n, (coeffOf (IP α) g₀ φ n k) ^ 2 ≤ R ^ 2
  hCoeffBound : ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
    IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, ∑ k : Fin n, (c τ k) ^ 2 ≤ R ^ 2
  hProfileBdd : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    ProfileBdd (profileFam φ c)
  hProfileSpace : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    EquicontSpace (profileFam φ c)
  hProfileTau : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    EquicontTau (profileFam φ c)
  hRegLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → RegPkg α g
  hDataLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → ∀ z θ, g z θ 0 = g₀ z θ
  hPsiLim : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ∃ Φ : Fam, ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ
  hGalWeak : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g Φ : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ →
    IsDynWeakOn α (IP α) φ g Φ ∧ (∀ τ : ℝ, 0 ≤ τ → Law (Work.Construction.Ftau α g τ) (slice Φ τ))
  hDetermines : WeakDetermines α (IP α) φ
  hLimBound : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    (∀ τ : ℝ, 0 ≤ τ → Work.FTS.EllipticEst.SmoothOpen (slice g τ)) →
    ∀ τ : ℝ, 0 ≤ τ → Work.Spaces.HkNorm α 4 (slice g τ) ≤ C₀ * α ^ 2

/-- The stream-function assignment of the core bundle. -/
def DynCore.Psi {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ : ℝ} (hin : DynCore Law α g₀ C₀) :
    Fam → Fam := PsiCan hin.Φs hin.EllSol

/-- **The Galerkin a-priori bundle in the primed vocabulary**: the open-quadrant packages
`StarPkgo`/`EllPkgGo` and the open-quadrant limit bound.  This is what replaces
`Work.FTS.Galerkin.DynInputs` on the migrated route. -/
structure DynInputsOpen (Law : Fn → Fn → Prop) (α : ℝ) (g₀ : Fn) (C₀ : ℝ) where
  /-- the fields shared with `DynCore` -/
  core : DynCore Law α g₀ C₀
  Cs : ℝ
  Ce : ℝ
  hΦs : StarPkgo α Cs (core.Φs)
  hEllSol : ∀ g : Fn, GalClass α g → EllPkgGo α Ce g (core.EllSol g)

end Work.FTS.OpenPkg
end
end
