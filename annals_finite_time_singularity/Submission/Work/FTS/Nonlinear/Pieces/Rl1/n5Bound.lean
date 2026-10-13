/-
# The `N₅`-row of `AuxRows.rl1`: `E₅ ≤ K(α² + √α·X + α^{-3/2}X²)`

`Work.FTS.Nonlinear.Pieces.Rl1.n5Bound` asks for the absolutely convergent density integral

`E₅ = ∫_{s>0} ‖L₁₂dens(N₅ α (F_* + g) (Φ_s + Φ_g)) s‖ ds ≤ K·(α² + √α·X + α^{-3/2}·X²)`

under the frozen context `N4Norm Ci α₂`, `GalClass α g`, `StarPkg α Cs Φ_s`, `EllPkgG α Ce g Φ_g`,
`0 < α ≤ 1`, `α ≤ α₂` (`Submission/Work/FTS/Vocab.lean`), with `X = Xn α g = |g|_{ℋ⁴}`.

`N₅ α F Φ = -sin²θ (F,K)_{L²_θ} F` does **not** depend on `Φ`, and
`F = F_* + g` with `F_*` explicit, so the whole estimate is a two-factor estimate:

* both `|(F,K)_{L²_θ}(s)|` and `∫_θ K(θ)|F(s,θ)|` are bounded by
  `Z(s) := ∫_θ K(θ)|F_*(s,θ)| + ∫_θ K(θ)|g(s,θ)|` (the first by `|∫| ≤ ∫|·|`, the second
  by `|F_*+g| ≤ |F_*|+|g|`), so

  `‖L₁₂dens(N₅)(s)‖ ≤ |(F,K)_{L²_θ}(s)|/s · ∫_θ K(θ)|F(s,θ)| ≤ Z(s)²/s`
  (`n5_dens_le`: `sin²θ ≤ 1`, the *transported* half only needs the cheap `n = 2` bound);

* the `F_*`-part is explicit: `|F_*(s,θ)| ≤ 20αs/(1+s)²` (`Γ ≤ 1`, `c(α) ≥ 1/10`,
  `F_{*,rad}(s) = 2s/(1+s)²`), hence `∫_θ K(θ)|F_*| ≤ 20αs/(1+s)²` since `∫_θ K = 1`;
* the `g`-part is `≤ 4√(Ph s)`, `Ph s := ∫_θ g(s,θ)²`, by Cauchy–Schwarz against `K ∈ L²(Iθ)`
  (`∫_θK(θ)² ≤ 3 ≤ 4²`), so `Z(s) ≤ c(s) + 4√(Ph s)` with `c(s) = 20αs/(1+s)²`.

For the radial integral (`n5_radial`) the cross term is *not* treated by Cauchy–Schwarz: the
crude `(u+v)² ≤ 2u²+2v²` already suffices, and the two pieces are controlled by
`2c²/s ≤ 800α²(1+s)^{-2}` (integrable, `∫ ≤ 2`, `InvOneAddSq`) and
`32·Ph(s)/s ≤ 32·Ph(s)w(s)` with `w(s) = (1+s)²/s²`, whose integral is `≤ X²`
(`Work.FTS.H2.L12Q.phiWeight_slice_le`).  Hence

`E₅ ≤ 1600α² + 32X² ≤ K(α² + √α·X + α^{-3/2}X²)` for `α ≤ 1` (`α^{-3/2} ≥ 1`), e.g. `K = 2000`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.H2.L12ZeroQ
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono
import Submission.Work.Coercivity.integral_Itheta_K
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.Nonlinear.FstarPkgAll

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

/-- `Γ_α(θ) = (sinθ cos²θ)^{α/3}` is continuous: the base is continuous and nonnegative
everywhere and `α/3 > 0`. -/
lemma n5_continuous_Gam {α : ℝ} (hα : 0 < α) :
    Continuous (fun θ : ℝ => Work.Spaces.Gam α θ) := by
  unfold Work.Spaces.Gam
  exact (Continuous.mul Real.continuous_sin (Real.continuous_cos.pow 2)).rpow_const
    (fun θ => Or.inr (le_of_lt (by positivity)))

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

/-- The `F_*`-part of the slice factor: `∫_θ K(θ)|F_*(s,θ)| ≤ 20αs/(1+s)²`. -/
lemma n5_FstarK_le {α s : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hs : 0 < s) :
    IntegrableOn (fun θ => Work.Spaces.K θ * |Work.Construction.Fstar α s θ|)
        Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |Work.Construction.Fstar α s θ|)
        ≤ 20 * α * s / (1 + s) ^ 2 := by
  have hmaj : IntegrableOn (fun θ => (20 * α * s / (1 + s) ^ 2) * Work.Spaces.K θ)
      Work.Spaces.Iθ :=
    n5_integrableOn_K.const_mul (20 * α * s / (1 + s) ^ 2)
  have haesm : AEStronglyMeasurable
      (fun θ => Work.Spaces.K θ * |Work.Construction.Fstar α s θ|)
      (volume.restrict Work.Spaces.Iθ) := by
    have hGam : Measurable (fun θ : ℝ => Work.Spaces.Gam α θ) :=
      (n5_continuous_Gam hα).measurable
    have hFs : Measurable (fun θ : ℝ => Work.Construction.Fstar α s θ) := by
      unfold Work.Construction.Fstar Work.FM.Fstar
      exact (measurable_const.mul (hGam.div measurable_const)).mul measurable_const
    exact (n5_measurable_K.mul hFs.abs).aestronglyMeasurable
  have hint : IntegrableOn (fun θ => Work.Spaces.K θ * |Work.Construction.Fstar α s θ|)
      Work.Spaces.Iθ := by
    refine hmaj.mono' haesm ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (n5_K_nonneg hθ) (abs_nonneg _))]
    rw [mul_comm (Work.Spaces.K θ)]
    exact mul_le_mul_of_nonneg_right (n5_Fstar_abs_le hα hα1 hs hθ) (n5_K_nonneg hθ)
  refine ⟨hint, ?_⟩
  refine le_trans (integral_mono_of_nonneg ?_ hmaj ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (n5_K_nonneg hθ) (abs_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [mul_comm (Work.Spaces.K θ)]
    exact mul_le_mul_of_nonneg_right (n5_Fstar_abs_le hα hα1 hs hθ) (n5_K_nonneg hθ)
  · rw [MeasureTheory.integral_const_mul, Work.Coercivity.integral_Itheta_K, mul_one]

/-- **The slice bound.**  For `0 < α ≤ 1`, `g` of class `SmoothQuad ∩ ℋ⁴` and every `s > 0`, the
`L₁₂`-density of `N₅` is bounded by `(20αs/(1+s)² + 4√(∫_θ g(s,θ)²))²/s`.

`N₅ α F Φ = -sin²θ (F,K)_{L²_θ} F` does not depend on `Φ`; both the angular moment
`(F,K)_{L²_θ}(s)` of `F = F_* + g` and the transported factor `F` are bounded by
`∫_θ K(θ)|F_*(s,θ)| + ∫_θ K(θ)|g(s,θ)| ≤ 20αs/(1+s)² + 4√(∫_θ g(s,θ)²)`. -/
lemma n5_dens_le {α : ℝ} {g Φ : Work.FTS.Galerkin.Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ s : ℝ, 0 < s →
      ‖Work.Construction.L12dens (Work.Construction.N5 α (Work.Construction.Ftot α g) Φ) s‖
        ≤ (20 * α * s / (1 + s) ^ 2
            + 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)) ^ 2 / s := by
  intro s hs
  set c : ℝ := 20 * α * s / (1 + s) ^ 2 with hc
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 with hP
  have hs0 : (0 : ℝ) ≤ s := hs.le
  have hden : 0 < (1 + s) ^ 2 := by positivity
  have hP0 : 0 ≤ P := by
    rw [hP]
    exact integral_nonneg_of_ae (Eventually.of_forall fun θ => sq_nonneg _)
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact div_nonneg (by positivity) hden.le
  -- the slice regularity
  have hsql : IntegrableOn (fun θ => (g s θ) ^ 2) Work.Spaces.Iθ :=
    Work.FTS.H2.l12q_slice_sq_integrableOn α g hsm hmem hs
  have haesmg : AEStronglyMeasurable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ) := by
    have hcont : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
      refine hsm.continuousOn.mono ?_
      intro p hp
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
      exact ⟨by linarith [hp.1], hp.2⟩
    simpa only [Function.uncurry] using
      Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry g) hcont hs
  -- the two slice factors
  obtain ⟨hKgi, hKg⟩ := n5_K_mul_abs_le (g := g) hs hsql haesmg
  obtain ⟨hKFi, hKF⟩ := n5_FstarK_le (α := α) hα hα1 hs
  -- the majorant `c·K θ + K θ·|g(s,θ)|`
  have hmajint : IntegrableOn (fun θ => c * Work.Spaces.K θ + Work.Spaces.K θ * |g s θ|)
      Work.Spaces.Iθ := (n5_integrableOn_K.const_mul c).add hKgi
  have hFpt : ∀ θ ∈ Work.Spaces.Iθ, Work.Spaces.K θ * |Work.Construction.Ftot α g s θ|
      ≤ c * Work.Spaces.K θ + Work.Spaces.K θ * |g s θ| := by
    intro θ hθ
    have h1 : |Work.Construction.Ftot α g s θ| ≤ c + |g s θ| := by
      have h2 : |Work.Construction.Ftot α g s θ|
          = |Work.Construction.Fstar α s θ + g s θ| := by
        simp only [Work.Construction.Ftot]
      rw [h2, hc]
      exact le_trans (abs_add_le _ _) (add_le_add (n5_Fstar_abs_le hα hα1 hs hθ) (le_refl _))
    calc Work.Spaces.K θ * |Work.Construction.Ftot α g s θ|
        ≤ Work.Spaces.K θ * (c + |g s θ|) := mul_le_mul_of_nonneg_left h1 (n5_K_nonneg hθ)
      _ = c * Work.Spaces.K θ + Work.Spaces.K θ * |g s θ| := by ring
  have hFint : IntegrableOn (fun θ => Work.Spaces.K θ * |Work.Construction.Ftot α g s θ|)
      Work.Spaces.Iθ := by
    refine hmajint.mono' ?_ ?_
    · have hFsm : Measurable (fun θ : ℝ => Work.Construction.Fstar α s θ) := by
        unfold Work.Construction.Fstar Work.FM.Fstar
        exact (measurable_const.mul ((n5_continuous_Gam hα).measurable.div measurable_const)).mul
          measurable_const
      have hFt : AEStronglyMeasurable (fun θ : ℝ => Work.Construction.Ftot α g s θ)
          (volume.restrict Work.Spaces.Iθ) := by
        refine (hFsm.aestronglyMeasurable.add haesmg).congr ?_
        filter_upwards with θ
        simp only [Pi.add_apply, Work.Construction.Ftot]
      exact n5_measurable_K.aestronglyMeasurable.mul
        (continuous_abs.comp_aestronglyMeasurable hFt)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_of_nonneg (mul_nonneg (n5_K_nonneg hθ) (abs_nonneg _))]
      exact hFpt θ hθ
  -- `Z ≤ c + 4√P`
  have hZ : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |Work.Construction.Ftot α g s θ|)
      ≤ c + 4 * Real.sqrt P := by
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |Work.Construction.Ftot α g s θ|)
        ≤ ∫ θ in Work.Spaces.Iθ, (c * Work.Spaces.K θ + Work.Spaces.K θ * |g s θ|) := by
      refine integral_mono_of_nonneg ?_ hmajint ?_
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        exact mul_nonneg (n5_K_nonneg hθ) (abs_nonneg _)
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        exact hFpt θ hθ
    have h2 : (∫ θ in Work.Spaces.Iθ, (c * Work.Spaces.K θ + Work.Spaces.K θ * |g s θ|))
        = c + ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |g s θ| := by
      rw [MeasureTheory.integral_add (n5_integrableOn_K.const_mul c) hKgi,
        MeasureTheory.integral_const_mul, Work.Coercivity.integral_Itheta_K, mul_one]
    rw [← hP] at hKg
    linarith [h1, hKg]
  have hZ0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |Work.Construction.Ftot α g s θ| :=
    integral_nonneg_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact mul_nonneg (n5_K_nonneg hθ) (abs_nonneg _))
  -- `|FK F(s)| ≤ Z`
  have hFKF : |Work.Construction.FK (Work.Construction.Ftot α g) s|
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |Work.Construction.Ftot α g s θ| := by
    rw [Work.Construction.FK]
    refine MeasureTheory.norm_integral_le_of_norm_le
      (f := fun θ => Work.Construction.Ftot α g s θ * Work.Spaces.K θ) hFint ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (n5_K_nonneg hθ), mul_comm]
  -- the main chain
  have hmaj2int : IntegrableOn (fun θ => (|Work.Construction.FK (Work.Construction.Ftot α g) s| / s)
      * (Work.Spaces.K θ * |Work.Construction.Ftot α g s θ|)) Work.Spaces.Iθ :=
    hFint.const_mul _
  calc ‖Work.Construction.L12dens (Work.Construction.N5 α (Work.Construction.Ftot α g) Φ) s‖
      = ‖∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ
          * Work.Construction.N5 α (Work.Construction.Ftot α g) Φ s θ / s‖ := rfl
    _ ≤ ∫ θ in Work.Spaces.Iθ, (|Work.Construction.FK (Work.Construction.Ftot α g) s| / s)
          * (Work.Spaces.K θ * |Work.Construction.Ftot α g s θ|) := by
        refine MeasureTheory.norm_integral_le_of_norm_le
          (f := fun θ => Work.Spaces.K θ
            * Work.Construction.N5 α (Work.Construction.Ftot α g) Φ s θ / s) hmaj2int ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
        have hK0 := n5_K_nonneg hθ
        have hsin : (Real.sin θ) ^ 2 ≤ 1 := Real.sin_sq_le_one θ
        have hA0 : 0 ≤ Work.Spaces.K θ * |Work.Construction.FK (Work.Construction.Ftot α g) s|
            * |Work.Construction.Ftot α g s θ| / s :=
          div_nonneg (mul_nonneg (mul_nonneg hK0 (abs_nonneg _)) (abs_nonneg _)) hs0
        have h1 : ‖Work.Spaces.K θ
              * Work.Construction.N5 α (Work.Construction.Ftot α g) Φ s θ / s‖
            = Work.Spaces.K θ * (Real.sin θ) ^ 2
              * |Work.Construction.FK (Work.Construction.Ftot α g) s|
              * |Work.Construction.Ftot α g s θ| / s := by
          rw [Real.norm_eq_abs]
          simp only [Work.Construction.N5, abs_div, abs_mul, abs_neg, abs_of_nonneg hK0,
            abs_of_pos hs, abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
        rw [h1]
        calc Work.Spaces.K θ * (Real.sin θ) ^ 2
              * |Work.Construction.FK (Work.Construction.Ftot α g) s|
              * |Work.Construction.Ftot α g s θ| / s
            = (Work.Spaces.K θ * |Work.Construction.FK (Work.Construction.Ftot α g) s|
                * |Work.Construction.Ftot α g s θ| / s) * (Real.sin θ) ^ 2 := by ring
          _ ≤ (Work.Spaces.K θ * |Work.Construction.FK (Work.Construction.Ftot α g) s|
                * |Work.Construction.Ftot α g s θ| / s) * 1 :=
              mul_le_mul_of_nonneg_left hsin hA0
          _ = (|Work.Construction.FK (Work.Construction.Ftot α g) s| / s)
                * (Work.Spaces.K θ * |Work.Construction.Ftot α g s θ|) := by ring
    _ = (|Work.Construction.FK (Work.Construction.Ftot α g) s| / s)
          * ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * |Work.Construction.Ftot α g s θ| :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ ((c + 4 * Real.sqrt P) / s) * (c + 4 * Real.sqrt P) := by
        refine mul_le_mul ?_ hZ hZ0 ?_
        · exact div_le_div_of_nonneg_right (le_trans hFKF hZ) hs0
        · exact div_nonneg (by positivity) hs0
    _ = (c + 4 * Real.sqrt P) ^ 2 / s := by ring


/-! ## The radial endgame -/

/-- `1 ≤ w(s) = (1+s)²/s²` for `s > 0`. -/
lemma n5_one_le_w {s : ℝ} (hs : 0 < s) : 1 ≤ Work.Spaces.w s := by
  rw [Work.Spaces.w, one_le_div (by positivity)]
  nlinarith

/-- `1/s ≤ w(s) = (1+s)²/s²` for `s > 0` (equivalently `s ≤ (1+s)²`). -/
lemma n5_inv_le_w {s : ℝ} (hs : 0 < s) : 1 / s ≤ Work.Spaces.w s := by
  have hs2 : 0 < s ^ 2 := by positivity
  have h : (1 : ℝ) / s = s / s ^ 2 := by field_simp
  rw [h, Work.Spaces.w, div_le_div_iff₀ hs2 hs2]
  nlinarith [sq_nonneg (1 + s)]

/-- `HkSq` is nonnegative. -/
lemma n5_hkSq_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ Work.Spaces.HkSq α k f := by
  rw [Work.Spaces.HkSq]
  refine integral_nonneg_of_ae ?_
  filter_upwards with z
  refine integral_nonneg_of_ae ?_
  filter_upwards with θ
  exact Work.Spaces.HkIntegrand_nonneg α k f z θ

/-- **The radial estimate.**  With `Ph(s) = ∫_θ g(s,θ)²`:
`∫_{s>0} (20αs/(1+s)² + 4√(Ph s))²/s ds ≤ 2000(α² + √α·X + α^{-3/2}X²)`, `X = Xn α g`, and
the integrand is integrable.  The estimate is `(u+v)² ≤ 2u²+2v²` together with
`2u²/s ≤ 800α²(1+s)^{-2}`, `2v²/s ≤ 32·Ph(s)w(s)` and the two Hardy–weight bounds
`∫_{s>0}(1+s)^{-2} ≤ 2` (`InvOneAddSq`) and `∫_{s>0} Ph·w ≤ X²` (`phiWeight_le`). -/
lemma n5_radial {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    IntegrableOn (fun s => (20 * α * s / (1 + s) ^ 2
        + 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)) ^ 2 / s) (Set.Ioi 0) ∧
    (∫ s in Set.Ioi 0, (20 * α * s / (1 + s) ^ 2
        + 4 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2)) ^ 2 / s)
      ≤ 2000 * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  set Ph : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2 with hPh
  have hPh0 : ∀ s, 0 ≤ Ph s := by
    intro s
    rw [hPh]
    exact integral_nonneg_of_ae (Eventually.of_forall fun θ => sq_nonneg _)
  -- the weighted angular energy and its bound
  have hWeq : ∀ r : ℝ, (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) * ((1 + r) / r) ^ 2
      = Ph r * Work.Spaces.w r := by
    intro r
    rw [hPh, Work.Spaces.w, div_pow]
  have hWint : IntegrableOn (fun s => Ph s * Work.Spaces.w s) (Set.Ioi 0) :=
    (Work.FTS.H2.l12q_phiWeight_integrable α g hsm hmem).congr
      (Eventually.of_forall fun r => hWeq r)
  have hWle : (∫ s in Set.Ioi 0, Ph s * Work.Spaces.w s) ≤ Work.FTS.Nonlin.Xn α g ^ 2 := by
    have h := Work.FTS.H2.l12q_phiWeight_le α g hmem
    have h2 : (∫ s in Set.Ioi 0, Ph s * Work.Spaces.w s)
        = ∫ s in Set.Ioi 0, (∫ θ in Work.Spaces.Iθ, (g s θ) ^ 2) * ((1 + s) / s) ^ 2 :=
      setIntegral_congr_fun measurableSet_Ioi (fun r _ => (hWeq r).symm)
    rw [h2, Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm,
      Real.sq_sqrt (n5_hkSq_nonneg α 4 g)]
    exact h
  -- the integrable majorant
  obtain ⟨hBint, hBle⟩ := Work.FTS.H2.InvOneAddSq
  set M : ℝ → ℝ := fun s => 800 * α ^ 2 * (1 / (1 + s)) ^ 2 + 32 * (Ph s * Work.Spaces.w s)
    with hM
  have hMint : IntegrableOn M (Set.Ioi 0) :=
    (hBint.const_mul (800 * α ^ 2)).add (hWint.const_mul 32)
  -- the pointwise bound
  have hpt : ∀ᵐ s ∂(volume.restrict (Set.Ioi 0)), (20 * α * s / (1 + s) ^ 2
      + 4 * Real.sqrt (Ph s)) ^ 2 / s ≤ M s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hq : (20 * α * s / (1 + s) ^ 2 + 4 * Real.sqrt (Ph s)) ^ 2
        ≤ 2 * (20 * α * s / (1 + s) ^ 2) ^ 2 + 2 * (4 * Real.sqrt (Ph s)) ^ 2 := by
      have h := add_sq_le (a := 20 * α * s / (1 + s) ^ 2) (b := 4 * Real.sqrt (Ph s))
      linarith [h]
    have h1 : (20 * α * s / (1 + s) ^ 2 + 4 * Real.sqrt (Ph s)) ^ 2 / s
        ≤ (2 * (20 * α * s / (1 + s) ^ 2) ^ 2 + 2 * (4 * Real.sqrt (Ph s)) ^ 2) / s :=
      div_le_div_of_nonneg_right hq hs.le
    refine le_trans h1 ?_
    have hsplit : (2 * (20 * α * s / (1 + s) ^ 2) ^ 2
          + 2 * (4 * Real.sqrt (Ph s)) ^ 2) / s
        = 2 * (20 * α * s / (1 + s) ^ 2) ^ 2 / s + 2 * (4 * Real.sqrt (Ph s)) ^ 2 / s := by
      ring
    rw [hsplit, hM]
    have hA : 2 * (20 * α * s / (1 + s) ^ 2) ^ 2 / s
        ≤ 800 * α ^ 2 * (1 / (1 + s)) ^ 2 := by
      have hAeq : 2 * (20 * α * s / (1 + s) ^ 2) ^ 2 / s
          = 800 * α ^ 2 * (s / (1 + s) ^ 4) := by
        field_simp
        ring
      rw [hAeq]
      have hspos : (0 : ℝ) < 1 + s := by
        have hs0 : 0 < s := hs
        linarith
      have hkey : s / (1 + s) ^ 4 ≤ (1 / (1 + s)) ^ 2 := by
        have h1 : (1 / (1 + s)) ^ 2 = 1 / (1 + s) ^ 2 := by rw [div_pow, one_pow]
        rw [h1, div_le_div_iff₀ (pow_pos hspos 4) (pow_pos hspos 2)]
        nlinarith [sq_nonneg (1 + s), sq_nonneg s]
      exact mul_le_mul_of_nonneg_left hkey (mul_nonneg (by norm_num) (sq_nonneg α))
    have hB : 2 * (4 * Real.sqrt (Ph s)) ^ 2 / s ≤ 32 * (Ph s * Work.Spaces.w s) := by
      have hBeq : 2 * (4 * Real.sqrt (Ph s)) ^ 2 / s = 32 * (Ph s / s) := by
        rw [mul_pow, Real.sq_sqrt (hPh0 s)]
        ring
      rw [hBeq]
      have hkey : s⁻¹ ≤ Work.Spaces.w s := by
        rw [← one_div]
        exact n5_inv_le_w hs
      have h2 : Ph s / s ≤ Ph s * Work.Spaces.w s := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hkey (hPh0 s)
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    linarith
  -- integrability of the integrand
  have hTint : IntegrableOn (fun s => (20 * α * s / (1 + s) ^ 2
      + 4 * Real.sqrt (Ph s)) ^ 2 / s) (Set.Ioi 0) := by
    have hPhm : AEStronglyMeasurable Ph (volume.restrict (Set.Ioi 0)) := by
      rw [hPh]
      exact Work.FTS.H2.l12q_phi_aesm g hsm
    have hlinaesm : AEStronglyMeasurable (fun s : ℝ => 20 * α * s / (1 + s) ^ 2)
        (volume.restrict (Set.Ioi 0)) := by
      have hne : ∀ s ∈ Set.Ioi (0 : ℝ), (1 + s) ^ 2 ≠ 0 := by
        intro s hs
        have hs0 : 0 < s := hs
        exact pow_ne_zero 2 (ne_of_gt (by linarith))
      exact (ContinuousOn.div (continuousOn_const.mul continuousOn_id)
        ((continuousOn_const.add continuousOn_id).pow 2) hne).aestronglyMeasurable
        measurableSet_Ioi
    have hsq : AEStronglyMeasurable
        (fun s : ℝ => (20 * α * s / (1 + s) ^ 2 + 4 * Real.sqrt (Ph s)) ^ 2)
        (volume.restrict (Set.Ioi 0)) :=
      (hlinaesm.add (aestronglyMeasurable_const.mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable hPhm))).pow 2
    refine hMint.mono' (hsq.div₀ measurable_id.aestronglyMeasurable) ?_
    filter_upwards [hpt, ae_restrict_mem measurableSet_Ioi] with s hsB hs
    have hs0 : 0 < s := hs
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) hs0.le)]
    exact hsB
  refine ⟨hTint, ?_⟩
  refine le_trans (integral_mono_of_nonneg ?_ hMint hpt) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 < s := hs
    exact div_nonneg (sq_nonneg _) hs0.le
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hpow : 1 ≤ α ^ (-(3 / 2 : ℝ)) := by
    rw [Real.rpow_neg hα.le]
    refine (one_le_inv₀ (Real.rpow_pos_of_pos hα (3 / 2))).mpr ?_
    exact Real.rpow_le_one hα.le hα1 (by norm_num)
  have heq : (∫ s in Set.Ioi 0, M s)
      = 800 * α ^ 2 * (∫ s in Set.Ioi 0, (1 / (1 + s)) ^ 2)
        + 32 * (∫ s in Set.Ioi 0, Ph s * Work.Spaces.w s) := by
    simp only [hM]
    rw [MeasureTheory.integral_add (hBint.const_mul _) (hWint.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [heq]
  have h1 : 800 * α ^ 2 * (∫ s in Set.Ioi 0, (1 / (1 + s)) ^ 2) ≤ 800 * α ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hBle (by positivity)
  have h2 : 32 * (∫ s in Set.Ioi 0, Ph s * Work.Spaces.w s)
      ≤ 32 * Work.FTS.Nonlin.Xn α g ^ 2 :=
    mul_le_mul_of_nonneg_left hWle (by norm_num)
  nlinarith [h1, h2, hX0, hpow, Real.sqrt_nonneg α, sq_nonneg (Work.FTS.Nonlin.Xn α g)]


theorem n5Bound {α₂ Ci Ce Cs : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.Nonlin.GalClass α g → Work.FTS.Nonlin.StarPkg α Cs Φs →
      Work.FTS.Nonlin.EllPkgG α Ce g Φg → 0 < α → α ≤ 1 → α ≤ α₂ →
      (∫ s in Set.Ioi (0 : ℝ), ‖Work.Construction.L12dens (Work.Construction.N5 α
          (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) s‖)
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  refine ⟨2000, by norm_num, ?_⟩
  intro α g Φs Φg hgal hstar hell hα hα1 hαα₂
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)
  obtain ⟨hsm, hmem, _⟩ := hreg4
  obtain ⟨hTint, hTle⟩ := n5_radial (g := g) hα hα1 hsm hmem
  have hdens := n5_dens_le (Φ := fun z θ => Φs z θ + Φg z θ) hα hα1 hsm hmem
  refine le_trans ?_ hTle
  refine integral_mono_of_nonneg ?_ hTint ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact norm_nonneg _
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact hdens s hs

end Work.FTS.Nonlinear.Pieces.Rl1
