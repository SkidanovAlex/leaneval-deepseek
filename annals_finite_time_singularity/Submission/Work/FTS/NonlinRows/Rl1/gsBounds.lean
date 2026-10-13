import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.FaStep
import Submission.Work.FTS.NonlinRows.Rl1.gsTools
import Submission.Work.FTS.NonlinRows.Rl1.gsRow2
import Submission.Work.FTS.NonlinRows.Rl1.gsRow3

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-- Row `N₁^{gs} = 2ℛ(Φ̃_g)·F_*`: the `L₁₂`-density estimate with the explicit `r`-dependent
majorant `M r = √(CA/(γ-1)·Ψ r)` of the `HQo`-coefficient `ℛ(Φ̃_g)`.  The pointwise input is
`|K θ·F_*| ≤ 60α·r/(1+r)²` (`Work.FTS.NonlinRows.Rl1.K_Fstar_pt`), and the profile
`c r = 120α·r/(1+r)` closes the `r`-step through `Fa_le_of_profile`. -/
theorem row1gs {CA α Ce : ℝ} {g Φg : Fn} (hCA : 0 < CA)
    (hang : ∀ (A : Fn), Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (A z θ) ^ 2 ≤ CA / (Work.Spaces.gam α - 1)
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A z θ')
    (hα : 0 < α) (hα1 : α ≤ 1) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Fa (Work.FTS.Nonlin.N1gs α g Φg)
      ≤ ENNReal.ofReal (2000 * Real.sqrt (10 * CA) * max Ce 0
          * α ^ (1 / 2 : ℝ) * Xn α g) := by
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam]; linarith
  have hC : 0 ≤ CA / (Work.Spaces.gam α - 1) := div_nonneg hCA.le hγ.le
  -- the coefficient `A = ℛ(Φ̃_g)` and its energy `Ψ`
  set A : Fn := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) with hA
  have hAsm : Work.FTS.EllipticEst.SmoothOpen A := by rw [hA]; exact hell.R.1.1
  have hAmem : Work.Spaces.HkMem α 4 A := by rw [hA]; exact hell.R.1.2
  have hAxn : Xn α A ≤ Ce * Xn α g := by rw [hA]; exact hell.R.2
  set Ψ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ
    with hΨ
  set M : ℝ → ℝ := fun r => Real.sqrt (CA / (Work.Spaces.gam α - 1) * Ψ r) with hM
  set cc : ℝ → ℝ := fun r => 120 * α * r / (1 + r) with hcc
  have hccnn : ∀ r, 0 < r → 0 ≤ cc r := by
    intro r hr
    rw [hcc]
    positivity
  have hMnn : ∀ r, 0 ≤ M r := fun r => Real.sqrt_nonneg _
  have hΨnn : ∀ r, 0 ≤ Ψ r := by
    intro r
    exact MeasureTheory.setIntegral_nonneg
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 A r θ)
  have hMle : ∀ r, 0 < r → (M r) ^ 2 ≤ CA / (Work.Spaces.gam α - 1) * Ψ r := by
    intro r _
    exact (Real.sq_sqrt (mul_nonneg hC (hΨnn r))).le
  obtain ⟨hΨmeas, hΨint, hΨle⟩ := HkSlot_data hAmem
  -- `r⁻¹ · cc r = 120α/(1+r)` on `r > 0`
  have hccinv : ∀ r, 0 < r → r⁻¹ * cc r = 120 * α / (1 + r) := by
    intro r hr
    rw [hcc]
    have hr0 : r ≠ 0 := ne_of_gt hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hccmeas : AEMeasurable (fun r => r⁻¹ * cc r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hbase : AEMeasurable (fun r : ℝ => 120 * α * (1 + r)⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (measurable_const.mul ((measurable_const.add measurable_id).inv)).aemeasurable
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact (hccinv r hr).symm
  have hccint : MeasureTheory.IntegrableOn (fun r => (r⁻¹ * cc r) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
    have hbase : MeasureTheory.IntegrableOn (fun r => (120 * α / (1 + r)) ^ 2)
        (Set.Ioi (0 : ℝ)) := by
      have h2 : MeasureTheory.IntegrableOn (fun r => (120 * α) ^ 2 * (1 / (1 + r)) ^ 2)
          (Set.Ioi (0 : ℝ)) := (integrableOn_inv_one_add_sq'.1).const_mul _
      refine MeasureTheory.IntegrableOn.congr_fun h2 ?_ measurableSet_Ioi
      intro r hr
      field_simp
    refine MeasureTheory.IntegrableOn.congr_fun hbase ?_ measurableSet_Ioi
    intro r hr
    exact congrArg (fun x => x ^ 2) (hccinv r hr).symm
  -- the θ-step
  have hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg r θ| ≤ cc r * M r := by
    intro r hr θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ1.le⟩
    have hR : |A r θ| ≤ M r := by
      have h2 := hang A hAsm hAmem r θ hr hθ0 hθ1
      have h3 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq_eq_abs] at h3
    have hF := K_Fstar_pt hα hα1 hr hθI
    have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N1gs α g Φg r θ|
        = 2 * |A r θ| * |Work.Spaces.K θ * Work.Construction.Fstar α r θ| := by
      simp only [Work.FTS.Nonlin.N1gs, Work.FTS.Nonlin.PhiTg, hA, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [habs]
    have h1r : (0 : ℝ) < 1 + r := by linarith
    have hle : (1 : ℝ) + r ≤ (1 + r) ^ 2 := by nlinarith [sq_nonneg r]
    have hdiv : r / (1 + r) ^ 2 ≤ r / (1 + r) := by
      rw [div_le_div_iff₀ (by positivity) h1r]
      nlinarith [mul_le_mul_of_nonneg_left hle hr.le]
    have hstep : 2 * |A r θ| * |Work.Spaces.K θ * Work.Construction.Fstar α r θ|
        ≤ 2 * M r * (60 * α * r / (1 + r) ^ 2) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hR (by norm_num)) hF (abs_nonneg _) ?_
      positivity
    refine hstep.trans ?_
    rw [hcc]
    have h1 : 2 * M r * (60 * α * r / (1 + r) ^ 2)
        = 120 * α * (r / (1 + r) ^ 2) * M r := by ring
    rw [h1]
    have h2 : 120 * α * (r / (1 + r) ^ 2) * M r ≤ 120 * α * (r / (1 + r)) * M r := by
      refine mul_le_mul_of_nonneg_right ?_ (hMnn r)
      exact mul_le_mul_of_nonneg_left hdiv (by positivity)
    have h3 : 120 * α * (r / (1 + r)) * M r = 120 * α * r / (1 + r) * M r := by ring
    linarith [h2, h3.le, h3.ge]
  -- the Cauchy–Schwarz step
  have hmain := Fa_le_of_profile (N := Work.FTS.Nonlin.N1gs α g Φg) (c := cc) (M := M)
    (Ψ := Ψ) (C := CA / (Work.Spaces.gam α - 1)) hC hccnn hMnn hΨnn hΨmeas hΨint
    hccmeas hccint hMle hpt
  have hX0 : 0 ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hCa0 : 0 ≤ max Ce 0 := le_max_right Ce 0
  have hsq : Work.Spaces.HkSq α 4 A = (Xn α A) ^ 2 :=
    (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 A)).symm
  have hΨbd : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ max Ce 0 * Xn α g := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ (Xn α A) ^ 2 :=
      hΨle.trans (le_of_eq hsq)
    have h2 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Xn α A := by
      calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Real.sqrt ((Xn α A) ^ 2) :=
            Real.sqrt_le_sqrt h1
        _ = |Xn α A| := Real.sqrt_sq_eq_abs _
        _ = Xn α A := abs_of_nonneg (Work.Spaces.HkNorm_nonneg α 4 A)
    calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Xn α A := h2
      _ ≤ Ce * Xn α g := hAxn
      _ ≤ max Ce 0 * Xn α g := mul_le_mul_of_nonneg_right (le_max_left Ce 0) hX0
  have hcinteg : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
      = (120 * α) ^ 2 * ∫ r in Set.Ioi (0 : ℝ), (1 / (1 + r)) ^ 2 := by
    have hcong : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
        = ∫ r in Set.Ioi (0 : ℝ), (120 * α) ^ 2 * (1 / (1 + r)) ^ 2 := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
      intro r hr
      change (r⁻¹ * cc r) ^ 2 = (120 * α) ^ 2 * (1 / (1 + r)) ^ 2
      rw [hccinv r hr]
      field_simp
    rw [hcong, MeasureTheory.integral_const_mul]
  have hcbd : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
      ≤ 120 * α * Real.sqrt 2 := by
    have h1 : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2) ≤ (120 * α) ^ 2 * 2 := by
      rw [hcinteg]
      exact mul_le_mul_of_nonneg_left integrableOn_inv_one_add_sq'.2 (sq_nonneg _)
    calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
        ≤ Real.sqrt ((120 * α) ^ 2 * 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt ((120 * α) ^ 2) * Real.sqrt 2 := Real.sqrt_mul (sq_nonneg _) 2
      _ = 120 * α * Real.sqrt 2 := by rw [Real.sqrt_sq (by positivity)]
  have hkey : Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2))
      ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g := by
    have h1 : Real.sqrt (CA / (Work.Spaces.gam α - 1))
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
        ≤ Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (max Ce 0 * Xn α g)
            * (120 * α * Real.sqrt 2) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hΨbd (Real.sqrt_nonneg _)) hcbd
        (Real.sqrt_nonneg _) ?_
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCa0 hX0)
    have h2 : Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * (max Ce 0 * Xn α g) * (120 * α * Real.sqrt 2))
        = Real.pi / 2 * Real.sqrt 2 * 120
            * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α)
            * max Ce 0 * Xn α g := by ring
    have h3 : Real.pi / 2 * Real.sqrt 2 * 120
        * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α) * max Ce 0 * Xn α g
        ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g := by
      rw [sqrt_coef_mul_alpha hCA.le hα]
      have h4 : Real.pi / 2 * Real.sqrt 2 * 120 * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ))
          * max Ce 0 * Xn α g
          = (Real.pi / 2 * Real.sqrt 2 * 120) * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ)
              * max Ce 0 * Xn α g) := by ring
      rw [h4]
      calc (Real.pi / 2 * Real.sqrt 2 * 120) * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ)
            * max Ce 0 * Xn α g)
          ≤ 2000 * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0 * Xn α g) :=
            mul_le_mul_of_nonneg_right pi_div_two_mul_sqrt_two_mul
              (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
                (Real.rpow_nonneg hα.le _)) hCa0) hX0)
        _ = 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g := by ring
    calc Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2))
        ≤ Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (max Ce 0 * Xn α g)
            * (120 * α * Real.sqrt 2)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.pi / 2 * Real.sqrt 2 * 120
            * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α) * max Ce 0 * Xn α g := h2
      _ ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g := h3
  exact hmain.trans (ENNReal.ofReal_le_ofReal hkey)

/-
The three `gs`-rows (coefficient a `HQo`-coefficient of `EllPkgGo`, slot an explicit profile
`F_*`, `∂_θF_*`, `D_zF_*`).  Route (unprimed sibling: `rl1Pieces.Pgs` in
`Pieces/rl1Pieces/Pgs.lean`, constant bounds via `gPt`; here the coefficient majorant is
`z`-dependent):
* for `N1gs = 2ℛ(Φ̃_g)·F_*` use the pointwise `|K θ·F_*| ≤ 60 α z/(1+z)²`
  (`Work.FTS.NonlinRows.Rl1.K_Fstar_pt`), so
  `∫⁻_θ |K·N1gs| ≤ ofReal(M r)·ofReal(60 α r/(1+r)²)` with `M r` the coefficient majorant
  (`angSup_le`), and then `outer_gen` with `θw r := 60α/(1+r)` (valid since
  `r/(1+r)² ≤ 1/(1+r)`), `Ψ` the coefficient energy (`HkSlot_data`), `C = C_A/(γ-1)·4`
  (the factor `2` of the piece), `∫θw² ≤ 3600α²·2`.  Rate: `C·α^{1/2}·Ce·X ≤ Ce·Env`.
* `N2gs = -2𝒰(Φ̃_g)·∂_θF_*`: write `𝒰 = sin2θ·(𝒰/sin2θ)` (valid on `Ioo 0 (π/2)`; at the
  endpoints `K = 0`), use `K_sin_pth_Fstar_pt`-style pointwise bound
  `|K θ·∂_θF_*| ≤ 80α² z/(1+z)²` (`Work.FTS.NonlinRows.Rl1.K_pthFstar_pt`), same `outer_gen`.
* `N3gs = -2α𝒱(Φ̃_g)·D_zF_*`: `|K θ·D_zF_*| ≤ 60α z/(1+z)²` (`K_DzFstar_pt`), `outer_gen`.
All three rates fit `K·Env α g` since `√α·X` and `α^{3/2}·X` are dominated by `Env`.
-/
theorem gsBounds {Ce : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φg : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1gs α g Φg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2gs α g Φg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3gs α g Φg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) := by
  obtain ⟨CA, hCApos, hCA⟩ := angSup_le
  set K : ℝ := 1 + 2000 * (max Ce 0 * Real.sqrt (10 * CA)) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have hA : 0 ≤ max Ce 0 * Real.sqrt (10 * CA) :=
      mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
    linarith
  refine ⟨K, hKpos, ?_⟩
  intro α g Φg hα hα1 hgal hell
  have hEnv : 0 ≤ Env α g := Env_nonneg g hα.le
  have hK : 2000 * Real.sqrt (10 * CA) * max Ce 0 * α ^ (1 / 2 : ℝ) * Xn α g
      ≤ K * Env α g := by
    rw [hKdef]
    exact const_mul_le_K hCApos.le hα hEnv
  have hang : ∀ (A : Fn), Work.FTS.EllipticEst.SmoothOpen A → Work.Spaces.HkMem α 4 A →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (A z θ) ^ 2 ≤ CA / (Work.Spaces.gam α - 1)
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A z θ' :=
    fun A => hCA α A hα hα1
  refine ⟨?_, ?_, ?_⟩
  · exact (row1gs (CA := CA) hCApos hang hα hα1 hell).trans
      (ENNReal.ofReal_le_ofReal hK)
  · exact (gsRow2 (CA := CA) hCApos hang hα hα1 hell).trans
      (ENNReal.ofReal_le_ofReal hK)
  · exact (gsRow3 (CA := CA) hCApos hang hα hα1 hell).trans
      (ENNReal.ofReal_le_ofReal hK)

end Work.FTS.NonlinRows.Rl1
