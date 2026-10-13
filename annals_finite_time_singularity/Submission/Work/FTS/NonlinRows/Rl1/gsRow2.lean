import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Rl1.gsTools
import Submission.Work.FTS.NonlinRows.Rl1.FaStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false

/-- Row `N₂^{gs} = -2𝒰(Φ̃_g)·∂_θF_*` of the primed `gs`-block (namespace
`Work.FTS.NonlinRows.Rl1`).  With the `r`-dependent coefficient majorant
`M₂ r = √(CA/(γ-1) · ∫_θ HkIntegrand α 4 (𝒰/sin 2θ) r θ)` (`hang` is the angular sup bound of
`Work.FTS.NonlinRows.Rl1.angSup_le`, instantiated at the `HQo`-coefficient `𝒰/sin2θ` of
`hell.U`) and the pointwise profile bound `|K θ · ∂_θF_*| ≤ 80α²·r/(1+r)²`
(`Work.FTS.NonlinRows.Rl1.K_pthFstar_pt`), the `L₁₂`-density functional satisfies
`Fa (N2gs) ≤ ofReal (2000·√(10CA)·max Ce 0·α^{1/2}·|g|_{ℋ⁴})`.  Route: write
`𝒰 = sin2θ·(𝒰/sin2θ)` (valid on `Ioo 0 (π/2)`, and the endpoints are null), then
`Work.FTS.NonlinRows.Rl1.Fa_le_of_profile` with profile `c r = 160α²·r/(1+r)`, using
`Work.FTS.NonlinRows.Rl1.profile_data` for the profile and `HkSlot_data`/`hell.U.2` for the
coefficient energy.  Template: `row1gs` in
`Submission/Work/FTS/NonlinRows/Rl1/gsBounds.lean` (proved). -/
theorem gsRow2 {CA α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn} (hCA : 0 < CA)
    (hang : ∀ (A : Work.FTS.Galerkin.Fn), Work.FTS.EllipticEst.SmoothOpen A →
      Work.Spaces.HkMem α 4 A →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (A z θ) ^ 2 ≤ CA / (Work.Spaces.gam α - 1)
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A z θ')
    (hα : 0 < α) (hα1 : α ≤ 1) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2gs α g Φg)
      ≤ ENNReal.ofReal (2000 * Real.sqrt (10 * CA) * max Ce 0
          * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  have hγ : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam]; linarith
  have hC : 0 ≤ CA / (Work.Spaces.gam α - 1) := div_nonneg hCA.le hγ.le
  -- the `HQo`-coefficient `𝒰/sin 2θ` of `hell.U`, and its angular slot
  set A : Work.FTS.Galerkin.Fn := fun z θ =>
    Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ with hA
  have hAsm : Work.FTS.EllipticEst.SmoothOpen A := hell.U.1.1
  have hAmem : Work.Spaces.HkMem α 4 A := hell.U.1.2
  have hAxn : Work.FTS.Nonlin.Xn α A ≤ Ce * Work.FTS.Nonlin.Xn α g := hell.U.2
  set Ψ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ with hΨ
  set M : ℝ → ℝ := fun r => Real.sqrt (CA / (Work.Spaces.gam α - 1) * Ψ r) with hM
  set cc : ℝ → ℝ := fun r => 160 * α ^ 2 * r / (1 + r) with hcc
  have hccnn : ∀ r, 0 < r → 0 ≤ cc r := by
    intro r hr
    have h : cc r = 160 * α ^ 2 * r / (1 + r) := rfl
    rw [h]; positivity
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
  have hccmeas : AEMeasurable (fun r => r⁻¹ * cc r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (profile_data (d := 160 * α ^ 2) (by positivity)).1
  have hccint : MeasureTheory.IntegrableOn (fun r => (r⁻¹ * cc r) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    (profile_data (d := 160 * α ^ 2) (by positivity)).2.1
  -- ### the pointwise (angular) step: `𝒰 = sin 2θ · (𝒰/sin 2θ)`
  have hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * Work.FTS.Nonlin.N2gs α g Φg r θ| ≤ cc r * M r := by
    intro r hr θ hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have hs2pos : 0 < Work.Construction.s2 θ := by
      rw [Work.Construction.s2_eq]
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs2le : Work.Construction.s2 θ ≤ 1 := by
      rw [Work.Construction.s2_eq]; exact Real.sin_le_one _
    have hUfac : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ
        = Work.Construction.s2 θ * A r θ := by
      have hA' : A r θ = Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ
          / Work.Construction.s2 θ := rfl
      rw [hA', mul_div_assoc', mul_div_cancel_left₀ _ (ne_of_gt hs2pos)]
    have hAabs : |A r θ| ≤ M r := by
      have h2 := hang A hAsm hAmem r θ hr hθ0 hθ1
      have h3 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq_eq_abs] at h3
    have hK := K_pthFstar_pt hα hα1 hr hθ0 hθ1
    have hs2nn : 0 ≤ Work.Construction.s2 θ := le_of_lt hs2pos
    have habs : |Work.Spaces.K θ * Work.FTS.Nonlin.N2gs α g Φg r θ|
        = 2 * (Work.Construction.s2 θ * |A r θ|)
            * |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ| := by
      have hval : Work.Spaces.K θ * Work.FTS.Nonlin.N2gs α g Φg r θ
          = -2 * (Work.Construction.s2 θ * A r θ)
              * (Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ) := by
        simp only [Work.FTS.Nonlin.N2gs]
        rw [hUfac]
        ring
      rw [hval]
      simp only [abs_mul, abs_neg, abs_of_nonneg hs2nn,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs]
    have h2le : Work.Construction.s2 θ * |A r θ| ≤ 1 * M r :=
      mul_le_mul hs2le hAabs (abs_nonneg _) zero_le_one
    have h1 : 2 * (Work.Construction.s2 θ * |A r θ|) ≤ 2 * (1 * M r) :=
      mul_le_mul_of_nonneg_left h2le (by norm_num)
    have hmid : 2 * (Work.Construction.s2 θ * |A r θ|)
        * |Work.Spaces.K θ * Work.Spaces.pth (Work.Construction.Fstar α) r θ|
        ≤ 2 * (1 * M r) * (80 * α ^ 2 * (r / (1 + r) ^ 2)) :=
      mul_le_mul h1 hK (abs_nonneg _) (by positivity)
    refine hmid.trans ?_
    have h1r : (0 : ℝ) < 1 + r := by linarith
    have hstepp : 160 * α ^ 2 * (r / (1 + r) ^ 2) ≤ 160 * α ^ 2 * (r / (1 + r)) := by
      have hle : r / (1 + r) ^ 2 ≤ r / (1 + r) := by
        rw [div_le_div_iff₀ (by positivity) h1r]
        nlinarith [hr.le, h1r.le, sq_nonneg r, mul_nonneg hr.le h1r.le]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    calc 2 * (1 * M r) * (80 * α ^ 2 * (r / (1 + r) ^ 2))
        = 160 * α ^ 2 * (r / (1 + r) ^ 2) * M r := by ring
      _ ≤ 160 * α ^ 2 * (r / (1 + r)) * M r := mul_le_mul_of_nonneg_right hstepp (hMnn r)
      _ = cc r * M r := by
          have hcc' : cc r = 160 * α ^ 2 * r / (1 + r) := rfl
          rw [hcc']
          ring
  -- ### the Cauchy–Schwarz step
  have hmain := Fa_le_of_profile (N := Work.FTS.Nonlin.N2gs α g Φg) (c := cc) (M := M)
    (Ψ := Ψ) (C := CA / (Work.Spaces.gam α - 1)) hC hccnn hMnn hΨnn hΨmeas hΨint
    hccmeas hccint hMle hpt
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hCa0 : 0 ≤ max Ce 0 := le_max_right Ce 0
  have hs10 : 0 ≤ Real.sqrt (10 * CA) := Real.sqrt_nonneg _
  have hα12 : 0 ≤ α ^ (1 / 2 : ℝ) := Real.rpow_nonneg hα.le _
  have hΨbd : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
      ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g := by
    have h1 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Work.FTS.Nonlin.Xn α A :=
      Real.sqrt_le_sqrt hΨle
    calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r) ≤ Work.FTS.Nonlin.Xn α A := h1
      _ ≤ Ce * Work.FTS.Nonlin.Xn α g := hAxn
      _ ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right (le_max_left Ce 0) hX0
  have hcbd : Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
      ≤ 160 * α ^ 2 * Real.sqrt 2 :=
    (profile_data (d := 160 * α ^ 2) (by positivity)).2.2.2
  have hkey : Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2))
      ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0
          * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by
    have h1 : Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2)
        ≤ Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (max Ce 0 * Work.FTS.Nonlin.Xn α g)
            * (160 * α ^ 2 * Real.sqrt 2) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hΨbd (Real.sqrt_nonneg _)) hcbd
        (Real.sqrt_nonneg _) ?_
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hCa0 hX0)
    have h2 : Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * (max Ce 0 * Work.FTS.Nonlin.Xn α g) * (160 * α ^ 2 * Real.sqrt 2))
        = Real.pi / 2 * Real.sqrt 2 * 160
            * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2)
            * max Ce 0 * Work.FTS.Nonlin.Xn α g := by ring
    have h3 : Real.pi / 2 * Real.sqrt 2 * 160
          * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2)
          * max Ce 0 * Work.FTS.Nonlin.Xn α g
        ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0
            * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by
      rw [sqrt_coef_mul_alpha_sq hCA.le hα]
      have h3232 : α ^ (3 / 2 : ℝ) ≤ α ^ (1 / 2 : ℝ) := rpow_three_halves_le' hα hα1
      have hα32 : 0 ≤ α ^ (3 / 2 : ℝ) := Real.rpow_nonneg hα.le _
      have hconst : Real.pi / 2 * Real.sqrt 2 * 160 ≤ 2000 := by
        have h2 : Real.sqrt 2 ≤ 2 := by
          have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
          have h2' := Real.sqrt_nonneg 2
          nlinarith
        have hp : Real.pi / 2 ≤ 2 := by
          have h := Real.pi_lt_four
          have h2' := Real.pi_pos
          linarith
        nlinarith [Real.sqrt_nonneg 2, Real.pi_pos]
      have hR : 0 ≤ Real.sqrt (10 * CA) * max Ce 0 * Work.FTS.Nonlin.Xn α g :=
        mul_nonneg (mul_nonneg hs10 hCa0) hX0
      have hR32 : 0 ≤ Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0
          * Work.FTS.Nonlin.Xn α g :=
        mul_nonneg (mul_nonneg (mul_nonneg hs10 hα32) hCa0) hX0
      have hstep : Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0 * Work.FTS.Nonlin.Xn α g
          ≤ Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0 * Work.FTS.Nonlin.Xn α g := by
        calc Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0 * Work.FTS.Nonlin.Xn α g
            = (Real.sqrt (10 * CA) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
                * α ^ (3 / 2 : ℝ) := by ring
          _ ≤ (Real.sqrt (10 * CA) * max Ce 0 * Work.FTS.Nonlin.Xn α g)
                * α ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left h3232 hR
          _ = Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0
                * Work.FTS.Nonlin.Xn α g := by ring
      calc Real.pi / 2 * Real.sqrt 2 * 160 * (Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ))
            * max Ce 0 * Work.FTS.Nonlin.Xn α g
          = (Real.pi / 2 * Real.sqrt 2 * 160)
              * (Real.sqrt (10 * CA) * α ^ (3 / 2 : ℝ) * max Ce 0
                * Work.FTS.Nonlin.Xn α g) := by ring
        _ ≤ 2000 * (Real.sqrt (10 * CA) * α ^ (1 / 2 : ℝ) * max Ce 0
              * Work.FTS.Nonlin.Xn α g) :=
            mul_le_mul hconst hstep hR32 (by norm_num)
        _ = 2000 * Real.sqrt (10 * CA) * max Ce 0
              * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := by ring
    calc Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), Ψ r)
          * Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * cc r) ^ 2))
        ≤ Real.pi / 2 * (Real.sqrt (CA / (Work.Spaces.gam α - 1))
            * (max Ce 0 * Work.FTS.Nonlin.Xn α g) * (160 * α ^ 2 * Real.sqrt 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.pi / 2 * Real.sqrt 2 * 160
            * (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * α ^ 2)
            * max Ce 0 * Work.FTS.Nonlin.Xn α g := h2
      _ ≤ 2000 * Real.sqrt (10 * CA) * max Ce 0
            * α ^ (1 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g := h3
  exact hmain.trans (ENNReal.ofReal_le_ofReal hkey)

end Work.FTS.NonlinRows.Rl1
