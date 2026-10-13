/-
# `Rows45` — the `FK`-rows of the primed `rl1` estimate

The three row groups of the `rl1` zero-mode estimate (`Fa (Nᵢ)(·) ≤ K · Env α g`) split into

* rows 1--3, whose coefficient is an `HQo`-function of a package (proved in `Rl1/ggBounds`,
  `Rl1/gsBounds`, `Rl1/sgBounds`), and
* rows 4--5, whose coefficient is an *angular moment*: `FK g = ∫_θ g(·,θ)K(θ)dθ` (`N4gg`, `N5gg`),
  `FK (F_*) = α·2z/(1+z)²` (`N4sg`, `N5sg`), or a combination with the explicit profile `F_*`
  (`N4gs`, `N5gs`).

This file proves the six rows 4--5:

* `ggRows45` (`N4gg`, `N5gg`): `|FK g z| ≤ 4√(Φ0 g z)` (`FK_g_pt`) turns the piece into the
  factorisation `|K θ·N| ≤ |A||B|` with `A = 3·FK g` (controlled by the slot energy `Φ0 g`) and
  `B` the slot `D_θg` resp. `g`; `Fa_le_coef_slot` then gives `≤ ofReal (12√(π/2)·|g|²_{ℋ⁴})`,
  and `|g|²_{ℋ⁴} ≤ Env α g`.
* `gsRows45` (`N4gs`, `N5gs`): the `F_*`-slot is an explicit profile
  (`DthFstar_pt`, `Fstar_pt`), so `Fa_le_of_profile` applies with `M r = 4√(Φ0 g r)`.
* `sgRows45` (`N4sg`, `N5sg`): `FK (F_*)` is the explicit profile `α·2r/(1+r)²`
  (`FK_Fstar_pt`), hence a *pointwise* coefficient; the engine `PsgAux.rl1_slot_le`
  (already proved) applies with the slots `D_θg` resp. `g`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Rl1.FaCoefSlot
import Submission.Work.FTS.NonlinRows.Rl1.gsTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows.Rl1

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary consequences of the envelope -/

/-- `|g|²_{ℋ⁴} ≤ Env α g` for `0 < α ≤ 1` (the weight `α^{-3/2}` of the `Env`-definition is
`≥ 1`). -/
theorem Xn_sq_le_Env (g : Fn) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (Work.FTS.Nonlin.Xn α g) ^ 2 ≤ Env α g := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have h1 : (1 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1
      (show (-(3 / 2 : ℝ)) ≤ 0 by norm_num)
    simpa using h
  have h2 : (Work.FTS.Nonlin.Xn α g) ^ 2
      ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    le_mul_of_one_le_left (sq_nonneg _) h1
  rw [Env]
  have h3 : 0 ≤ α ^ 2 := sq_nonneg α
  have h4 : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg (Real.sqrt_nonneg α) hX
  linarith

/-- `α·|g|_{ℋ⁴} ≤ Env α g` for `0 < α ≤ 1`. -/
theorem alpha_mul_Xn_le_Env {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have h1 : α ≤ Real.sqrt α := by
    have hα2 : α ^ 2 ≤ α := by nlinarith [hα.le, hα1]
    calc α = Real.sqrt (α ^ 2) := (Real.sqrt_sq hα.le).symm
      _ ≤ Real.sqrt α := Real.sqrt_le_sqrt hα2
  have h2 : Real.sqrt α * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
    rw [Env]
    have h3 : 0 ≤ α ^ 2 := sq_nonneg α
    have h4 : 0 ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    linarith
  exact (mul_le_mul_of_nonneg_right h1 hX).trans h2

/-- `α²·|g|_{ℋ⁴} ≤ Env α g` for `0 < α ≤ 1`. -/
theorem alpha_sq_mul_Xn_le_Env {α : ℝ} {g : Fn} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ 2 * Work.FTS.Nonlin.Xn α g ≤ Env α g := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have h1 : α ^ 2 ≤ α := by nlinarith [hα.le, hα1]
  exact (mul_le_mul_of_nonneg_right h1 hX).trans (alpha_mul_Xn_le_Env (g := g) hα hα1)

/-! ## The weight comparison `r⁻² ≤ w r` and its consequence for slot energies -/

/-- `|K θ| ≤ 3` on the open angular interval. -/
theorem K_abs_le_three' {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |Work.Spaces.K θ| ≤ 3 := by
  rw [abs_le]
  exact ⟨by
      have h := Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.K_nonneg_of_mem_Iθ
        (show θ ∈ Work.Spaces.Iθ from ⟨hθ.1.le, hθ.2.le⟩)
      linarith,
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.K_le_three θ⟩

theorem inv_sq_le_w {r : ℝ} (hr : 0 < r) : (r⁻¹) ^ 2 ≤ Work.Spaces.w r := by
  have h1 : (r⁻¹) ^ 2 = 1 / r ^ 2 := by rw [inv_pow, one_div]
  rw [Work.Spaces.w, h1, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < r ^ 2)]
  nlinarith [sq_nonneg (1 + r)]

/-- **The `r⁻²`-weighted slot energy.**  If `Φ ≥ 0` is measurable and `w·Φ` is integrable with
`∫ w Φ ≤ Xs`, then `r⁻²Φ` is integrable with `∫ r⁻²Φ ≤ Xs` (because `r⁻² ≤ w` on `r > 0`). -/
theorem invSq_mul_integrable_le {Φ : ℝ → ℝ} {Xs : ℝ}
    (hΦnn : ∀ r, 0 ≤ Φ r)
    (hΦmeas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hΦintw : MeasureTheory.IntegrableOn (fun r => Work.Spaces.w r * Φ r) (Set.Ioi (0 : ℝ)))
    (hΦlew : (∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Φ r) ≤ Xs) :
    MeasureTheory.IntegrableOn (fun r => (r⁻¹) ^ 2 * Φ r) (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * Φ r) ≤ Xs := by
  have hle : ∀ᵐ r ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (r⁻¹) ^ 2 * Φ r ≤ Work.Spaces.w r * Φ r := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_le_mul_of_nonneg_right (inv_sq_le_w hr) (hΦnn r)
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun r => (r⁻¹) ^ 2 * Φ r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : Measurable (fun r : ℝ => (r⁻¹) ^ 2) := by fun_prop
    exact (h1.aemeasurable.mul hΦmeas).aestronglyMeasurable
  have hint : MeasureTheory.IntegrableOn (fun r => (r⁻¹) ^ 2 * Φ r) (Set.Ioi (0 : ℝ)) :=
    hΦintw.mono' hmeas (hle.mono fun r hr => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hΦnn r))]
      exact hr)
  refine ⟨hint, ?_⟩
  exact (MeasureTheory.integral_mono_ae hint hΦintw hle).trans hΦlew

/-- The `B`-slot energy as a `θ`-lintegral: if `Φ r = ∫_θ (B r θ)²` and the slice is
integrable, then `∫⁻_θ ofReal (B r θ²) = ofReal (Φ r)`. -/
theorem slot_lintegral_eq {B : ℝ → ℝ → ℝ} {Φ : ℝ → ℝ} {r : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => (B r θ) ^ 2) Work.Spaces.Iθ)
    (hΦ : Φ r = ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2)) = ENNReal.ofReal (Φ r) := by
  rw [hΦ]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun θ => sq_nonneg (B r θ))).symm

/-! ## The angular moment `FK g` and its pointwise bound -/

/-- `(FK g r)² ≤ 16·Φ0 g r`, i.e. `|FK g r| ≤ 4√(Φ0 g r)` (`FK_g_pt`). -/
theorem FK_sq_le {g : Fn} {r : ℝ} (hr : 0 < r)
    (hint : MeasureTheory.IntegrableOn (fun θ => (g r θ) ^ 2) Work.Spaces.Iθ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => g r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (Work.Construction.FK g r) ^ 2
      ≤ 16 * Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r := by
  have h := FK_g_pt (g := g) hr hint hmeas
  have hΦ0 : (0 : ℝ) ≤ Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r :=
    MeasureTheory.integral_nonneg (fun θ => sq_nonneg (g r θ))
  have hsq : |Work.Construction.FK g r| ^ 2
      ≤ (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)) ^ 2 := by
    have h2 := mul_self_le_mul_self (abs_nonneg _) h
    rw [pow_two, pow_two]
    exact h2
  rw [mul_pow, Real.sq_sqrt hΦ0, sq_abs] at hsq
  linarith [hsq]

/-- The profile data of `c r = d·r/(1+r)²`: `r⁻¹c r = d/(1+r)²` on `r > 0`, so its square is
integrable with square-integral `≤ 2d²` (because `(1+r)^{-4} ≤ (1+r)^{-2}`). -/
theorem profile_data_sq {d : ℝ} (hd : 0 ≤ d) :
    AEMeasurable (fun r : ℝ => r⁻¹ * (d * r / (1 + r) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) ∧
      MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2)
        (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2) ≤ d ^ 2 * 2 ∧
      Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2)
        ≤ d * Real.sqrt 2 := by
  have hkey : ∀ r : ℝ, 0 < r → r⁻¹ * (d * r / (1 + r) ^ 2) = d / (1 + r) ^ 2 := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hmeas : AEMeasurable (fun r : ℝ => r⁻¹ * (d * r / (1 + r) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hbase : AEMeasurable (fun r : ℝ => d * ((1 + r) ^ 2)⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (measurable_const.mul ((measurable_const.add measurable_id).pow_const 2).inv).aemeasurable
    refine hbase.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    rw [hkey r hr]
    rfl
  have hbaseint : MeasureTheory.IntegrableOn
      (fun r : ℝ => d ^ 2 * (1 / (1 + r)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_inv_one_add_sq'.1).const_mul _
  -- on `r > 0`, the square is `d²/(1+r)⁴`, which is dominated by `d²/(1+r)²`
  have hval : ∀ r : ℝ, 0 < r → (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2 = d ^ 2 / (1 + r) ^ 4 := by
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith)
    rw [hkey r hr, div_pow, ← pow_mul]
  have hbaseval : ∀ r : ℝ, d ^ 2 * (1 / (1 + r)) ^ 2 = d ^ 2 / (1 + r) ^ 2 := by
    intro r
    rw [div_pow, one_pow]
    ring
  have hdom : ∀ r ∈ Set.Ioi (0 : ℝ),
      (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2 ≤ d ^ 2 * (1 / (1 + r)) ^ 2 := by
    intro r hr
    have hr' : (0 : ℝ) < r := hr
    have h1r : (0 : ℝ) < 1 + r := by linarith
    rw [hval r hr', hbaseval r]
    refine div_le_div_of_nonneg_left (sq_nonneg d) (pow_pos h1r 2) ?_
    nlinarith [sq_nonneg r, hr'.le]
  have hsm : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (hmeas.pow_const 2).aestronglyMeasurable
  have hint : MeasureTheory.IntegrableOn (fun r : ℝ => (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2)
      (Set.Ioi (0 : ℝ)) :=
    hbaseint.mono' hsm (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hdom r hr)
  have hle : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2) ≤ d ^ 2 * 2 := by
    refine (MeasureTheory.integral_mono_ae hint hbaseint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hdom)).trans ?_
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left integrableOn_inv_one_add_sq'.2 (sq_nonneg _)
  refine ⟨hmeas, hint, hle, ?_⟩
  calc Real.sqrt (∫ r in Set.Ioi (0 : ℝ), (r⁻¹ * (d * r / (1 + r) ^ 2)) ^ 2)
      ≤ Real.sqrt (d ^ 2 * 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt (d ^ 2) * Real.sqrt 2 := Real.sqrt_mul (sq_nonneg _) 2
    _ = d * Real.sqrt 2 := by rw [Real.sqrt_sq hd]

/-! ## The six rows -/

/-- **Rows `N₄^{gg}`, `N₅^{gg}`** (`FK g` against `D_θg` resp. `g`). -/
theorem ggRows45 : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g : Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g →
    Fa (Work.FTS.Nonlin.N4gg α g) ≤ ENNReal.ofReal (K * Env α g) ∧
    Fa (Work.FTS.Nonlin.N5gg g) ≤ ENNReal.ofReal (K * Env α g) := by
  refine ⟨12 * Real.sqrt (Real.pi / 2) + 1, by positivity, ?_⟩
  intro α g hα hα1 hgal
  have hreg : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hsq : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have haxis : ∀ θ ∈ Work.Spaces.Iθ, g 0 θ = 0 := fun θ hθ => (hgal.axis θ hθ).1
  have s0 := slot0 (α := α) (g := g) hsq hmem
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_zero_of_axis haxis)
  have s1 := slot1 (α := α) (g := g) hα.le hsq hmem
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_zero_Dth_of_axis haxis)
  have hXs : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
  have hΦ1w := invSq_mul_integrable_le (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 g)
    (Xs := Work.Spaces.HkSq α 4 g) s1.nonneg s1.meas s1.intw s1.lew
  have hΦ0w := invSq_mul_integrable_le (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g)
    (Xs := Work.Spaces.HkSq α 4 g) s0.nonneg s0.meas s0.intw s0.lew
  have hEnvn : 0 ≤ Env α g := Env_nonneg g hα.le
  have hX2 := Xn_sq_le_Env g hα hα1
  have hfinal : ∀ {N : Fn}, Fa N ≤ ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
      * (Work.FTS.Nonlin.Xn α g) ^ 2) →
      Fa N ≤ ENNReal.ofReal ((12 * Real.sqrt (Real.pi / 2) + 1) * Env α g) := by
    intro N hN
    refine hN.trans (ENNReal.ofReal_le_ofReal ?_)
    have h12 : 0 ≤ 12 * Real.sqrt (Real.pi / 2) := by positivity
    calc 12 * Real.sqrt (Real.pi / 2) * (Work.FTS.Nonlin.Xn α g) ^ 2
        ≤ 12 * Real.sqrt (Real.pi / 2) * Env α g := mul_le_mul_of_nonneg_left hX2 h12
      _ ≤ (12 * Real.sqrt (Real.pi / 2) + 1) * Env α g := by
          nlinarith [hEnvn, Real.sqrt_nonneg (Real.pi / 2)]
  constructor
  · -- `N₄^{gg} = -(1/2)·FK g·D_θ g`
    have hmain := Fa_le_coef_slot (N := Work.FTS.Nonlin.N4gg α g)
      (A := fun r _ => 3 * Work.Construction.FK g r) (B := Work.Spaces.Dth g)
      (C := 144) (Ys := Work.Spaces.HkSq α 4 g) (Zs := Work.Spaces.HkSq α 4 g)
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g)
      (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 g)
      (by norm_num) hXs hXs s0.nonneg s0.meas s0.int s0.le
      s1.nonneg s1.meas hΦ1w.1 hΦ1w.2
      (fun r _ => aestronglyMeasurable_const)
      (fun r hr => s1.aesm r hr)
      (fun r hr => s1.sqint r hr)
      (fun r hr => Filter.Eventually.of_forall fun θ => by
        have h := FK_sq_le (g := g) hr (s0.sqint r hr) (s0.aesm r hr)
        have h9 : (3 * Work.Construction.FK g r) ^ 2 = 9 * (Work.Construction.FK g r) ^ 2 := by
          ring
        rw [h9]
        linarith [h])
      (fun r hr => (slot_lintegral_eq (s1.sqint r hr) rfl).le)
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N4gg α g r θ|
            = |Work.Spaces.K θ| * (1 / 2) * |Work.Construction.FK g r|
              * |Work.Spaces.Dth g r θ| := by
          rw [Work.FTS.Nonlin.N4gg]
          simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
          ring
        have h2 : |Work.Spaces.K θ| * (1 / 2) * |Work.Construction.FK g r|
              * |Work.Spaces.Dth g r θ|
            ≤ 3 * (1 / 2) * |Work.Construction.FK g r| * |Work.Spaces.Dth g r θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right hK (by norm_num)
        have h3 : 3 * (1 / 2) * |Work.Construction.FK g r| * |Work.Spaces.Dth g r θ|
            ≤ |3 * Work.Construction.FK g r| * |Work.Spaces.Dth g r θ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
          nlinarith [abs_nonneg (Work.Construction.FK g r),
            abs_nonneg (Work.Spaces.Dth g r θ)]
        exact (le_of_eq h1).trans (h2.trans h3))
    have hsimp : ENNReal.ofReal (Real.sqrt 144 * Real.sqrt (Real.pi / 2)
          * Real.sqrt (Work.Spaces.HkSq α 4 g) * Real.sqrt (Work.Spaces.HkSq α 4 g))
        = ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
          * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
      have hK : Real.sqrt (144 : ℝ) = 12 := by
        rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hX : Real.sqrt (Work.Spaces.HkSq α 4 g) = Work.FTS.Nonlin.Xn α g := rfl
      rw [hK, hX]
      congr 1
      ring
    rw [hsimp] at hmain
    exact hfinal hmain
  · -- `N₅^{gg} = -sin²θ·FK g·g`
    have hmain := Fa_le_coef_slot (N := Work.FTS.Nonlin.N5gg g)
      (A := fun r _ => 3 * Work.Construction.FK g r) (B := g)
      (C := 144) (Ys := Work.Spaces.HkSq α 4 g) (Zs := Work.Spaces.HkSq α 4 g)
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g)
      (Φ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g)
      (by norm_num) hXs hXs s0.nonneg s0.meas s0.int s0.le
      s0.nonneg s0.meas hΦ0w.1 hΦ0w.2
      (fun r _ => aestronglyMeasurable_const)
      (fun r hr => s0.aesm r hr)
      (fun r hr => s0.sqint r hr)
      (fun r hr => Filter.Eventually.of_forall fun θ => by
        have h := FK_sq_le (g := g) hr (s0.sqint r hr) (s0.aesm r hr)
        have h9 : (3 * Work.Construction.FK g r) ^ 2 = 9 * (Work.Construction.FK g r) ^ 2 := by
          ring
        rw [h9]
        linarith [h])
      (fun r hr => (slot_lintegral_eq (s0.sqint r hr) rfl).le)
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have hs : (Real.sin θ) ^ 2 ≤ 1 := by
          nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N5gg g r θ|
            = |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK g r|
              * |g r θ| := by
          rw [Work.FTS.Nonlin.N5gg]
          simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
        have h2 : |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK g r|
              * |g r θ|
            ≤ 3 * 1 * |Work.Construction.FK g r| * |g r θ| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul hK hs (sq_nonneg _) (by norm_num)
        have h3 : 3 * 1 * |Work.Construction.FK g r| * |g r θ|
            ≤ |3 * Work.Construction.FK g r| * |g r θ| := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), mul_one]
        exact (le_of_eq h1).trans (h2.trans h3))
    have hsimp : ENNReal.ofReal (Real.sqrt 144 * Real.sqrt (Real.pi / 2)
          * Real.sqrt (Work.Spaces.HkSq α 4 g) * Real.sqrt (Work.Spaces.HkSq α 4 g))
        = ENNReal.ofReal (12 * Real.sqrt (Real.pi / 2)
          * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
      have hK : Real.sqrt (144 : ℝ) = 12 := by
        rw [show (144 : ℝ) = 12 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hX : Real.sqrt (Work.Spaces.HkSq α 4 g) = Work.FTS.Nonlin.Xn α g := rfl
      rw [hK, hX]
      congr 1
      ring
    rw [hsimp] at hmain
    exact hfinal hmain

/-- **Rows `N₄^{gs}`, `N₅^{gs}`** (`FK g` against the explicit profiles `D_θF_*` resp. `F_*`). -/
theorem gsRows45 {Ce : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φg : Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
    Fa (Work.FTS.Nonlin.N4gs α g) ≤ ENNReal.ofReal (K * Env α g) ∧
    Fa (Work.FTS.Nonlin.N5gs α g) ≤ ENNReal.ofReal (K * Env α g) := by
  refine ⟨80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1, by positivity, ?_⟩
  intro α g Φg hα hα1 hgal hell
  have hreg : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hsq : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have haxis : ∀ θ ∈ Work.Spaces.Iθ, g 0 θ = 0 := fun θ hθ => (hgal.axis θ hθ).1
  have s0 := slot0 (α := α) (g := g) hsq hmem
    (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_zero_of_axis haxis)
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hEnvn : 0 ≤ Env α g := Env_nonneg g hα.le
  have hsqrtX : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
      Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r) ≤ Work.FTS.Nonlin.Xn α g :=
    Real.sqrt_le_sqrt s0.le
  have hX2 := Xn_sq_le_Env g hα hα1
  have hα2X := alpha_sq_mul_Xn_le_Env (g := g) hα hα1
  have hαX := alpha_mul_Xn_le_Env (g := g) hα hα1
  have hrad2 : Real.sqrt 2 ≤ 2 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  constructor
  · -- `N₄^{gs} = -(1/2)·sin2θ·FK g·∂_θF_*`
    have hp := profile_data_sq (d := 40 * α ^ 2) (by positivity)
    have hmain := Fa_le_of_profile (N := Work.FTS.Nonlin.N4gs α g)
      (c := fun r => 40 * α ^ 2 * r / (1 + r) ^ 2)
      (M := fun r => 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r))
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g) (C := 16)
      (by norm_num)
      (fun r hr => by positivity)
      (fun r => by positivity)
      s0.nonneg s0.meas s0.int hp.1 hp.2.1
      (fun r hr => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (s0.nonneg r)]
        norm_num))
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have hd := DthFstar_pt (α := α) hα hα1 hr hθ.1 hθ.2
        have hFKabs : |Work.Construction.FK g r|
            ≤ 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r) := by
          have hFK := Real.abs_le_sqrt (FK_sq_le (g := g) hr (s0.sqint r hr) (s0.aesm r hr))
          rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
            show Real.sqrt (16 : ℝ) = 4 from by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hFK
        have hDth : |Work.Spaces.Dth (Work.Construction.Fstar α) r θ|
            ≤ (80 / 3) * α ^ 2 * (r / (1 + r) ^ 2) := hd
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N4gs α g r θ|
            = |Work.Spaces.K θ| * (1 / 2)
              * |Work.Spaces.Dth (Work.Construction.Fstar α) r θ|
              * |Work.Construction.FK g r| := by
          rw [Work.FTS.Nonlin.N4gs]
          simp only [Work.Construction.s2, Work.Spaces.Dth, abs_mul, abs_neg,
            abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
          ring
        have hb : (0 : ℝ) ≤ (80 / 3) * α ^ 2 * (r / (1 + r) ^ 2) := by positivity
        have h4 : (0 : ℝ) ≤ 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r) :=
          by positivity
        have hstep : |Work.Spaces.K θ| * (1 / 2)
              * |Work.Spaces.Dth (Work.Construction.Fstar α) r θ|
              * |Work.Construction.FK g r|
            ≤ 3 * (1 / 2) * ((80 / 3) * α ^ 2 * (r / (1 + r) ^ 2))
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)) := by
          refine mul_le_mul ?_ hFKabs (abs_nonneg _) (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_right hK (by norm_num)) hDth (abs_nonneg _)
            (by norm_num)
        have heq : 3 * (1 / 2) * ((80 / 3) * α ^ 2 * (r / (1 + r) ^ 2))
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r))
            = (40 * α ^ 2 * r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)) := by ring
        exact (le_of_eq h1).trans (hstep.trans (le_of_eq heq)))
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show Real.sqrt (16 : ℝ) = 4 from by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have hsq := (profile_data_sq (d := 40 * α ^ 2) (by positivity)).2.2.2
    have h40 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2) ≤ 40 * α ^ 2 * 2 :=
      hsq.trans (by nlinarith [Real.sqrt_nonneg 2, hrad2, sq_nonneg α])
    have hstep : Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (40 * α ^ 2 * r / (1 + r) ^ 2)) ^ 2))
        ≤ Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g) * (40 * α ^ 2 * 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrtX (by norm_num)) h40
        (Real.sqrt_nonneg _) (by positivity)
    refine hstep.trans ?_
    have hEnv : Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g) * (40 * α ^ 2 * 2))
        ≤ (80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1) * Env α g := by
      have h1 : Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g) * (40 * α ^ 2 * 2))
          = (160 * Real.pi) * (α ^ 2 * Work.FTS.Nonlin.Xn α g) := by ring
      rw [h1]
      have h2 : (160 * Real.pi) * (α ^ 2 * Work.FTS.Nonlin.Xn α g)
          ≤ (160 * Real.pi) * Env α g :=
        mul_le_mul_of_nonneg_left hα2X (by positivity)
      have h3 : (160 : ℝ) * Real.pi
          ≤ 80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1 := by
        have hs2 : (1 : ℝ) ≤ Real.sqrt 2 := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]
          norm_num
        nlinarith [Real.pi_pos, hs2]
      calc (160 * Real.pi) * (α ^ 2 * Work.FTS.Nonlin.Xn α g)
          ≤ (160 * Real.pi) * Env α g := h2
        _ ≤ (80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1) * Env α g :=
            mul_le_mul_of_nonneg_right h3 hEnvn
    exact hEnv
  · -- `N₅^{gs} = -sin²θ·FK g·F_*`
    have hp := profile_data_sq (d := 60 * α) (by positivity)
    have hmain := Fa_le_of_profile (N := Work.FTS.Nonlin.N5gs α g)
      (c := fun r => 60 * α * r / (1 + r) ^ 2)
      (M := fun r => 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r))
      (Ψ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g) (C := 16)
      (by norm_num)
      (fun r hr => by positivity)
      (fun r => by positivity)
      s0.nonneg s0.meas s0.int hp.1 hp.2.1
      (fun r hr => le_of_eq (by
        rw [mul_pow, Real.sq_sqrt (s0.nonneg r)]
        norm_num))
      (fun r hr θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have hs : (Real.sin θ) ^ 2 ≤ 1 := by
          nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
        have hF : |Work.Construction.Fstar α r θ|
            ≤ 20 * α * (r / (1 + r) ^ 2) := by
          have h := Fstar_pt (α := α) hα hα1 hr ⟨hθ.1.le, hθ.2.le⟩
          rwa [mul_div_assoc] at h
        have hFKabs : |Work.Construction.FK g r|
            ≤ 4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r) := by
          have hFK := Real.abs_le_sqrt (FK_sq_le (g := g) hr (s0.sqint r hr) (s0.aesm r hr))
          rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
            show Real.sqrt (16 : ℝ) = 4 from by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at hFK
        have h1 : |Work.Spaces.K θ * Work.FTS.Nonlin.N5gs α g r θ|
            = |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK g r|
              * |Work.Construction.Fstar α r θ| := by
          rw [Work.FTS.Nonlin.N5gs]
          simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
        have hstep : |Work.Spaces.K θ| * (Real.sin θ) ^ 2 * |Work.Construction.FK g r|
              * |Work.Construction.Fstar α r θ|
            ≤ 3 * 1 * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r))
              * (20 * α * (r / (1 + r) ^ 2)) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hK hs (sq_nonneg _) (by norm_num))
            hFKabs (abs_nonneg _) (by positivity)) hF (abs_nonneg _) (by positivity)
        have heq : 3 * 1 * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r))
              * (20 * α * (r / (1 + r) ^ 2))
            = (60 * α * r / (1 + r) ^ 2)
              * (4 * Real.sqrt (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)) := by ring
        exact (le_of_eq h1).trans (hstep.trans (le_of_eq heq)))
    refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show Real.sqrt (16 : ℝ) = 4 from by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have hsq := (profile_data_sq (d := 60 * α) (by positivity)).2.2.2
    have h60 : Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
        (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2) ≤ 60 * α * 2 :=
      hsq.trans (by nlinarith [Real.sqrt_nonneg 2, hrad2, hα.le])
    have hstep : Real.pi / 2 * (4 * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g r)
        * Real.sqrt (∫ r in Set.Ioi (0 : ℝ),
          (r⁻¹ * (60 * α * r / (1 + r) ^ 2)) ^ 2))
        ≤ Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g) * (60 * α * 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrtX (by norm_num)) h60
        (Real.sqrt_nonneg _) (by positivity)
    refine hstep.trans ?_
    have h1 : Real.pi / 2 * (4 * (Work.FTS.Nonlin.Xn α g) * (60 * α * 2))
        = (240 * Real.pi) * (α * Work.FTS.Nonlin.Xn α g) := by ring
    rw [h1]
    have h3 : (240 : ℝ) * Real.pi
        ≤ 80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1 := by
      have hs2 : ((6 : ℝ) / 5) ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      nlinarith [Real.pi_pos, hs2]
    calc (240 * Real.pi) * (α * Work.FTS.Nonlin.Xn α g)
        ≤ (240 * Real.pi) * Env α g := mul_le_mul_of_nonneg_left hαX (by positivity)
      _ ≤ (80 * Real.pi * Real.sqrt 2 + 120 * Real.pi * Real.sqrt 2 + 1) * Env α g :=
          mul_le_mul_of_nonneg_right h3 hEnvn

/-- The `Fa`-functional only sees the product `A·B` up to the association of the three
factors `K θ·A·B` (the engine `PsgAux.rl1_slot_le` groups them as `(K θ·A)·B`). -/
theorem Fa_mul_eq (A B : Fn) :
    Fa (fun r θ => A r θ * B r θ)
      = (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * A r θ * B r θ|)) := by
  rw [Fa]
  refine MeasureTheory.lintegral_congr fun r => ?_
  congr 1
  refine MeasureTheory.lintegral_congr fun θ => ?_
  rw [mul_assoc]

/-- **Rows `N₄^{sg}`, `N₅^{sg}`** (`FK (F_*) = α·2r/(1+r)²` against `D_θg` resp. `g`). -/
theorem sgRows45 {Cs : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs : Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.StarPkgo α Cs Φs →
    Fa (Work.FTS.Nonlin.N4sg α g) ≤ ENNReal.ofReal (K * Env α g) ∧
    Fa (Work.FTS.Nonlin.N5sg α g) ≤ ENNReal.ofReal (K * Env α g) := by
  refine ⟨6 * Real.sqrt (Real.pi / 2) + 1, by positivity, ?_⟩
  intro α g Φs hα hα1 hgal hs
  have hreg : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hsq : Work.FTS.LocData.SmoothQuad g := hreg.1
  have hmem : Work.Spaces.HkMem α 4 g := hreg.2.1
  have hEnvn : 0 ≤ Env α g := Env_nonneg g hα.le
  have hαX := alpha_mul_Xn_le_Env (g := g) hα hα1
  have hcont : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.contOn_of_smoothQuad hsq
  have hcontD : ContinuousOn (Function.uncurry (Work.Spaces.Dth g))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.contOn_of_smoothQuad
      (Work.FTS.LocData.SmoothQuad.DthIter hsq 1)
  have hFKF : ∀ r : ℝ, 0 < r → |Work.Construction.FK (Work.Construction.Fstar α) r|
      ≤ α / 2 := by
    intro r hr
    rw [FK_Fstar_pt hα hα1]
    have h1 : (0 : ℝ) ≤ 2 * r / (1 + r) ^ 2 := div_nonneg (by linarith) (by positivity)
    rw [abs_mul, abs_of_nonneg hα.le, abs_of_nonneg h1]
    have h2 : 2 * r / (1 + r) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (1 - r)]
    nlinarith [h2, hα.le]
  constructor
  · -- `N₄^{sg} = -(1/2)·FK (F_*)·D_θ g`
    have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le
      (α := α) (C := 3 * α) (g := g)
      (A := fun z _ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z)
      (B := Work.Spaces.Dth g)
      (by positivity) hmem
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have h1 : |Work.Spaces.K θ * (-(1 / 2)
              * Work.Construction.FK (Work.Construction.Fstar α) r)| 
            = |Work.Spaces.K θ| * (1 / 2)
              * |Work.Construction.FK (Work.Construction.Fstar α) r| := by
          simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 / 2))]
          ring
        rw [h1]
        have h3 : |Work.Spaces.K θ| * (1 / 2)
            * |Work.Construction.FK (Work.Construction.Fstar α) r| ≤ 3 * (1 / 2) * (α / 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right hK (by norm_num)) (hFKF r hr)
            (abs_nonneg _) (by positivity)
        refine h3.trans ?_
        nlinarith [hα.le])
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slice_sq_aemeasurable hcontD hr)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hcontD)
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ =>
        Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_dth hα hr hθ g)
    have hid : Work.FTS.Nonlin.N4sg α g
        = fun r θ => (-(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) r)
            * Work.Spaces.Dth g r θ := by
      funext r θ
      simp only [Work.FTS.Nonlin.N4sg]
    rw [hid, Fa_mul_eq (A := fun z _ =>
        -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z)
      (B := Work.Spaces.Dth g)]
    refine hmain.trans ?_
    · exact ENNReal.ofReal_le_ofReal (by
        have h1 : (3 * α) * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
            = (3 * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g) := by ring
        rw [h1]
        have h2 : (3 * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g)
            ≤ (3 * Real.sqrt (Real.pi / 2)) * Env α g :=
          mul_le_mul_of_nonneg_left hαX (by positivity)
        have h3 : (3 * Real.sqrt (Real.pi / 2))
            ≤ (6 * Real.sqrt (Real.pi / 2) + 1) := by
          nlinarith [Real.sqrt_nonneg (Real.pi / 2)]
        exact h2.trans (mul_le_mul_of_nonneg_right h3 hEnvn))
  · -- `N₅^{sg} = -sin²θ·FK (F_*)·g`
    have hmain := Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.rl1_slot_le
      (α := α) (C := 6 * α) (g := g)
      (A := fun z θ => -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z)
      (B := g)
      (by positivity) hmem
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ => by
        have hK : |Work.Spaces.K θ| ≤ 3 := K_abs_le_three' hθ
        have hsin : (Real.sin θ) ^ 2 ≤ 1 := by
          nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
        have h1 : |Work.Spaces.K θ * (-(Real.sin θ) ^ 2
              * Work.Construction.FK (Work.Construction.Fstar α) r)|
            = |Work.Spaces.K θ| * (Real.sin θ) ^ 2
              * |Work.Construction.FK (Work.Construction.Fstar α) r| := by
          simp only [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
        rw [h1]
        have h3 : |Work.Spaces.K θ| * (Real.sin θ) ^ 2
            * |Work.Construction.FK (Work.Construction.Fstar α) r|
            ≤ 3 * 1 * (α / 2) := by
          refine mul_le_mul (mul_le_mul hK hsin (sq_nonneg _) (by norm_num)) (hFKF r hr)
            (abs_nonneg _) (by positivity)
        exact h3.trans (by nlinarith [hα.le]))
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slice_sq_aemeasurable hcont hr)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_aemeasurable hcont)
      (fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo fun θ hθ =>
        Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.slot_g hα hr hθ g)
    have hid : Work.FTS.Nonlin.N5sg α g
        = fun r θ => (-(Real.sin θ) ^ 2
            * Work.Construction.FK (Work.Construction.Fstar α) r) * g r θ := by
      funext r θ
      simp only [Work.FTS.Nonlin.N5sg]
    rw [hid, Fa_mul_eq (A := fun z θ =>
        -(Real.sin θ) ^ 2 * Work.Construction.FK (Work.Construction.Fstar α) z) (B := g)]
    refine hmain.trans ?_
    · exact ENNReal.ofReal_le_ofReal (by
        have h1 : (6 * α) * Real.sqrt (Real.pi / 2) * Work.FTS.Nonlin.Xn α g
            = (6 * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g) := by ring
        rw [h1]
        have h2 : (6 * Real.sqrt (Real.pi / 2)) * (α * Work.FTS.Nonlin.Xn α g)
            ≤ (6 * Real.sqrt (Real.pi / 2)) * Env α g :=
          mul_le_mul_of_nonneg_left hαX (by positivity)
        exact h2.trans (mul_le_mul_of_nonneg_right (by
          nlinarith [Real.sqrt_nonneg (Real.pi / 2)]) hEnvn))

end Work.FTS.NonlinRows.Rl1
