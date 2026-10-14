import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.Vocab
-- ===== merged: Submission.Work.FTS.NonlinRows.Rl1.ggBounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.Rl1

/-
The three `gg`-rows whose coefficient is an `ℋ⁴`-coefficient of `EllPkgGo` (`Rop α (PhiTg α g Φg)`,
`Uop α (PhiTg α g Φg)/sin 2θ`, `Vop (PhiTg α g Φg)`) and whose slot is the datum's `g`, `D_θg`,
`D_zg`.  Route (see the unprimed sibling `Work.FTS.Nonlinear.Pieces.Rl1.ggRow1/2/3` in
`Pieces/Rl1/rl1Main.lean`, which uses the stronger `RegQ`-based `gPt`):
* pull the constant out of the `∫⁻_θ` and bound `|K θ · N| ≤ M r · K|slot|` pointwise, where
  `M r` is the coefficient's angular majorant `angSup_le` gives for the `HQo`-coefficient `A`:
  `A z θ ^ 2 ≤ C_A/(γ-1) · ∫_θ' HkIntegrand α 4 A z θ'`;
* the θ-step is `Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.inner_lintegral_le` (with a
  `z`-dependent `M := 3√(π/2)·M r` and `B` the slot, `Φ` its energy `Phi0/1/2 g`), and the
  `r`-step is `Work.FTS.NonlinRows.Rl1.outer_gen` with `C` the squared coefficient constant,
  `Ψ` the coefficient's `HkIntegrand`-energy (data: `HkSlot_data`) and `θw r = r⁻¹·√(Φ r)`
  (`∫θw² = ∫r⁻²Φ ≤ ∫wΦ ≤ HkSq α 4 g`, using `r⁻² ≤ w`).
For `N2gg` use `Work.FTS.Nonlinear.Pieces.rl1Pieces.N2gg_eq` (valid on `Ioo 0 (π/2)`,
`K` vanishes at the endpoints so `ae`-form suffices).  The constants come out as
`C·α^{-1/2}·max Ce 0·X²` (rows 1,2) and `C·α^{1/2}·max Ce 0·X²` (row 3), all `≤ C·Env α g`
for `0 < α ≤ 1` since `α^{-1/2} ≤ α^{-3/2}`, `α^{1/2} ≤ α^{-3/2}`.

The formalisation below uses the shared two-step engine
`Work.FTS.NonlinRows.Rl1.Fa_le_coef_slot` of `Submission/Work/FTS/NonlinRows/Rl1/FaCoefSlot.lean`
(Cauchy–Schwarz in `θ` against the slot energy, then in `r` against the coefficient energy): the
only row-dependent input is the pointwise factorisation `|K θ · N r θ| ≤ c·|A r θ|·|slot r θ|`
(the constant `c` absorbs the row factor `2` of `N` and the bound `|K| ≤ 3`), and the three
slot energies `Phi0 g`, `Phi1 g`, `Phi2 g` (`Work.FTS.NonlinRows.Rl1.slot0/1/2`).
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-! ## Elementary arithmetic: `√(C_A/(γ-1))` and the row constant -/

/-- `√(C_A/(γ-1)) = √(10·C_A)·α^{-1/2}` (`γ - 1 = α/10`). -/
private theorem sqrt_div_gam' {CA α : ℝ} (hCA : 0 ≤ CA) (hα : 0 < α) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) = Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ)) := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have hγ : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have h10 : (0 : ℝ) ≤ 10 * CA := by linarith
  have hsq : (Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ))) ^ 2 = CA / (Work.Spaces.gam α - 1) := by
    rw [mul_pow, Real.sq_sqrt h10, ← Real.rpow_two, ← Real.rpow_mul hα.le,
      show -(1 / 2 : ℝ) * 2 = -1 by norm_num, Real.rpow_neg_one, hγ]
    field_simp
  rw [← hsq, Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hα.le _))]

/-- **The row constant is dominated by `Env`.**  For `0 < α ≤ 1`, `C_A, B ≥ 0` and `c ≤ 2·max α 1`,
the row expression `√(C_A/(γ-1))·3√(π/2)·c·B·|g|²_{ℋ⁴}` is at most `(6√(π/2)√(10C_A)·B + 1)·Env α g`
(because `α^{-1/2}·c ≤ 2·α^{-3/2}` and `α^{-3/2}|g|²_{ℋ⁴} ≤ Env α g`). -/
private theorem rowConstLe' {α CA B c : ℝ} {g : Fn} (hCA : 0 ≤ CA) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hc2 : c ≤ 2 * max α 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * c * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2
      ≤ (6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B + 1)
        * Work.FTS.NonlinRows.Rl1.Env α g := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hX2 : 0 ≤ (Work.FTS.Nonlin.Xn α g) ^ 2 := sq_nonneg _
  have hEnv : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α g := Env_nonneg g hα.le
  have hp3 : 0 ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- `c ≤ 2`
  have hmax : max α 1 = 1 := le_antisymm (max_le hα1 le_rfl) (le_max_right α 1)
  have hc2' : c ≤ 2 := by rw [hmax] at hc2; linarith
  -- `α^{-1/2} ≤ α^{-3/2}`
  have hpow : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) := by
    have h1 : α ^ (-(3 / 2 : ℝ)) = α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hα]
      congr 1
      norm_num
    rw [h1]
    have h2 : 1 ≤ α ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]
      simpa only [one_div] using one_le_one_div hα hα1
    have h3 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    nlinarith
  have h0 : 0 ≤ 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) hB
  have hpos : 0 ≤ Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
      * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))) hB) hX2
  have hstep1 : α ^ (-(1 / 2 : ℝ)) * c ≤ 2 * α ^ (-(3 / 2 : ℝ)) := by
    have h := mul_le_mul hpow hc2' hc hp3
    linarith [h]
  -- `α^{-3/2}|g|² ≤ Env`
  have hEnvge : α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2
      ≤ Work.FTS.NonlinRows.Rl1.Env α g := by
    rw [Env]
    have h1 : 0 ≤ α ^ 2 := sq_nonneg α
    have h2 : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hX
    linarith
  rw [sqrt_div_gam' hCA hα]
  have h1 : Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ)) * (3 * Real.sqrt (Real.pi / 2)) * c * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2
      = (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
          * (Work.FTS.Nonlin.Xn α g) ^ 2) * (α ^ (-(1 / 2 : ℝ)) * c) := by ring
  rw [h1]
  have h2 : (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2) * (α ^ (-(1 / 2 : ℝ)) * c)
      ≤ (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2) * (2 * α ^ (-(3 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hstep1 hpos
  have h3 : (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2) * (2 * α ^ (-(3 / 2 : ℝ)))
      = 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2) := by ring
  have h4 : 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2)
      ≤ 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * Work.FTS.NonlinRows.Rl1.Env α g :=
    mul_le_mul_of_nonneg_left hEnvge h0
  have h5 : 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * Work.FTS.NonlinRows.Rl1.Env α g
      ≤ (6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B + 1)
        * Work.FTS.NonlinRows.Rl1.Env α g := by
    nlinarith [hEnv]
  exact le_trans h2 (le_trans (le_of_eq h3) (le_trans h4 h5))

/-- `r⁻² ≤ w r` for `r > 0`, so that the `L₁₂`-weight `r⁻¹` of a slot energy is
dominated by the Hardy weight of `HkSq`. -/
private theorem inv_sq_int_le' {Φ : ℝ → ℝ} (hΦnn : ∀ r, 0 ≤ Φ r)
    (hint : MeasureTheory.IntegrableOn (fun r => Work.Spaces.w r * Φ r) (Set.Ioi (0 : ℝ))) :
    MeasureTheory.IntegrableOn (fun r => (r⁻¹) ^ 2 * Φ r) (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * Φ r)
        ≤ ∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Φ r := by
  have hwpt : ∀ r, 0 < r → (r⁻¹) ^ 2 ≤ Work.Spaces.w r := by
    intro r hr
    have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr 2
    rw [Work.Spaces.w, inv_pow, inv_eq_one_div, div_le_div_iff_of_pos_right hr2]
    nlinarith [sq_nonneg r, hr.le]
  have hΦasm : MeasureTheory.AEStronglyMeasurable Φ
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hwm : Measurable (fun r : ℝ => (Work.Spaces.w r)⁻¹) := by
      unfold Work.Spaces.w
      fun_prop
    have h1 : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => (Work.Spaces.w r)⁻¹)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hwm.aestronglyMeasurable
    refine (h1.mul hint.aestronglyMeasurable).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    have h1r : (1 : ℝ) + r ≠ 0 := ne_of_gt (by linarith [hr0] : (0 : ℝ) < 1 + r)
    have hw : Work.Spaces.w r ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 h1r) (pow_ne_zero 2 (ne_of_gt hr))
    show (Work.Spaces.w r)⁻¹ * (Work.Spaces.w r * Φ r) = Φ r
    rw [inv_mul_cancel_left₀ hw]
  have hgasm : MeasureTheory.AEStronglyMeasurable (fun r => (r⁻¹) ^ 2 * Φ r)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : Measurable (fun r : ℝ => (r⁻¹) ^ 2) := by fun_prop
    exact (h1.aestronglyMeasurable).mul hΦasm
  have hfint : MeasureTheory.IntegrableOn (fun r => (r⁻¹) ^ 2 * Φ r) (Set.Ioi (0 : ℝ)) :=
    MeasureTheory.Integrable.mono' hint hgasm (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hΦnn r))]
      exact mul_le_mul_of_nonneg_right (hwpt r hr) (hΦnn r))
  exact ⟨hfint, MeasureTheory.integral_mono_ae hfint hint (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      exact mul_le_mul_of_nonneg_right (hwpt r hr) (hΦnn r))⟩

/-! ## The generic row engine -/

/-- **The engine of a primed `gg`-row.**  `|K θ · N r θ| ≤ c·|A r θ|·|B₀ r θ|` pointwise, `A` an
`ℋ⁴`-coefficient with the angular majorant `√(C_A/(γ-1)·∫_θ HkIntegrand α 4 A)` and `|A|_{ℋ⁴}` at
most `max Ce 0·|g|_{ℋ⁴}`, and `B₀` a slot with `SlotData α B₀ Φ₀ (HkSq α 4 g)`; then
`Fa N ≤ ofReal (√(C_A/(γ-1))·√(π/2)·c·max Ce 0·|g|²_{ℋ⁴})`. -/
theorem rowGG_engine {CA : ℝ} (hCA : 0 < CA)
    {α Ce : ℝ} (hα : 0 < α) {g : Fn} {A B₀ : ℝ → ℝ → ℝ} {Φ₀ : ℝ → ℝ} {N : Fn} {c : ℝ}
    (hAopen : Work.FTS.EllipticEst.SmoothOpen A) (hAmem : Work.Spaces.HkMem α 4 A)
    (hXnA : Work.FTS.Nonlin.Xn α A ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g)
    (hsup : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (A z θ) ^ 2 ≤ CA / (Work.Spaces.gam α - 1)
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A z θ')
    (hS : SlotData α B₀ Φ₀ (Work.Spaces.HkSq α 4 g))
    (hΦ₀eq : ∀ r, 0 < r → Φ₀ r = ∫ θ in Work.Spaces.Iθ, (B₀ r θ) ^ 2)
    (hc : 0 ≤ c)
    (hpt : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * N r θ| ≤ c * (|A r θ| * |B₀ r θ|)) :
    Fa N ≤ ENNReal.ofReal (Real.sqrt (CA / (Work.Spaces.gam α - 1))
      * Real.sqrt (Real.pi / 2) * c * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hC : 0 ≤ CA / (Work.Spaces.gam α - 1) := le_of_lt (div_pos hCA hγ)
  have hXs : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
  -- the scaled slot `B = c·B₀` and its energy `Φ`
  set B : Fn := fun z θ => c * B₀ z θ with hBdef
  set Φ : ℝ → ℝ := fun r => ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2 with hΦdef
  have hΦval : ∀ r, 0 < r → Φ r = c ^ 2 * Φ₀ r := by
    intro r hr
    calc Φ r = ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2 := rfl
      _ = ∫ θ in Work.Spaces.Iθ, c ^ 2 * (B₀ r θ) ^ 2 := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
          rw [hBdef]
          ring
      _ = c ^ 2 * ∫ θ in Work.Spaces.Iθ, (B₀ r θ) ^ 2 := MeasureTheory.integral_const_mul _ _
      _ = c ^ 2 * Φ₀ r := by rw [← hΦ₀eq r hr]
  have hBmeas : ∀ r, 0 < r → MeasureTheory.AEStronglyMeasurable (fun θ => B r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro r hr
    have h := (hS.aesm r hr).const_mul c
    simpa only [hBdef] using h
  have hBsq : ∀ r, 0 < r → MeasureTheory.IntegrableOn (fun θ => (B r θ) ^ 2)
      Work.Spaces.Iθ := by
    intro r hr
    refine MeasureTheory.IntegrableOn.congr_fun ((hS.sqint r hr).const_mul (c ^ 2)) ?_
      measurableSet_Icc
    intro θ _
    rw [hBdef]
    ring
  have hB : ∀ r, 0 < r → (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((B r θ) ^ 2))
      ≤ ENNReal.ofReal (Φ r) := by
    intro r hr
    rw [show Φ r = ∫ θ in Work.Spaces.Iθ, (B r θ) ^ 2 from rfl]
    exact le_of_eq (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hBsq r hr)
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)).symm
  have hΦnn : ∀ r, 0 ≤ Φ r := fun r => MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hΦmeas : AEMeasurable Φ (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : AEMeasurable (fun r : ℝ => c ^ 2 * Φ₀ r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := hS.meas.const_mul (c ^ 2)
    refine h1.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    exact (hΦval r hr).symm
  have hD1 := inv_sq_int_le' hS.nonneg hS.intw
  have hΦint : MeasureTheory.IntegrableOn (fun r => (r⁻¹) ^ 2 * Φ r) (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (hD1.1.const_mul (c ^ 2)) ?_ measurableSet_Ioi
    intro r hr
    show c ^ 2 * ((r⁻¹) ^ 2 * Φ₀ r) = (r⁻¹) ^ 2 * Φ r
    rw [hΦval r hr]
    ring
  have hΦle : (∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * Φ r)
      ≤ c ^ 2 * Work.Spaces.HkSq α 4 g := by
    calc (∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * Φ r)
        = ∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * (c ^ 2 * Φ₀ r) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r hr => by rw [hΦval r hr])
      _ = ∫ r in Set.Ioi (0 : ℝ), c ^ 2 * ((r⁻¹) ^ 2 * Φ₀ r) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r _ => by ring)
      _ = c ^ 2 * ∫ r in Set.Ioi (0 : ℝ), (r⁻¹) ^ 2 * Φ₀ r :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ c ^ 2 * ∫ r in Set.Ioi (0 : ℝ), Work.Spaces.w r * Φ₀ r :=
          mul_le_mul_of_nonneg_left hD1.2 (sq_nonneg c)
      _ ≤ c ^ 2 * Work.Spaces.HkSq α 4 g :=
          mul_le_mul_of_nonneg_left hS.lew (sq_nonneg c)
  have hZs : 0 ≤ c ^ 2 * Work.Spaces.HkSq α 4 g := mul_nonneg (sq_nonneg c) hXs
  -- the coefficient side
  obtain ⟨hΨmeas, hΨint, hΨle⟩ := HkSlot_data hAmem
  have hΨnn : ∀ r, 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ :=
    fun r => MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 A r θ
  have hAmeas : ∀ r, 0 < r → MeasureTheory.AEStronglyMeasurable (fun θ => A r θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun r hr => Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry A)
      hAopen.continuousOn hr
  have hAb : ∀ r, 0 < r → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (A r θ) ^ 2 ≤ (CA / (Work.Spaces.gam α - 1))
        * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ' :=
    fun r hr => Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgAux.ae_Iθ_of_forall_Ioo
      (fun θ hθ => hsup r θ hr hθ.1 hθ.2)
  have hpt' : ∀ r, 0 < r → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Work.Spaces.K θ * N r θ| ≤ |A r θ| * |B r θ| := by
    intro r hr θ hθ
    have h1 := hpt r hr θ hθ
    have h2 : |B r θ| = c * |B₀ r θ| := by
      rw [hBdef]
      simp only [abs_mul, abs_of_nonneg hc]
    calc |Work.Spaces.K θ * N r θ| ≤ c * (|A r θ| * |B₀ r θ|) := h1
      _ = |A r θ| * |B r θ| := by rw [h2]; ring
  have hmain := Fa_le_coef_slot (N := N) (A := A) (B := B)
    (C := CA / (Work.Spaces.gam α - 1))
    (Ys := Work.Spaces.HkSq α 4 A) (Zs := c ^ 2 * Work.Spaces.HkSq α 4 g)
    (Ψ := fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 A r θ) (Φ := Φ)
    hC (Work.Spaces.HkSq_nonneg α 4 A) hZs hΨnn hΨmeas hΨint hΨle
    hΦnn hΦmeas hΦint hΦle hAmeas hBmeas hBsq hAb hB hpt'
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hZs' : Real.sqrt (c ^ 2 * Work.Spaces.HkSq α 4 g) = c * Work.FTS.Nonlin.Xn α g := by
    rw [Real.sqrt_mul (sq_nonneg c) (Work.Spaces.HkSq α 4 g), Real.sqrt_sq hc]
    rfl
  have hYs' : Real.sqrt (Work.Spaces.HkSq α 4 A) ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g := hXnA
  have hfac : 0 ≤ Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hcX : 0 ≤ c * Work.FTS.Nonlin.Xn α g :=
    mul_nonneg hc (Work.Spaces.HkNorm_nonneg α 4 g)
  rw [hZs']
  calc Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2)
        * Real.sqrt (Work.Spaces.HkSq α 4 A) * (c * Work.FTS.Nonlin.Xn α g)
      ≤ Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2)
        * (max Ce 0 * Work.FTS.Nonlin.Xn α g) * (c * Work.FTS.Nonlin.Xn α g) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYs' hfac) hcX
    _ = Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * c * max Ce 0
        * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring

/-! ## The `N₂^{gg}` identity on the open quadrant -/

/-- `N₂^{gg} = -2·𝒰(Φ̃_g)∂_θg = -2·(𝒰(Φ̃_g)/sin 2θ)·D_θg` on the open quadrant. -/
private theorem n2gg_eq' (α : ℝ) (g Φg : Fn) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.Nonlin.N2gg α g Φg z θ
      = -2 * ((Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          / Work.Construction.s2 θ) * Work.Spaces.Dth g z θ) := by
  have hs : Work.Construction.s2 θ ≠ 0 := by
    rw [show Work.Construction.s2 θ = Real.sin (2 * θ) from rfl]
    exact ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, Real.pi_pos])
        (by linarith [hθ.2, Real.pi_pos]))
  have h1 : Work.Spaces.Dth g z θ = Work.Construction.s2 θ * Work.Spaces.pth g z θ := rfl
  have hU : Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ
      * (Work.Construction.s2 θ * Work.Spaces.pth g z θ)
      = Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ * Work.Spaces.pth g z θ := by
    rw [← mul_assoc, div_mul_cancel₀ _ hs]
  simp only [Work.FTS.Nonlin.N2gg]
  rw [h1, hU]
  ring

/-! ## The three rows -/

/-- Row 1: `N₁^{gg} = 2ℛ(Φ̃_g)·g`. -/
private theorem row1_gg {CA : ℝ} (hCA : 0 < CA) {α Ce : ℝ} (hα : 0 < α)
    {g Φg : Fn} (hgal : Work.FTS.Nonlin.GalClass α g)
    (hEll : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hsup : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ) ^ 2
        ≤ CA / (Work.Spaces.gam α - 1)
          * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
              (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) z θ') :
    Fa (Work.FTS.Nonlin.N1gg α g Φg) ≤ ENNReal.ofReal
      (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * 6
        * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
  obtain ⟨hRq, hRle⟩ := hEll.R
  have hsl : SlotData α g (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g)
      (Work.Spaces.HkSq α 4 g) :=
    slot0 hgal.reg.1 (Work.FTS.OpenPkg.galClass_HkMem4 hgal)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_zero_of_axis
        (fun θ hθ => (hgal.axis θ hθ).1))
  refine rowGG_engine (CA := CA) (α := α) (Ce := Ce) (g := g)
    (A := Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) (B₀ := g)
    (Φ₀ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi0 g)
    (N := Work.FTS.Nonlin.N1gg α g Φg) (c := 6)
    hCA hα hRq.1 hRq.2 ?_ hsup hsl (fun r _ => rfl) (by norm_num) ?_
  · calc Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α g := hRle
      _ ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right (le_max_left Ce 0) (Work.Spaces.HkNorm_nonneg α 4 g)
  · intro r _ θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 :=
      Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.abs_K_le_three_aux θ
    have hA0 : 0 ≤ |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ| := abs_nonneg _
    have hg0 : 0 ≤ |g r θ| := abs_nonneg _
    have habs : |Work.Spaces.K θ * (2 * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)
          r θ * g r θ)|
        = 2 * (|Work.Spaces.K θ|
            * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ| * |g r θ|) := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    simp only [Work.FTS.Nonlin.N1gg]
    rw [habs]
    calc 2 * (|Work.Spaces.K θ|
            * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ| * |g r θ|)
        ≤ 2 * (3 * |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ| * |g r θ|) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hA0) hg0
      _ = 6 * (|Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ| * |g r θ|) := by ring

/-- Row 2: `N₂^{gg} = -2𝒰(Φ̃_g)∂_θg`. -/
private theorem row2_gg {CA : ℝ} (hCA : 0 < CA) {α Ce : ℝ} (hα : 0 < α)
    {g Φg : Fn} (hgal : Work.FTS.Nonlin.GalClass α g)
    (hEll : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hsup : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ((Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ)) ^ 2
        ≤ CA / (Work.Spaces.gam α - 1)
          * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
              (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
                / Work.Construction.s2 θ) z θ') :
    Fa (Work.FTS.Nonlin.N2gg α g Φg) ≤ ENNReal.ofReal
      (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * 6
        * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
  obtain ⟨hUq, hUle⟩ := hEll.U
  have hsl : SlotData α (Work.Spaces.Dth g) (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 g)
      (Work.Spaces.HkSq α 4 g) :=
    slot1 hα.le hgal.reg.1 (Work.FTS.OpenPkg.galClass_HkMem4 hgal)
      (Work.FTS.Nonlinear.Pieces.rl1Pieces.aesm_slice_zero_Dth_of_axis
        (fun θ hθ => (hgal.axis θ hθ).1))
  refine rowGG_engine (CA := CA) (α := α) (Ce := Ce) (g := g)
    (A := fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
      / Work.Construction.s2 θ)
    (B₀ := Work.Spaces.Dth g)
    (Φ₀ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi1 g)
    (N := Work.FTS.Nonlin.N2gg α g Φg) (c := 6)
    hCA hα hUq.1 hUq.2 ?_ hsup hsl (fun r _ => rfl) (by norm_num) ?_
  · calc Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
          / Work.Construction.s2 θ)
        ≤ Ce * Work.FTS.Nonlin.Xn α g := hUle
      _ ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right (le_max_left Ce 0) (Work.Spaces.HkNorm_nonneg α 4 g)
  · intro r _ θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 :=
      Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.abs_K_le_three_aux θ
    have hA0 : 0 ≤ |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ
        / Work.Construction.s2 θ| := abs_nonneg _
    have hg0 : 0 ≤ |Work.Spaces.Dth g r θ| := abs_nonneg _
    have habs : |Work.Spaces.K θ * (-2 * ((Work.Construction.Uop α
          (Work.FTS.Nonlin.PhiTg α g Φg) r θ / Work.Construction.s2 θ)
            * Work.Spaces.Dth g r θ))|
        = 2 * |Work.Spaces.K θ|
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ
              / Work.Construction.s2 θ| * |Work.Spaces.Dth g r θ| := by
      simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    rw [n2gg_eq' α g Φg hθ, habs]
    calc 2 * |Work.Spaces.K θ|
          * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ
              / Work.Construction.s2 θ| * |Work.Spaces.Dth g r θ|
        ≤ 2 * 3 * |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ
              / Work.Construction.s2 θ| * |Work.Spaces.Dth g r θ| := by
          refine mul_le_mul_of_nonneg_right ?_ hg0
          refine mul_le_mul_of_nonneg_right ?_ hA0
          nlinarith [hK]
      _ = 6 * (|Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) r θ
              / Work.Construction.s2 θ| * |Work.Spaces.Dth g r θ|) := by ring

/-- Row 3: `N₃^{gg} = -2α𝒱(Φ̃_g)D_zg`. -/
private theorem row3_gg {CA : ℝ} (hCA : 0 < CA) {α Ce : ℝ} (hα : 0 < α)
    {g Φg : Fn} (hgal : Work.FTS.Nonlin.GalClass α g)
    (hEll : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hsup : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ) ^ 2
        ≤ CA / (Work.Spaces.gam α - 1)
          * ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4
              (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) z θ') :
    Fa (Work.FTS.Nonlin.N3gg α g Φg) ≤ ENNReal.ofReal
      (Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * (6 * α)
        * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2) := by
  obtain ⟨hVq, hVle⟩ := hEll.V
  have hsl : SlotData α (Work.Spaces.Dz g) (Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi2 g)
      (Work.Spaces.HkSq α 4 g) :=
    slot2 hgal.reg.1 (Work.FTS.OpenPkg.galClass_HkMem4 hgal)
  refine rowGG_engine (CA := CA) (α := α) (Ce := Ce) (g := g)
    (A := Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) (B₀ := Work.Spaces.Dz g)
    (Φ₀ := Work.FTS.Nonlinear.Pieces.rl1Pieces.Phi2 g)
    (N := Work.FTS.Nonlin.N3gg α g Φg) (c := 6 * α)
    hCA hα hVq.1 hVq.2 ?_ hsup hsl (fun r _ => rfl) (by positivity) ?_
  · calc Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg))
        ≤ Ce * Work.FTS.Nonlin.Xn α g := hVle
      _ ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right (le_max_left Ce 0) (Work.Spaces.HkNorm_nonneg α 4 g)
  · intro r _ θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 :=
      Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.abs_K_le_three_aux θ
    have hA0 : 0 ≤ |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ| := abs_nonneg _
    have hg0 : 0 ≤ |Work.Spaces.Dz g r θ| := abs_nonneg _
    have habs : |Work.Spaces.K θ * (-2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)
          r θ * Work.Spaces.Dz g r θ)|
        = 2 * α * |Work.Spaces.K θ|
            * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
            * |Work.Spaces.Dz g r θ| := by
      simp only [abs_mul, abs_neg, abs_of_nonneg hα.le, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    simp only [Work.FTS.Nonlin.N3gg]
    rw [habs]
    calc 2 * α * |Work.Spaces.K θ|
          * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ| * |Work.Spaces.Dz g r θ|
        ≤ 2 * α * 3 * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
            * |Work.Spaces.Dz g r θ| := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hA0) hg0
          nlinarith [hK, hα]
      _ = 6 * α * (|Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) r θ|
            * |Work.Spaces.Dz g r θ|) := by ring

/-! ## The assembly -/

theorem ggBounds {Ce : ℝ} : ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φg : Work.FTS.Galerkin.Fn},
    0 < α → α ≤ 1 → Work.FTS.Nonlin.GalClass α g → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
    Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1gg α g Φg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2gg α g Φg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3gg α g Φg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α g) := by
  obtain ⟨CA, hCA, hang⟩ := angSup_le
  refine ⟨6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * max Ce 0 + 1, ?_, ?_⟩
  · have h : 0 ≤ 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * max Ce 0 := by
      have := Real.sqrt_nonneg (Real.pi / 2)
      have := Real.sqrt_nonneg (10 * CA)
      have := le_max_right Ce 0
      positivity
    linarith
  intro α g Φg hα hα1 hgal hEll
  have hB0 : 0 ≤ max Ce 0 := le_max_right Ce 0
  -- the three row constants
  have hc12 : (2 : ℝ) ≤ 2 * max α 1 := by
    have := le_max_right α 1
    linarith
  have hc3 : 2 * α ≤ 2 * max α 1 := by
    have := le_max_left α 1
    linarith
  have hrc12 := rowConstLe' (α := α) (CA := CA) (B := max Ce 0) (c := 2) (g := g)
    hCA.le hB0 (by norm_num) hc12 hα hα1
  have hrc3 := rowConstLe' (α := α) (CA := CA) (B := max Ce 0) (c := 2 * α) (g := g)
    hCA.le hB0 (by positivity) hc3 hα hα1
  refine ⟨?_, ?_, ?_⟩
  · have h1 := row1_gg (CA := CA) hCA (α := α) (Ce := Ce) hα hgal hEll
      (fun z θ hz hθ0 hθ1 =>
        hang α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) hα hα1
          hEll.R.1.1 hEll.R.1.2 z θ hz hθ0 hθ1)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have heq : Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * 2
          * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2
        = Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * 6
          * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
    rw [← heq]
    exact hrc12
  · have h2 := row2_gg (CA := CA) hCA (α := α) (Ce := Ce) hα hgal hEll
      (fun z θ hz hθ0 hθ1 =>
        hang α (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ
            / Work.Construction.s2 θ) hα hα1 hEll.U.1.1 hEll.U.1.2 z θ hz hθ0 hθ1)
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    have heq : Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * 2
          * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2
        = Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * 6
          * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
    rw [← heq]
    exact hrc12
  · have h3 := row3_gg (CA := CA) hCA (α := α) (Ce := Ce) hα hgal hEll
      (fun z θ hz hθ0 hθ1 =>
        hang α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) hα hα1
          hEll.V.1.1 hEll.V.1.2 z θ hz hθ0 hθ1)
    refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
    have heq : Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * (2 * α)
          * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2
        = Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * (6 * α)
          * max Ce 0 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
    rw [← heq]
    exact hrc3

end

end Work.FTS.NonlinRows.Rl1
end
-- ===== merged: Submission.Work.FTS.PhiStar.RadialWAux.radPsi_contDiffOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped ContDiff Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadialWAux

/-- **Derivative-to-smoothness upgrade.**  If `f` has derivative `g` at every point of an open set
and `g` is `C^n` there, then `f` is `C^{n+1}` there. -/
theorem contDiffOn_succ_of_hasDerivAt_eq {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {n : ℕ}
    (hf : ∀ x ∈ s, HasDerivAt f (g x) x) (hg : ContDiffOn ℝ (n : ℕ∞ω) g s) :
    ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) f s := by
  have hsucc : ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 := by norm_num
  rw [hsucc, contDiffOn_succ_iff_deriv_of_isOpen hs]
  exact ⟨fun x hx => (hf x hx).differentiableAt.differentiableWithinAt,
    fun h => absurd h (by norm_num),
    hg.congr (fun x hx => (hf x hx).deriv)⟩

/-- **Derivative of a tail integral.**  If `k` is continuous on `(0,∞)` and integrable on every
tail `Ioi a` with `a > 0`, then `z ↦ ∫_{Ioi z} k` is differentiable at every `x > 0` with
derivative `-k x`. -/
theorem hasDerivAt_tailIntegral {k : ℝ → ℝ} (hk : ContinuousOn k (Ioi 0))
    (hint : ∀ a ∈ Ioi (0 : ℝ), IntegrableOn k (Ioi a) volume) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z => ∫ y in Ioi z, k y) (-(k x)) x := by
  obtain ⟨a, ha0, hax⟩ : ∃ a : ℝ, 0 < a ∧ a < x := ⟨x / 2, by linarith, by linarith⟩
  have hIa : IntegrableOn k (Ioi a) volume := hint a ha0
  have hsub : uIcc a x ⊆ Ioi (0 : ℝ) := by
    intro y hy
    have hy' : y ∈ Icc a x := by simpa [uIcc_of_le (le_of_lt hax)] using hy
    exact lt_of_lt_of_le ha0 hy'.1
  have hInt : IntervalIntegrable k volume a x := hk.mono hsub |>.intervalIntegrable
  have hsm : StronglyMeasurableAtFilter k (𝓝 x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun y hy => hk.continuousAt (isOpen_Ioi.mem_nhds hy)) x hx
  have hcx : ContinuousAt k x := hk.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hFTC : HasDerivAt (fun u => ∫ y in a..u, k y) (k x) x :=
    intervalIntegral.integral_hasDerivAt_right hInt hsm hcx
  refine (hFTC.const_sub (∫ y in Ioi a, k y)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hax] with u hu
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi hIa (le_of_lt hu)
  linarith [hsplit]

/-- **Smoothness of a tail integral.**  The tail integral of a `C^n` function which is integrable
on every tail `Ioi a` with `a > 0` is `C^{n+1}` on `(0,∞)`. -/
theorem contDiffOn_tailIntegral {k : ℝ → ℝ} {n : ℕ} (hk : ContDiffOn ℝ (n : ℕ∞ω) k (Ioi 0))
    (hint : ∀ a ∈ Ioi (0 : ℝ), IntegrableOn k (Ioi a) volume) :
    ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (fun z => ∫ y in Ioi z, k y) (Ioi 0) :=
  contDiffOn_succ_of_hasDerivAt_eq isOpen_Ioi
    (fun x hx => hasDerivAt_tailIntegral hk.continuousOn hint hx) hk.neg




/-- The `m = 0` instance of the rescaled identity. -/
theorem radPsi_zero_eq {α : ℝ} {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    radPsi α 0 c z = ∫ t in Ioi z, c t * t⁻¹ := by
  have hid := integral_Ioi_one_rpow c (-(radP α 0) - 1) (z := z) hz
  have h1 : radP α 0 = 0 := by simp [radP]
  have h2 : -(-(radP α 0) - 1 + 1) = 0 := by rw [h1]; norm_num
  rw [h2, Real.rpow_zero, one_mul] at hid
  have h3 : -(radP α 0) - 1 = -1 := by rw [h1]; norm_num
  simpa only [radPsi, h3, Real.rpow_neg_one] using hid



end Work.FTS.PhiStar.RadialWAux
end
end
