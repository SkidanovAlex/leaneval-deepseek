/-
# `FKgFacts` — the facts about the angular moment `FK g = ∫_θ K(θ) g(z,θ) dθ`

The datum is a perturbation `g` of the modulation class (`GalClass α g`, hence `RegQ α 6 g`
and `L₁₂ g 0 = 0`).  The norm-level interface `N4Norm.fkH` gives both halves of the *first*
two conjuncts: `FK g ∈ ℋ⁴` and `|FK g|_{ℋ⁴} ≤ Ci·|g|_{ℋ⁴}`.

The remaining two conjuncts of the first part, and the whole second part, are the statements
that for a **radial** datum `ρ` (`Rho z θ = ρ z`) the `ℋ⁴`-norm dominates the plain weighted
`L²`-norm and the weighted `L¹`-norm of `ρ`:

* `∫_{Ioi 0} ρ² w² ≤ HkSq α 4 Rho` and `∫_{Ioi 0} ρ² w ≤ HkSq α 4 Rho`;
* `∫_{Ioi 0} |ρ|/(1+z)² ≤ 2·HkNorm α 4 Rho`.

The first is pointwise for `z > 0`: `(ρ z)² w(z)² ≤ HkIntegrand α 4 Rho z θ` on the open
angular interval (the `i = 0` summand of `HkIntegrand` is `(ρ z·w(z)/sin(2θ)^{η/2})²` and
`sin(2θ)^{η/2} ≤ 1`), and the angular interval `[0,1]` — of measure exactly `1`, contained in
`Iθ` — already integrates that pointwise bound into the `z`-slice `Φ(z) = ∫_θ HkIntegrand`,
whose `z`-integral over `Iz` is `HkSq`.  The `L¹`-bound follows from Cauchy–Schwarz in `z`
against `z²/(1+z)⁴` (whose squared `L²`-norm is `1/105 ≪ 4`), the `L²`-function being the
square root of `Φ` (a.e. strongly measurable by hypothesis); that is `fk_radialL1_le` below
(a sibling `radialL1_le`, proved independently by a colleague from the same statement,
exists as well). -/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.BqSqIntegral

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

/-- `∫_{z>0} ρ² w² ≤ |Rho|²_{ℋ⁴}` for a radial function. -/
theorem radial_w_sq_le_HkSq {α : ℝ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 (fun z _ => ρ z)) :
    ∫ z in Set.Ioi (0 : ℝ), (ρ z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ Work.Spaces.HkSq α 4 (fun z _ => ρ z) := by
  have hle : (fun z => (ρ z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] Phi α 4 ρ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => radial_slot_le_Phi hmem hz)
  calc ∫ z in Set.Ioi (0 : ℝ), (ρ z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ ∫ z in Set.Ioi (0 : ℝ), Phi α 4 ρ z :=
        MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity)
          (Phi_integrable_Ioi hmem) hle
    _ = Work.Spaces.HkSq α 4 (fun z _ => ρ z) := Phi_integral_Ioi_eq_HkSq α 4 ρ

/-- `∫_{z>0} ρ² w ≤ |Rho|²_{ℋ⁴}` for a radial function (`w ≥ 1` on `(0,∞)`). -/
theorem radial_w_le_HkSq {α : ℝ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 (fun z _ => ρ z)) :
    ∫ z in Set.Ioi (0 : ℝ), (ρ z) ^ 2 * Work.Spaces.w z
      ≤ Work.Spaces.HkSq α 4 (fun z _ => ρ z) := by
  have hpt : ∀ z : ℝ, 0 < z → (ρ z) ^ 2 * Work.Spaces.w z ≤ Phi α 4 ρ z := by
    intro z hz
    have hw1 : (1 : ℝ) ≤ Work.Spaces.w z := Work.Elliptic.one_le_w hz
    have hwle : Work.Spaces.w z ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
    exact le_trans (mul_le_mul_of_nonneg_left hwle (sq_nonneg (ρ z)))
      (radial_slot_le_Phi hmem hz)
  have hle : (fun z => (ρ z) ^ 2 * Work.Spaces.w z)
      ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] Phi α 4 ρ :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => hpt z hz
  calc ∫ z in Set.Ioi (0 : ℝ), (ρ z) ^ 2 * Work.Spaces.w z
      ≤ ∫ z in Set.Ioi (0 : ℝ), Phi α 4 ρ z :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => by unfold Work.Spaces.w; positivity)
          (Phi_integrable_Ioi hmem) hle
    _ = Work.Spaces.HkSq α 4 (fun z _ => ρ z) := Phi_integral_Ioi_eq_HkSq α 4 ρ

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

theorem FKgFacts {α₂ Ci : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    (∀ {α : ℝ} {g : Work.FTS.Galerkin.Fn}, 0 < α → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)
        ≤ Ci * Work.FTS.Nonlin.Xn α g ∧
      (∫ z in Set.Ioi (0 : ℝ), (Work.Construction.FK g z) ^ 2 * Work.Spaces.w z
        ≤ Work.Spaces.HkSq α 4 (fun z _ => Work.Construction.FK g z)) ∧
      (∫ z in Set.Ioi (0 : ℝ), |Work.Construction.FK g z| / (1 + z) ^ 2
        ≤ 2 * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z))) ∧
    (∀ {α : ℝ} {ρ : ℝ → ℝ}, Work.Spaces.HkMem α 4 (fun z _ => ρ z) →
      ∫ z in Set.Ioi (0 : ℝ), (ρ z) ^ 2 * (Work.Spaces.w z) ^ 2
        ≤ Work.Spaces.HkSq α 4 (fun z _ => ρ z)) := by
  constructor
  · intro α g hα hαα₂ hgal
    obtain ⟨hmem, hbnd⟩ := hN.fkH α ⟨hα, hαα₂⟩ g
      (Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)) hgal.l12
    exact ⟨hmem, hbnd, radial_w_le_HkSq hmem, fk_radialL1_le hmem⟩
  · intro α ρ hmem
    exact radial_w_sq_le_HkSq hmem

end Work.FTS.Nonlinear.Pieces.rl1Tools
