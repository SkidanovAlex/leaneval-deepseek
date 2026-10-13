/-
# `FKradialL1` — the weighted radial `L¹`-bound for the angular moment `FK g`

`Work.Construction.FK g z = ∫_θ K(θ) g(z,θ) dθ` is the angular moment of the perturbation `g`
(row 20 of the table of design §3.4).  The target states that its *plain* weighted radial
`L¹`-norm is controlled by the `ℋ⁴`-norm of `g` itself:

`∫_{z>0} |FK g z|/(1+z)² ≤ 2·Ci·|g|_{ℋ⁴}`,

together with the integrability of that radial function.

The proof has three ingredients.

* `N4Norm.fkH` gives `FK g ∈ ℋ⁴` and `|FK g|_{ℋ⁴} ≤ Ci·|g|_{ℋ⁴}`
  (`Work.FTS.Nonlinear.Pieces.rl1Tools.FKgFacts`).
* `fk_radialL1_le` (same file) turns `FK g ∈ ℋ⁴` into the weighted `L¹`-bound
  `∫ |FK g z|/(1+z)² ≤ 2·|FK g|_{ℋ⁴}`, via Cauchy–Schwarz in `z`.
* The *integrability* of `z ↦ |FK g z|/(1+z)²`, which is not part of the second ingredient, is
  obtained here: the `ℋ⁴`-slice integral `Φ z = ∫_θ HkIntegrand α 4 (FK g) z θ` dominates
  `(|FK g z|·w z)²` (`radial_slot_le_Phi`), so

  `|FK g z|/(1+z)² = (|FK g z|·w z)·(z²/(1+z)⁴) ≤ √(Φ z)·(z²/(1+z)⁴)`

  where `√Φ ∈ L²` (because `Φ` is integrable, the second half of `HkMem`) and
  `z²/(1+z)⁴ ∈ L²` (`BqSqIntegral`), so the right-hand side is integrable
  (`Integrable.mono'`).  This only needs the *almost everywhere* strong measurability of
  `z ↦ |FK g z|/(1+z)²`, which is supplied by `FK_aesm_of_cont` below from the joint
  continuity of `g` on the open quadrant (`SmoothQuad g`, part of `GalClass`).
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FKgFacts
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.LintEngine
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

/-! ## Measurability of the angular moment -/

/-- The angular moment `FK g z = ∫_θ K(θ) g(z,θ) dθ` is a.e. strongly measurable in `z` on
`(0,∞)` as soon as `g` is continuous on the open quadrant: the uncurried integrand
`(z,θ) ↦ g z θ·K θ` is then a.e. strongly measurable for the product of the restrictions
(`Work.Spaces.aesm_of_continuousOn_Qd`), and `AEStronglyMeasurable.integral_prod_right'`
integrates it in `θ`. -/
theorem FK_aesm_of_cont {g : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry g)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable (fun z => Work.Construction.FK g z)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hK : Continuous fun θ : ℝ => Work.Spaces.K θ := by
    unfold Work.Spaces.K
    fun_prop
  have hjoint : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.1 p.2 * Work.Spaces.K p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (hcont.mul ((hK.comp continuous_snd).continuousOn))
  have h := hjoint.integral_prod_right'
  have hrestrict : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact Measure.restrict_congr_set (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))
  rw [hrestrict]
  simpa [Work.Construction.FK] using h

/-! ## The integrable majorant `√Φ · z²/(1+z)⁴` -/

/-- The majorant `z ↦ √(Φ z)·z²/(1+z)⁴` of `z ↦ |ρ z|/(1+z)²` is integrable on `(0,∞)` for a
radial function of class `ℋ⁴`: `√Φ ∈ L²` because `Φ` is integrable (`HkMem`), and
`z²/(1+z)⁴ ∈ L²`. -/
theorem radialL1_majorant_integrable {α : ℝ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 (fun z _ => ρ z)) :
    Integrable (fun z => Real.sqrt (Phi α 4 ρ z) * (z ^ 2 / (1 + z) ^ 4))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hΦi : IntegrableOn (Phi α 4 ρ) (Set.Ioi (0 : ℝ)) := Phi_integrable_Ioi hmem
  have hΦnn : ∀ z, 0 ≤ Phi α 4 ρ z := Phi_nonneg α 4 ρ
  have hAesm : AEStronglyMeasurable (fun z => Real.sqrt (Phi α 4 ρ z))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hΦi.aestronglyMeasurable
  have hAint : Integrable (fun z => Real.sqrt (Phi α 4 ρ z) ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hΦi.congr (Filter.Eventually.of_forall fun z => (Real.sq_sqrt (hΦnn z)).symm)
  have hAmem : MemLp (fun z => Real.sqrt (Phi α 4 ρ z)) 2
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (memLp_two_iff_integrable_sq hAesm).mpr hAint
  have hBmem : MemLp (fun z : ℝ => z ^ 2 / (1 + z) ^ 4) 2
      (volume.restrict (Set.Ioi (0 : ℝ))) := BqSqIntegral.1
  exact memLp_one_iff_integrable.mp (hAmem.mul hBmem)

/-- The pointwise domination `|ρ z|/(1+z)² ≤ √(Φ z)·z²/(1+z)⁴` for `z > 0`, the
`L¹`-functional being split as `(|ρ z|·w z)·(z²/(1+z)⁴)` with `w z = (1+z)²/z²`. -/
theorem radialL1_pointwise {α : ℝ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 (fun z _ => ρ z)) {z : ℝ} (hz : 0 < z) :
    |ρ z| / (1 + z) ^ 2 ≤ Real.sqrt (Phi α 4 ρ z) * (z ^ 2 / (1 + z) ^ 4) := by
  have hΦnn : 0 ≤ Phi α 4 ρ z := Phi_nonneg α 4 ρ z
  have hw0 : 0 ≤ Work.Spaces.w z := by unfold Work.Spaces.w; positivity
  have hsq : (|ρ z| * Work.Spaces.w z) ^ 2 ≤ Phi α 4 ρ z := by
    rw [mul_pow, sq_abs]
    exact radial_slot_le_Phi hmem hz
  have hle : |ρ z| * Work.Spaces.w z ≤ Real.sqrt (Phi α 4 ρ z) :=
    (Real.le_sqrt (mul_nonneg (abs_nonneg _) hw0) hΦnn).mpr hsq
  have hB0 : 0 ≤ z ^ 2 / (1 + z) ^ 4 := by positivity
  have hstep := mul_le_mul_of_nonneg_right hle hB0
  have hid : |ρ z| / (1 + z) ^ 2 = |ρ z| * Work.Spaces.w z * (z ^ 2 / (1 + z) ^ 4) := by
    unfold Work.Spaces.w
    field_simp
  rw [hid]
  exact hstep

/-- **Integrability of the weighted radial `L¹`-functional** of a radial `ℋ⁴`-function which is
a.e. strongly measurable: domination by the integrable majorant `√Φ·z²/(1+z)⁴`. -/
theorem radialL1_integrableOn {α : ℝ} {ρ : ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 4 (fun z _ => ρ z))
    (hρ : AEStronglyMeasurable (fun z => |ρ z| / (1 + z) ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ)))) :
    IntegrableOn (fun z => |ρ z| / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) := by
  refine Integrable.mono' (radialL1_majorant_integrable hmem) hρ ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (by positivity))]
  exact radialL1_pointwise hmem hz

/-! ## The target -/

theorem FKradialL1 {α₂ Ci : ℝ} (hN : Work.FTS.Nonlin.N4Norm Ci α₂) :
    ∀ {α : ℝ} {g : Work.FTS.Galerkin.Fn}, 0 < α → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      MeasureTheory.IntegrableOn (fun z => |Work.Construction.FK g z| / (1 + z) ^ 2)
        (Set.Ioi (0 : ℝ)) ∧
      (∫ z in Set.Ioi (0 : ℝ), |Work.Construction.FK g z| / (1 + z) ^ 2)
        ≤ 2 * Ci * Work.FTS.Nonlin.Xn α g := by
  intro α g hα hαα₂ hgal
  -- `GalClass α g` is an `ℋ⁶`-class, hence an `ℋ⁴`-class, with vanishing zero mode of `L₁₂`.
  have hreg : Work.FTS.Nonlin.RegQ α 4 g :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hgal.reg (by norm_num)
  obtain ⟨hmem, hbnd⟩ := hN.fkH α ⟨hα, hαα₂⟩ g hreg hgal.l12
  -- `g` is `C^∞` on the open quadrant, so `FK g` is a.e. strongly measurable.
  have hcont : ContinuousOn (Function.uncurry g)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hgal.reg.1.continuousOn.mono (by
      intro p hp
      simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hp ⊢
      exact ⟨by linarith [hp.1], hp.2⟩)
  have haesm : AEStronglyMeasurable (fun z => Work.Construction.FK g z)
      (volume.restrict (Set.Ioi (0 : ℝ))) := FK_aesm_of_cont hcont
  have haesm2 : AEStronglyMeasurable
      (fun z => |Work.Construction.FK g z| / (1 + z) ^ 2)
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    haesm.norm.mul (by fun_prop)
  refine ⟨radialL1_integrableOn hmem haesm2, ?_⟩
  have h1 : (∫ z in Set.Ioi (0 : ℝ), |Work.Construction.FK g z| / (1 + z) ^ 2)
      ≤ 2 * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z) :=
    fk_radialL1_le hmem
  have h2 : 2 * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)
      ≤ 2 * Ci * Work.FTS.Nonlin.Xn α g := by linarith [hbnd]
  exact le_trans h1 h2

end Work.FTS.Nonlinear.Pieces.rl1Tools
