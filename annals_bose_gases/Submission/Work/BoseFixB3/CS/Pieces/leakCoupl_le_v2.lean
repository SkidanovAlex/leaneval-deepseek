import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.CS.LeakCouplGen
import Submission.Work.BoseFixB3.CS.Pieces.acube_setIntegral_iter_swap
import Submission.Work.BoseFixB3.CS.Pieces.integrable_leakCoupl_integrand
import Submission.Work.BoseFixB3.CS.Quant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.leakCoupl_le_v2`

The **leakage coupling** of the `CS` step of the `B3` chapter, at an arbitrary order `N`:

    |leakCoupl fc κ ℓ (omC w₀) (wLoc ℓ g₀ 0)| ≤ C·(ℓκ)^{-N}·ℓ³ ,

with `C` depending only on `v`, `R`, `h`, `N` — uniformly in the cut-off `fc : LowCut` and in
`κ, ℓ > 0` in the dilute regime `R ≤ ℓ·chiR0`.  Here `w₀ := Classical.choose h` is a scattering
solution of the nonnegative radial potential `v` (supported in `ball 0 R`) and `g₀ := g0 v h`.

## Route

Unfolding `leakCoupl`, `omC`, `wLoc` the coupling is

    ∫_{Λ} ∫_{Λ} χ_Λ(a)·F(a−b)·χ_Λ(b)·leak(b) ,      F := w₀·(g₀ / C_ℓ) ,  C_ℓ := convScale ℓ ,

so it is the core coupling `LeakCouplGen.leakCoupl_core_gen` (which gives `(ℓκ)^{-N}` with no
`R/ℓ` residual) once the order of the two box integrals is exchanged.  The exchange is done with
`Pieces.acube_setIntegral_iter_swap`, joint integrability being supplied by
`Pieces.integrable_leakCoupl_integrand`; the `b`-carried leakage factor is then pulled out of the
inner (`a`)-integral by `integral_mul_const`.

The only inputs on the weight are

* `convScale ℓ ≥ 1/2` on `ball 0 R` — this is where the regime hypothesis `R ≤ ℓ·chiR0` enters
  (`Submission.BoseGases.convScale_ge_half_ball`), and it gives the *`ℓ`-independent* bound
  `‖F z‖ ≤ 2‖g₀ z·w₀ z‖`;
* `w₀·g₀ ∈ L¹` (`Submission.BoseGases.g0w0_integrable`, hence `hv`, `hvrad` are used).

Hence `F ∈ L¹` with `∫‖F‖ ≤ 2∫‖w₀g₀‖`, a constant independent of `fc, κ, ℓ`, and the claimed `C`
is `C_core · 2∫‖w₀g₀‖`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.CS.Pieces

set_option maxHeartbeats 1000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem leakCoupl_le_v2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (hκ : 0 < κ) (hℓ : 0 < ℓ)
      (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0),
      |Work.BoseFixB3.CS.leakCoupl fc κ ℓ (Submission.BoseGases.omC (Classical.choose h))
          (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0)|
        ≤ C * (ℓ * κ) ^ (-(N : ℝ)) * ℓ ^ 3 := by
  obtain ⟨C_core, hC_core0, hC_core⟩ := Work.BoseFixB3.CS.LeakCouplGen.leakCoupl_core_gen N hN
  set w0 : E3 → ℝ := Classical.choose h with hw0
  set g : E3 → ℝ := Submission.BoseGases.g0 v h with hg
  -- the weight `w₀·g₀` is integrable, which is the only use of `hv`, `hvrad` and `hR`
  have hgw_int : MeasureTheory.Integrable (fun z : E3 => g z * w0 z) := by
    rw [hg, hw0]
    exact Submission.BoseGases.g0w0_integrable hR hv hvrad hv_supp h
  -- `g₀` (hence the weight) vanishes outside `ball 0 R`
  have hg_zero : ∀ z : E3, R ≤ ‖z‖ → g z = 0 := by
    intro z hz
    rw [hg]
    exact Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hI0 : 0 ≤ ∫ z : E3, ‖g z * w0 z‖ := MeasureTheory.integral_nonneg (fun z => norm_nonneg _)
  refine ⟨C_core * (2 * ∫ z : E3, ‖g z * w0 z‖), mul_nonneg hC_core0 (by positivity), ?_⟩
  intro fc κ ℓ hκ hℓ hRℓ
  set F : E3 → ℝ := fun z => w0 z * Submission.BoseGases.wScaled ℓ g z with hF
  -- `convScale ℓ ≥ 1/2` on `ball 0 R`, from the dilute-regime hypothesis
  have hcs : ∀ z : E3, ‖z‖ ≤ R → (1 / 2 : ℝ) ≤ Submission.BoseGases.convScale ℓ z :=
    fun z hz => Submission.BoseGases.convScale_ge_half_ball hℓ hR.le hRℓ hz
  -- the `ℓ`-independent pointwise bound on the weight
  have hF_le : ∀ z : E3, ‖F z‖ ≤ 2 * ‖g z * w0 z‖ := by
    intro z
    by_cases hz : ‖z‖ ≤ R
    · have hcsz : (1 / 2 : ℝ) ≤ Submission.BoseGases.convScale ℓ z := hcs z hz
      have hcspos : 0 < Submission.BoseGases.convScale ℓ z := lt_of_lt_of_le (by norm_num) hcsz
      have h1 : ‖F z‖ = ‖w0 z‖ * (‖g z‖ / Submission.BoseGases.convScale ℓ z) := by
        rw [hF]
        simp only [Submission.BoseGases.wScaled]
        rw [norm_mul, norm_div, Real.norm_of_nonneg (le_of_lt hcspos)]
      rw [h1]
      have hquot : ‖g z‖ / Submission.BoseGases.convScale ℓ z ≤ 2 * ‖g z‖ := by
        rw [div_le_iff₀ hcspos]
        nlinarith [norm_nonneg (g z), hcsz]
      calc ‖w0 z‖ * (‖g z‖ / Submission.BoseGases.convScale ℓ z)
          ≤ ‖w0 z‖ * (2 * ‖g z‖) := mul_le_mul_of_nonneg_left hquot (norm_nonneg _)
        _ = 2 * ‖g z * w0 z‖ := by rw [norm_mul]; ring
    · have hzR : R ≤ ‖z‖ := le_of_lt (lt_of_not_ge hz)
      rw [hF]
      simp only [Submission.BoseGases.wScaled, hg_zero z hzR]
      simp
  have hF_meas : AEStronglyMeasurable F volume := by
    have h2 : AEStronglyMeasurable (fun z : E3 => (Submission.BoseGases.convScale ℓ z)⁻¹) volume :=
      (Submission.BoseGases.convScale_continuous ℓ).measurable.inv.aestronglyMeasurable
    refine (hgw_int.aestronglyMeasurable.mul h2).congr ?_
    filter_upwards with z
    simp only [Pi.mul_apply, hF, Submission.BoseGases.wScaled]
    ring
  have hF_int : MeasureTheory.Integrable F :=
    (hgw_int.norm.const_mul 2).mono' hF_meas (Filter.Eventually.of_forall hF_le)
  have hF_zero : ∀ z : E3, R ≤ ‖z‖ → F z = 0 := by
    intro z hz
    simp only [hF, Submission.BoseGases.wScaled, hg_zero z hz]
    simp
  -- joint integrability of the coupling integrand, and the exchange of the two box integrals
  have hGint : MeasureTheory.Integrable
      (Function.uncurry (fun a b : E3 => Submission.BoseGases.chiU ℓ 0 a * F (a - b) *
        Submission.BoseGases.chiU ℓ 0 b * Work.BoseFixB3.CS.leakFn fc κ ℓ b))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    Work.BoseFixB3.CS.Pieces.integrable_leakCoupl_integrand fc hκ hℓ hF_int
  have hswap := Work.BoseFixB3.CS.Pieces.acube_setIntegral_iter_swap ℓ
    (fun a b : E3 => Submission.BoseGases.chiU ℓ 0 a * F (a - b) *
      Submission.BoseGases.chiU ℓ 0 b * Work.BoseFixB3.CS.leakFn fc κ ℓ b) hGint
  -- the `b`-carried leakage factor comes out of the inner integral
  have hpull : (∫ b in Submission.BoseGases.acube ℓ, ∫ a in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.chiU ℓ 0 a * F (a - b) * Submission.BoseGases.chiU ℓ 0 b *
          Work.BoseFixB3.CS.leakFn fc κ ℓ b)
      = ∫ b in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ b *
          (∫ a in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.chiU ℓ 0 a * F (a - b) * Submission.BoseGases.chiU ℓ 0 b) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with b
    rw [MeasureTheory.integral_mul_const]
    ring
  -- the coupling in the shape of the core estimate
  have hcongr : Work.BoseFixB3.CS.leakCoupl fc κ ℓ (Submission.BoseGases.omC w0)
        (Submission.BoseGases.wLoc ℓ g 0)
      = ∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.chiU ℓ 0 a * F (a - b) * Submission.BoseGases.chiU ℓ 0 b *
            Work.BoseFixB3.CS.leakFn fc κ ℓ b := by
    simp only [Work.BoseFixB3.CS.leakCoupl, Submission.BoseGases.omC,
      Submission.BoseGases.wLoc, hF]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with a
    apply MeasureTheory.integral_congr_ae
    filter_upwards with b
    ring
  have hcore := hC_core fc κ ℓ R hκ hℓ hR hRℓ F hF_int hF_zero
  have hint_le : (∫ z : E3, ‖F z‖) ≤ 2 * ∫ z : E3, ‖g z * w0 z‖ := by
    calc (∫ z : E3, ‖F z‖) ≤ ∫ z : E3, 2 * ‖g z * w0 z‖ :=
          MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
            (hgw_int.norm.const_mul 2) (Filter.Eventually.of_forall hF_le)
      _ = 2 * ∫ z : E3, ‖g z * w0 z‖ := by rw [MeasureTheory.integral_const_mul]
  calc |Work.BoseFixB3.CS.leakCoupl fc κ ℓ (Submission.BoseGases.omC w0)
        (Submission.BoseGases.wLoc ℓ g 0)|
      = |∫ a in Submission.BoseGases.acube ℓ, ∫ b in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.chiU ℓ 0 a * F (a - b) * Submission.BoseGases.chiU ℓ 0 b *
            Work.BoseFixB3.CS.leakFn fc κ ℓ b| := by rw [hcongr]
    _ = |∫ b in Submission.BoseGases.acube ℓ, Work.BoseFixB3.CS.leakFn fc κ ℓ b *
          (∫ a in Submission.BoseGases.acube ℓ,
            Submission.BoseGases.chiU ℓ 0 a * F (a - b) * Submission.BoseGases.chiU ℓ 0 b)| := by
          rw [hswap, hpull]
    _ ≤ C_core * (ℓ * κ) ^ (-(N : ℝ)) * ℓ ^ 3 * ∫ z : E3, ‖F z‖ := hcore
    _ ≤ C_core * (ℓ * κ) ^ (-(N : ℝ)) * ℓ ^ 3 * (2 * ∫ z : E3, ‖g z * w0 z‖) := by
          refine mul_le_mul_of_nonneg_left hint_le ?_
          have h1 : 0 ≤ (ℓ * κ) ^ (-(N : ℝ)) := Real.rpow_nonneg (by positivity) _
          have h2 : 0 ≤ ℓ ^ 3 := by positivity
          positivity
    _ = (C_core * (2 * ∫ z : E3, ‖g z * w0 z‖)) * (ℓ * κ) ^ (-(N : ℝ)) * ℓ ^ 3 := by ring

end Work.BoseFixB3.CS.Pieces
