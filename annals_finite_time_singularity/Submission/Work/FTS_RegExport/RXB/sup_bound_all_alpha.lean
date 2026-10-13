import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.SupPort.classC_sup_le
import Submission.Work.FTS.StrongEps.SupPort.ae_integrableOn_mixed_sq_w
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS_RegExport.RXB.SupGen.thetaHardyGen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXB.sup_bound_all_alpha`

The pointwise `L^∞`–`ℋ⁴` trade-off of Elgindi's Corollary `SecondDerivativesBounded` in its
**`α`-free** form: for every `α > 0` there is `C = C(α) > 0` with

  `f(z,θ)² ≤ C · |f|²_{ℋ⁴}`

for every `f` which is `C^∞` on the open quadrant (`SmoothOpen`), honestly in `ℋ⁴`
(`HkMem α 4`) and satisfies the boundary-trace vanishing `BdryTraces α 4`, at every point
`z > 0`, `0 < θ < π/2` of the open quadrant.

The available port of the Corollary to the open class
(`Work.FTS.StrongEps.SupPort.mixed_abs_le_of_smoothOpen`) is stated only for `α ≤ 1`, because
the two ingredients `HardyThetaOpen` and `sin_two_rpow` are (`sin_two_rpow` needs
`γ - 2 ≤ 0`).  Here the angular Hardy inequality is used in the form
`Work.FTS_RegExport.RXB.SupGen.thetaHardyGen`, which carries the *abstract* constant `K` in
place of `100/(γ-1)`; the concrete choice

  `K = max (100/(γ-1)) (π/2)`

is supplied by `sin_two_rpow_max` below (`∫_{Iθ} sin(2σ)^p ≤ π/2` for `p ≥ 0`, since `sin ≤ 1`
on `Iθ`; the constant `100/(p+1)` alone is false for large positive `p`).  With that, the
whole chain of `mixed_abs_le_of_smoothOpen` — `slotM_open` for the `(1,1)`-slot, the angular
Hardy inequality, the radial Hardy inequality `mixed_slice_hardyZ_open` and the identification
of the two weighted slots — goes through verbatim for an arbitrary `α > 0`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXB

set_option autoImplicit false

/-- **The weighted angular integral bound, for every `p > -1`.**
`∫_{Iθ} sin(2θ)^p dθ ≤ max (100/(p+1)) (π/2)`: for `p ≤ 0` this is
`Work.Spaces.sin_two_rpow`, and for `p ≥ 0` the integrand is bounded by `1` on the interval
`Iθ` of length `π/2`.  (The constant `100/(p+1)` alone is *false* for large positive `p`:
`∫_{Iθ} sin(2θ)^p ∼ c/√p` while `100/(p+1) ∼ 100/p`.) -/
theorem sin_two_rpow_max (p : ℝ) (hp : -1 < p) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p
        ≤ max (100 / (p + 1)) (Real.pi / 2) := by
  have hvol : MeasureTheory.volume Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  rcases lt_or_ge p 0 with hp0 | hp0
  · obtain ⟨hi, hv⟩ := Work.Spaces.sin_two_rpow p hp (le_of_lt hp0)
    exact ⟨hi, le_trans hv (le_max_left _ _)⟩
  · have hbdd : ∀ θ ∈ Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p ≤ 1 := fun θ hθ =>
      Real.rpow_le_one (Work.FTS.H2.sin_two_nonneg hθ) (Real.sin_le_one _) hp0
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (Measurable.pow_const
        (Real.measurable_sin.comp (measurable_const.mul measurable_id)) p).aestronglyMeasurable
    have hint : MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p)
        Work.Spaces.Iθ := by
      refine MeasureTheory.IntegrableOn.of_bound hvol hmeas 1 ?_
      filter_upwards [MeasureTheory.ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hθ) p)]
      exact hbdd θ hθ
    refine ⟨hint, ?_⟩
    have hone : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = Real.pi / 2 := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
        Work.Spaces.Iθ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p
        ≤ ∫ θ in Work.Spaces.Iθ, (1 : ℝ) :=
          MeasureTheory.setIntegral_mono_on hint
            (MeasureTheory.integrableOn_const (ne_of_lt hvol) (by simp)) measurableSet_Icc hbdd
      _ = Real.pi / 2 := hone
      _ ≤ max (100 / (p + 1)) (Real.pi / 2) := le_max_right _ _

/-- **The algebraic identity behind the angular Hardy inequality, in the interior.**
On `0 < θ < π/2` (where `sin(2θ) > 0`) the `∂_θ`-slot with the weight `sin(2θ)^{2-γ}` equals
the `D_θ`-slot with the weight `sin(2θ)^{-γ}`.  Unlike `Work.FTS.H2.pth_sq_mul_sin_eq` the
identity is asserted for *every* `α` (and only off the endpoints `θ = 0, π/2`, where the two
sides can genuinely differ when `γ = 2`). -/
theorem pth_sq_mul_sin_eq_Ioo (α : ℝ) (u : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.pth u z θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.Dth u z θ) ^ 2 := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.H2.sin_two_pos_of_mem_Ioo hθ
  have hD : Work.Spaces.Dth u z θ = Real.sin (2 * θ) * Work.Spaces.pth u z θ := rfl
  rw [hD, mul_pow, show 2 - Work.Spaces.gam α = 2 + (-(Work.Spaces.gam α)) by ring,
    Real.rpow_add hs, Real.rpow_two]
  ring

theorem sup_bound_all_alpha {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.Nonlin.BdryTraces α 4 f →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (f z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 4 f := by
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hπ : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hK0 : 0 ≤ max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2) :=
    le_trans hπ (le_max_right _ _)
  refine ⟨max (max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2)) 1,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro f hF hmem hbd z θ hz hθ0 hθ1
  -- the angular Hardy constant
  have hp1 : -1 < Work.Spaces.gam α - 2 := by rw [Work.Spaces.gam]; linarith
  obtain ⟨hSint, hSval₀⟩ := sin_two_rpow_max (Work.Spaces.gam α - 2) hp1
  have hSval : ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (Work.Spaces.gam α - 2)
      ≤ max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2) := by
    refine le_trans hSval₀ ?_
    rw [show Work.Spaces.gam α - 2 + 1 = Work.Spaces.gam α - 1 by ring]
  -- the `(1,1)`-slot of `HkSq`, in the `θ`-first form
  have hγne : Work.Spaces.gam α ≠ 0 := ne_of_gt (by linarith : 0 < Work.Spaces.gam α)
  obtain ⟨hTle, hTint, hTae⟩ :=
    Work.FTS.StrongEps.SupPort.slotM_open α f hF hmem 1 1 (by norm_num) (by norm_num)
  have hptslot : ∀ σ ∈ Work.Spaces.Iθ, ∀ z : ℝ,
      (Work.Spaces.mixed 1 1 f z σ * Work.Spaces.Wt α z σ) ^ 2
        = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * ((Work.Spaces.mixed 1 1 f z σ) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro σ hσ z
    rw [show Work.Spaces.Wt α z σ
        = Work.Spaces.w z * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α / 2)) from rfl,
      mul_pow, Work.FTS.H2.Wt_sq α hα z σ hσ]
    ring
  set B : ℝ → ℝ := fun σ => ∫ z in Work.Spaces.Iz,
    (Work.Spaces.mixed 1 1 f z σ) ^ 2 * (Work.Spaces.w z) ^ 2 with hBdef
  have hBae : (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      fun σ => ∫ z in Work.Spaces.Iz,
        (Work.Spaces.mixed 1 1 f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
    filter_upwards [hTae, MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with σ _ hσI
    rw [hBdef]
    have hstep : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (∫ z in Work.Spaces.Iz,
              (Work.Spaces.mixed 1 1 f z σ) ^ 2 * (Work.Spaces.w z) ^ 2)
        = ∫ z in Work.Spaces.Iz,
            (Work.Spaces.mixed 1 1 f z σ * Work.Spaces.Wt α z σ) ^ 2 := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ici fun z _ => (hptslot σ hσI z).symm
    exact hstep
  have hTint' : MeasureTheory.Integrable
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hTint.congr hBae.symm
  set T : ℝ := ∫ σ in Work.Spaces.Iθ,
    (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ with hTdef
  have hTle' : T ≤ Work.Spaces.HkSq α 4 f := by
    rw [hTdef]
    rw [show (∫ σ in Work.Spaces.Iθ,
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
        = ∫ σ in Work.Spaces.Iθ, ∫ z in Work.Spaces.Iz,
            (Work.Spaces.mixed 1 1 f z σ * Work.Spaces.Wt α z σ) ^ 2
        from integral_congr_ae hBae]
    exact hTle
  -- the angular vanishing at `θ = 0⁺`, from the boundary traces
  have hlim0 : Tendsto (fun θ' => f z θ') (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := (hbd 0 0 (by norm_num)).2 z (Set.mem_Ioi.mpr hz)
    exact Work.FTS.H2.tendsto_nhdsGT_zero_of_traces α hα (by simpa using h.1)
  -- the angular integrability of the `∂_θ`-slot
  have hint_ang : MeasureTheory.IntegrableOn (fun σ => (Work.Spaces.pth f z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    Work.FTS.TransportS.T2SupB2.integrableOn_pth_sq_rpow hF hmem 0 0 (by norm_num) hz
  -- the angular Hardy inequality
  have hHT : ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2), (f z θ') ^ 2
      ≤ max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2)
        * ∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth f z σ) ^ 2
            * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α) :=
    SupGen.thetaHardyGen hα (max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2)) hK0 f z
      hF hz hlim0 hint_ang hSint hSval
  -- the `D_θ`-slot with the weight `sin^{-γ}` is integrable
  have hDth_int2 : MeasureTheory.IntegrableOn
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.Dth f z σ) ^ 2) Work.Spaces.Iθ := by
    have h1 : MeasureTheory.Integrable (fun σ => (Work.Spaces.pth f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hint_ang
    refine h1.congr ?_
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => ?_)
    exact pth_sq_mul_sin_eq_Ioo α f hσ
  have hI1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.Dth f z σ) ^ 2 :=
    Work.FTS.EllipticEst.setIntegral_Iθ_congr_of_forall_Ioo
      (fun σ hσ => pth_sq_mul_sin_eq_Ioo α f hσ)
  -- the radial Hardy inequality at a.e. angle
  have hrad : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.Dth f z σ) ^ 2
        ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ := by
    filter_upwards [hTae, MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with σ hσint hσI
    rcases eq_or_lt_of_le hσI.1 with hσeq | hσpos
    · have hsin0 : Real.sin (2 * σ) = 0 := by rw [← hσeq]; simp
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hsin0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    rcases eq_or_lt_of_le hσI.2 with hσeq | hσlt
    · have hsin0 : Real.sin (2 * σ) = 0 := by
        rw [hσeq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hsin0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    · have hσ' : σ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hσpos, hσlt⟩
      have hDth_eq : Work.Spaces.Dth f z σ = Work.Spaces.mixed 0 1 f z σ :=
        Work.FTS.StrongEps.SupPort.Dth_mixed_open hF 0 0 hz hσ'
      rw [hDth_eq]
      exact mul_le_mul_of_nonneg_left
        (Work.FTS.StrongEps.SupPort.mixed_slice_hardyZ_open α f hF hbd 0 1 (by norm_num)
          hσ' hσint z (Set.mem_Ioi.mpr hz))
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσI) _)
  have hIntLe : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) ≤ T := by
    rw [hI1, hTdef]
    exact integral_mono_ae hDth_int2 hTint' hrad
  have hfin : (f z θ) ^ 2 ≤ max (100 / (Work.Spaces.gam α - 1)) (Real.pi / 2) * T :=
    le_trans (hHT θ ⟨hθ0, hθ1⟩) (mul_le_mul_of_nonneg_left hIntLe hK0)
  exact le_trans (le_trans hfin (mul_le_mul_of_nonneg_left hTle' hK0))
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Work.Spaces.HkSq_nonneg α 4 f))

end Work.FTS_RegExport.RXB
