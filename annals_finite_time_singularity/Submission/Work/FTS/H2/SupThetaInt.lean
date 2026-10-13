import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.pth_integral
import Submission.Work.FTS.H2.SliceFacts
import Submission.Work.FTS.H2.T2SliceAux
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Small interface lemmas -/

/-- `mixed b 1 f = D_θ(D_z^b f) = sin(2θ)·∂_θ(D_z^b f)` on the closed quadrant. -/
theorem mixed_one_eq_sin_mul_pth {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (b : ℕ) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed b 1 f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  have hc : Work.Spaces.DthIter 1 (Work.Spaces.DzIter b f) z θ
      = Work.Spaces.DzIter b (Work.Spaces.DthIter 1 f) z θ := by
    have h := Work.Spaces.DthIter_DzIter_comm_eqOn hf b 1 hy
    simpa [Function.uncurry] using h
  show Work.Spaces.DzIter b (Work.Spaces.DthIter 1 f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.DzIter b f) z θ
  rw [← hc]
  rfl

/-- The angular slice of a function smooth on a neighbourhood of the closed quadrant is
smooth on `(-1, π/2 + 1)`. -/
theorem contDiffOn_theta_slice {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g)
    {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    ContDiffOn ℝ ⊤ (fun θ => g z θ) (Set.Ioo (-1) (π / 2 + 1)) := by
  have hz1 : (-1 : ℝ) < z := by
    simp only [Work.Spaces.Iz, Set.mem_Ici] at hz
    linarith
  have hp : ContDiffOn ℝ ⊤ (fun θ : ℝ => (z, θ)) (Set.Ioo (-1) (π / 2 + 1)) :=
    contDiffOn_const.prodMk contDiffOn_id
  have h := hg.comp hp (fun θ hθ => ⟨hz1, hθ⟩)
  simpa [Function.comp_def, Function.uncurry] using h

/-- The weight identity relating `∂_θ(D_z^b f)` and `D_z^bD_θ f`:
`(∂_θ D_z^b f)² w² sin(2θ)^{2-γ} = (D_z^b D_θ f · W)²` on the closed quadrant. -/
theorem pth_DzIter_weight_sq {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (b : ℕ) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 :=
  Work.Spaces.bt_mixed_weight_gen α z θ hα hα1 hθ
    (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) (Work.Spaces.mixed b 1 f z θ)
    (mixed_one_eq_sin_mul_pth hf b hz hθ)

/-- **Angular oscillation bound.**  For `1 < γ ≤ 2` and a `C¹` function `u` on a
neighbourhood of `Iθ` whose weighted derivative square is integrable on `Iθ`, the difference
of two values of `u` at points of `Iθ` is bounded by the weighted `L²`-norm of `u'` with the
sharp weight `sin(2θ)^{2-γ}` and the constant `100/(γ-1)`:

`(u b - u a)² ≤ (100/(γ-1)) ∫_{Iθ} (u')² sin(2θ)^{2-γ}`.

This is the Cauchy–Schwarz/mean-value content of Elgindi's Lemma `infinity_separated` on the
angular interval: by the fundamental theorem of calculus `u b - u a = ∫_a^b u'`, and splitting
`u' = (u' sin^{(2-γ)/2}) · sin^{(γ-2)/2}` on the open interval `(a,b) ⊆ (0,π/2)` (where
`sin(2·) > 0`, so that the two weights multiply to `1`) Cauchy–Schwarz in `L²` gives the
product of `∫_{(a,b)} (u')² sin^{2-γ}` and `∫_{(a,b)} sin^{γ-2}`, the second factor being
bounded by `100/(γ-1)` (`Work.Spaces.sin_two_rpow`). -/
theorem slice_osc_le {γ : ℝ} (hγ1 : 1 < γ) (hγ2 : γ ≤ 2) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hintp : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ) :
    ∀ a ∈ Work.Spaces.Iθ, ∀ b ∈ Work.Spaces.Iθ, a ≤ b →
      (u b - u a) ^ 2 ≤ (100 / (γ - 1)) * ∫ s in Work.Spaces.Iθ,
        (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by
  intro a ha b hb hab
  have hp1 : -1 < γ - 2 := by linarith
  have hp0 : γ - 2 ≤ 0 := by linarith
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIoo_meas : MeasurableSet (Set.Ioo a b) := measurableSet_Ioo
  have hsin_nonneg : ∀ s ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * s) :=
    fun s hs => Work.Spaces.bt_sin_nonneg hs
  have hsub_Iθ : Set.Ioo a b ⊆ Work.Spaces.Iθ := by
    intro s hs
    exact ⟨by linarith [ha.1, hs.1], by linarith [hb.2, hs.2]⟩
  have hsin_pos : ∀ s ∈ Set.Ioo a b, 0 < Real.sin (2 * s) := by
    intro s hs
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [ha.1, hs.1]) ?_
    linarith [hb.2, hs.2, Real.pi_pos]
  have hJint : MeasureTheory.IntegrableOn
      (fun s => (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ)) (Set.Ioo a b) :=
    hintp.mono_set hsub_Iθ
  -- the fundamental theorem of calculus on `[a,b]`
  have hsub_box : Set.Icc a b ⊆ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
    intro s hs
    exact ⟨by linarith [ha.1, hs.1], by linarith [hb.2, hs.2, Real.pi_pos]⟩
  have hderiv_cont_Icc : ContinuousOn (deriv u) (Set.Icc a b) :=
    (hu.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub_box
  have hFTC : ∫ s in a..b, deriv u s = u b - u a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      (hu.continuousOn.mono hsub_box) ?_ ?_
    · intro x hx
      exact ((hu.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_Ioo.mem_nhds (hsub_box ⟨hx.1.le, hx.2.le⟩))).hasDerivAt
    · have h : ContinuousOn (deriv u) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab]
        exact hderiv_cont_Icc
      exact h.intervalIntegrable
  -- the Cauchy–Schwarz step on the open interval
  have hCS : (∫ s in Set.Ioo a b, deriv u s) ^ 2
      ≤ (∫ s in Set.Ioo a b, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ))
        * (∫ s in Set.Ioo a b, (Real.sin (2 * s)) ^ (γ - 2)) := by
    have hXaesm : AEStronglyMeasurable
        (fun s => deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2))
        (MeasureTheory.volume.restrict (Set.Ioo a b)) := by
      have hdu : ContinuousOn (deriv u) (Set.Ioo a b) :=
        hderiv_cont_Icc.mono Set.Ioo_subset_Icc_self
      have hsinX : ContinuousOn (fun s => (Real.sin (2 * s)) ^ ((2 - γ) / 2))
          (Set.Ioo a b) :=
        ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
          (fun s hs => Or.inl (ne_of_gt (hsin_pos s hs)))
      exact (hdu.mul hsinX).aestronglyMeasurable hIoo_meas
    have hXsq_key : ∀ s ∈ Set.Ioo a b,
        (deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2)) ^ 2
          = (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by
      intro s hs
      rw [mul_pow]
      congr 1
      rw [pow_two, ← Real.rpow_add (hsin_pos s hs),
        show (2 - γ) / 2 + (2 - γ) / 2 = 2 - γ by ring]
    have hXsq : MeasureTheory.IntegrableOn
        (fun s => (deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2)) ^ 2) (Set.Ioo a b) :=
      hJint.congr_fun (fun s hs => (hXsq_key s hs).symm) hIoo_meas
    have hu1 : MemLp (fun s => deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2)) 2
        (MeasureTheory.volume.restrict (Set.Ioo a b)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq hXaesm).mpr hXsq
    have hYaesm : AEStronglyMeasurable
        (fun s => (Real.sin (2 * s)) ^ ((γ - 2) / 2))
        (MeasureTheory.volume.restrict (Set.Ioo a b)) :=
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun s hs => Or.inl (ne_of_gt (hsin_pos s hs)))).aestronglyMeasurable hIoo_meas
    have hYsq : MeasureTheory.IntegrableOn
        (fun s => ((Real.sin (2 * s)) ^ ((γ - 2) / 2)) ^ 2) (Set.Ioo a b) :=
      ((Work.Spaces.sin_two_rpow (γ - 2) hp1 hp0).1.mono_set hsub_Iθ).congr_fun (fun s hs => by
        rw [pow_two, ← Real.rpow_add (hsin_pos s hs),
          show (γ - 2) / 2 + (γ - 2) / 2 = γ - 2 by ring]) hIoo_meas
    have hu2 : MemLp (fun s => (Real.sin (2 * s)) ^ ((γ - 2) / 2)) 2
        (MeasureTheory.volume.restrict (Set.Ioo a b)) :=
      (MeasureTheory.memLp_two_iff_integrable_sq hYaesm).mpr hYsq
    have hcs := Work.Spaces.cs_integral hu1 hu2
    have e1 : (∫ s in Set.Ioo a b, (deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2))
          * (Real.sin (2 * s)) ^ ((γ - 2) / 2))
        = ∫ s in Set.Ioo a b, deriv u s := by
      refine MeasureTheory.setIntegral_congr_fun hIoo_meas (fun s hs => ?_)
      rw [mul_assoc, ← Real.rpow_add (hsin_pos s hs),
        show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring, Real.rpow_zero, mul_one]
    have e2 : (∫ s in Set.Ioo a b, (deriv u s * (Real.sin (2 * s)) ^ ((2 - γ) / 2)) ^ 2)
        = ∫ s in Set.Ioo a b, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) :=
      MeasureTheory.setIntegral_congr_fun hIoo_meas hXsq_key
    have e3 : (∫ s in Set.Ioo a b, ((Real.sin (2 * s)) ^ ((γ - 2) / 2)) ^ 2)
        = ∫ s in Set.Ioo a b, (Real.sin (2 * s)) ^ (γ - 2) := by
      refine MeasureTheory.setIntegral_congr_fun hIoo_meas (fun s hs => ?_)
      rw [pow_two, ← Real.rpow_add (hsin_pos s hs),
        show (γ - 2) / 2 + (γ - 2) / 2 = γ - 2 by ring]
    rw [e1, e2, e3] at hcs
    exact hcs
  -- the two factors are bounded by the `Iθ`-integrals
  have hA2 : (∫ s in Set.Ioo a b, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ))
      ≤ ∫ s in Work.Spaces.Iθ, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) :=
    MeasureTheory.setIntegral_mono_set hintp
      (MeasureTheory.ae_restrict_of_forall_mem hIθ_meas
        (fun s hs => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin_nonneg s hs) _)))
      (Filter.Eventually.of_forall (fun s hs => hsub_Iθ hs))
  have hB2 : (∫ s in Set.Ioo a b, (Real.sin (2 * s)) ^ (γ - 2)) ≤ 100 / (γ - 1) := by
    have h1 : (∫ s in Set.Ioo a b, (Real.sin (2 * s)) ^ (γ - 2))
        ≤ ∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (γ - 2) :=
      MeasureTheory.setIntegral_mono_set (Work.Spaces.sin_two_rpow (γ - 2) hp1 hp0).1
        (MeasureTheory.ae_restrict_of_forall_mem hIθ_meas
          (fun s hs => Real.rpow_nonneg (hsin_nonneg s hs) _))
        (Filter.Eventually.of_forall (fun s hs => hsub_Iθ hs))
    have h2 : (∫ s in Work.Spaces.Iθ, (Real.sin (2 * s)) ^ (γ - 2)) ≤ 100 / ((γ - 2) + 1) :=
      (Work.Spaces.sin_two_rpow (γ - 2) hp1 hp0).2
    have h3 : 100 / ((γ - 2) + 1) = 100 / (γ - 1) := by
      congr 1
      ring
    linarith [h1, h2, h3.le, h3.ge]
  have hIoo_nonneg : 0 ≤ ∫ s in Set.Ioo a b, (Real.sin (2 * s)) ^ (γ - 2) :=
    MeasureTheory.setIntegral_nonneg hIoo_meas
      (fun s hs => Real.rpow_nonneg (hsin_nonneg s (hsub_Iθ hs)) _)
  have hIθ_nonneg : 0 ≤ ∫ s in Work.Spaces.Iθ, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun s hs => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin_nonneg s hs) _))
  have hbridge : ∫ s in a..b, deriv u s = ∫ s in Set.Ioo a b, deriv u s := by
    rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc (u b - u a) ^ 2 = (∫ s in a..b, deriv u s) ^ 2 := by rw [hFTC]
    _ = (∫ s in Set.Ioo a b, deriv u s) ^ 2 := by rw [hbridge]
    _ ≤ (∫ s in Set.Ioo a b, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ))
          * (∫ s in Set.Ioo a b, (Real.sin (2 * s)) ^ (γ - 2)) := hCS
    _ ≤ (∫ s in Work.Spaces.Iθ, (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ))
          * (100 / (γ - 1)) := mul_le_mul hA2 hB2 hIoo_nonneg hIθ_nonneg
    _ = (100 / (γ - 1)) * (∫ s in Work.Spaces.Iθ,
          (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ)) := by ring

/-- **Angular Hardy inequality with mean-value base point.**  For `1 < γ ≤ 2` and `u` of
class `C¹` on a neighbourhood of `Iθ` with `u²` and `(u')² sin(2θ)^{2-γ}` integrable on `Iθ`,
every `θ ∈ Iθ` satisfies

`u(θ)² ≤ (4/π) ∫_{Iθ} u² + (200/(γ-1)) ∫_{Iθ} (u')² sin(2θ)^{2-γ}`.

Proof: `MeasureTheory.exists_le_setAverage` supplies `θ₀ ∈ Iθ` whose value is below the mean
`⨍_{Iθ} u² = (2/π)∫_{Iθ} u²`; writing `u(θ)² ≤ 2u(θ₀)² + 2(u(θ)-u(θ₀))²` and bounding the
oscillation by `slice_osc_le` (with `(a,b) = (θ₀,θ)` or `(θ,θ₀)`) gives the claim. -/
theorem slice_sup_sq_le {γ : ℝ} (hγ1 : 1 < γ) (hγ2 : γ ≤ 2) {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 1 u (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (hint2 : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ)
    (hintp : MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ) :
    ∀ θ ∈ Work.Spaces.Iθ, (u θ) ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      + (200 / (γ - 1)) * ∫ θ in Work.Spaces.Iθ,
          (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ) := by
  intro θ hθ
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hvol : MeasureTheory.volume.real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.measureReal_def, show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hIθ_ne_zero : MeasureTheory.volume Work.Spaces.Iθ ≠ 0 := by
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl, Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])).ne'
  have hIθ_ne_top : MeasureTheory.volume Work.Spaces.Iθ ≠ ⊤ := by
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  obtain ⟨θ₀, hθ₀_mem, hθ₀_le⟩ :=
    MeasureTheory.exists_le_setAverage (s := Work.Spaces.Iθ) (f := fun a => (u a) ^ 2)
      hIθ_ne_zero hIθ_ne_top hint2
  have havg : ⨍ a in Work.Spaces.Iθ, (u a) ^ 2 ∂MeasureTheory.volume
      = (2 / Real.pi) * (∫ a in Work.Spaces.Iθ, (u a) ^ 2) := by
    rw [MeasureTheory.setAverage_eq, hvol, smul_eq_mul, inv_div]
  have h0 : (u θ₀) ^ 2 ≤ (2 / Real.pi) * (∫ a in Work.Spaces.Iθ, (u a) ^ 2) := by
    rw [← havg]
    exact hθ₀_le
  have hosc : (u θ - u θ₀) ^ 2 ≤ (100 / (γ - 1)) * ∫ s in Work.Spaces.Iθ,
      (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by
    rcases lt_trichotomy θ₀ θ with hlt | heq | hgt
    · exact slice_osc_le hγ1 hγ2 hu hintp θ₀ hθ₀_mem θ hθ hlt.le
    · subst heq
      have hC : 0 ≤ (100 / (γ - 1)) * ∫ s in Work.Spaces.Iθ,
          (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) :=
        mul_nonneg (by positivity)
          (MeasureTheory.setIntegral_nonneg hIθ_meas
            (fun s hs => mul_nonneg (sq_nonneg _)
              (Real.rpow_nonneg (Work.Spaces.bt_sin_nonneg hs) _)))
      simpa using hC
    · have h := slice_osc_le hγ1 hγ2 hu hintp θ hθ θ₀ hθ₀_mem hgt.le
      have h2 : (u θ - u θ₀) ^ 2 = (u θ₀ - u θ) ^ 2 := by ring
      rw [h2]
      exact h
  have hsq : (u θ) ^ 2 ≤ 2 * (u θ₀) ^ 2 + 2 * (u θ - u θ₀) ^ 2 := by
    nlinarith [sq_nonneg (u θ₀ - (u θ - u θ₀))]
  calc (u θ) ^ 2 ≤ 2 * (u θ₀) ^ 2 + 2 * (u θ - u θ₀) ^ 2 := hsq
    _ ≤ 2 * ((2 / Real.pi) * (∫ a in Work.Spaces.Iθ, (u a) ^ 2))
          + 2 * ((100 / (γ - 1)) * ∫ s in Work.Spaces.Iθ,
              (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ)) :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (by norm_num))
          (mul_le_mul_of_nonneg_left hosc (by norm_num))
    _ = (4 / Real.pi) * (∫ a in Work.Spaces.Iθ, (u a) ^ 2)
          + (200 / (γ - 1)) * ∫ s in Work.Spaces.Iθ,
              (deriv u s) ^ 2 * (Real.sin (2 * s)) ^ (2 - γ) := by ring

/-- The angular Hardy inequality of Elgindi's Lemma `infinity_separated`, integrated in the radial variable: for `b ≤ 3` and `f ∈ ℋ⁴`, `∫_z sup_θ |D_z^b f(z,θ)·w(z)|² dz ≤ C/(γ-1)·HkSq α 4 f`.  `supAbsTh u z` is the supremum of `|u z θ|` over `θ ∈ Iθ` at fixed `z` (defined in `Submission/Work/FTS/H2/Transport1Aux`).  Proof route: at fixed `z`, choose `θ₀` with `|u(z,θ₀)|² ≤ (2/π)∫_θ u(z,θ)²dθ`, split `sup_θ|u|² ≤ 2|u(z,θ₀)|² + 2 sup_θ|u(z,θ) - u(z,θ₀)|²` and bound the oscillation by Cauchy–Schwarz: `≤ C/(γ-1)∫_θ (∂_θ u)²sin(2θ)^{2-γ}`.  Multiplying by `w(z)²` and integrating in `z` gives the two sub-blocks `∫∫(D_z^b f)²w²sin(2θ)^{-η} ≤ HkSq α 4 f` (as `sin(2θ)^{-η} ≥ 1`) and `∫∫(D_z^b D_θ f / sin(2θ))²w²sin(2θ)^{2-γ} = ∫∫(mixed b 1 f)²W² ≤ HkSq α 4 f` (since `∂_θ` commutes with `D_z`), both valid for `b ≤ 3`. -/
theorem SupThetaInt : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b : ℕ), 0 < α → α ≤ 1 → b ≤ 3 →
    Work.Spaces.SmoothNbhd f → Work.Spaces.DecayAll 4 f → Work.Spaces.HkMem α 4 f →
    MeasureTheory.IntegrableOn
        (fun z => (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2)
        Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ C / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f := by
  refine ⟨1000, by norm_num, ?_⟩
  intro α f b hα hα1 hb3 hsm _hdec hmem
  -- ## Basic numerology and standing facts
  have hγ1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hγpos : 0 < Work.Spaces.gam α - 1 := by linarith
  have hb4 : b ≤ 4 := by omega
  have hb1 : 1 + b ≤ 4 := by omega
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIz_meas : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hsmu : Work.Spaces.SmoothNbhd (Work.Spaces.DzIter b f) :=
    Work.Spaces.SmoothNbhd.DzIter hsm b
  -- the a.e. slice-integrability of the two weighted derivatives (HkMem bookkeeping)
  have hD3 : (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter b f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ) ∧
      (∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ) := by
    have hQd : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ⊆ Work.Spaces.nbhU := by
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      have hz' : (0 : ℝ) < z := hz
      have hθ1 : (0 : ℝ) < θ := hθ.1
      have hθ2 : θ < Real.pi / 2 := hθ.2
      refine ⟨?_, ?_, ?_⟩
      · show (-1 : ℝ) < z; linarith
      · show (-1 : ℝ) < θ; linarith
      · show θ < Real.pi / 2 + 1; linarith [Real.pi_pos]
    have hsin_pos_Qd : ∀ p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2),
        0 < Real.sin (2 * p.2) := by
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      have hθ1 : (0 : ℝ) < θ := hθ.1
      have hθ2 : θ < Real.pi / 2 := hθ.2
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hw_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := by
      simp only [Work.Spaces.w]
      exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
        (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))
    have hsp_Qd : ContinuousOn (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsin_pos_Qd p hp)))
    have hDz_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter b f p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
      ((Work.Spaces.SmoothNbhd.DzIter hsm b : ContDiffOn ℝ ⊤
        (Function.uncurry (Work.Spaces.DzIter b f)) Work.Spaces.nbhU).continuousOn).mono hQd
    have hmix_Qd : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed b 1 f p.1 p.2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
      ((Work.Spaces.SmoothNbhd.DzIter (Work.Spaces.SmoothNbhd.DthIter hsm 1) b :
        ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.mixed b 1 f)) Work.Spaces.nbhU).continuousOn).mono
        hQd
    have hcont1 : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter b f p.1 p.2
        * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
      (hDz_Qd.mul (hw_Qd.div hsp_Qd
        (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsin_pos_Qd p hp) _)))).pow 2
    have hcont2 : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.Spaces.mixed b 1 f p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := by
      have hWt : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := by
        simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
        exact hw_Qd.mul (((Real.continuous_sin.comp
          (continuous_const.mul continuous_snd)).continuousOn).rpow_const
          (fun p hp => Or.inl (ne_of_gt (hsin_pos_Qd p hp))))
      exact (hmix_Qd.mul hWt).pow 2
    have haesm1 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont1
    have haesm2 := Work.Spaces.aesm_of_continuousOn_Qd _ hcont2
    refine ⟨?_, ?_⟩
    · filter_upwards [haesm1.prodMk_left, MeasureTheory.ae_restrict_mem hIz_meas]
        with z hz_meas hz
      refine MeasureTheory.Integrable.mono' (hmem.1 z hz) hz_meas ?_
      exact MeasureTheory.ae_restrict_of_forall_mem hIθ_meas (fun θ _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ b hb4)
    · filter_upwards [haesm2.prodMk_left, MeasureTheory.ae_restrict_mem hIz_meas]
        with z hz_meas hz
      refine MeasureTheory.Integrable.mono' (hmem.1 z hz) hz_meas ?_
      exact MeasureTheory.ae_restrict_of_forall_mem hIθ_meas (fun θ _ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 b le_rfl hb1)
  -- a.e. measurability of the angular supremum
  have hmeas_sup : AEMeasurable (fun z => Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    classical
    have hslice_meas : ∀ q ∈ Work.Spaces.Iθ,
        AEMeasurable (fun z => Work.Spaces.DzIter b f z q)
          (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      intro q hq
      have hcd := Work.Spaces.hardyZ_contDiffOn_slice (Work.Spaces.DzIter b f) hsmu hq
      refine (hcd.continuousOn.mono ?_).aemeasurable hIz_meas
      intro z hz
      simp only [Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi] at hz ⊢
      linarith
    let G : ℝ → ℝ := fun z => ⨆ (q : ℚ),
      (if ((q : ℚ) : ℝ) ∈ Work.Spaces.Iθ
        then |Work.Spaces.DzIter b f z ((q : ℚ) : ℝ)| else 0)
    have hG_aem : AEMeasurable G (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      dsimp only [G]
      refine AEMeasurable.iSup (fun q : ℚ => ?_)
      by_cases hq : ((q : ℚ) : ℝ) ∈ Work.Spaces.Iθ
      · have : (fun z : ℝ => (if ((q : ℚ) : ℝ) ∈ Work.Spaces.Iθ
            then |Work.Spaces.DzIter b f z ((q : ℚ) : ℝ)| else 0))
            = fun z => |Work.Spaces.DzIter b f z ((q : ℚ) : ℝ)| := by
          funext z
          rw [ite_eq_left hq]
        rw [this]
        exact (hslice_meas ((q : ℚ) : ℝ) hq).abs
      · have : (fun z : ℝ => (if ((q : ℚ) : ℝ) ∈ Work.Spaces.Iθ
            then |Work.Spaces.DzIter b f z ((q : ℚ) : ℝ)| else 0))
            = fun _ => (0 : ℝ) := by
          funext z
          rw [ite_eq_right hq]
        rw [this]
        exact aemeasurable_const
    have hG_eq : ∀ z ∈ Work.Spaces.Iz,
        Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z = G z := by
      intro z hz
      obtain ⟨C, hCnn, hC⟩ := exists_nonneg_bound_abs (continuousOn_slice hsmu hz)
      have hBddS : BddAbove {y : ℝ | ∃ θ ∈ Work.Spaces.Iθ,
          y = |Work.Spaces.DzIter b f z θ|} :=
        ⟨C, fun y hy => by obtain ⟨θ, hθ, rfl⟩ := hy; exact hC θ hθ⟩
      have hBddG : BddAbove (Set.range (fun q : ℚ =>
          (if ((q : ℚ) : ℝ) ∈ Work.Spaces.Iθ
            then |Work.Spaces.DzIter b f z ((q : ℚ) : ℝ)| else 0))) := by
        refine ⟨C, ?_⟩
        rintro y ⟨q, rfl⟩
        by_cases hq : ((q : ℚ) : ℝ) ∈ Work.Spaces.Iθ
        · simp only [ite_eq_left hq]; exact hC _ hq
        · simp only [ite_eq_right hq]; exact hCnn
      -- rationals of `Iθ` come arbitrarily close to a given point of `Iθ`
      have hdens : ∀ θ ∈ Work.Spaces.Iθ, ∀ δ > 0, ∃ q : ℚ,
          ((q : ℚ) : ℝ) ∈ Work.Spaces.Iθ ∧ |((q : ℚ) : ℝ) - θ| < δ := by
        intro θ hθ δ hδ
        rcases lt_or_eq_of_le hθ.2 with hlt | heq
        · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show θ < θ + min δ (Real.pi / 2 - θ) by
            have h1 : 0 < min δ (Real.pi / 2 - θ) := lt_min hδ (by linarith)
            linarith)
          refine ⟨q, ⟨le_of_lt (lt_of_le_of_lt hθ.1 hq1),
            by linarith [min_le_right δ (Real.pi / 2 - θ), hq2]⟩, ?_⟩
          rw [abs_lt]
          exact ⟨by linarith [min_le_left δ (Real.pi / 2 - θ), hq1, hδ],
            by linarith [min_le_left δ (Real.pi / 2 - θ), hq2]⟩
        · subst heq
          obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
            (show Real.pi / 2 - min δ (Real.pi / 2) < Real.pi / 2 by
              have h1 : 0 < min δ (Real.pi / 2) := lt_min hδ (by linarith [Real.pi_pos])
              linarith)
          refine ⟨q, ⟨by linarith [min_le_right δ (Real.pi / 2), hq1], le_of_lt hq2⟩, ?_⟩
          rw [abs_lt]
          exact ⟨by linarith [min_le_left δ (Real.pi / 2)], by linarith [hq2]⟩
      refine le_antisymm ?_ ?_
      · rw [Work.FTS.H2.supAbsTh_def]
        refine csSup_le ⟨|Work.Spaces.DzIter b f z 0|, 0, Work.Spaces.zero_mem_Iθ, rfl⟩
          (fun y hy => ?_)
        obtain ⟨θ, hθ, rfl⟩ := hy
        by_contra hcon
        rw [not_le] at hcon
        have hε : 0 < (|Work.Spaces.DzIter b f z θ| - G z) / 2 := by linarith
        obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousOn_iff.mp (continuousOn_slice hsmu hz))
          θ hθ ((|Work.Spaces.DzIter b f z θ| - G z) / 2) hε
        obtain ⟨q, hqIθ, hqdist⟩ := hdens θ hθ δ hδpos
        have h1 : |Work.Spaces.DzIter b f z ((q : ℚ) : ℝ)| ≤ G z := by
          have hle := le_ciSup hBddG q
          rwa [ite_eq_left hqIθ] at hle
        have h2 := hδ ((q : ℚ) : ℝ) hqIθ hqdist
        rw [Real.dist_eq] at h2
        have h3 : |Work.Spaces.DzIter b f z θ|
            ≤ |Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z ((q : ℚ) : ℝ)|
              + |Work.Spaces.DzIter b f z ((q : ℚ) : ℝ)| := by
          have h := abs_add_le (Work.Spaces.DzIter b f z θ - Work.Spaces.DzIter b f z ((q : ℚ) : ℝ))
            (Work.Spaces.DzIter b f z ((q : ℚ) : ℝ))
          rwa [sub_add_cancel] at h
        rw [abs_sub_comm] at h2
        linarith
      · dsimp only [G]
        refine ciSup_le (fun q => ?_)
        by_cases hq : ((q : ℚ) : ℝ) ∈ Work.Spaces.Iθ
        · rw [ite_eq_left hq]
          exact le_csSup hBddS ⟨((q : ℚ) : ℝ), hq, rfl⟩
        · rw [ite_eq_right hq]
          have hmem : |Work.Spaces.DzIter b f z 0| ∈ {y : ℝ | ∃ θ ∈ Work.Spaces.Iθ,
              y = |Work.Spaces.DzIter b f z θ|} := ⟨0, Work.Spaces.zero_mem_Iθ, rfl⟩
          exact le_trans (abs_nonneg _) (le_csSup hBddS hmem)
    refine hG_aem.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hIz_meas] with z hz
    exact (hG_eq z hz).symm
  -- ## Step 1: the pointwise (in `z`) bound, a.e. in `z`
  have hIz_eq : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm
  have hD3z : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter b f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ := by
    rw [← hIz_eq]; exact hD3.1
  have hD3m : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      MeasureTheory.IntegrableOn (fun θ =>
        (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) Work.Spaces.Iθ := by
    rw [← hIz_eq]; exact hD3.2
  have hstep : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem (show MeasurableSet (Set.Ioi (0 : ℝ))
        from measurableSet_Ioi), hD3z, hD3m] with z hzpos hDz hmix
    have hzIz : z ∈ Work.Spaces.Iz := by
      simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hzpos
    have hz0 : (0 : ℝ) < z := hzpos
    have hwz_nn : 0 ≤ Work.Spaces.w z := by
      simp only [Work.Spaces.w]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hwz_ne : Work.Spaces.w z ≠ 0 := by
      simp only [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (ne_of_gt (by linarith : (0 : ℝ) < 1 + z)))
        (pow_ne_zero 2 (ne_of_gt hz0))
    -- the two integrability hypotheses of the slice estimate
    have hint2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter b f z θ) ^ 2)
        Work.Spaces.Iθ :=
      (SliceFacts hsmu).2.1 z hzIz
    have hintp : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun θ' => Work.Spaces.DzIter b f z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ := by
      have hscaled : MeasureTheory.IntegrableOn (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹
          * ((Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)) Work.Spaces.Iθ :=
        hmix.const_mul _
      refine hscaled.congr_fun ?_ hIθ_meas
      intro θ hθ
      simp only []
      rw [← pth_DzIter_weight_sq hsm α hα hα1 b hzIz hθ]
      rw [show (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
          = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) by ring]
      exact inv_mul_cancel_left₀ (pow_ne_zero 2 hwz_ne) _
    -- the slice estimate
    have hslice := slice_sup_sq_le hγ1 hγ2 ((contDiffOn_theta_slice hsmu hzIz).of_le le_top)
      hint2 hintp
    -- the two dominating θ-integrals, weighted
    set B : ℝ := (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
        + (200 / (Work.Spaces.gam α - 1)) * ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) with hB
    have hsliceB : ∀ θ ∈ Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2 ≤ B := by
      intro θ hθ
      rw [hB]
      exact hslice θ hθ
    have hBnn : 0 ≤ B := by
      rw [hB]
      refine add_nonneg (mul_nonneg (by positivity)
        (MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _))) ?_
      refine mul_nonneg (by positivity) (MeasureTheory.setIntegral_nonneg hIθ_meas
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.Spaces.bt_sin_nonneg hθ) _)))
    have hsup_nn : 0 ≤ Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z := by
      refine Work.FTS.H2.supAbsTh_nonneg ?_
      obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (continuousOn_slice hsmu hzIz).abs
      exact ⟨C, fun y hy => by
        obtain ⟨θ, hθ, rfl⟩ := hy
        exact hC ⟨θ, hθ, rfl⟩⟩
    have hsup_le : Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z ≤ Real.sqrt B :=
      Work.FTS.H2.supAbsTh_le (fun θ hθ => by
        rw [← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (hsliceB θ hθ))
    have hstep1 : (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ B * (Work.Spaces.w z) ^ 2 := by
      have h1 : Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z
          ≤ Real.sqrt B * Work.Spaces.w z :=
        mul_le_mul_of_nonneg_right hsup_le hwz_nn
      have h0 : 0 ≤ Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z :=
        mul_nonneg hsup_nn hwz_nn
      calc (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
          ≤ (Real.sqrt B * Work.Spaces.w z) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = B * (Work.Spaces.w z) ^ 2 := by rw [mul_pow, Real.sq_sqrt hBnn]
    -- the pointwise comparison `1 ≤ sin(2θ)^{-η}` on the open interval
    have hcomp : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        (Work.Spaces.DzIter b f z θ * Work.Spaces.w z) ^ 2
          ≤ (Work.Spaces.DzIter b f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      intro θ hθ
      have hsinpos : 0 < Real.sin (2 * θ) := by
        refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
        linarith [hθ.2, Real.pi_pos]
      have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
        Real.rpow_pos_of_pos hsinpos _
      have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
        Real.rpow_le_one (le_of_lt hsinpos) (Real.sin_le_one _)
          (by norm_num [Work.Spaces.eta])
      have hle : Work.Spaces.w z
          ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
        rw [le_div_iff₀ hspos]
        nlinarith [hwz_nn, hsle]
      rw [sq_le_sq, abs_mul, abs_mul, abs_of_nonneg hwz_nn,
        abs_of_nonneg (div_nonneg hwz_nn (le_of_lt hspos))]
      exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    have hIθ_open : (Work.Spaces.Iθ : Set ℝ) =ᵐ[MeasureTheory.volume] Set.Ioo 0 (π / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := π / 2)).symm
    have hDz_open : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter b f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (Set.Ioo 0 (π / 2)) := hDz.mono_set Set.Ioo_subset_Icc_self
    -- block 1: the `D_z`-slot
    have hA1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
          * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
      have e1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
            * (Work.Spaces.w z) ^ 2
          = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ * Work.Spaces.w z) ^ 2 := by
        rw [mul_comm, ← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
      rw [e1]
      calc ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ * Work.Spaces.w z) ^ 2
          = ∫ θ in Set.Ioo (0 : ℝ) (π / 2),
              (Work.Spaces.DzIter b f z θ * Work.Spaces.w z) ^ 2 :=
            MeasureTheory.setIntegral_congr_set hIθ_open
        _ ≤ ∫ θ in Set.Ioo (0 : ℝ) (π / 2), (Work.Spaces.DzIter b f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) hDz_open ?_
            exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
              (fun θ hθ => hcomp θ hθ)
        _ = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
            (MeasureTheory.setIntegral_congr_set hIθ_open).symm
        _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
            refine MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) (hmem.1 z hzIz) ?_
            exact MeasureTheory.ae_restrict_of_forall_mem hIθ_meas
              (fun θ _ => Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ b hb4)
    -- block 2: the mixed slot
    have hA2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ := by
      have e2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2
          = ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed b 1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
        rw [mul_comm, ← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun hIθ_meas (fun θ hθ => ?_)
        rw [← pth_DzIter_weight_sq hsm α hα hα1 b hzIz hθ]
        ring
      rw [e2]
      refine MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) (hmem.1 z hzIz) ?_
      exact MeasureTheory.ae_restrict_of_forall_mem hIθ_meas
        (fun θ _ => Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ 1 b le_rfl hb1)
    calc (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ B * (Work.Spaces.w z) ^ 2 := hstep1
      _ = (4 / Real.pi) * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.DzIter b f z θ) ^ 2)
              * (Work.Spaces.w z) ^ 2)
            + (200 / (Work.Spaces.gam α - 1)) * ((∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.DzIter b f) z θ) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) * (Work.Spaces.w z) ^ 2) := by
          rw [hB]; ring
      _ ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
            + (200 / (Work.Spaces.gam α - 1))
              * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
          add_le_add (mul_le_mul_of_nonneg_left hA1 (by positivity))
            (mul_le_mul_of_nonneg_left hA2 (by positivity))
      _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := by ring
  -- ## Step 2: integrate in `z`
  have hfstep : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := by
    rw [hIz_eq]
    exact hstep
  have hdom_nn : ∀ z, 0 ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
      * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) := fun z =>
    mul_nonneg (by positivity)
      (MeasureTheory.setIntegral_nonneg hIθ_meas
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ))
  have hdom_int : MeasureTheory.Integrable
      (fun z => (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
        * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hmem.2.const_mul _
  have hf_aesm : AEStronglyMeasurable
      (fun z => (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hw_meas : AEMeasurable (fun z : ℝ => Work.Spaces.w z)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      rw [hIz_eq]
      change AEMeasurable (fun z : ℝ => (1 + z) ^ 2 / z ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).aemeasurable
        measurableSet_Ioi
    exact ((hmeas_sup.mul hw_meas).pow_const 2).aestronglyMeasurable
  have hf_int : MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz := by
    refine MeasureTheory.Integrable.mono' hdom_int hf_aesm ?_
    filter_upwards [hfstep] with z hz
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hz
  have hmain : ∫ z in Work.Spaces.Iz,
        (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
      ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := by
    calc ∫ z in Work.Spaces.Iz,
          (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
        ≤ ∫ z in Work.Spaces.Iz, (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ) :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun z => sq_nonneg _)) hdom_int hfstep
      _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
            * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 4 f z θ) :=
          MeasureTheory.integral_const_mul _ _
      _ = (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := rfl
  have hcoef : (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
      ≤ 1000 / (Work.Spaces.gam α - 1) := by
    have heq : (4 / Real.pi + 200 / (Work.Spaces.gam α - 1))
        = (4 / Real.pi * (Work.Spaces.gam α - 1) + 200) / (Work.Spaces.gam α - 1) := by
      field_simp
    rw [heq]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hγpos)
    have h1 : (4 / Real.pi) * (Work.Spaces.gam α - 1) ≤ (4 / Real.pi) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (4 : ℝ) / Real.pi ≤ 4 := by
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    linarith
  refine ⟨hf_int, ?_⟩
  calc ∫ z in Work.Spaces.Iz,
        (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter b f) z * Work.Spaces.w z) ^ 2
      ≤ (4 / Real.pi + 200 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f := hmain
    _ ≤ 1000 / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 4 f)

end

end Work.FTS.H2
