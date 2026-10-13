import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Blocks.IMC.cs_integral_mul_le
import Submission.Work.FTS.EllSol.slice_zero_slot_finite
import Submission.Work.FTS.EllSol.thetaWeightedCS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice Cauchy–Schwarz mass bound `(∫_{θ₁}^{θ} u)² ≤ (π/2) ∫_{Iθ} u² sin(2θ)^{-η}`

The proof is the plain Cauchy–Schwarz inequality on the subinterval `[θ₁,θ] ⊆ (0,π/2)`
(`(∫_a^b u)² ≤ (b-a) ∫_a^b u²`, obtained from Hölder with `p = q = 2` for the pair
`(|u|,1)` on `volume.restrict (Ioc a b)`), together with the two elementary facts

* `θ - θ₁ ≤ π/2`, and
* `u² ≤ u² sin(2θ)^{-η}` on `(θ₁,θ)`, because `sin(2θ)^{-η} ≥ 1` there
  (`Work.FTS.EllSol.one_le_sEta_of_mem_Ioo`).
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllSol.FlatFT

noncomputable section

set_option autoImplicit false

/-- **Cauchy–Schwarz for interval integrals.**  For `a ≤ b` and `u` continuous on `[a,b]`,

`(∫_a^b u)² ≤ (b - a) ∫_a^b u²`.

This is Hölder with `p = q = 2` applied to the pair `(|u|, 1)` on the finite measure
`volume.restrict (Ioc a b)` (whose total mass is `b - a`), followed by `|∫ u| ≤ ∫ |u|`. -/
private lemma sq_intervalIntegral_le {a b : ℝ} (hab : a ≤ b) {u : ℝ → ℝ}
    (hu : ContinuousOn u (Set.Icc a b)) :
    (∫ t in a..b, u t) ^ 2 ≤ (b - a) * ∫ t in a..b, u t ^ 2 := by
  have hIoc : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
  have hvol : volume.real (Set.Ioc a b) = b - a := by
    rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  have huIoc : ContinuousOn u (Set.Ioc a b) := hu.mono Set.Ioc_subset_Icc_self
  -- square-integrability of the two factors of the Hölder pair
  have hInt2 : IntegrableOn (fun t : ℝ => |u t| ^ 2) (Set.Ioc a b) := by
    have h : IntegrableOn (fun t : ℝ => u t ^ 2) (Set.Ioc a b) :=
      ((hu.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    exact h.congr (Eventually.of_forall (fun t => (sq_abs (u t)).symm))
  have hInt1 : IntegrableOn (fun _ : ℝ => (1 : ℝ) ^ 2) (Set.Ioc a b) := by
    simpa only [one_pow] using (MeasureTheory.integrableOn_const
      (μ := volume) (s := Set.Ioc a b) (C := (1 : ℝ))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) (by norm_num))
  -- Hölder
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Set.Ioc a b))
    (f := fun t : ℝ => |u t|) (g := fun _ : ℝ => (1 : ℝ))
    (by simpa [Real.norm_eq_abs] using (huIoc.aestronglyMeasurable hIoc).norm)
    aestronglyMeasurable_const hInt2 hInt1
  have hleft : (∫ x, |u x| * 1 ∂(volume.restrict (Set.Ioc a b))) = ∫ t in a..b, |u t| := by
    simp only [mul_one]
    exact (intervalIntegral.integral_of_le hab).symm
  have hright1 : (∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b))) = ∫ t in a..b, u t ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall (fun x => sq_abs (u x)))
  have hright2 : (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b))) = b - a := by
    rw [MeasureTheory.setIntegral_const, hvol]
    norm_num
  have hMnn : 0 ≤ ∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b)) :=
    MeasureTheory.setIntegral_nonneg hIoc (fun x _ => sq_nonneg _)
  have hNnn : 0 ≤ ∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b)) := by
    rw [hright2]; linarith
  have h1 : (∫ x, |u x| * 1 ∂(volume.restrict (Set.Ioc a b))) ^ 2 ≤
      (∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b))) *
        (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b))) := by
    calc (∫ x, |u x| * 1 ∂(volume.restrict (Set.Ioc a b))) ^ 2
        = |∫ x, |u x| * 1 ∂(volume.restrict (Set.Ioc a b))| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.sqrt (∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b))) *
            Real.sqrt (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b)))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = (∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b))) *
            (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b))) := by
          rw [mul_pow, Real.sq_sqrt hMnn, Real.sq_sqrt hNnn]
  calc (∫ t in a..b, u t) ^ 2 ≤ (∫ t in a..b, |u t|) ^ 2 := by
        have h0 := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := u) hab
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h0 2
    _ = (∫ x, |u x| * 1 ∂(volume.restrict (Set.Ioc a b))) ^ 2 := by rw [hleft]
    _ ≤ (∫ x, |u x| ^ 2 ∂(volume.restrict (Set.Ioc a b))) *
        (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (Set.Ioc a b))) := h1
    _ = (b - a) * ∫ t in a..b, u t ^ 2 := by rw [hright1, hright2, mul_comm]

/-- The mass bound in the ordered case `θ₀ ≤ θ`. -/
private lemma sliceCSMass_aux {u : ℝ → ℝ} {θ₀ θ : ℝ}
    (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hle : θ₀ ≤ θ) (hu : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun t : ℝ => u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ) :
    (∫ t in θ₀..θ, u t) ^ 2 ≤ (Real.pi / 2) *
      (∫ t in Work.Spaces.Iθ, u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) := by
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- the subinterval is contained in `Iθ`
  have hsub : Set.Ioc θ₀ θ ⊆ Work.Spaces.Iθ := fun x hx =>
    ⟨le_of_lt (lt_of_lt_of_le hθ₀.1 hx.1.le), le_of_lt (lt_of_le_of_lt hx.2 hθ.2)⟩
  -- `u` is continuous on the closed subinterval
  have huIcc : ContinuousOn u (Set.Icc θ₀ θ) :=
    hu.mono (fun x hx => ⟨lt_of_lt_of_le hθ₀.1 hx.1, lt_of_le_of_lt hx.2 hθ.2⟩)
  -- Cauchy–Schwarz on the subinterval
  have hcs := sq_intervalIntegral_le hle huIcc
  have hlen : θ - θ₀ ≤ Real.pi / 2 := by linarith [hθ₀.1, hθ.2]
  -- comparing the weighted mass on `(θ₀,θ)` with the one on `Iθ`
  have hInt1 : IntegrableOn (fun t : ℝ => u t ^ 2) (Set.Ioc θ₀ θ) :=
    ((huIcc.pow 2).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hInt2 : IntegrableOn (fun t : ℝ => u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
      (Set.Ioc θ₀ θ) := hint.mono_set hsub
  have hstep : (∫ t in θ₀..θ, u t ^ 2) ≤
      ∫ t in Work.Spaces.Iθ, u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) := by
    rw [intervalIntegral.integral_of_le hle]
    refine (MeasureTheory.setIntegral_mono_on hInt1 hInt2 measurableSet_Ioc ?_).trans
      (MeasureTheory.setIntegral_mono_set hint ?_ ?_)
    · intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [hx.1, hθ₀.1], by linarith [hx.2, hθ.2]⟩
      have h1 : 1 ≤ (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) :=
        Work.FTS.EllSol.one_le_sEta_of_mem_Ioo hx'
      calc u x ^ 2 = u x ^ 2 * 1 := by ring
        _ ≤ u x ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    · filter_upwards [ae_restrict_mem hIθ_meas] with x hx
      exact mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.sEta_nonneg_of_mem_Iθ hx)
    · exact Eventually.of_forall (fun x hx => hsub hx)
  have hMnn : 0 ≤ ∫ t in Work.Spaces.Iθ, u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun x hx => mul_nonneg (sq_nonneg _) (Work.FTS.EllSol.sEta_nonneg_of_mem_Iθ hx))
  have hlennn : 0 ≤ ∫ t in θ₀..θ, u t ^ 2 :=
    intervalIntegral.integral_nonneg hle (fun x _ => sq_nonneg _)
  calc (∫ t in θ₀..θ, u t) ^ 2 ≤ (θ - θ₀) * ∫ t in θ₀..θ, u t ^ 2 := hcs
    _ ≤ (Real.pi / 2) *
        (∫ t in Work.Spaces.Iθ, u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) :=
        mul_le_mul hlen hstep hlennn (by positivity)

theorem sliceCSMass {u : ℝ → ℝ} {θ₁ θ : ℝ}
    (hθ₁ : θ₁ ∈ Set.Ioo 0 (Real.pi / 2)) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hu : ContinuousOn u (Set.Ioo 0 (Real.pi / 2)))
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ =>
      u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ) :
    (∫ t in θ₁..θ, u t) ^ 2
      ≤ (Real.pi / 2) * (∫ t in Work.Spaces.Iθ,
          u t ^ 2 * (Real.sin (2 * t)) ^ (-(Work.Spaces.eta))) := by
  rcases le_total θ₁ θ with hle | hle
  · exact sliceCSMass_aux hθ₁ hθ hle hu hint
  · -- the reversed order: the integral changes sign, the square does not
    have h := sliceCSMass_aux hθ hθ₁ hle hu hint
    have h2 : (∫ t in θ₁..θ, u t) ^ 2 = (∫ t in θ..θ₁, u t) ^ 2 := by
      rw [intervalIntegral.integral_symm]
      ring
    rw [h2]
    exact h

end

end Work.FTS.EllSol.FlatFT
