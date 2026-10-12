import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

/-- Integrability of the heat-triple integrand restricted to the `s > 1` region:
for a measurable, bounded, integrable real `u` on `V = EuclideanSpace ℝ (Fin 3)`, the function
`(p, s) ↦ u p.1 * (u p.2 * s^(−3/2)·exp(−π‖p.1 − p.2‖²/s))` on `(V × V) × ℝ` is integrable
w.r.t. `(volume.prod volume).prod (volume.restrict (Set.Ioi (1 : ℝ)))`.
Strategy: for `s > 1` bound the kernel by `s^(−3/2)` (exp ≤ 1), giving the product of
`|u(p.1)||u(p.2)|` (integrable by `MeasureTheory.Integrable.mul_prod`) and `s^(−3/2)` on `(1,∞)`
(`MeasureTheory.integrableOn_Ioi_rpow_of_lt`, exponent −3/2 < −1), then
`MeasureTheory.Integrable.mono'`. -/
theorem heat_triple_integrable_large (u : EuclideanSpace ℝ (Fin 3) → ℝ) (hmu : Measurable u)
    (hu_bdd : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin 3), |u x| ≤ C)
    (hui : MeasureTheory.Integrable u) :
    MeasureTheory.Integrable
      (fun z : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × ℝ =>
        u z.1.1 * (u z.1.2 *
          (z.2 ^ (-(3 / 2 : ℝ)) * Real.exp (-(Real.pi * ‖z.1.1 - z.1.2‖ ^ 2) / z.2))))
      (((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (1 : ℝ)))) := by
  classical
  let a : ℝ := -(3 / 2 : ℝ)
  let V := EuclideanSpace ℝ (Fin 3)
  let μ : MeasureTheory.Measure ((V × V) × ℝ) :=
    (((MeasureTheory.volume : MeasureTheory.Measure V).prod
        (MeasureTheory.volume : MeasureTheory.Measure V)).prod
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (1 : ℝ))))
  let F : (V × V) × ℝ → ℝ := fun z =>
    u z.1.1 * (u z.1.2 * (z.2 ^ a * Real.exp (-(Real.pi * ‖z.1.1 - z.1.2‖ ^ 2) / z.2)))
  let B : (V × V) × ℝ → ℝ := fun z => ‖u z.1.1‖ * (‖u z.1.2‖ * z.2 ^ a)
  have ha : a < -1 := by norm_num [a]
  have hB : MeasureTheory.Integrable B μ := by
    have hnn : MeasureTheory.Integrable (fun x : V => ‖u x‖)
        (MeasureTheory.volume : MeasureTheory.Measure V) := hui.norm
    have hB0 : MeasureTheory.Integrable (fun z : V × V => ‖u z.1‖ * ‖u z.2‖)
        ((MeasureTheory.volume : MeasureTheory.Measure V).prod
          (MeasureTheory.volume : MeasureTheory.Measure V)) :=
      hnn.mul_prod hnn
    have hrp : MeasureTheory.Integrable (fun t : ℝ => t ^ a)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioi (1 : ℝ))) := by
      exact integrableOn_Ioi_rpow_of_lt ha (by norm_num : (0 : ℝ) < 1)
    have hprod := hB0.mul_prod hrp
    dsimp [B, μ]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
  have hmeas : MeasureTheory.AEStronglyMeasurable F μ := by
    dsimp [F, μ]
    fun_prop
  have hs_ae' : ∀ᵐ z ∂μ, z ∈ (Set.univ : Set (V × V)) ×ˢ (Set.Ioi (1 : ℝ)) := by
    dsimp [μ]
    rw [MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem]
    · exact Filter.Eventually.of_forall (fun x : V × V => by
        simpa using (MeasureTheory.ae_restrict_mem (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))
          (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi))
    · exact MeasurableSet.univ.prod measurableSet_Ioi
  have hs_ae : ∀ᵐ z ∂μ, (1 : ℝ) < z.2 := by
    exact hs_ae'.mono (fun z hz => by simpa using hz)
  have hbnd : ∀ z : (V × V) × ℝ, (1 : ℝ) < z.2 → ‖F z‖ ≤ B z := by
    intro z hz
    let p : V := z.1.1
    let q : V := z.1.2
    let s : ℝ := z.2
    let e : ℝ := Real.exp (-(Real.pi * ‖p - q‖ ^ 2) / s)
    have hs0 : 0 < s := by
      dsimp [s]
      linarith
    have hsa : 0 ≤ s ^ a := Real.rpow_nonneg (le_of_lt hs0) a
    have ht : -(Real.pi * ‖p - q‖ ^ 2) / s ≤ 0 := by
      have h1 : 0 ≤ Real.pi * ‖p - q‖ ^ 2 := mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg _)
      have h2 : -(Real.pi * ‖p - q‖ ^ 2) ≤ 0 := (neg_nonpos).mpr h1
      exact div_nonpos_of_nonpos_of_nonneg h2 (le_of_lt hs0)
    have hexp_le : e ≤ 1 := by
      dsimp [e]
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr ht
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    have hse : 0 ≤ s ^ a * e := mul_nonneg hsa he0
    have hs_exp : s ^ a * e ≤ s ^ a := by
      simpa using (mul_le_mul_of_nonneg_left hexp_le hsa)
    have hle_inner : |u q| * (s ^ a * e) ≤ |u q| * s ^ a := by
      exact mul_le_mul_of_nonneg_left hs_exp (abs_nonneg _)
    have hle_abs : |F z| ≤ |u p| * (|u q| * s ^ a) := by
      calc
        |F z| = |u p| * (|u q| * (s ^ a * e)) := by
          dsimp [F, p, q, s, e]
          rw [abs_mul, abs_mul, abs_of_nonneg hse]
        _ ≤ |u p| * (|u q| * s ^ a) := by
          exact mul_le_mul_of_nonneg_left hle_inner (abs_nonneg _)
    calc
      ‖F z‖ = |F z| := by rw [Real.norm_eq_abs]
      _ ≤ |u p| * (|u q| * s ^ a) := hle_abs
      _ = B z := by
        dsimp [B, p, q, s]
  exact hB.mono' hmeas (hs_ae.mono (fun z hz => hbnd z hz))

end Commons.Analysis.Fourier