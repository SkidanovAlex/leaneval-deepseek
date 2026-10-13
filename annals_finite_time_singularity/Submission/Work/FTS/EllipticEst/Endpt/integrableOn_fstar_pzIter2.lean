/-
Copyright: work module for the Elgindi finite-time singularity project.

# Integrability of the angular moment of `∂_z²Ψ` on a compact subinterval of `(0,∞)`

For `Ψ` of class `C^∞` on the open quadrant `(0,∞) × (0,π/2)` whose second radial
derivative satisfies `z² ∂_z²Ψ ∈ ℋ⁰` (the level-`0` weighted space of `Work.Spaces.HkMem`,
whose integrand is the single square `(z² ∂_z²Ψ · w/ sin(2θ)^{η/2})²`), the angular moment

  `F_*(∂_z²Ψ)(z) = ∫_θ ∂_z²Ψ(z,θ) sin θ cos²θ dθ`

is integrable on every `[a,b] ⊆ (0,∞)`.

## Route

* **Pointwise.**  On the *open* angular interval, `(∂_z²Ψ z θ)² sin(2θ)^{-η}` is dominated by
  the level-`0` integrand of `z² ∂_z²Ψ` (`pzIter2_sq_mul_sEta_le_HkIntegrand`, already proved in
  `Endpt/boxIntegrable_pzIter2Psi`); multiplying by `sin(2θ)^{η} ≤ 1` removes the weight and
  gives `(∂_z²Ψ z θ)² ≤ HkIntegrand α 0 (z² ∂_z²Ψ) z θ` (`pzIter2_sq_le_HkIntegrand`).
  The degenerate angles `θ = 0, π/2` are null, so the inequality holds a.e. on `Iθ`.
* **Slice.**  `Work.Elliptic.Fstar_sq_le` (Cauchy–Schwarz in `θ` against `sinθcos²θ ∈ [0,1]`)
  plus the monotone comparison above give
  `F_*(∂_z²Ψ)(z)² ≤ (π/2) ∫_θ HkIntegrand α 0 (z² ∂_z²Ψ) z θ` for every `z > 0`
  (`Fstar_pzIter2_sq_le`).
* **Assembly.**  The right-hand side is integrable in `z` on `[a,b]` by `hmZ.2` (restricted),
  and `|F_*(∂_z²Ψ)(z)| ≤ F_*(∂_z²Ψ)(z)² + 1`, so the moment is dominated by an integrable
  function and is a.e. strongly measurable (`aestronglyMeasurable_integral_Itheta_Q0`, from the
  continuity of `∂_z²Ψ` on the open quadrant).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0
import Submission.Work.Elliptic.Fstar_sq_le
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst.Endpt

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The elementary absorption `|x| ≤ x² + 1`: for `|x| ≤ 1` the right-hand side is at least `1`,
and for `|x| ≥ 1` one has `|x| ≤ |x|² = x²`. -/
theorem abs_le_sq_add_one' (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  rcases le_or_gt |x| 1 with h | h
  · nlinarith [sq_nonneg x]
  · have h2 : |x| ≤ |x| * |x| := by
      calc |x| = 1 * |x| := (one_mul _).symm
        _ ≤ |x| * |x| := mul_le_mul_of_nonneg_right (le_of_lt h) (abs_nonneg x)
    have h3 : |x| * |x| = x ^ 2 := by
      rw [← sq_abs]
      ring
    linarith [h2, h3]

/-- **Pointwise domination on the open angular interval.**  For `z > 0` and `θ ∈ (0,π/2)`,

  `(∂_z²Ψ(z,θ))² ≤ HkIntegrand α 0 (z² ∂_z²Ψ) (z,θ)`.

Indeed `(∂_z²Ψ)² sin(2θ)^{-η} ≤ HkIntegrand` (`pzIter2_sq_mul_sEta_le_HkIntegrand`) and
multiplication by `sin(2θ)^{η} ≤ 1` (with `sin(2θ) > 0`) removes the weight. -/
theorem pzIter2_sq_le_HkIntegrand {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hspos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hsle : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hpowle : Real.sin (2 * θ) ^ Work.Spaces.eta ≤ 1 :=
    Real.rpow_le_one hspos.le hsle (by norm_num [Work.Spaces.eta])
  have hmul := mul_le_mul_of_nonneg_right
    (pzIter2_sq_mul_sEta_le_HkIntegrand (α := α) (Ψ := Ψ) hz hθI)
    (Real.rpow_nonneg hspos.le Work.Spaces.eta)
  have hid : (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)
      * Real.sin (2 * θ) ^ Work.Spaces.eta = (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 := by
    rw [mul_assoc, ← Real.rpow_add hspos, neg_add_cancel, Real.rpow_zero, mul_one]
  rw [hid] at hmul
  exact le_trans hmul
    (mul_le_of_le_one_right (Work.Spaces.HkIntegrand_nonneg α 0 _ z θ) hpowle)

/-- **The slicewise `L²`-bound for the angular moment of `∂_z²Ψ`.**  For `z > 0`, if the
level-`0` integrand of `z² ∂_z²Ψ` is `θ`-integrable and the slice of `∂_z²Ψ` is a.e. strongly
measurable, then

  `F_*(∂_z²Ψ)(z)² ≤ (π/2) ∫_θ HkIntegrand α 0 (z² ∂_z²Ψ) z θ`.

This is Cauchy–Schwarz in `θ` (`Work.Elliptic.Fstar_sq_le`) followed by the monotone comparison
`(∂_z²Ψ)² ≤ HkIntegrand` on the full-measure set `(0,π/2) ⊆ Iθ`. -/
theorem Fstar_pzIter2_sq_le {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hH : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.HkIntegrand α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) Work.Spaces.Iθ)
    (hae : AEStronglyMeasurable (fun θ => Work.Spaces.pzIter 2 Ψ z θ)
      (volume.restrict Work.Spaces.Iθ)) :
    (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  have hle_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
    have hEq : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (π / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
    rw [MeasureTheory.Measure.restrict_congr_set hEq]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact pzIter2_sq_le_HkIntegrand hz hθ
  have hsq : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2)
      Work.Spaces.Iθ := by
    refine Integrable.mono' hH (hae.pow 2) ?_
    filter_upwards [hle_ae] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hθ
  have hcs := Work.Elliptic.Fstar_sq_le (Work.Spaces.pzIter 2 Ψ) z hsq
  have hmono : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) hH hle_ae
  calc (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z) ^ 2
      ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 := hcs
    _ ≤ (π / 2) * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
        mul_le_mul_of_nonneg_left hmono (by linarith [Real.pi_pos])

theorem integrableOn_fstar_pzIter2 {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmZ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ))
        (Set.Icc a b) := by
  intro a b ha hab
  have hΨ : SmoothOpen Ψ := smoothOpen_of_forall hsm
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz := fun x hx => le_trans (le_of_lt ha) hx.1
  -- Strong measurability of the moment, from continuity of `∂_z²Ψ` on the open quadrant.
  have hFstar_aesm : AEStronglyMeasurable
      (fun z => Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z)
      (volume.restrict (Set.Icc a b)) := by
    have h0 : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
        (volume.restrict (Set.Ioi 0)) :=
      aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.pzIter 2 Ψ)
        (hΨ.pzIter 2).continuousOn Work.Elliptic.sinCos2
        (by unfold Work.Elliptic.sinCos2; fun_prop)
    exact AEStronglyMeasurable.mono_set (t := Set.Ioi 0)
      (fun x hx => by simp only [Set.mem_Ioi]; linarith [ha, hx.1]) h0
  -- The dominating function `(π/2)·∫_θ HkIntegrand + 1` is integrable on `[a,b]`.
  have hJint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
      (Set.Icc a b) := hmZ.2.mono_set hsub
  have hconst_int : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  refine hJint.const_mul (π / 2) |>.add hconst_int |>.mono' hFstar_aesm ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with z hz
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hzI : z ∈ Work.Spaces.Iz := hsub hz
  have hpt := Fstar_pzIter2_sq_le (α := α) (Ψ := Ψ) hzpos (hmZ.1 z hzI)
    (hΨ.aesm_slice_pzIter 2 hzpos)
  have hJnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply] at *
  exact le_trans (abs_le_sq_add_one' _) (by linarith)

end Work.FTS.EllipticEst.Endpt
