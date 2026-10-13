/-
Copyright: work module for the Elgindi finite-time singularity project.

# Box integrability of `(∂_z²Ψ)² sin(2θ)^{-η}` from `HkMem α 0 (z² ∂_z²Ψ)`

Let `Ψ` be `C^∞` on the open quadrant `(0,∞) × (0,π/2)` and let `z² ∂_z²Ψ` be honestly in
the level-`0` weighted space `ℋ⁰`, i.e. `(z² ∂_z²Ψ)² w(z)² sin(2θ)^{-η}` has finite iterated
integral.  Then for every `[a,b] ⊆ (0,∞)`,

  `Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi`:
  the uncurried function `(s,θ) ↦ (∂_z²Ψ(s,θ))² · sin(2θ)^{-η}` is integrable on the box
  `[a,b] ×ˢ Iθ`.

This is the exact `pzIter 2`-analogue of `Work.FTS.EllipticEst.Endpt.boxIntegrable_pzPsi`
(with `∂_zΨ` replaced by `∂_z²Ψ`): the datum `z² ∂_z²Ψ` has a *single* `ℋ⁰`-summand, namely
`(z² ∂_z²Ψ · w/sin(2θ)^{η/2})²`, and the factor `z² w(z) = (1+z)² ≥ 1` absorbs the gap
between `(∂_z²Ψ)² sin(2θ)^{-η}` and that summand.

## Route

* the pointwise domination `pzIter2_sq_mul_sEta_le_HkIntegrand`
  (`(∂_z²Ψ)² sin(2θ)^{-η} ≤ HkIntegrand α 0 (z² ∂_z²Ψ)`, for `z > 0`, `θ ∈ Iθ`) is proved
  from the `rpow` algebra `Work.FTS.H2.T1HardWeightAlg` and
  `Work.Spaces.sq_le_HkIntegrand_z` at `i = 0` (using `z² w(z) = (1+z)² ≥ 1`);
* `Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg` (proved in
  `boxIntegrable_DzIter`) assembles the box integrability from continuity on the open
  quadrant, nonnegativity on the box, angular-slice integrability and integrability of the
  iterated `θ`-integral; the last two are read off `hmZ.1` / `hmZ.2` through the pointwise
  domination above.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.boxIntegrable_DzIter
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.H2.T1HardWeightAlg

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

/-- **Pointwise domination of the `∂_z²Ψ`-term by the `ℋ⁰`-integrand of `z² ∂_z²Ψ`.**

For `z > 0` and `θ ∈ Iθ`,

  `(∂_z²Ψ)² · sin(2θ)^{-η}  ≤  HkIntegrand α 0 (z² ∂_z²Ψ)`,

because `z²·w(z) = (1+z)² ≥ 1`, so multiplying the left-hand side by the square of that
factor can only increase it, and `T1HardWeightAlg` identifies the result with the `i = 0`
summand `(z²·∂_z²Ψ · w(z)/sin(2θ)^{η/2})²` of the level-`0` integrand. -/
theorem pzIter2_sq_mul_sEta_le_HkIntegrand {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
  set a : ℝ := Work.Spaces.pzIter 2 Ψ z θ with ha
  have hS : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  have hnn : 0 ≤ a ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (sq_nonneg a) (Real.rpow_nonneg hS _)
  -- The `i = 0` slot of `HkIntegrand α 0 (z² a)` is `(z²·a·(w/sin(2θ)^{η/2}))²`, and
  -- `T1HardWeightAlg` rewrites that square as `w(z)²·((z²·a)²·sin(2θ)^{-η})`.
  refine le_trans ?_ (Work.Spaces.sq_le_HkIntegrand_z α 0
    (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ 0 (le_refl 0))
  have hkey := (Work.FTS.H2.T1HardWeightAlg α z θ (z ^ 2 * a) 0 (le_of_lt hz) hθ).1
  have hz0 : Work.Spaces.DzIter 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      = z ^ 2 * a := by simp only [Work.Spaces.DzIter_zero, ha]
  rw [hz0, ← hkey]
  -- `(z²·w(z))²·(a²·sin(2θ)^{-η})` beats `a²·sin(2θ)^{-η}` since `z²·w(z) ≥ 1`.
  have h2 : (Work.Spaces.w z) ^ 2 * ((z ^ 2 * a) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = (z ^ 2 * Work.Spaces.w z) ^ 2
        * (a ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by ring
  rw [h2]
  have hzw : 1 ≤ z ^ 2 * Work.Spaces.w z := by
    have hzw' : z ^ 2 * Work.Spaces.w z = (1 + z) ^ 2 := by
      rw [Work.Spaces.w, sq]
      field_simp
    rw [hzw']
    nlinarith [hz]
  exact le_mul_of_one_le_left hnn (one_le_pow₀ hzw)

theorem boxIntegrable_pzIter2Psi {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmZ : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pzIter 2 Ψ s θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro a b ha hab
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  -- The integrand is continuous on the open quadrant: `∂_z²Ψ` is `C^∞` there and
  -- `sin(2θ) > 0` on the quadrant, so its negative power is continuous.
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hg : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.mul ?_ ?_
    · exact (((Work.FTS.EllipticEst.smoothOpen_of_forall hsm).pzIter 2).continuousOn).pow 2
    · exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  -- Nonnegativity on the box.
  have hnn : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  -- Angular slices: dominate by the level-`0` integrand of `z² ∂_z²Ψ`.
  have hsl : ∀ s ∈ Set.Icc a b, Integrable (fun θ : ℝ =>
      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hsz : s ∈ Work.Spaces.Iz := hsub hs
    refine Integrable.mono' (hmZ.1 s hsz) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hg hspos
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (hnn s hs θ hθ)]
      exact pzIter2_sq_mul_sEta_le_HkIntegrand hspos hθ
  -- The iterated `θ`-integral over `[a,b]`: the `θ`-integral of the summand is bounded
  -- pointwise by that of `HkIntegrand α 0 (z² ∂_z²Ψ)`, whose `z`-integral is finite by `hmZ`.
  have hint : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pzIter 2 Ψ s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b)) := by
    have hbase : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) s θ)
        (volume.restrict (Set.Icc a b)) :=
      hmZ.2.mono_set hsub
    refine Integrable.mono' hbase ?_ ?_
    · -- Measurability of the iterated integral, by Fubini.
      have hle : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
          ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
        Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
      have hAEj : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          (Work.Spaces.pzIter 2 Ψ p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
          ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
        (Work.Spaces.aesm_of_continuousOn_Qd _ hg).mono_measure hle
      have h2 := hAEj.integral_prod_right' (μ := volume.restrict (Set.Icc a b))
        (ν := volume.restrict Work.Spaces.Iθ)
      simpa only using h2
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet (Set.Icc a b) from measurableSet_Icc)] with s hs
      have hspos : 0 < s := lt_of_lt_of_le ha hs.1
      have hsz : s ∈ Work.Spaces.Iz := hsub hs
      have hnonneg : 0 ≤ ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pzIter 2 Ψ s θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      rw [Real.norm_of_nonneg hnonneg]
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hmZ.1 s hsz) ?_
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact pzIter2_sq_mul_sEta_le_HkIntegrand hspos hθ
  exact integrableOn_box_of_slice_of_nonneg ha hab hg hnn hsl hint

end Work.FTS.EllipticEst.Endpt
