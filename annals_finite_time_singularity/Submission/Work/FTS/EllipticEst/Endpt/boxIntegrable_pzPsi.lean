/-
Copyright: work module for the Elgindi finite-time singularity project.

# Box integrability of `(∂_zΨ)² sin(2θ)^{-η}` from `HkMem α 0 (z ∂_zΨ)`

Let `Ψ` be `C^∞` on the open quadrant `(0,∞) × (0,π/2)` and let `z ∂_zΨ` be honestly in the
level-`0` weighted space `ℋ⁰`, i.e. `(z ∂_zΨ)² w(z)² sin(2θ)^{-η}` has finite iterated
integral.  Then for every `[a,b] ⊆ (0,∞)`,

  `Work.FTS.EllipticEst.Endpt.boxIntegrable_pzPsi`:
  the uncurried function `(s,θ) ↦ (∂_zΨ(s,θ))² · sin(2θ)^{-η}` is integrable on the box
  `[a,b] ×ˢ Iθ`.

Note that *no* hypothesis is made about `Ψ` or `∂_θΨ` being in `ℋ⁰`: the statement is exactly
the `pz`-shadow of the radial `H^1`-slot, which is what the endpoint analysis
(`Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB`, `l2etaEndpointZeroLeft`) consumes.

## Route

This is the `DzIter`-version of `Work.FTS.EllipticEst.boxIntegrable_DzIter` at `k = 0` for the
datum `D_zΨ = z ∂_zΨ`, whose `ℋ⁰`-integrand is the single square
`(D_zΨ · w/sin(2θ)^{η/2})²`:

* `Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term` at `j = 0` gives the pointwise
  domination `(∂_zΨ)² sin(2θ)^{-η} ≤ (z·∂_zΨ · w/sin(2θ)^{η/2})²` (using `z·w(z) ≥ 1`), and
  `Work.Spaces.sq_le_HkIntegrand_z` identifies the right-hand side with the single `i = 0`
  summand of `HkIntegrand α 0 (z ∂_zΨ)`;
* `Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg` (proved in
  `boxIntegrable_DzIter`) assembles the box integrability from continuity on the open
  quadrant, nonnegativity on the box, angular-slice integrability and integrability of the
  iterated `θ`-integral; the last two are read off `hmU.1` / `hmU.2` through the pointwise
  domination above.

Everything here is complete (no placeholders) and rests on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.boxIntegrable_DzIter
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term

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

/-- **Pointwise domination of the `∂_zΨ`-term by the `ℋ⁰`-integrand of `D_zΨ = z ∂_zΨ`.**

For `z > 0` and `θ ∈ Iθ`,

  `(∂_zΨ)² · sin(2θ)^{-η}  ≤  HkIntegrand α 0 (z ∂_zΨ)`,

because `pz_DzIter_sq_mul_sin_le_term` absorbs the angular weight into
`(z·∂_zΨ · w(z)/sin(2θ)^{η/2})² = (D_zΨ · w/sin(2θ)^{η/2})²` (using `z·w(z) ≥ 1`), which is
the `i = 0` summand of the level-`0` integrand of `D_zΨ`. -/
theorem pz_sq_mul_sEta_le_HkIntegrand_Dz (α : ℝ) {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.pz Ψ z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ := by
  have h1 := Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term (F := Ψ) 0 hz hθ
  have h2 := Work.Spaces.sq_le_HkIntegrand_z α 0
    (fun z θ => z * Work.Spaces.pz Ψ z θ) z θ 0 (le_refl 0)
  refine le_trans h1 ?_
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz] using h2

theorem boxIntegrable_pzPsi {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmU : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ)) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pz Ψ s θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro a b ha hab
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  -- The integrand is continuous on the open quadrant: `∂_zΨ` is `C^∞` there and
  -- `sin(2θ) > 0` on the quadrant, so its negative power is continuous.
  have hsinpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hg : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz Ψ p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      Work.FTS.EllipticEst.Q0 := by
    refine ContinuousOn.mul ?_ ?_
    · exact ((((Work.FTS.EllipticEst.smoothOpen_of_forall hsm).pz).forall 0).continuousOn).pow 2
    · exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  -- Nonnegativity on the box.
  have hnn : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (Work.Spaces.pz Ψ z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  -- Angular slices: dominate by the level-`0` integrand of `D_zΨ`.
  have hsl : ∀ s ∈ Set.Icc a b, Integrable (fun θ : ℝ =>
      (Work.Spaces.pz Ψ s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hsz : s ∈ Work.Spaces.Iz := hsub hs
    refine Integrable.mono' (hmU.1 s hsz) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pz Ψ p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hg hspos
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (hnn s hs θ hθ)]
      exact pz_sq_mul_sEta_le_HkIntegrand_Dz α hspos hθ
  -- The iterated `θ`-integral over `[a,b]`: the `θ`-integral of the summand is bounded
  -- pointwise by that of `HkIntegrand α 0 (z ∂_zΨ)`, whose `z`-integral is finite by `hmU`.
  have hint : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pz Ψ s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b)) := by
    have hbase : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) s θ)
        (volume.restrict (Set.Icc a b)) :=
      hmU.2.mono_set hsub
    refine Integrable.mono' hbase ?_ ?_
    · -- Measurability of the iterated integral, by Fubini.
      have hle : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
          ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
        Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
      have hAEj : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          (Work.Spaces.pz Ψ p.1 p.2) ^ 2
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
          (Work.Spaces.pz Ψ s θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      rw [Real.norm_of_nonneg hnonneg]
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hmU.1 s hsz) ?_
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact pz_sq_mul_sEta_le_HkIntegrand_Dz α hspos hθ
  exact integrableOn_box_of_slice_of_nonneg ha hab hg hnn hsl hint

end Work.FTS.EllipticEst.Endpt
