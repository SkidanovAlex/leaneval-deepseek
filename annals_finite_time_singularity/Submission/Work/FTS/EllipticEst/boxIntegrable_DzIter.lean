/-
Copyright: work module for the Elgindi finite-time singularity project.

# Box integrability of the squared `∂_z D_z^j`-term weighted by `sin(2θ)^{-η}`

For `F` smooth on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`) and `F ∈ ℋ^k`
(`Work.Spaces.HkMem α k F`), every `j` with `j + 1 ≤ k` and every compact interval
`[a,b] ⊆ (0,∞)`,

  `Work.FTS.EllipticEst.boxIntegrable_DzIter`:
  the uncurried function `(s,θ) ↦ (∂_z D_z^j F (s,θ))² · sin(2θ)^{-η}` is integrable
  on the box `[a,b] ×ˢ Iθ`.

## Route

* `Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term` (a delegated lemma) is the pointwise
  domination of the summand by the single `i = j+1` slot of the `ℋ^k`-integrand:
  `(∂_z D_z^j F)² sin(2θ)^{-η} ≤ (D_z^{j+1} F · w / sin(2θ)^{η/2})²` (here `z > 0` is used
  through `z·w(z) = (1+z)²/z ≥ 1` and `D_z^{j+1} F = z·∂_z D_z^j F`), and
  `Work.Spaces.sq_le_HkIntegrand_z` bounds that slot by `HkIntegrand α k F`.
* `Work.FTS.EllipticEst.integrableOn_box_of_slice_of_nonneg` (proved here) is the box
  version of Fubini: continuity on the open quadrant, nonnegativity *on the box*, angular
  slice integrability and integrability of the iterated `θ`-integral give integrability on
  the box.  It is built on `Work.FTS.EllipticEst.integrable_prod_ae` (a delegated lemma,
  the a.e.-nonnegativity form of `Work.Spaces.integrable_prod_of_iterated`), the a.e. strong
  measurability of the uncurried integrand on the box
  (`Work.Spaces.aesm_of_continuousOn_Qd` plus monotonicity of the product measure), and the
  identification of the planar Lebesgue measure on a box with the product of the restrictions
  (`Measure.prod_restrict`).
* The two remaining hypotheses are read off `hmem`: the angular slices are integrable by
  `hmem.1`, and the iterated `θ`-integral over `[a,b]` by `hmem.2` (restricted from `Iz`).

Note that the hypothesis `a < b` is not used: the argument only needs `0 < a` (and hence
`[a,b] ⊆ Iz = [0,∞)`); it is kept because the statement is fixed.

Everything here is complete (no placeholders) and rests on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.integrable_prod_ae
import Submission.Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- The planar Lebesgue measure restricted to a box is the product of the restrictions of
the Lebesgue measure to the two sides. -/
theorem volume_restrict_box (a b : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ)
      = (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ) :=
  (Measure.prod_restrict (Set.Icc a b) Work.Spaces.Iθ).symm

/-- **Box integrability from the angular slices.**  If `g` is continuous on the open quadrant,
nonnegative on the box `[a,b] ×ˢ Iθ` (`0 < a`), has integrable angular slices and an integrable
iterated `θ`-integral over `[a,b]`, then its uncurried version is integrable on the box.

This is the `0 < a`-form of `integrableOn_box_of_slice`, with nonnegativity required only on
the box (which is what the weighted integrands of the elliptic estimates satisfy: the
`sin(2θ)^{-η}` factor is only nonnegative for `θ ∈ Iθ`). -/
theorem integrableOn_box_of_slice_of_nonneg {g : ℝ → ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) Q0)
    (hnn : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ g z θ)
    (hsl : ∀ s ∈ Set.Icc a b, Integrable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ))
    (hint : Integrable (fun s => ∫ θ in Work.Spaces.Iθ, g s θ)
      (volume.restrict (Set.Icc a b))) :
    IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  -- Strong measurability on the box, from continuity on the open quadrant.
  have hle : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
    Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
  have hAE : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => g p.1 p.2) hg).mono_measure hle
  -- Nonnegativity on the box, in the a.e. form needed for the product integral.
  have hnn' : ∀ᵐ x ∂(volume.restrict (Set.Icc a b)),
      ∀ᵐ y ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ g x y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    filter_upwards [ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with y hy
    exact hnn x hx y hy
  have hsl' : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)),
      Integrable (fun θ => g s θ) (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hsl s hs
  -- Fubini for the product measure, then the identification of the restricted planar
  -- measure on the box with that product.
  have hbox : Integrable (Function.uncurry g)
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.FTS.EllipticEst.integrable_prod_ae hnn' hAE hsl' hint
  show Integrable (Function.uncurry g) (volume.restrict (Set.Icc a b ×ˢ Work.Spaces.Iθ))
  rw [volume_restrict_box]
  exact hbox

theorem boxIntegrable_DzIter (α : ℝ) (k : ℕ) {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Function.uncurry (fun s θ : ℝ =>
        (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) (Set.Icc a b ×ˢ Work.Spaces.Iθ) := by
  intro a b ha hab
  have hsub : Set.Icc a b ⊆ Work.Spaces.Iz :=
    fun x hx => Set.mem_Ici.mpr (le_trans (le_of_lt ha) hx.1)
  -- The integrand is continuous on the open quadrant: `∂_z D_z^j F` is `C^∞` there and
  -- `sin(2θ) > 0` on the quadrant, so its negative power is continuous.
  have hsinpos : ∀ p ∈ Q0, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := mem_Q0.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hg : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
        * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Q0 := by
    refine ContinuousOn.mul ?_ ?_
    · exact ((hF.DzIter j).pz.continuousOn).pow 2
    · exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
        (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
  -- Nonnegativity on the box.
  have hnn : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ (Work.Spaces.pz (Work.Spaces.DzIter j F) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    fun z _ θ hθ => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.Spaces.sin_two_nonneg_of_Iθ hθ) _)
  -- Angular slices: dominate by the `i = j+1` slot of the `ℋ^k`-integrand.
  have hsl : ∀ s ∈ Set.Icc a b, Integrable (fun θ : ℝ =>
      (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le ha hs.1
    have hsz : s ∈ Work.Spaces.Iz := hsub hs
    refine Integrable.mono' (hmem.1 s hsz) ?_ ?_
    · exact Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) hg hspos
    · filter_upwards [ae_restrict_mem
        (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
      rw [Real.norm_of_nonneg (hnn s hs θ hθ)]
      exact le_trans (Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term j hspos hθ)
        (Work.Spaces.sq_le_HkIntegrand_z α k F s θ (j + 1) hj)
  -- The iterated `θ`-integral over `[a,b]`: the `θ`-integral of the summand is bounded
  -- pointwise by that of `HkIntegrand α k F`, whose `z`-integral is finite by `hmem`.
  have hint : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict (Set.Icc a b)) := by
    have hbase : Integrable (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F s θ) (volume.restrict (Set.Icc a b)) :=
      hmem.2.mono_set hsub
    refine Integrable.mono' hbase ?_ ?_
    · -- Measurability of the iterated integral, by Fubini.
      have hle : (volume.restrict (Set.Icc a b)).prod (volume.restrict Work.Spaces.Iθ)
          ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
        Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
      have hAEj : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          (Work.Spaces.pz (Work.Spaces.DzIter j F) p.1 p.2) ^ 2
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
          (Work.Spaces.pz (Work.Spaces.DzIter j F) s θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        refine MeasureTheory.integral_nonneg_of_ae ?_
        filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      rw [Real.norm_of_nonneg hnonneg]
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 s hsz) ?_
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact hnn s hs θ hθ
      · filter_upwards [ae_restrict_mem
          (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
        exact le_trans (Work.FTS.EllipticEst.pz_DzIter_sq_mul_sin_le_term j hspos hθ)
          (Work.Spaces.sq_le_HkIntegrand_z α k F s θ (j + 1) hj)
  exact integrableOn_box_of_slice_of_nonneg ha hab hg hnn hsl hint

end Work.FTS.EllipticEst
