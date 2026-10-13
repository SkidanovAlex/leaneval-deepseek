/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.PsiSlices.PsiMoments`: the moment chain of `Ψ` in the weak class

For a datum of the weak class (`Ψ` smooth on the open quadrant, `∂_θ²Ψ` honestly in `ℋ²`, and
`F_* Ψ = 0` a.e.), this module produces the two analytic inputs of the *integrated* moment chain
for `Ψ`:

  `F_* Ψ(z) - F_* Ψ(s) = ∫_s^z F_*(∂_zΨ)(r) dr`,   `F_*(∂_zΨ)(z) - F_*(∂_zΨ)(s) = ∫_s^z F_*(∂_z²Ψ)(r) dr`

(`Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz`, whose box-integrability hypothesis is supplied
by `box_pz` / `box_pzIter2` from the fibre bounds of `PsiBox`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.PsiBox
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open
import Submission.Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz
import Submission.Work.FTS.EllipticEst.Mine.SliceMomentTaylor

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.PsiSlices

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## §0 Elementary facts -/

/-- `sinθcos²θ` is continuous. -/
theorem continuous_sinCos2 : Continuous fun θ : ℝ => Work.Elliptic.sinCos2 θ := by
  simp only [Work.Elliptic.sinCos2]
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- The first coordinate is a.e. non-zero on the box `(s,z] × Iθ` when `s > 0`. -/
theorem ae_fst_ne_zero {s z : ℝ} (hs : 0 < s) :
    ∀ᵐ p ∂((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)), p.1 ≠ 0 := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae (p := fun p : ℝ × ℝ => p.1 ≠ 0)
    ((measurableSet_singleton 0).compl.preimage measurable_fst)]
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with r hr
  filter_upwards with θ
  exact ne_of_gt (lt_trans hs hr.1)

/-! ## §1 Slice integrability from the Taylor estimate -/

/-- `θ ↦ D_z^i Ψ(u,θ)·sinθcos²θ` is integrable on `Iθ` for `i ≤ 2` and `u > 0`. -/
theorem slice_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.DzIter i Ψ u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
  (Work.FTS.EllipticEst.Mine.SliceMomentTaylor (contDiffOn_slice_two (hΨ.DzIter i) hu)
    (integrableOn_pthIter2_slice hΨ hB i hi hu)).1

/-- `|D_z^i Ψ(u,·)|·sinθcos²θ` is integrable on `Iθ`. -/
theorem slice_abs_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) (i : ℕ) (hi : i ≤ 2)
    {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => |Work.Spaces.DzIter i Ψ u θ| * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
  (slice_integrableOn hΨ hB i hi hu).norm.congr
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
      show ‖Work.Spaces.DzIter i Ψ u θ * Work.Elliptic.sinCos2 θ‖
        = |Work.Spaces.DzIter i Ψ u θ| * Work.Elliptic.sinCos2 θ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg hθ)]))

/-- `θ ↦ |∂_zΨ(u,θ)|·sinθcos²θ` is integrable on `Iθ` for `u > 0`. -/
theorem slice_abs_pz_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.pz Ψ u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  have hkey : ∀ p : ℝ × ℝ, p.1 ≠ 0 → Work.Spaces.Dz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 / p.1
      = Work.Spaces.pz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 := by
    intro p hp
    simp only [Work.Spaces.Dz]
    field_simp
  refine (((slice_integrableOn hΨ hB 1 (by norm_num) hu).div_const u)).congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
  exact hkey (u, θ) (ne_of_gt hu)

/-! ## §2 Box integrability of the two differentiated moments -/

/-- **Box integrability of `∂_zΨ·sinθcos²θ`.** -/
theorem box_pz {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {s z : ℝ} (hs : 0 < s)
    (hsz : s ≤ z) :
    Integrable (Function.uncurry (fun r θ : ℝ => Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hr0 := ae_fst_ne_zero (s := s) (z := z) hs
  have hsm : ContinuousOn (Function.uncurry (fun r θ : ℝ =>
      Work.Spaces.pz Ψ r θ * Work.Elliptic.sinCos2 θ)) Work.FTS.EllipticEst.Q0 :=
    (hΨ.pz.continuousOn).mul ((continuous_sinCos2.comp continuous_snd).continuousOn)
  have hkey : ∀ p : ℝ × ℝ, p.1 ≠ 0 → Work.Spaces.Dz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 / p.1
      = Work.Spaces.pz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 := by
    intro p hp
    simp only [Work.Spaces.Dz]
    field_simp
  have hae : AEStronglyMeasurable (Function.uncurry (fun r θ : ℝ =>
      Work.Spaces.Dz Ψ r θ * Work.Elliptic.sinCos2 θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.FTS.EllipticEst.aesm_uncurry_restrict_open
      (fun p : ℝ × ℝ => Work.Spaces.pz Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2) hsm
      hs.le).congr (by
        filter_upwards [hr0] with p hp
        simp only [Function.uncurry]
        exact (hkey p hp).symm)
  have hfib : ∀ r ∈ Set.Ioc s z,
      IntegrableOn (fun θ : ℝ => Work.Spaces.Dz Ψ r θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ :=
    fun r hr => slice_integrableOn hΨ hB 1 (by norm_num) (lt_trans hs hr.1)
  have hle : ∀ r ∈ Set.Ioc s z,
      ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ * Work.Elliptic.sinCos2 θ| ≤ Bnd Ψ 1 r := by
    intro r hr
    have hsb := slice_bound hΨ hB 1 (by norm_num) r (lt_trans hs hr.1)
    have heq : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ
          * Work.Elliptic.sinCos2 θ|)
        = ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ :=
      MeasureTheory.integral_congr_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
          show |Work.Spaces.Dz Ψ r θ * Work.Elliptic.sinCos2 θ|
            = |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ
          rw [abs_mul, abs_of_nonneg (sinCos2_nonneg hθ)]))
    rw [heq]
    exact hsb
  have hb := integrable_uncurry_div_of_fibre_bound hs hsz hae hfib hle
    (Bnd_integrableOn hΨ hB 1 (by norm_num) hs)
  refine hb.congr (by
    filter_upwards [hr0] with p hp
    simp only [Function.uncurry]
    exact hkey p hp)

/-- **Box integrability of `∂_z²Ψ·sinθcos²θ`.** -/
theorem box_pzIter2 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {s z : ℝ} (hs : 0 < s)
    (hsz : s ≤ z) :
    Integrable (Function.uncurry (fun r θ : ℝ =>
      Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hr0 := ae_fst_ne_zero (s := s) (z := z) hs
  have hsm : ContinuousOn (Function.uncurry (fun r θ : ℝ =>
      Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ)) Work.FTS.EllipticEst.Q0 :=
    ((hΨ.pzIter 2).continuousOn).mul ((continuous_sinCos2.comp continuous_snd).continuousOn)
  have hkey : ∀ p : ℝ × ℝ, p.1 ≠ 0 →
      p.1 * Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 / p.1
        = Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2 := by
    intro p hp
    field_simp
  have hae : AEStronglyMeasurable (Function.uncurry (fun r θ : ℝ =>
      r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ / r))
      ((volume.restrict (Set.Ioc s z)).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.FTS.EllipticEst.aesm_uncurry_restrict_open
      (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 Ψ p.1 p.2 * Work.Elliptic.sinCos2 p.2)
      hsm hs.le).congr (by
        filter_upwards [hr0] with p hp
        simp only [Function.uncurry]
        exact (hkey p hp).symm)
  -- the fibre pointwise bound `|r ∂_z²Ψ| ≤ (|D_z²Ψ| + |D_zΨ|)·s⁻¹`
  have hpt : ∀ r ∈ Set.Ioc s z, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |r * Work.Spaces.pzIter 2 Ψ r θ| ≤ (|Work.Spaces.DzIter 2 Ψ r θ|
        + |Work.Spaces.Dz Ψ r θ|) * s⁻¹ := by
    intro r hr θ hθ
    have hr0' : 0 < r := lt_trans hs hr.1
    have hid := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open Ψ hΨ hr0' hθ
    have h1 : r * Work.Spaces.pzIter 2 Ψ r θ
        = (Work.Spaces.DzIter 2 Ψ r θ - Work.Spaces.Dz Ψ r θ) / r := by
      rw [← hid]
      field_simp
    rw [h1, abs_div, abs_of_pos hr0']
    calc |Work.Spaces.DzIter 2 Ψ r θ - Work.Spaces.Dz Ψ r θ| / r
        ≤ (|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|) / r :=
          div_le_div_of_nonneg_right (abs_sub _ _) (le_of_lt hr0')
      _ = (|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|) * r⁻¹ := by
          rw [div_eq_mul_inv]
      _ ≤ (|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|) * s⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hs (le_of_lt hr.1)) (by positivity)
  -- the `D_z`-form of the `i = 1` slice integrability
  have hm2 : ∀ r : ℝ, 0 < r → IntegrableOn (fun θ : ℝ =>
      |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    intro r hr
    exact (slice_abs_integrableOn hΨ hB 1 (by norm_num) hr).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        show |Work.Spaces.DzIter 1 Ψ r θ| * Work.Elliptic.sinCos2 θ
          = |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ
        rfl))
  -- the majorant is integrable
  have hmaj : ∀ r ∈ Set.Ioc s z,
      IntegrableOn (fun θ : ℝ => s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ|
        * Work.Elliptic.sinCos2 θ + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ))
        Work.Spaces.Iθ := by
    intro r hr
    have hr0' : 0 < r := lt_trans hs hr.1
    exact ((slice_abs_integrableOn hΨ hB 2 (by norm_num) hr0').add (hm2 r hr0')).const_mul s⁻¹
  have hfib : ∀ r ∈ Set.Ioc s z, IntegrableOn (fun θ : ℝ =>
      r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
    intro r hr
    have hr0' : 0 < r := lt_trans hs hr.1
    refine Integrable.mono' (hmaj r hr) ?_ ?_
    · exact ((hΨ.aesm_slice_pzIter 2 hr0').const_mul r).mul
        continuous_sinCos2.aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc,
        Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hpt r hr θ hθ)]
        with θ hθ hb
      show ‖r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ‖
        ≤ s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
            + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg hθ)]
      calc |r * Work.Spaces.pzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
          ≤ ((|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|) * s⁻¹)
              * Work.Elliptic.sinCos2 θ := mul_le_mul_of_nonneg_right hb (sinCos2_nonneg hθ)
        _ = s⁻¹ * ((|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|)
              * Work.Elliptic.sinCos2 θ) := by ring
        _ = s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
              + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ) := by ring
  have hle : ∀ r ∈ Set.Ioc s z, ∫ θ in Work.Spaces.Iθ,
      |r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ|
        ≤ s⁻¹ * (Bnd Ψ 2 r + Bnd Ψ 1 r) := by
    intro r hr
    have hr0' : 0 < r := lt_trans hs hr.1
    have hb1 := slice_bound hΨ hB 2 (by norm_num) r hr0'
    have hb2 : ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ
        ≤ Bnd Ψ 1 r := by
      have h := slice_bound hΨ hB 1 (by norm_num) r hr0'
      have heq : (∫ θ in Work.Spaces.Iθ, |Work.Spaces.DzIter 1 Ψ r θ|
            * Work.Elliptic.sinCos2 θ)
          = ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ :=
        MeasureTheory.integral_congr_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
            show |Work.Spaces.DzIter 1 Ψ r θ| * Work.Elliptic.sinCos2 θ
              = |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ
            rfl))
      rwa [heq] at h
    have hm1 := slice_abs_integrableOn hΨ hB 2 (by norm_num) hr0'
    have hm2' := hm2 r hr0'
    have hmono : ∫ θ in Work.Spaces.Iθ, |r * Work.Spaces.pzIter 2 Ψ r θ
          * Work.Elliptic.sinCos2 θ|
        ≤ ∫ θ in Work.Spaces.Iθ, s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ|
            * Work.Elliptic.sinCos2 θ + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ) := by
      refine integral_mono_ae ?_ (hmaj r hr) ?_
      · refine (hfib r hr).norm.congr (Filter.Eventually.of_forall fun θ => ?_)
        show ‖r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ‖
          = |r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ|
        rw [Real.norm_eq_abs]
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc,
          Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hpt r hr θ hθ)]
          with θ hθ hb
        show |r * Work.Spaces.pzIter 2 Ψ r θ * Work.Elliptic.sinCos2 θ|
          ≤ s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
              + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ)
        rw [abs_mul, abs_of_nonneg (sinCos2_nonneg hθ)]
        calc |r * Work.Spaces.pzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
            ≤ ((|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|) * s⁻¹)
                * Work.Elliptic.sinCos2 θ := mul_le_mul_of_nonneg_right hb (sinCos2_nonneg hθ)
          _ = s⁻¹ * ((|Work.Spaces.DzIter 2 Ψ r θ| + |Work.Spaces.Dz Ψ r θ|)
                * Work.Elliptic.sinCos2 θ) := by ring
          _ = s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ
                + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ) := by ring
    have hEq : (∫ θ in Work.Spaces.Iθ, s⁻¹ * (|Work.Spaces.DzIter 2 Ψ r θ|
          * Work.Elliptic.sinCos2 θ + |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ))
        = s⁻¹ * ((∫ θ in Work.Spaces.Iθ,
              |Work.Spaces.DzIter 2 Ψ r θ| * Work.Elliptic.sinCos2 θ)
            + ∫ θ in Work.Spaces.Iθ, |Work.Spaces.Dz Ψ r θ| * Work.Elliptic.sinCos2 θ) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hm1 hm2']
    rw [hEq] at hmono
    refine le_trans hmono ?_
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (le_of_lt hs))
    linarith [hb1, hb2]
  have hb := ((Bnd_integrableOn hΨ hB 2 (by norm_num) (b := z) hs).add
      (Bnd_integrableOn hΨ hB 1 (by norm_num) (b := z) hs)).const_mul s⁻¹
  refine (integrable_uncurry_div_of_fibre_bound hs hsz hae hfib hle hb).congr ?_
  filter_upwards [hr0] with p hp
  simp only [Function.uncurry]
  exact hkey p hp

/-! ## §3 The integrated moment chain -/

/-- The chain rule for the moment of `Ψ` itself. -/
theorem Fstar_sub_pz {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {s z : ℝ} (hs : 0 < s)
    (hsz : s ≤ z) :
    Work.Elliptic.Fstar Ψ z - Work.Elliptic.Fstar Ψ s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pz Ψ) r :=
  Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz hΨ hs hsz
    (slice_integrableOn hΨ hB 0 (by norm_num) hs)
    (slice_integrableOn hΨ hB 0 (by norm_num) (lt_of_lt_of_le hs hsz))
    (box_pz hΨ hB hs hsz)

/-- The chain rule for the moment of `∂_zΨ`. -/
theorem Fstar_sub_pzIter2 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {s z : ℝ} (hs : 0 < s)
    (hsz : s ≤ z) :
    Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z - Work.Elliptic.Fstar (Work.Spaces.pz Ψ) s
      = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) r := by
  have hz : 0 < z := lt_of_lt_of_le hs hsz
  exact Work.EllipticEst.H2W.Fstar_sub_eq_integral_pz hΨ.pz hs hsz
    (slice_abs_pz_integrableOn hΨ hB hs) (slice_abs_pz_integrableOn hΨ hB hz)
    (box_pzIter2 hΨ hB hs hsz)

end Work.FTS.EllipticEst.H2W.PsiSlices
