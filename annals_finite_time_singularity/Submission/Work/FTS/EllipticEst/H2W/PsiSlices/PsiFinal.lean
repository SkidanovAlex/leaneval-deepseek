/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.PsiSlices.PsiFinal`: the angular moments of the radially differentiated data vanish a.e.

For a datum of the weak class `TT.EllWeakPos α 2 F Ψ` (the moment conditions are only known
almost everywhere in `z`, and `Ψ` is smooth on the *open* quadrant only), this module proves

  `F_*(D_z^j F) = 0` a.e.  and  `F_*(D_z^j Ψ) = 0` a.e.   for every `j ≤ 2`,

i.e. the a.e. form of the solvability condition for the radially differentiated data.  Both
halves are instances of the integrated moment chain `ae_eq_zero_of_moment_chain`:

* for `Ψ`, the chain rules are `Fstar_sub_pz` / `Fstar_sub_pzIter2` (the box integrability being
  supplied by `box_pz` / `box_pzIter2`), and the shift from `∂_z^jΨ` to `D_z^jΨ` is the
  product rule `D_z²Ψ = D_zΨ + z²∂_z²Ψ`;
* for `F`, the chain rule is `Cert.GbarSin.FstarDzIter_chain_open` (`D_z^jF` commutes with `F_*`
  up to the factor `1/r`), with the local integrability from `integrableOn_Bmom_div`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Interval.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.PsiBox
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.PsiMoments
import Submission.Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_mixed_open
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open

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

/-! ## §4 The angular moments of `∂_zΨ` and `∂_z²Ψ` -/

/-- From the box integrability of `g·sinθcos²θ`, the moment `F_*(g)` is interval integrable. -/
theorem intervalIntegrable_Fstar_of_box {g : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hbox : Integrable (Function.uncurry (fun r θ : ℝ => g r θ * Work.Elliptic.sinCos2 θ))
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict Work.Spaces.Iθ))) :
    IntervalIntegrable (Work.Elliptic.Fstar g) volume a b := by
  have hint : IntegrableOn (Work.Elliptic.Fstar g) (Set.Ioc a b) := by
    have h := hbox.integral_prod_left
    refine h.congr (Filter.Eventually.of_forall fun r => ?_)
    show (∫ θ, Function.uncurry (fun r θ : ℝ => g r θ * Work.Elliptic.sinCos2 θ) (r, θ)
        ∂(volume.restrict Work.Spaces.Iθ)) = Work.Elliptic.Fstar g r
    rw [Work.Elliptic.Fstar]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => rfl)
  have hIcc : IntegrableOn (Work.Elliptic.Fstar g) (Set.Icc a b) := by
    change Integrable (Work.Elliptic.Fstar g) (volume.restrict (Set.Icc a b))
    rw [← MeasureTheory.Measure.restrict_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))]
    exact hint
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
  exact hIcc

/-- `F_*(∂_zΨ) = 0` a.e., from `F_* Ψ = 0` a.e. -/
theorem Fstar_pz_ae_zero {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (h0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar Ψ z = 0) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z = 0 :=
  ae_eq_zero_of_moment_chain (W := Work.Elliptic.Fstar Ψ)
    (V := Work.Elliptic.Fstar (Work.Spaces.pz Ψ))
    (fun s t hs hst => Fstar_sub_pz hΨ hB hs hst) h0
    (fun a b ha hab => intervalIntegrable_Fstar_of_box hab (box_pz hΨ hB ha hab.le))

/-- `F_*(∂_z²Ψ) = 0` a.e., from `F_*(∂_zΨ) = 0` a.e. -/
theorem Fstar_pzIter2_ae_zero {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {α : ℝ}
    (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ))
    (h0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar (Work.Spaces.pz Ψ) z = 0) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ) z = 0 :=
  ae_eq_zero_of_moment_chain (W := Work.Elliptic.Fstar (Work.Spaces.pz Ψ))
    (V := Work.Elliptic.Fstar (Work.Spaces.pzIter 2 Ψ))
    (fun s t hs hst => Fstar_sub_pzIter2 hΨ hB hs hst) h0
    (fun a b ha hab => intervalIntegrable_Fstar_of_box hab (box_pzIter2 hΨ hB ha hab.le))

/-! ## §5 The shift from `∂_z^j` to `D_z^j` -/

/-- `F_*(D_z f)(z) = z·F_*(∂_z f)(z)`. -/
theorem Fstar_Dz_eq (f : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Elliptic.Fstar (Work.Spaces.Dz f) z
      = z * Work.Elliptic.Fstar (Work.Spaces.pz f) z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (fun θ : ℝ => Work.Spaces.Dz f z θ * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => z * (Work.Spaces.pz f z θ * Work.Elliptic.sinCos2 θ) from by
    funext θ; simp only [Work.Spaces.Dz]; ring]
  rw [MeasureTheory.integral_const_mul]

/-- The product rule for `D_z²`: `D_z²f = z ∂_zf + z²∂_z²f` on the open quadrant. -/
theorem DzIter_two_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 f z θ
      = z * Work.Spaces.pz f z θ + z ^ 2 * Work.Spaces.pzIter 2 f z θ := by
  have hfd : HasDerivAt (fun z' : ℝ => z' * Work.Spaces.pz f z' θ)
      (Work.Spaces.pz f z θ + z * Work.Spaces.pzIter 2 f z θ) z := by
    have h1 : HasDerivAt (fun z' : ℝ => z') 1 z := hasDerivAt_id z
    have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz f z' θ)
        (Work.Spaces.pzIter 2 f z θ) z := by
      have h := hf.hasDerivAt_slice_pzIter 1 hθ hz
      simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h
    have h := h1.mul h2
    convert h using 1
    ring
  have hderiv : Work.Spaces.pz (Work.Spaces.Dz f) z θ
      = deriv (fun z' : ℝ => z' * Work.Spaces.pz f z' θ) z := rfl
  show z * Work.Spaces.pz (Work.Spaces.Dz f) z θ
    = z * Work.Spaces.pz f z θ + z ^ 2 * Work.Spaces.pzIter 2 f z θ
  rw [hderiv, hfd.deriv]
  ring

/-- The moment of `D_z²` in terms of the moments of `∂_z` and `∂_z²`. -/
theorem Fstar_DzIter_two_eq {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) {z : ℝ}
    (hz : 0 < z)
    (hsl1 : IntegrableOn (fun θ : ℝ => Work.Spaces.pz f z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hsl2 : IntegrableOn (fun θ : ℝ => Work.Spaces.pzIter 2 f z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (Work.Spaces.DzIter 2 f) z
      = z * Work.Elliptic.Fstar (Work.Spaces.pz f) z
        + z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 f) z := by
  have hae : (fun θ : ℝ => Work.Spaces.DzIter 2 f z θ * Work.Elliptic.sinCos2 θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => z * (Work.Spaces.pz f z θ * Work.Elliptic.sinCos2 θ)
        + z ^ 2 * (Work.Spaces.pzIter 2 f z θ * Work.Elliptic.sinCos2 θ)) := by
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => by
      show Work.Spaces.DzIter 2 f z θ * Work.Elliptic.sinCos2 θ
        = z * (Work.Spaces.pz f z θ * Work.Elliptic.sinCos2 θ)
          + z ^ 2 * (Work.Spaces.pzIter 2 f z θ * Work.Elliptic.sinCos2 θ)
      rw [DzIter_two_eq hf hz hθ]; ring)] with θ hθ
    exact hθ
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, Work.Elliptic.Fstar,
    MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_add (hsl1.const_mul z) (hsl2.const_mul (z ^ 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- `θ ↦ (∂_z²Ψ)(u,θ)·sinθcos²θ` is integrable on `Iθ` for `u > 0`. -/
theorem slice_pzIter2_integrableOn {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {α : ℝ} (hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ)) {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun θ : ℝ => Work.Spaces.pzIter 2 Ψ u θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  have hu2 : (0 : ℝ) < u ^ 2 := by positivity
  have h1 := slice_abs_integrableOn hΨ hB 2 (by norm_num) hu
  have h2 : IntegrableOn (fun θ : ℝ =>
      |Work.Spaces.Dz Ψ u θ| * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (slice_abs_integrableOn hΨ hB 1 (by norm_num) hu).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        show |Work.Spaces.DzIter 1 Ψ u θ| * Work.Elliptic.sinCos2 θ
          = |Work.Spaces.Dz Ψ u θ| * Work.Elliptic.sinCos2 θ
        rfl))
  have h3 : IntegrableOn (fun θ : ℝ => (|Work.Spaces.DzIter 2 Ψ u θ|
      + |Work.Spaces.Dz Ψ u θ|) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    (h1.add h2).congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => by
        show |Work.Spaces.DzIter 2 Ψ u θ| * Work.Elliptic.sinCos2 θ
            + |Work.Spaces.Dz Ψ u θ| * Work.Elliptic.sinCos2 θ
          = (|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|)
            * Work.Elliptic.sinCos2 θ
        ring))
  have hmaj : IntegrableOn (fun θ : ℝ => (|Work.Spaces.DzIter 2 Ψ u θ|
      + |Work.Spaces.Dz Ψ u θ|) * Work.Elliptic.sinCos2 θ * (u ^ 2)⁻¹) Work.Spaces.Iθ :=
    (h3.const_mul (u ^ 2)⁻¹).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => by
        show (u ^ 2)⁻¹ * ((|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|)
            * Work.Elliptic.sinCos2 θ)
          = (|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|)
            * Work.Elliptic.sinCos2 θ * (u ^ 2)⁻¹
        ring))
  refine Integrable.mono' hmaj ?_ ?_
  · exact ((hΨ.aesm_slice_pzIter 2 hu).mul continuous_sinCos2.aestronglyMeasurable)
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc,
      Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hθ)] with θ hθ hθmem
    have hid := Work.FTS.EllipticEst.AgmonSlice.zsq_pzIter2_eq_open Ψ hΨ hu hθmem
    have hdiv : Work.Spaces.pzIter 2 Ψ u θ
        = (Work.Spaces.DzIter 2 Ψ u θ - Work.Spaces.Dz Ψ u θ) / u ^ 2 := by
      rw [← hid]
      field_simp
    show ‖Work.Spaces.pzIter 2 Ψ u θ * Work.Elliptic.sinCos2 θ‖
      ≤ (|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|)
        * Work.Elliptic.sinCos2 θ * (u ^ 2)⁻¹
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sinCos2_nonneg hθ), hdiv, abs_div,
      abs_of_pos hu2]
    calc |Work.Spaces.DzIter 2 Ψ u θ - Work.Spaces.Dz Ψ u θ| / u ^ 2
          * Work.Elliptic.sinCos2 θ
        ≤ (|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|) / u ^ 2
            * Work.Elliptic.sinCos2 θ :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (abs_sub _ _) (le_of_lt hu2))
            (sinCos2_nonneg hθ)
      _ = (|Work.Spaces.DzIter 2 Ψ u θ| + |Work.Spaces.Dz Ψ u θ|)
            * Work.Elliptic.sinCos2 θ * (u ^ 2)⁻¹ := by ring

/-! ## §6 The a.e. moments of the `Ψ`-slices -/

/-- **The angular moment of `D_z^jΨ` vanishes a.e. for `j ≤ 2`.** -/
theorem Fstar_DzIter_Psi_ae (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter j Ψ) z = 0 := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.Spaces.HkMem α 2 (Work.Spaces.pthIter 2 Ψ) := h.memB
  have hPsi0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar Ψ z = 0 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h.orthPsi
  have hA := Fstar_pz_ae_zero hΨ hB hPsi0
  have hA2 := Fstar_pzIter2_ae_zero hΨ hB hA
  intro j hj
  interval_cases j
  · exact hPsi0
  · filter_upwards [hA] with z hz
    show Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0
    rw [show Work.Spaces.DzIter 1 Ψ = Work.Spaces.Dz Ψ from rfl, Fstar_Dz_eq, hz, mul_zero]
  · filter_upwards [hA, hA2, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hz2 hzpos
    show Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z = 0
    rw [Fstar_DzIter_two_eq hΨ hzpos (slice_abs_pz_integrableOn hΨ hB hzpos)
      (slice_pzIter2_integrableOn hΨ hB hzpos), hz, hz2]
    ring

/-! ## §7 The a.e. moments of the `F`-slices -/

/-- **The angular moment of `D_z^jF` vanishes a.e. for `j ≤ 2`.** -/
theorem Fstar_DzIter_F_ae (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ j : ℕ, j ≤ 2 → ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z = 0 := by
  have hF : Work.FTS.EllipticEst.SmoothOpen F :=
    (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak h 0).1
  have hmem : Work.Spaces.HkMem α 2 F := h.memF
  -- the interval integrability of the divided moments
  have hInt : ∀ j : ℕ, j ≤ 2 → ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r)
        volume a b := by
    intro j hj a b ha hab
    have h1 := Work.FTS.EllipticEst.integrableOn_Bmom_div α 2 hF hmem j hj a b ha hab
    have h2 : IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r)
        (Set.Icc a b) :=
      h1.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => by
        show Work.FTS.EllipticEst.Bmom F j r / r
          = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) r / r
        rw [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter]))
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact h2
  -- `j = 0`
  have h0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar F z = 0 :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h.orthF
  -- `j = 1`
  have h1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0 := by
    have hraw := ae_eq_zero_of_moment_chain
      (W := Work.Elliptic.Fstar F)
      (V := fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) r / r)
      (fun s t hs hst => Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF hmem
        0 (by norm_num) hs hst)
      h0 (hInt 1 (by norm_num))
    filter_upwards [hraw, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    rw [div_eq_zero_iff] at hz
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' hzpos.ne'
  -- `j = 2`
  have h2 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 := by
    have hraw := ae_eq_zero_of_moment_chain
      (W := Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F))
      (V := fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) r / r)
      (fun s t hs hst => Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open α 2 F hF hmem
        1 (by norm_num) hs hst)
      h1 (hInt 2 (by norm_num))
    filter_upwards [hraw, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
      with z hz hzpos
    rw [div_eq_zero_iff] at hz
    rcases hz with h' | h'
    · exact h'
    · exact absurd h' hzpos.ne'
  intro j hj
  interval_cases j
  · simpa using h0
  · exact h1
  · exact h2

end Work.FTS.EllipticEst.H2W.PsiSlices
