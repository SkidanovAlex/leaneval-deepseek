/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `γ`-weighted angular slice of the `(1,1)`-mixed slot, uniformly in `z`

`Work.FTS.StrongPersist.H6Row6Gam.gamSliceSup11`: for a datum `f` of the open class
(`Work.FTS.EllipticEst.SmoothOpen`) that lies honestly in `ℋ⁴` (`Work.Spaces.HkMem α 4 f`) and
every `z > 0`,

  `∫_{Iθ} sin(2θ)^{-γ} · (D_z D_θ f (z,θ))²  ≤  3 · |f|²_{ℋ⁴}`.

The auxiliary `mixed_slice_z_le_three` below exposes the argument of the delivered
`Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform` (whose statement carries only an
*existential* constant `C`) at the literal constant `3`: the one-dimensional window form of the
radial Hardy inequality (`Work.FTS.TransportS.half_line_window_bound`), applied to the angular
slice `x ↦ D_z^jD_θ^i f (x,σ)` whose `z`-derivative is the *next* mixed slot `D_z^{j+1}D_θ^i f`,
gives, after multiplication by `sin(2σ)^{-γ} ≥ 0` and integration in `σ`, the coefficient
`2 + 2/R₀`; both window integrands are dominated by `HkIntegrand α 4 f` (the `(j+1,i)`-slot via
`Wt_sq_eq` and `sq_le_HkIntegrand_mixed`, and the `(j,i)`-slot itself via `1 ≤ w`), Tonelli
(`sda_HkSqSwap_open`) identifies the `σ`-integral of the dominating function with `HkSq α 4 f`,
and `R₀ = max z 2` makes the coefficient `≤ 3`.  The requested slot is the case `(j,i) = (1,1)`,
which satisfies `i + j = 2 ≤ 3`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzAux.sup_dz_ang_le
import Submission.Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6Gam

set_option maxHeartbeats 4000000

/-- **The `θ`-slice of a mixed slot, uniformly in `z`, with the constant exposed.**  For a datum
`f` of the open class lying in `ℋ⁴`, and for `1 ≤ i`, `i + j ≤ 3`, the `γ`-weighted angular slice
of `D_z^j D_θ^i f` at any `z > 0` is at most `3 · |f|²_{ℋ⁴}`.  This is
`Work.FTS.TransportS.T2SupB2.mixed_slice_z_uniform` with the constant `C = 3` exposed. -/
theorem mixed_slice_z_le_three :
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 3 → ∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ 3 * Work.Spaces.HkSq α 4 f := by
  intro α f _hα _hα1 hF hmem j i hi hij z hz
  obtain ⟨hswap, hGint, hGslice⟩ :=
    Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  -- almost every angle is interior
  have haeθ : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), σ ∈ Set.Ioo 0 (π / 2) := by
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iθ) measurableSet_Icc]
    filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
      (b := π / 2)] with σ h
    exact fun hmem' => h.mpr hmem'
  -- the window bound, for every radius `R₀ ≥ z`
  have hbound : ∀ R₀ : ℝ, z ≤ R₀ →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by
    intro R₀ hR
    have hRpos : 0 < R₀ := lt_of_lt_of_le hz hR
    have hz2R : z ≤ 2 * R₀ := by linarith
    have hR2R : R₀ ≤ 2 * R₀ := by linarith
    have hσbound : ∀ σ : ℝ, σ ∈ Set.Ioo 0 (π / 2) →
        IntegrableOn (fun s => Work.Spaces.HkIntegrand α 4 f s σ) Work.Spaces.Iz →
        (Work.Spaces.mixed j i f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          ≤ (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
      intro σ hσ hσint
      have hsinσ : 0 < Real.sin (2 * σ) := Work.FTS.TransportS.T2SupB2.sin_two_pos_of_mem_Ioo hσ
      have hlam : 0 ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) :=
        Real.rpow_nonneg (le_of_lt hsinσ) _
      -- the hypotheses of the one-dimensional window inequality
      have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
          HasDerivAt (fun x : ℝ => Work.Spaces.mixed j i f x σ)
            (Work.Spaces.pz (Work.Spaces.mixed j i f) x σ) x :=
        fun x hx => (hF.mixed j i).hasDerivAt_slice hσ (lt_of_lt_of_le hz hx.1)
      have hcont : ContinuousOn (fun x : ℝ => Work.Spaces.mixed j i f x σ)
          (Set.Icc R₀ (2 * R₀)) :=
        ((hF.mixed j i).curry_z hσ).continuousOn.mono
          (fun x hx => lt_of_lt_of_le hRpos hx.1)
      have hcont' : ContinuousOn
          (fun x : ℝ => Work.Spaces.pz (Work.Spaces.mixed j i f) x σ)
          (Set.Icc z (2 * R₀)) :=
        (((hF.mixed j i).pz).curry_z hσ).continuousOn.mono
          (fun x hx => lt_of_lt_of_le hz hx.1)
      have hint : IntegrableOn
          (fun x : ℝ => (Work.Spaces.mixed j i f x σ) ^ 2) (Set.Icc R₀ (2 * R₀)) :=
        (hcont.pow 2).integrableOn_Icc
      have hwin := Work.FTS.TransportS.half_line_window_bound
        (h := fun x : ℝ => Work.Spaces.mixed j i f x σ)
        (h' := fun x : ℝ => Work.Spaces.pz (Work.Spaces.mixed j i f) x σ)
        hz hR hderiv hcont hcont' hint
      -- continuity of the relevant slices
      have hcontW : ContinuousOn
          (fun x : ℝ => x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x)
          (Set.Icc z (2 * R₀)) := by
        refine ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_
        refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) ?_
        intro x hx
        exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hz hx.1))
      have hHkcont : ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.Icc z (2 * R₀)) := by
        have hmap : MapsTo (fun x : ℝ => (x, σ)) (Set.Icc z (2 * R₀))
            Work.FTS.EllipticEst.Q0 :=
          fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨lt_of_lt_of_le hz hx.1, hσ.1, hσ.2⟩
        have hc := (hF.continuousOn_HkIntegrand α 4).comp
          (continuousOn_id.prodMk continuousOn_const) hmap
        simpa only [Function.comp_def, id_eq] using hc
      -- interval integrability
      have hIntL1 : IntervalIntegrable
          (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2)
            (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact ContinuousOn.mul continuousOn_const (hcontW.pow 2)
      have hIntR1 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume z (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hz2R]
        exact hHkcont
      have hIntL2 : IntervalIntegrable
          (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2) volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2) (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact ContinuousOn.mul continuousOn_const (hcont.pow 2)
      have hIntR2 : IntervalIntegrable (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          volume R₀ (2 * R₀) := by
        refine (show ContinuousOn (fun x : ℝ => Work.Spaces.HkIntegrand α 4 f x σ)
          (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
        rw [Set.uIcc_of_le hR2R]
        exact hHkcont.mono (fun x hx => ⟨le_trans hR hx.1, hx.2⟩)
      -- the pointwise domination of the two window integrands by the `ℋ⁴`-integrand
      have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ * Work.Spaces.w x) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le hz hx.1
        have hcomm : x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
            = Work.Spaces.mixed (j + 1) i f x σ := rfl
        rw [hcomm]
        have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed (j + 1) i f x σ * Work.Spaces.w x) ^ 2
            = (Work.Spaces.mixed (j + 1) i f x σ * Work.Spaces.w x) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by ring
        rw [h1]
        exact Work.FTS.TransportS.T2SupB2.mixed_succ_mul_w_sq_le_HkIntegrand hx0 hσ j i hi (by omega)
      have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2
            = (Work.Spaces.mixed j i f x σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by ring
        rw [h1]
        exact Work.FTS.TransportS.T2SupB2.mixed_sq_le_HkIntegrand (lt_of_lt_of_le hRpos hx.1) hσ j i hi (by omega)
      -- the two window integrals are dominated by the full radial integral
      have hbigA : ∫ x in z..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hz2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
      have hbigB : ∫ x in R₀..(2 * R₀), Work.Spaces.HkIntegrand α 4 f x σ
          ≤ ∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ := by
        rw [intervalIntegral.integral_of_le hR2R]
        refine MeasureTheory.setIntegral_mono_set hσint
          (Eventually.of_forall fun x => Work.Spaces.HkIntegrand_nonneg α 4 f x σ) ?_
        exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
      have hmonoA := intervalIntegral.integral_mono_on hz2R hIntL1 hIntR1 hptA
      have hmonoB := intervalIntegral.integral_mono_on hR2R hIntL2 hIntR2 hptB
      -- the weight factors out of the interval integrals
      have hAeq : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                * Work.Spaces.w x) ^ 2)
          = ∫ x in z..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                * Work.Spaces.w x) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      have hBeq : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (∫ x in R₀..(2 * R₀), (Work.Spaces.mixed j i f x σ) ^ 2)
          = ∫ x in R₀..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f x σ) ^ 2 :=
        (intervalIntegral.integral_const_mul _ _).symm
      calc (Work.Spaces.mixed j i f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f z σ) ^ 2 := by ring
        _ ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
              * (2 * (∫ x in z..(2 * R₀),
                    (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                      * Work.Spaces.w x) ^ 2)
                + (2 / R₀) * ∫ x in R₀..(2 * R₀),
                    (Work.Spaces.mixed j i f x σ) ^ 2) :=
              mul_le_mul_of_nonneg_left hwin hlam
        _ = 2 * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                * (∫ x in z..(2 * R₀), (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                    * Work.Spaces.w x) ^ 2))
              + (2 / R₀) * ((Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                * (∫ x in R₀..(2 * R₀), (Work.Spaces.mixed j i f x σ) ^ 2)) := by ring
        _ = 2 * (∫ x in z..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                * (x * Work.Spaces.pz (Work.Spaces.mixed j i f) x σ
                    * Work.Spaces.w x) ^ 2)
              + (2 / R₀) * (∫ x in R₀..(2 * R₀), (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
                  * (Work.Spaces.mixed j i f x σ) ^ 2) := by
              rw [hAeq, hBeq]
        _ ≤ 2 * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ)
              + (2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) :=
              add_le_add (mul_le_mul_of_nonneg_left (le_trans hmonoA hbigA) (by norm_num))
                (mul_le_mul_of_nonneg_left (le_trans hmonoB hbigB) (by positivity))
        _ = (2 + 2 / R₀) * (∫ s in Work.Spaces.Iz, Work.Spaces.HkIntegrand α 4 f s σ) := by
              ring
    -- integrate the a.e. pointwise bound
    have hle : (fun σ : ℝ => (Work.Spaces.mixed j i f z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
          Work.Spaces.HkIntegrand α 4 f s σ) := by
      filter_upwards [hGslice, haeθ] with σ hσint hσθ
      exact hσbound σ hσθ hσint
    have hfae : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun σ : ℝ => (Work.Spaces.mixed j i f z σ) ^ 2
          * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
          (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hσ.1],
            by linarith [hσ.2, Real.pi_pos]⟩) _)
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
        ≤ ∫ σ in Work.Spaces.Iθ, (2 + 2 / R₀) * ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ :=
          integral_mono_of_nonneg hfae (hGint.const_mul _) hle
      _ = (2 + 2 / R₀) * (∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            Work.Spaces.HkIntegrand α 4 f s σ) := MeasureTheory.integral_const_mul _ _
      _ = (2 + 2 / R₀) * Work.Spaces.HkSq α 4 f := by rw [hswap]
  -- take `R₀ = max z 2`, so that the coefficient is at most `3`
  have hzmax : z ≤ max z 2 := le_max_left z 2
  have hbnd := hbound (max z 2) hzmax
  have hpos : 0 < max z 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right z 2)
  have h2max : 2 ≤ max z 2 := le_max_right z 2
  have hcoef : 2 + 2 / max z 2 ≤ 3 := by
    have h : 2 / max z 2 ≤ 1 := by
      rw [div_le_one hpos]
      exact h2max
    linarith
  calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed j i f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ (2 + 2 / max z 2) * Work.Spaces.HkSq α 4 f := hbnd
    _ ≤ 3 * Work.Spaces.HkSq α 4 f :=
        mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α 4 f)

theorem gamSliceSup11 : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    ∀ z : ℝ, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.mixed 1 1 f z θ) ^ 2) ≤ 3 * Work.Spaces.HkSq α 4 f := by
  intro α f hα hα1 hF hmem z hz
  have h := mixed_slice_z_le_three α f hα hα1 hF hmem 1 1 (by norm_num) (by norm_num) z hz
  have hcomm : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.mixed 1 1 f z θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 1 1 f z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)
  rw [hcomm]
  exact h

end Work.FTS.StrongPersist.H6Row6Gam
