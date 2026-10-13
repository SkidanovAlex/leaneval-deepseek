/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ`-slice of a mixed slot is uniformly bounded in `z`

For a datum `f` of the open class (`Work.FTS.EllipticEst.SmoothOpen`) which lies honestly in
`ℋ⁴` (`Work.Spaces.HkMem α 4 f`), and for a *mixed* slot `D_z^j D_θ^i f` with `i ≥ 1`,
`i + j ≤ 3`,

  `∫_{Iθ} (D_z^j D_θ^i f(z,θ))² · sin(2θ)^{-γ}  ≤  C · |f|²_{ℋ⁴}`  for every `z > 0`,

with a universal constant `C` (`C = 3` works).  This is the mixed-slot companion of
`Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le` (which is the pure `D_z`-slot with the
weight `sin(2θ)^{-η}`) and of `Work.FTS.TransportS.SupDzAux.sup_dz_ang_le` (the `i = 1` case with
the weight `sin(2θ)^{2-γ}`).

ROUTE (verbatim the scheme of `supDz_weighted_avg_le`, with the mixed slot in place of `D_z^b f`):

1. For fixed angle `σ ∈ (0,π/2)`, the one-dimensional window form of the radial Hardy inequality
   (`Work.FTS.TransportS.half_line_window_bound`) applied to the slice
   `h := fun x => mixed j i f x σ`, `h' := fun x => ∂_z(mixed j i f) x σ` gives, for `z ≤ R₀`,

     `h(z)² ≤ 2 ∫_z^{2R₀}(x h'(x) w(x))² + (2/R₀) ∫_{R₀}^{2R₀} h²`.

   The point is the identity `x · ∂_z(D_z^j D_θ^i f) = D_z^{j+1}D_θ^i f` (definitional: `D_z = z∂_z`
   and the `z`-derivative does not touch `D_θ^i`), so `x h' x` is the *next* mixed slot.

2. Multiply by `sin(2σ)^{-γ} ≥ 0` and integrate in `σ`.  Both window integrands are dominated by
   the `ℋ⁴`-integrand:
   * `sin(2σ)^{-γ}·(D_z^{j+1}D_θ^i f · w)² = (D_z^{j+1}D_θ^i f · Wt α)² ≤ HkIntegrand α 4 f`
     (`Wt_sq_eq` and `sq_le_HkIntegrand_mixed`, using `i + (j+1) ≤ 4` — this is where the
     hypothesis `i + j ≤ 3` is used, *no* derivative is lost);
   * `sin(2σ)^{-γ}·(D_z^jD_θ^i f)² ≤ (D_z^jD_θ^i f · Wt α)² ≤ HkIntegrand α 4 f`, using `1 ≤ w`
     on `z > 0`.

3. The `σ`-integral of the dominating function is `(2 + 2/R₀)·HkSq α 4 f` (Tonelli,
   `Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open`), and taking `R₀ = max z 2` gives
   `2 + 2/R₀ ≤ 3`.

Every declaration here is fully proved: the module rests on
`[propext, Classical.choice, Quot.sound]` only.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.TransportS.SupDzWeighted.supDz_weighted_avg_le
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.FTS.TransportS.t2SupF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2SupB2

set_option maxHeartbeats 1600000

/-! ## Elementary facts -/

/-- `sin(2σ) > 0` for `σ` in the interior of `Iθ`. -/
theorem sin_two_pos_of_mem_Ioo {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * σ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hσ.1]) (by linarith [hσ.2, Real.pi_pos])

/-! ## The pointwise domination by the `ℋ⁴`-integrand -/

/-- The next mixed slot, weighted by `w` and by `sin(2σ)^{-γ}`, is the `(i, j+1)` summand of
`HkIntegrand α 4 f`. -/
theorem mixed_succ_mul_w_sq_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {z σ : ℝ} (hz : 0 < z)
    (hσ : σ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) (hi1 : 1 ≤ i) (hij : i + (j + 1) ≤ 4) :
    (Work.Spaces.mixed (j + 1) i f z σ * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
  have hsin : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo hσ
  calc (Work.Spaces.mixed (j + 1) i f z σ * Work.Spaces.w z) ^ 2
        * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      = (Work.Spaces.mixed (j + 1) i f z σ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by ring
    _ = (Work.Spaces.mixed (j + 1) i f z σ) ^ 2 * (Work.Spaces.Wt α z σ) ^ 2 := by
        rw [Work.H2.T1Q.Wt_sq_eq α z σ hsin]
    _ = (Work.Spaces.mixed (j + 1) i f z σ * Work.Spaces.Wt α z σ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 f z σ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ i (j + 1) hi1 hij

/-- The mixed slot, weighted by `sin(2σ)^{-γ}`, is dominated by `HkIntegrand α 4 f` (because
`w ≥ 1` on `z > 0`). -/
theorem mixed_sq_le_HkIntegrand {α : ℝ} {f : ℝ → ℝ → ℝ} {z σ : ℝ} (hz : 0 < z)
    (hσ : σ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) (hi1 : 1 ≤ i) (hij : i + j ≤ 4) :
    (Work.Spaces.mixed j i f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ Work.Spaces.HkIntegrand α 4 f z σ := by
  have hsin : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo hσ
  have hw1 : (1 : ℝ) ≤ (Work.Spaces.w z) ^ 2 :=
    one_le_pow₀ (Work.FTS.TransportS.one_le_w hz)
  have hkey : (Work.Spaces.mixed j i f z σ) ^ 2
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)))
      = (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.Wt α z σ) ^ 2 := by
    rw [Work.H2.T1Q.Wt_sq_eq α z σ hsin]
  calc (Work.Spaces.mixed j i f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      ≤ (Work.Spaces.mixed j i f z σ) ^ 2
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact le_mul_of_one_le_left (Real.rpow_nonneg (le_of_lt hsin) _) hw1
    _ = (Work.Spaces.mixed j i f z σ) ^ 2 * (Work.Spaces.Wt α z σ) ^ 2 := hkey
    _ = (Work.Spaces.mixed j i f z σ * Work.Spaces.Wt α z σ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α 4 f z σ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z σ i j hi1 hij

/-! ## The main estimate -/

theorem mixed_slice_z_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ (j i : ℕ), 1 ≤ i → i + j ≤ 3 → ∀ z : ℝ, 0 < z →
        (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          ≤ C * Work.Spaces.HkSq α 4 f := by
  refine ⟨3, by norm_num, ?_⟩
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
      have hsinσ : 0 < Real.sin (2 * σ) := sin_two_pos_of_mem_Ioo hσ
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
        exact mixed_succ_mul_w_sq_le_HkIntegrand hx0 hσ j i hi (by omega)
      have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
          (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f x σ := by
        intro x hx
        have h1 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f x σ) ^ 2
            = (Work.Spaces.mixed j i f x σ) ^ 2
              * (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) := by ring
        rw [h1]
        exact mixed_sq_le_HkIntegrand (lt_of_lt_of_le hRpos hx.1) hσ j i hi (by omega)
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

end Work.FTS.TransportS.T2SupB2
