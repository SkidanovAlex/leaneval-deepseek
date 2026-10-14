import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.HkSq_terms
-- ===== merged: Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces
open Work.FTS.EllipticEst (SmoothOpen Q0 mem_Q0)

/-- Almost every angle of `Iθ` lies in the open interval `(0, π/2)`. -/
theorem ae_mem_Ioo_Iθ :
    ∀ᵐ σ ∂(volume.restrict Iθ), σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [MeasureTheory.ae_restrict_iff' (s := Iθ) measurableSet_Icc]
  filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)]
    with σ h
  exact fun hmem => h.mpr hmem

/-! ## The angular average of a mixed slot -/

theorem sliceAvg_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → SmoothOpen f → HkMem α 4 f → a + b ≤ 3 → ∀ z : ℝ, 0 < z →
      ∫ θ in Iθ, (mixed b a f z θ) ^ 2 ≤ C * HkSq α 4 f := by
  refine ⟨4, by norm_num, ?_⟩
  intro α f b a hα hα1 hF hmem hab z hz
  obtain ⟨hswap, hGint, hGslice⟩ := Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  have hHknn : 0 ≤ HkSq α 4 f := HkSq_nonneg α 4 f
  set R₀ : ℝ := max z 1 with hR₀def
  have hzR : z ≤ R₀ := le_max_left _ _
  have hR1 : (1 : ℝ) ≤ R₀ := le_max_right _ _
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hzR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  -- the pointwise-in-θ bound on a slice
  have hbound : ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      IntegrableOn (fun s => HkIntegrand α 4 f s θ) Iz →
      (mixed b a f z θ) ^ 2 ≤ (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 4 f s θ := by
    intro θ hθ hθint
    have hθIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    -- the window bound at the angle `θ`
    have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
        HasDerivAt (fun x' : ℝ => mixed b a f x' θ) (pz (mixed b a f) x θ) x :=
      fun x hx => (hF.mixed b a).hasDerivAt_slice hθ (lt_of_lt_of_le hz hx.1)
    have hcont : ContinuousOn (fun x : ℝ => mixed b a f x θ) (Set.Icc R₀ (2 * R₀)) :=
      ((hF.mixed b a).curry_z hθ).continuousOn.mono
        (fun x hx => lt_of_lt_of_le hRpos hx.1)
    have hcont' : ContinuousOn (fun x : ℝ => pz (mixed b a f) x θ) (Set.Icc z (2 * R₀)) :=
      (((hF.mixed b a).pz).curry_z hθ).continuousOn.mono
        (fun x hx => lt_of_lt_of_le hz hx.1)
    have hint : IntegrableOn (fun x : ℝ => (mixed b a f x θ) ^ 2)
        (Set.Icc R₀ (2 * R₀)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc (hcont.pow 2)
    have hwin := Work.FTS.TransportS.half_line_window_bound
      (h := fun x : ℝ => mixed b a f x θ)
      (h' := fun x : ℝ => pz (mixed b a f) x θ) hz hzR hderiv hcont hcont' hint
    -- the two summands are dominated by the `ℋ⁴`-integrand
    have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
        (x * pz (mixed b a f) x θ * w x) ^ 2 ≤ HkIntegrand α 4 f x θ := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
      have heq : x * pz (mixed b a f) x θ = mixed (b + 1) a f x θ := rfl
      rw [heq, mul_pow]
      exact Work.H2.T1Q.mixed_sq_w_sq_le_HkIntegrand α hα f (b + 1) a (by omega) hxpos hθ.1 hθ.2
    have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
        (mixed b a f x θ) ^ 2 ≤ HkIntegrand α 4 f x θ := fun x hx =>
      Work.H2.T1Q.mixed_sq_le_HkIntegrand α hα f b a (by omega)
        (lt_of_lt_of_le hRpos hx.1) hθ.1 hθ.2
    -- interval integrals
    have hIntA : IntervalIntegrable
        (fun x : ℝ => (x * pz (mixed b a f) x θ * w x) ^ 2) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (x * pz (mixed b a f) x θ * w x) ^ 2)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      refine (ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_).pow 2
      unfold w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hHkcont : ∀ {a' b' : ℝ}, 0 < a' →
        ContinuousOn (fun x : ℝ => HkIntegrand α 4 f x θ) (Set.Icc a' b') := by
      intro a' b' ha'
      have hmap : MapsTo (fun x : ℝ => (x, θ)) (Set.Icc a' b') Q0 := fun x hx =>
        mem_Q0.mpr ⟨lt_of_lt_of_le ha' hx.1, hθ.1, hθ.2⟩
      have hc := (hF.continuousOn_HkIntegrand α 4).comp
        (continuousOn_id.prodMk continuousOn_const) hmap
      simpa only [Function.comp_def, id_eq] using hc
    have hIntA' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 4 f x θ) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 4 f x θ)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      exact hHkcont hz
    have hIntB : IntervalIntegrable (fun x : ℝ => (mixed b a f x θ) ^ 2) volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (mixed b a f x θ) ^ 2)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact hcont.pow 2
    have hIntB' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 4 f x θ) volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 4 f x θ)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact hHkcont hRpos
    -- extend the interval integrals to `Iz`
    have hbigA : ∫ x in z..(2 * R₀), HkIntegrand α 4 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 4 f s θ := by
      rw [intervalIntegral.integral_of_le hz2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 4 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
    have hbigB : ∫ x in R₀..(2 * R₀), HkIntegrand α 4 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 4 f s θ := by
      rw [intervalIntegral.integral_of_le hR2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 4 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
    have hmA := intervalIntegral.integral_mono_on hz2R hIntA hIntA' hptA
    have hmB := intervalIntegral.integral_mono_on hR2R hIntB hIntB' hptB
    calc (mixed b a f z θ) ^ 2
        ≤ 2 * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2)
          + (2 / R₀) * ∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2 := hwin
      _ ≤ 2 * (∫ s in Iz, HkIntegrand α 4 f s θ)
          + (2 / R₀) * (∫ s in Iz, HkIntegrand α 4 f s θ) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left (le_trans hmA hbigA) (by norm_num)
          · exact mul_le_mul_of_nonneg_left (le_trans hmB hbigB) (by positivity)
      _ = (2 + 2 / R₀) * (∫ s in Iz, HkIntegrand α 4 f s θ) := by ring
  -- integrate the pointwise (a.e.) bound over `θ`
  have hle : (fun θ : ℝ => (mixed b a f z θ) ^ 2)
      ≤ᵐ[volume.restrict Iθ]
      fun θ : ℝ => (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 4 f s θ := by
    filter_upwards [hGslice, ae_mem_Ioo_Iθ] with θ hθint hθ
    exact hbound θ hθ hθint
  have hfae : 0 ≤ᵐ[volume.restrict Iθ] (fun θ : ℝ => (mixed b a f z θ) ^ 2) :=
    ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => sq_nonneg _
  calc ∫ θ in Iθ, (mixed b a f z θ) ^ 2
      ≤ ∫ θ in Iθ, (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 4 f s θ :=
        integral_mono_of_nonneg hfae (hGint.const_mul _) hle
    _ = (2 + 2 / R₀) * HkSq α 4 f := by
        rw [MeasureTheory.integral_const_mul, hswap]
    _ ≤ 4 * HkSq α 4 f := by
        refine mul_le_mul_of_nonneg_right ?_ hHknn
        have : 2 / R₀ ≤ 2 := by
          rw [div_le_iff₀ hRpos]; linarith
        linarith

/-! ## The weighted angular integral of a mixed slot -/

theorem sliceAng_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → SmoothOpen f → HkMem α 4 f → 1 ≤ a → a + b ≤ 3 → ∀ z : ℝ, 0 < z →
      ∫ θ in Iθ, (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        ≤ C * HkSq α 4 f := by
  refine ⟨4, by norm_num, ?_⟩
  intro α f b a hα hα1 hF hmem ha hab z hz
  obtain ⟨hswap, hGint, hGslice⟩ := Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  have hHknn : 0 ≤ HkSq α 4 f := HkSq_nonneg α 4 f
  set R₀ : ℝ := max z 1 with hR₀def
  have hzR : z ≤ R₀ := le_max_left _ _
  have hR1 : (1 : ℝ) ≤ R₀ := le_max_right _ _
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hzR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  have hbound : ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      IntegrableOn (fun s => HkIntegrand α 4 f s θ) Iz →
      (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        ≤ (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 4 f s θ := by
    intro θ hθ hθint
    have hθIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hsinpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hlamnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(gam α)) := Real.rpow_nonneg hsinpos.le _
    have hderiv : ∀ x ∈ Set.Icc z (2 * R₀),
        HasDerivAt (fun x' : ℝ => mixed b a f x' θ) (pz (mixed b a f) x θ) x :=
      fun x hx => (hF.mixed b a).hasDerivAt_slice hθ (lt_of_lt_of_le hz hx.1)
    have hcont : ContinuousOn (fun x : ℝ => mixed b a f x θ) (Set.Icc R₀ (2 * R₀)) :=
      ((hF.mixed b a).curry_z hθ).continuousOn.mono
        (fun x hx => lt_of_lt_of_le hRpos hx.1)
    have hcont' : ContinuousOn (fun x : ℝ => pz (mixed b a f) x θ) (Set.Icc z (2 * R₀)) :=
      (((hF.mixed b a).pz).curry_z hθ).continuousOn.mono
        (fun x hx => lt_of_lt_of_le hz hx.1)
    have hint : IntegrableOn (fun x : ℝ => (mixed b a f x θ) ^ 2)
        (Set.Icc R₀ (2 * R₀)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc (hcont.pow 2)
    have hwin := Work.FTS.TransportS.half_line_window_bound
      (h := fun x : ℝ => mixed b a f x θ)
      (h' := fun x : ℝ => pz (mixed b a f) x θ) hz hzR hderiv hcont hcont' hint
    -- domination of the two summands by the `ℋ⁴`-integrand
    have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
        (Real.sin (2 * θ)) ^ (-(gam α)) * (x * pz (mixed b a f) x θ * w x) ^ 2
          ≤ HkIntegrand α 4 f x θ := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
      have heq : x * pz (mixed b a f) x θ = mixed (b + 1) a f x θ := rfl
      rw [heq, mul_pow]
      have hkey : (Real.sin (2 * θ)) ^ (-(gam α))
            * ((mixed (b + 1) a f x θ) ^ 2 * (w x) ^ 2)
          = (mixed (b + 1) a f x θ * Wt α x θ) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α x θ hsinpos]
        ring
      calc (Real.sin (2 * θ)) ^ (-(gam α)) * ((mixed (b + 1) a f x θ) ^ 2 * (w x) ^ 2)
          = (mixed (b + 1) a f x θ * Wt α x θ) ^ 2 := hkey
        _ ≤ HkIntegrand α 4 f x θ :=
            sq_le_HkIntegrand_mixed α 4 f x θ a (b + 1) ha (by omega)
    have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
        (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
          ≤ HkIntegrand α 4 f x θ := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hRpos hx.1
      have hw : (1 : ℝ) ≤ w x := Work.FTS.TransportS.one_le_w hxpos
      have hcmp : (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
          ≤ (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
        have hw2 : (1 : ℝ) ≤ (w x) ^ 2 := by nlinarith [hw]
        have h1 : (mixed b a f x θ) ^ 2 ≤ (mixed b a f x θ) ^ 2 * (w x) ^ 2 := by
          calc (mixed b a f x θ) ^ 2 = (mixed b a f x θ) ^ 2 * 1 := by ring
            _ ≤ (mixed b a f x θ) ^ 2 * (w x) ^ 2 :=
                mul_le_mul_of_nonneg_left hw2 (sq_nonneg _)
        have h2 : (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
            ≤ (Real.sin (2 * θ)) ^ (-(gam α)) * ((mixed b a f x θ) ^ 2 * (w x) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 hlamnn
        calc (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2
            ≤ (Real.sin (2 * θ)) ^ (-(gam α)) * ((mixed b a f x θ) ^ 2 * (w x) ^ 2) := h2
          _ = (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by ring
      refine le_trans hcmp ?_
      have hkey : (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          = (mixed b a f x θ * Wt α x θ) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.Wt_sq_eq α x θ hsinpos]
        ring
      calc (mixed b a f x θ) ^ 2 * (w x) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
          = (mixed b a f x θ * Wt α x θ) ^ 2 := hkey
        _ ≤ HkIntegrand α 4 f x θ :=
            sq_le_HkIntegrand_mixed α 4 f x θ a b ha (by omega)
    -- interval integrals
    have hIntA : IntervalIntegrable
        (fun x : ℝ => (x * pz (mixed b a f) x θ * w x) ^ 2) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (x * pz (mixed b a f) x θ * w x) ^ 2)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      refine (ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_).pow 2
      unfold w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hIntAw : IntervalIntegrable
        (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α)) * (x * pz (mixed b a f) x θ * w x) ^ 2)
        volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α))
        * (x * pz (mixed b a f) x θ * w x) ^ 2) (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      refine ContinuousOn.mul continuousOn_const ?_
      refine (ContinuousOn.mul (ContinuousOn.mul continuousOn_id hcont') ?_).pow 2
      unfold w
      refine ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
        (continuousOn_id.pow 2) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))
    have hIntBw : IntervalIntegrable
        (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f x θ) ^ 2)
        volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (Real.sin (2 * θ)) ^ (-(gam α))
        * (mixed b a f x θ) ^ 2) (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact ContinuousOn.mul continuousOn_const (hcont.pow 2)
    have hHkcont : ∀ {a' b' : ℝ}, 0 < a' →
        ContinuousOn (fun x : ℝ => HkIntegrand α 4 f x θ) (Set.Icc a' b') := by
      intro a' b' ha'
      have hmap : MapsTo (fun x : ℝ => (x, θ)) (Set.Icc a' b') Q0 := fun x hx =>
        mem_Q0.mpr ⟨lt_of_lt_of_le ha' hx.1, hθ.1, hθ.2⟩
      have hc := (hF.continuousOn_HkIntegrand α 4).comp
        (continuousOn_id.prodMk continuousOn_const) hmap
      simpa only [Function.comp_def, id_eq] using hc
    have hIntA' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 4 f x θ) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 4 f x θ)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      exact hHkcont hz
    have hIntB' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 4 f x θ) volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 4 f x θ)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact hHkcont hRpos
    have hbigA : ∫ x in z..(2 * R₀), HkIntegrand α 4 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 4 f s θ := by
      rw [intervalIntegral.integral_of_le hz2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 4 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
    have hbigB : ∫ x in R₀..(2 * R₀), HkIntegrand α 4 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 4 f s θ := by
      rw [intervalIntegral.integral_of_le hR2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 4 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
    have hmA := intervalIntegral.integral_mono_on hz2R hIntAw hIntA' hptA
    have hmB := intervalIntegral.integral_mono_on hR2R hIntBw hIntB' hptB
    have hsplitA : (Real.sin (2 * θ)) ^ (-(gam α))
        * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2)
        = ∫ x in z..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
            * (x * pz (mixed b a f) x θ * w x) ^ 2 :=
      (intervalIntegral.integral_const_mul _ _).symm
    have hsplitB : (Real.sin (2 * θ)) ^ (-(gam α))
        * (∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2)
        = ∫ x in R₀..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
            * (mixed b a f x θ) ^ 2 :=
      (intervalIntegral.integral_const_mul _ _).symm
    calc (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        = (Real.sin (2 * θ)) ^ (-(gam α)) * (mixed b a f z θ) ^ 2 := by ring
      _ ≤ (Real.sin (2 * θ)) ^ (-(gam α))
            * (2 * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2)
              + (2 / R₀) * ∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hwin hlamnn
      _ = 2 * ((Real.sin (2 * θ)) ^ (-(gam α))
              * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2))
            + (2 / R₀) * ((Real.sin (2 * θ)) ^ (-(gam α))
              * (∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2)) := by ring
      _ = 2 * (∫ x in z..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
              * (x * pz (mixed b a f) x θ * w x) ^ 2)
            + (2 / R₀) * (∫ x in R₀..(2 * R₀), (Real.sin (2 * θ)) ^ (-(gam α))
              * (mixed b a f x θ) ^ 2) := by rw [hsplitA, hsplitB]
      _ ≤ 2 * (∫ s in Iz, HkIntegrand α 4 f s θ)
            + (2 / R₀) * (∫ s in Iz, HkIntegrand α 4 f s θ) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left (le_trans hmA hbigA) (by norm_num)
          · exact mul_le_mul_of_nonneg_left (le_trans hmB hbigB) (by positivity)
      _ = (2 + 2 / R₀) * (∫ s in Iz, HkIntegrand α 4 f s θ) := by ring
  have hle : (fun θ : ℝ => (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)))
      ≤ᵐ[volume.restrict Iθ]
      fun θ : ℝ => (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 4 f s θ := by
    filter_upwards [hGslice, ae_mem_Ioo_Iθ] with θ hθint hθ
    exact hbound θ hθ hθint
  have hfae : 0 ≤ᵐ[volume.restrict Iθ]
      (fun θ : ℝ => (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) :=
    ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg
        (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _)
  calc ∫ θ in Iθ, (mixed b a f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
      ≤ ∫ θ in Iθ, (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 4 f s θ :=
        integral_mono_of_nonneg hfae (hGint.const_mul _) hle
    _ = (2 + 2 / R₀) * HkSq α 4 f := by
        rw [MeasureTheory.integral_const_mul, hswap]
    _ ≤ 4 * HkSq α 4 f := by
        refine mul_le_mul_of_nonneg_right ?_ hHknn
        have : 2 / R₀ ≤ 2 := by
          rw [div_le_iff₀ hRpos]; linarith
        linarith

end Work.FTS.OpenPkg.ProdOpen
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6.Slots =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The weighted square of a pure `D_z`-slot of order `≤ 6` is dominated by the
`ℋ⁶`-integrand. -/
theorem dzIter_sq_w_sq_le6 (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hj : j ≤ 6) :
    (DzIter j f z θ) ^ 2 * (w z) ^ 2 ≤ HkIntegrand α 6 f z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hη : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(eta)) :=
    Work.H2.T1Q.one_le_rpow_neg hsin (Real.sin_le_one _) eta_nonneg
  calc (DzIter j f z θ) ^ 2 * (w z) ^ 2
      = (DzIter j f z θ) ^ 2 * (w z) ^ 2 * 1 := by ring
    _ ≤ (DzIter j f z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) :=
        mul_le_mul_of_nonneg_left hη (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (DzIter j f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.div_rpow_sq (w z) (Real.sin (2 * θ)) eta hsin]
        ring
    _ ≤ HkIntegrand α 6 f z θ :=
        sq_le_HkIntegrand_z α 6 f z θ j hj

/-- On the open quadrant, the squared weighted mixed slot `(D_z^b D_θ^a f)² w²` of order
`a + b ≤ 6` is dominated by the `ℋ⁶`-integrand of `f`. -/
theorem mixed_sq_w_sq_le_HkIntegrand6 (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (b a : ℕ)
    (hab : a + b ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (mixed b a f z θ) ^ 2 * (w z) ^ 2 ≤ HkIntegrand α 6 f z θ := by
  have hθIθ : θ ∈ Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [mixed_zero_right]
    have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(eta)) :=
      Work.H2.T1Q.one_le_rpow_neg hsin hs1 eta_nonneg
    have hrew : (DzIter b f z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        = (DzIter b f z θ) ^ 2 * (w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(eta)) := by
      rw [mul_pow, Work.H2.T1Q.div_rpow_sq (w z) (Real.sin (2 * θ)) eta hsin]
      ring
    have hz2 := sq_le_HkIntegrand_z α 6 f z θ b (by omega)
    rw [hrew] at hz2
    calc (DzIter b f z θ) ^ 2 * (w z) ^ 2
        ≤ (DzIter b f z θ) ^ 2 * (w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(eta)) :=
          le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h1
      _ ≤ HkIntegrand α 6 f z θ := hz2
  · calc (mixed b a f z θ) ^ 2 * (w z) ^ 2
        ≤ (mixed b a f z θ) ^ 2 * (Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Work.H2.T1Q.w_sq_le_Wt_sq α hα hθIθ hsin) (sq_nonneg _)
      _ = (mixed b a f z θ * Wt α z θ) ^ 2 := (mul_pow _ _ 2).symm
      _ ≤ HkIntegrand α 6 f z θ :=
          sq_le_HkIntegrand_mixed α 6 f z θ a b ha (by omega)

/-- On the open quadrant, the squared mixed slot itself is dominated by the `ℋ⁶`-integrand. -/
theorem mixed_sq_le_HkIntegrand6 (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (b a : ℕ)
    (hab : a + b ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (mixed b a f z θ) ^ 2 ≤ HkIntegrand α 6 f z θ := by
  calc (mixed b a f z θ) ^ 2
      = (mixed b a f z θ) ^ 2 * 1 := by ring
    _ ≤ (mixed b a f z θ) ^ 2 * (w z) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        nlinarith [Work.FTS.TransportS.one_le_w hz, Work.FTS.TransportS.w_pos_of_pos hz]
    _ ≤ HkIntegrand α 6 f z θ :=
        mixed_sq_w_sq_le_HkIntegrand6 α hα f b a hab hz hθ0 hθ1

end Work.FTS.StrongPersist.N6
end
end
