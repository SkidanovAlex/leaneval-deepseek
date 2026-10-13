import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongPersist.N6.Swap6
import Submission.Work.FTS.StrongPersist.N6.Slots
import Submission.Work.FTS.OpenPkg.ProdOpen.SlicesOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open Work.Spaces

/-- Almost every angle of `Iθ` lies in the open interval `(0, π/2)`. -/
theorem ae_mem_Ioo_Iθ6 :
    ∀ᵐ σ ∂(volume.restrict Iθ), σ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [MeasureTheory.ae_restrict_iff' (s := Iθ) measurableSet_Icc]
  filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2)]
    with σ h
  exact fun hmem => h.mpr hmem

/-
Template (verbatim, level 4): `Work.FTS.OpenPkg.ProdOpen.sliceAvg_le`
(`Submission/Work/FTS/OpenPkg/ProdOpen/SlicesOpen.lean`).  This is the same proof with `4 ↦ 6`
and `a + b ≤ 3 ↦ a + b ≤ 5`; the level-6 slot dominations are
`Work.FTS.StrongPersist.N6.mixed_sq_w_sq_le_HkIntegrand6` and
`Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6` (in `N6/Slots`), and the Tonelli input
`Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open` is replaced by
`Work.FTS.StrongPersist.N6.sda_HkSqSwap_open6` (in `N6/Swap6`).

Please put the proof in `Submission/Work/FTS/StrongPersist/N6/sliceAvg_le6.lean` (module
`Submission.Work.FTS.StrongPersist.N6.sliceAvg_le6`), inside `namespace Work.FTS.StrongPersist.N6`.
-/
theorem sliceAvg_le6 : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b a : ℕ),
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    a + b ≤ 5 → ∀ z : ℝ, 0 < z →
      ∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed b a f z θ) ^ 2 ≤ C * Work.Spaces.HkSq α 6 f := by
  refine ⟨4, by norm_num, ?_⟩
  intro α f b a hα hα1 hF hmem hab z hz
  obtain ⟨hswap, hGint, hGslice⟩ := Work.FTS.StrongPersist.N6.sda_HkSqSwap_open6 α f hF hmem
  have hHknn : 0 ≤ HkSq α 6 f := HkSq_nonneg α 6 f
  set R₀ : ℝ := max z 1 with hR₀def
  have hzR : z ≤ R₀ := le_max_left _ _
  have hR1 : (1 : ℝ) ≤ R₀ := le_max_right _ _
  have hRpos : 0 < R₀ := lt_of_lt_of_le hz hzR
  have hz2R : z ≤ 2 * R₀ := by linarith
  have hR2R : R₀ ≤ 2 * R₀ := by linarith
  -- the pointwise-in-θ bound on a slice
  have hbound : ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      IntegrableOn (fun s => HkIntegrand α 6 f s θ) Iz →
      (mixed b a f z θ) ^ 2 ≤ (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 6 f s θ := by
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
    -- the two summands are dominated by the `ℋ⁶`-integrand
    have hptA : ∀ x ∈ Set.Icc z (2 * R₀),
        (x * pz (mixed b a f) x θ * w x) ^ 2 ≤ HkIntegrand α 6 f x θ := by
      intro x hx
      have hxpos : 0 < x := lt_of_lt_of_le hz hx.1
      have heq : x * pz (mixed b a f) x θ = mixed (b + 1) a f x θ := rfl
      rw [heq, mul_pow]
      exact Work.FTS.StrongPersist.N6.mixed_sq_w_sq_le_HkIntegrand6 α hα f (b + 1) a
        (by omega) hxpos hθ.1 hθ.2
    have hptB : ∀ x ∈ Set.Icc R₀ (2 * R₀),
        (mixed b a f x θ) ^ 2 ≤ HkIntegrand α 6 f x θ := fun x hx =>
      Work.FTS.StrongPersist.N6.mixed_sq_le_HkIntegrand6 α hα f b a (by omega)
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
        ContinuousOn (fun x : ℝ => HkIntegrand α 6 f x θ) (Set.Icc a' b') := by
      intro a' b' ha'
      have hmap : MapsTo (fun x : ℝ => (x, θ)) (Set.Icc a' b') Work.FTS.EllipticEst.Q0 :=
        fun x hx => Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le ha' hx.1, hθ.1, hθ.2⟩
      have hc := (hF.continuousOn_HkIntegrand α 6).comp
        (continuousOn_id.prodMk continuousOn_const) hmap
      simpa only [Function.comp_def, id_eq] using hc
    have hIntA' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 6 f x θ) volume z (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 6 f x θ)
        (Set.uIcc z (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hz2R]
      exact hHkcont hz
    have hIntB : IntervalIntegrable (fun x : ℝ => (mixed b a f x θ) ^ 2) volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => (mixed b a f x θ) ^ 2)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact hcont.pow 2
    have hIntB' : IntervalIntegrable (fun x : ℝ => HkIntegrand α 6 f x θ) volume R₀ (2 * R₀) := by
      refine (show ContinuousOn (fun x : ℝ => HkIntegrand α 6 f x θ)
        (Set.uIcc R₀ (2 * R₀)) from ?_).intervalIntegrable
      rw [Set.uIcc_of_le hR2R]
      exact hHkcont hRpos
    -- extend the interval integrals to `Iz`
    have hbigA : ∫ x in z..(2 * R₀), HkIntegrand α 6 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 6 f s θ := by
      rw [intervalIntegral.integral_of_le hz2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 6 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx.1)
    have hbigB : ∫ x in R₀..(2 * R₀), HkIntegrand α 6 f x θ
        ≤ ∫ s in Iz, HkIntegrand α 6 f s θ := by
      rw [intervalIntegral.integral_of_le hR2R]
      refine setIntegral_mono_set hθint
        (Eventually.of_forall fun x => HkIntegrand_nonneg α 6 f x θ) ?_
      exact Eventually.of_forall fun x hx => le_of_lt (lt_trans hRpos hx.1)
    have hmA := intervalIntegral.integral_mono_on hz2R hIntA hIntA' hptA
    have hmB := intervalIntegral.integral_mono_on hR2R hIntB hIntB' hptB
    calc (mixed b a f z θ) ^ 2
        ≤ 2 * (∫ x in z..(2 * R₀), (x * pz (mixed b a f) x θ * w x) ^ 2)
          + (2 / R₀) * ∫ x in R₀..(2 * R₀), (mixed b a f x θ) ^ 2 := hwin
      _ ≤ 2 * (∫ s in Iz, HkIntegrand α 6 f s θ)
          + (2 / R₀) * (∫ s in Iz, HkIntegrand α 6 f s θ) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left (le_trans hmA hbigA) (by norm_num)
          · exact mul_le_mul_of_nonneg_left (le_trans hmB hbigB) (by positivity)
      _ = (2 + 2 / R₀) * (∫ s in Iz, HkIntegrand α 6 f s θ) := by ring
  -- integrate the pointwise (a.e.) bound over `θ`
  have hle : (fun θ : ℝ => (mixed b a f z θ) ^ 2)
      ≤ᵐ[volume.restrict Iθ]
      fun θ : ℝ => (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 6 f s θ := by
    filter_upwards [hGslice, ae_mem_Ioo_Iθ6] with θ hθint hθ
    exact hbound θ hθ hθint
  have hfae : 0 ≤ᵐ[volume.restrict Iθ] (fun θ : ℝ => (mixed b a f z θ) ^ 2) :=
    ae_restrict_of_forall_mem measurableSet_Icc fun θ _ => sq_nonneg _
  calc ∫ θ in Iθ, (mixed b a f z θ) ^ 2
      ≤ ∫ θ in Iθ, (2 + 2 / R₀) * ∫ s in Iz, HkIntegrand α 6 f s θ :=
        integral_mono_of_nonneg hfae (hGint.const_mul _) hle
    _ = (2 + 2 / R₀) * HkSq α 6 f := by
        rw [MeasureTheory.integral_const_mul, hswap]
    _ ≤ 4 * HkSq α 6 f := by
        refine mul_le_mul_of_nonneg_right ?_ hHknn
        have : 2 / R₀ ≤ 2 := by
          rw [div_le_iff₀ hRpos]; linarith
        linarith

end Work.FTS.StrongPersist.N6
