import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.EllipticEst.Core.weightedCS
import Submission.Work.FTS.EllipticEst.TT.sliceFtcKey
import Submission.Work.FTS.EllipticEst.TT.sqBoundTendstoPos
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.PkgK5.TraceEngine

open MeasureTheory Set Filter
open scoped Real

/-- Elementary AM–GM bound: for `w > 0` with `w⁻¹ ≤ 1`,
`|g| ≤ ½ g² w + ½`.  Indeed `2 ab ≤ a² + b²` with `a = |g| √w`, `b = 1/√w`. -/
private lemma amgm_abs_le (g w : ℝ) (hw : 0 < w) (hw1 : w⁻¹ ≤ 1) :
    |g| ≤ (1 / 2) * (g ^ 2 * w) + 1 / 2 := by
  set s := Real.sqrt w with hs
  have hs2 : s ^ 2 = w := by rw [hs, Real.sq_sqrt hw.le]
  have hsne : s ≠ 0 := by rw [hs]; exact ne_of_gt (Real.sqrt_pos.mpr hw)
  have h2 := two_mul_le_add_sq (|g| * s) (s⁻¹)
  have hAB : (|g| * s) * s⁻¹ = |g| := by rw [mul_assoc, mul_inv_cancel₀ hsne, mul_one]
  have h2' : 2 * |g| ≤ g ^ 2 * w + w⁻¹ := by
    have h2'' : 2 * ((|g| * s) * s⁻¹) ≤ (|g| * s) ^ 2 + (s⁻¹) ^ 2 := by
      calc 2 * ((|g| * s) * s⁻¹) = 2 * (|g| * s) * s⁻¹ := by ring
        _ ≤ (|g| * s) ^ 2 + (s⁻¹) ^ 2 := h2
    rw [hAB, mul_pow, sq_abs, hs2, inv_pow, hs2] at h2''
    linarith
  linarith

/- Weighted slicewise rate bound at both endpoints of `(0,π/2)`, for the weight
`thEta θ = sin(2θ)^{-η}`, `η = 99/100`.

Intended proof route (both endpoints identical):
1. From `hint`, `deriv f` is integrable on `Ioo 0 (π/2)` and on every sub-interval (AM–GM:
   `|g| ≤ ((g^2 * thEta) + thEta⁻¹)/2`, and `thEta⁻¹ = sin(2θ)^η ≤ 1` is bounded, hence integrable
   on the finite-measure set).
2. `Work.FTS.EllipticEst.TT.sliceFtcKey` gives the two antiderivative relations
   `f θ - c = ∫ s in Ioo 0 θ, deriv f s` and `f θ - c' = -∫ s in Ioo θ (π/2), deriv f s`.
3. `Work.EllipticEst.Core.weightedCS` (weight `w := thEta`, `g := deriv f`, on `s := Ioo 0 θ`,
   which is measurable, with `thEta > 0` and continuous there) gives
   `(∫ s in Ioo 0 θ, deriv f s)^2 ≤ (∫ s in Ioo 0 θ, (deriv f s)^2 * thEta s) * (∫ s in Ioo 0 θ, (thEta s)⁻¹)`
   and `(thEta s)⁻¹ = sin(2s)^η ≤ 1` on `Ioo 0 θ`, so the last factor is `≤ θ`.
4. The constant `c` is `0`: step 3 gives `(f θ - c)^2 ≤ θ * K` with
   `K = ∫ s in Ioo 0 (π/2), (deriv f s)^2 * thEta s` fixed, so `f - c → 0` at `0⁺`
   (`Work.FTS.EllipticEst.TT.sqBoundTendstoPos`, or `Filter.Tendsto` by squeeze), while `f → 0`
   by `htr0`, whence `c = 0` (unique limits). Same at `π/2` with `htr1`.
   This is exactly the pattern of `Work.FTS.EllipticEst.EllTwoAsm.LightSliceRate` (the weight
   `sin(2θ)^a`, `0 < a < 1` case), but that result is NOT applicable here: it needs
   `∫ (deriv f)^2 sin(2θ)^a` with `0 < a < 1` and only yields the weaker factor `C θ^{1-a}`
   instead of `θ`. -/
theorem slice_rate_thEta (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)))
    (htr0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (htr1 : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun s : ℝ => (deriv f s) ^ 2 * Work.FTS.EllipticEst.thEta s) (Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (f θ) ^ 2 ≤ θ * ∫ s in Set.Ioo 0 θ, (deriv f s) ^ 2 * Work.FTS.EllipticEst.thEta s) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (f θ) ^ 2 ≤ (Real.pi / 2 - θ) *
        ∫ s in Set.Ioo θ (Real.pi / 2), (deriv f s) ^ 2 * Work.FTS.EllipticEst.thEta s) := by
  have hη0 : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
  -- ## Elementary facts about the weight `thEta`
  have hthEta_pos : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 < Work.FTS.EllipticEst.thEta t := by
    intro t ht
    exact Real.rpow_pos_of_pos (Work.FTS.EllipticEst.sin_two_pos ht) _
  have hthEta_eq : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.thEta t = ((Real.sin (2 * t)) ^ Work.Spaces.eta)⁻¹ := by
    intro t ht
    simp only [Work.FTS.EllipticEst.thEta]
    exact Real.rpow_neg (le_of_lt (Work.FTS.EllipticEst.sin_two_pos ht)) _
  have hthEta_inv : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.FTS.EllipticEst.thEta t)⁻¹ = (Real.sin (2 * t)) ^ Work.Spaces.eta := by
    intro t ht
    rw [hthEta_eq t ht, inv_inv]
  have hthEta_inv_le : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.FTS.EllipticEst.thEta t)⁻¹ ≤ 1 := by
    intro t ht
    rw [hthEta_inv t ht]
    exact Work.FTS.EllipticEst.sin_two_rpow_le_one hη0.le ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hthEta_cont : ContinuousOn (fun t : ℝ => Work.FTS.EllipticEst.thEta t)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h : ContinuousOn (fun t : ℝ => (Real.sin (2 * t)) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun t ht => Or.inl (ne_of_gt (Work.FTS.EllipticEst.sin_two_pos ht)))
    simpa only [Work.FTS.EllipticEst.thEta] using h
  -- ## Integrability of the dual weight and its integral bounds
  have hthEta_inv_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Work.FTS.EllipticEst.thEta t)⁻¹) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.sin (2 * t)) ^ Work.Spaces.eta)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Work.FTS.EllipticEst.integrableOn_sin_two_rpow hη0.le).1.mono_set Set.Ioo_subset_Icc_self
    refine hbase.congr_fun ?_ measurableSet_Ioo
    intro t ht
    exact (hthEta_inv t ht).symm
  have hIntInvL : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.thEta t)⁻¹) ≤ θ := by
    intro θ hθ
    have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 θ) :=
      MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    calc (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.thEta t)⁻¹)
        ≤ ∫ t in Set.Ioo 0 θ, (1 : ℝ) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ hone ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact inv_nonneg.mpr (le_of_lt (Real.rpow_pos_of_pos
              (Work.FTS.EllipticEst.sin_two_pos ⟨ht.1, lt_trans ht.2 hθ.2⟩) _))
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact hthEta_inv_le t ⟨ht.1, lt_trans ht.2 hθ.2⟩
      _ = θ := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hθ.1.le)]
          simp
  have hIntInvR : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.thEta t)⁻¹)
        ≤ Real.pi / 2 - θ := by
    intro θ hθ
    have hone : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo θ (Real.pi / 2)) :=
      MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    calc (∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.thEta t)⁻¹)
        ≤ ∫ t in Set.Ioo θ (Real.pi / 2), (1 : ℝ) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ hone ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact inv_nonneg.mpr (le_of_lt (Real.rpow_pos_of_pos
              (Work.FTS.EllipticEst.sin_two_pos ⟨lt_trans hθ.1 ht.1, ht.2⟩) _))
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
            exact hthEta_inv_le t ⟨lt_trans hθ.1 ht.1, ht.2⟩
      _ = Real.pi / 2 - θ := by
          rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
            ENNReal.toReal_ofReal (sub_nonneg.mpr hθ.2.le)]
          simp
  -- ## `deriv f` is integrable (AM–GM against the dual weight)
  have hderiv_int : MeasureTheory.IntegrableOn (fun t : ℝ => deriv f t)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hA : MeasureTheory.IntegrableOn
        (fun t : ℝ => (1 / 2) * ((deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hint.const_mul (1 / 2)
    have hB : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 / 2 : ℝ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have hF := hA.add hB
    refine MeasureTheory.Integrable.mono' hF ((measurable_deriv f).aestronglyMeasurable) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs]
    exact amgm_abs_le (deriv f t) (Work.FTS.EllipticEst.thEta t)
      (hthEta_pos t ht) (hthEta_inv_le t ht)
  have hderiv_sub : ∀ a b : ℝ, Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      MeasureTheory.IntegrableOn (fun t : ℝ => deriv f t) (Set.Ioo a b) :=
    fun a b h => hderiv_int.mono_set h
  -- ## The two antiderivative relations
  obtain ⟨⟨cL, hKeyL⟩, ⟨cR, hKeyR⟩⟩ := Work.FTS.EllipticEst.TT.sliceFtcKey f hf hderiv_sub
  have hderiv_cont : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have hKnn : 0 ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
      (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun t ht => mul_nonneg (sq_nonneg _) (le_of_lt (hthEta_pos t ht)))
  -- ## Left endpoint: Cauchy–Schwarz against the dual weight
  have hboundL : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - cL) ^ 2 ≤ θ * ∫ t in Set.Ioo 0 θ,
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    have hsub : Set.Ioo (0 : ℝ) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun t ht => ⟨ht.1, lt_trans ht.2 hθ.2⟩
    have hcs := Work.EllipticEst.Core.weightedCS (s := Set.Ioo (0 : ℝ) θ) measurableSet_Ioo
        (w := fun t : ℝ => Work.FTS.EllipticEst.thEta t) (g := fun t : ℝ => deriv f t)
        (fun t ht => hthEta_pos t (hsub ht))
        (hthEta_cont.mono hsub)
        (hderiv_cont.mono hsub)
        (hint.mono_set hsub)
        (hthEta_inv_int.mono_set hsub)
    have hAnn : 0 ≤ ∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo
        (fun t ht => mul_nonneg (sq_nonneg _) (le_of_lt (hthEta_pos t (hsub ht))))
    rw [hKeyL θ hθ]
    calc (∫ t in Set.Ioo 0 θ, deriv f t) ^ 2
        ≤ (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (∫ t in Set.Ioo 0 θ, (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
      _ ≤ (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) * θ :=
          mul_le_mul_of_nonneg_left (hIntInvL θ hθ) hAnn
      _ = θ * (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
  have hmonoL : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo 0 θ, (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (hthEta_pos t ht))
    · filter_upwards with t ht
      exact ⟨ht.1, lt_trans ht.2 hθ.2⟩
  have hcL0 : cL = 0 := by
    have hlim : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds cL) :=
      (Work.FTS.EllipticEst.TT.sqBoundTendstoPos (p := (1 : ℝ)) one_pos).1 f cL
        (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) hKnn
        (fun θ hθ => by
          calc (f θ - cL) ^ 2
              ≤ θ * (∫ t in Set.Ioo 0 θ,
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := hboundL θ hθ
            _ ≤ θ * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
                mul_le_mul_of_nonneg_left (hmonoL θ hθ) (le_of_lt hθ.1)
            _ = (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) * θ ^ (1 : ℝ) := by
                rw [Real.rpow_one]; ring)
    exact tendsto_nhds_unique hlim htr0
  -- ## Right endpoint
  have hboundR : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (f θ - cR) ^ 2 ≤ (Real.pi / 2 - θ) * ∫ t in Set.Ioo θ (Real.pi / 2),
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    have hsub : Set.Ioo θ (Real.pi / 2) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      fun t ht => ⟨lt_trans hθ.1 ht.1, ht.2⟩
    have hcs := Work.EllipticEst.Core.weightedCS (s := Set.Ioo θ (Real.pi / 2)) measurableSet_Ioo
        (w := fun t : ℝ => Work.FTS.EllipticEst.thEta t) (g := fun t : ℝ => deriv f t)
        (fun t ht => hthEta_pos t (hsub ht))
        (hthEta_cont.mono hsub)
        (hderiv_cont.mono hsub)
        (hint.mono_set hsub)
        (hthEta_inv_int.mono_set hsub)
    have hAnn : 0 ≤ ∫ t in Set.Ioo θ (Real.pi / 2),
        (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t :=
      MeasureTheory.setIntegral_nonneg measurableSet_Ioo
        (fun t ht => mul_nonneg (sq_nonneg _) (le_of_lt (hthEta_pos t (hsub ht))))
    rw [hKeyR θ hθ, neg_sq]
    calc (∫ t in Set.Ioo θ (Real.pi / 2), deriv f t) ^ 2
        ≤ (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (∫ t in Set.Ioo θ (Real.pi / 2), (Work.FTS.EllipticEst.thEta t)⁻¹) := hcs
      _ ≤ (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
            * (Real.pi / 2 - θ) := mul_le_mul_of_nonneg_left (hIntInvR θ hθ) hAnn
      _ = (Real.pi / 2 - θ) * (∫ t in Set.Ioo θ (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := by ring
  have hmonoR : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (∫ t in Set.Ioo θ (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)
        ≤ ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
            (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := by
    intro θ hθ
    refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      exact mul_nonneg (sq_nonneg _) (le_of_lt (hthEta_pos t ht))
    · filter_upwards with t ht
      exact ⟨lt_trans hθ.1 ht.1, ht.2⟩
  have hcR0 : cR = 0 := by
    have hlim : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds cR) :=
      (Work.FTS.EllipticEst.TT.sqBoundTendstoPos (p := (1 : ℝ)) one_pos).2 f cR
        (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
          (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) hKnn
        (fun θ hθ => by
          calc (f θ - cR) ^ 2
              ≤ (Real.pi / 2 - θ) * (∫ t in Set.Ioo θ (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) := hboundR θ hθ
            _ ≤ (Real.pi / 2 - θ) * (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) :=
                mul_le_mul_of_nonneg_left (hmonoR θ hθ) (by linarith [hθ.2])
            _ = (∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2),
                  (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t) * (Real.pi / 2 - θ) ^ (1 : ℝ) := by
                rw [Real.rpow_one]; ring)
    exact tendsto_nhds_unique hlim htr1
  constructor
  · intro θ hθ
    have h := hboundL θ hθ
    rw [hcL0] at h
    simpa using h
  · intro θ hθ
    have h := hboundR θ hθ
    rw [hcR0] at h
    simpa using h

end Work.FTS.EllSol.PkgK5.TraceEngine
