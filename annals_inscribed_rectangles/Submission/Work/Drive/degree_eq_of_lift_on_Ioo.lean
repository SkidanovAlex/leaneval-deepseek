import Mathlib
import Submission.Work.Drive.SeparationBase
import Submission.Work.Drive.WindingNumber

/-!
# The degree from a lift defined on the open interval `(0,1)`

`Submission/Work/Drive/WindingNumber.lean` defines the degree `Work.Drive.degree f hf` of a
continuous circle map as the monodromy of a global lift `ℝ → ℝ`, and proves it intrinsic
(`degree_eq_of_lift`).  This file supplies the *local* form used by Hugelmeyer's order theory: if the
lift of `f` is only specified on the open interval `(0,1)` — an `A : ℝ → ℝ` continuous on `(0,1)`
with `A x ≡ f (x mod 1)` there, whose one-sided limits at `0` and `1` are `a` and `b` — then
necessarily `b - a` is an integer, namely the degree of `f`.

The proof is the standard one: `liftOf f hf - A` is continuous and integer-valued on the *connected*
interval `(0,1)`, hence constant there; comparing the one-sided limits with the continuity of
`liftOf f hf` and the period relation `liftOf f hf (t+1) = liftOf f hf t + degree f hf` at `t = 0`
identifies the two limits and yields `b - a = degree f hf`.
-/

namespace Work.Drive

open Filter

theorem degree_eq_of_lift_on_Ioo {f : UnitAddCircle → UnitAddCircle} (hf : Continuous f)
    {A : ℝ → ℝ} (hA : ContinuousOn A (Set.Ioo (0:ℝ) 1))
    (hlift : ∀ x : ℝ, x ∈ Set.Ioo (0:ℝ) 1 →
      ((A x : ℝ) : UnitAddCircle) = f (x : UnitAddCircle))
    {a b : ℝ} (ha : Filter.Tendsto A (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds a))
    (hb : Filter.Tendsto A (nhdsWithin (1:ℝ) (Set.Iio 1)) (nhds b)) :
    ∃ n : ℤ, b - a = n ∧ degree f hf = n := by
  have hpre : PreconnectedSpace ↥(Set.Ioo (0:ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  -- `liftOf f hf - A` takes integer values on `(0,1)`
  have hint : ∀ x ∈ Set.Ioo (0:ℝ) 1, ∃ k : ℤ, liftOf f hf x - A x = (k : ℝ) := by
    intro x hx
    have h1 : ((liftOf f hf x - A x : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, liftOf_lifts f hf x, hlift x hx, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h1
    exact ⟨k, by simpa [zsmul_eq_mul] using hk.symm⟩
  -- hence it is locally constant on `(0,1)`
  have hloc : IsLocallyConstant (fun x : ↥(Set.Ioo (0:ℝ) 1) =>
      liftOf f hf x.1 - A x.1) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    obtain ⟨k, hk⟩ := hint x.1 x.2
    have hHc : ContinuousAt (fun t : ℝ => liftOf f hf t - A t) x.1 :=
      (liftOf_continuous f hf).continuousAt.sub
        (hA.continuousAt (isOpen_Ioo.mem_nhds x.2))
    obtain ⟨ε, hεpos, hε⟩ := Metric.continuousAt_iff.mp hHc (1/2) (by norm_num)
    have hnb : {y : ↥(Set.Ioo (0:ℝ) 1) | dist y.1 x.1 < ε} ∈ nhds x :=
      (continuous_subtype_val.continuousAt).preimage_mem_nhds
        (Metric.ball_mem_nhds x.1 hεpos)
    filter_upwards [hnb] with y hy
    show liftOf f hf y.1 - A y.1 = liftOf f hf x.1 - A x.1
    obtain ⟨l, hl⟩ := hint y.1 y.2
    have hd := hε hy
    rw [Real.dist_eq, hl, hk] at hd
    have hlt : |(l : ℝ) - (k : ℝ)| < 1 := by linarith
    have hlk : l = k := int_eq_of_abs_sub_lt_one hlt
    rw [hl, hk, hlk]
  -- so it is constant on the interval
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ x ∈ Set.Ioo (0:ℝ) 1, liftOf f hf x - A x = c :=
    ⟨liftOf f hf (1/2) - A (1/2), fun x hx => by
      haveI := hpre
      exact hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨1/2, by norm_num⟩⟩
  -- one-sided limits of `liftOf f hf - A` at `0` and `1`
  have hev0 : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), liftOf f hf x - A x = c := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Iio.mem_nhds (by norm_num : (0:ℝ) < 1)] with x hx1 hx0
    exact hc x ⟨hx0, hx1⟩
  have hev1 : ∀ᶠ x in nhdsWithin (1:ℝ) (Set.Iio 1), liftOf f hf x - A x = c := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0:ℝ) < 1)] with x hx0 hx1
    exact hc x ⟨hx0, hx1⟩
  have hlim0 : Filter.Tendsto (fun x : ℝ => liftOf f hf x - A x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds c) :=
    tendsto_const_nhds.congr' (EventuallyEq.symm hev0)
  have hlim1 : Filter.Tendsto (fun x : ℝ => liftOf f hf x - A x)
      (nhdsWithin (1:ℝ) (Set.Iio 1)) (nhds c) :=
    tendsto_const_nhds.congr' (EventuallyEq.symm hev1)
  have hH0 : Filter.Tendsto (fun x : ℝ => liftOf f hf x - A x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (liftOf f hf 0 - a)) :=
    ((liftOf_continuous f hf).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub ha
  have hH1 : Filter.Tendsto (fun x : ℝ => liftOf f hf x - A x)
      (nhdsWithin (1:ℝ) (Set.Iio 1)) (nhds (liftOf f hf 1 - b)) :=
    ((liftOf_continuous f hf).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub hb
  have heq0 : liftOf f hf 0 - a = c := tendsto_nhds_unique hH0 hlim0
  have heq1 : liftOf f hf 1 - b = c := tendsto_nhds_unique hH1 hlim1
  -- compare with the period relation at `0`
  have hdiff : (degree f hf : ℝ) = b - a := by
    have h01 := liftOf_add_one f hf 0
    simp only [zero_add] at h01
    linarith
  exact ⟨degree f hf, hdiff.symm, rfl⟩

end Work.Drive
