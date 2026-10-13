import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Separation.CompletelyRegular

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.I1cb

/-- The primitive of a function integrable on `(a,b)` is continuous at the right end `a`
of the interval: `∫_a^t f → 0` as `t → a⁺`.  (Only the values of `f` on `(a,b)` matter;
`f a` is irrelevant, which is why integrability on the open interval suffices.) -/
theorem primitive_tendsto_nhdsWithin_left {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioo a b)) :
    Filter.Tendsto (fun t => ∫ x in a..t, g x) (nhdsWithin a (Set.Ioi a)) (nhds 0) := by
  have hIcc : MeasureTheory.IntegrableOn g (Set.Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioo (f := g) (μ := MeasureTheory.volume)).2 hint
  have hIcc' : MeasureTheory.IntegrableOn g (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab.le] using hIcc
  have hcont : ContinuousOn (fun x => ∫ t in a..x, g t) (Set.Icc a b) := by
    simpa [Set.uIcc_of_le hab.le] using
      (intervalIntegral.continuousOn_primitive_interval (a := a) (b := b) (f := g) hIcc')
  have h1 : Filter.Tendsto (fun x => ∫ t in a..x, g t) (nhdsWithin a (Set.Icc a b))
      (nhds (∫ t in a..a, g t)) := hcont.continuousWithinAt (Set.left_mem_Icc.2 hab.le)
  rw [intervalIntegral.integral_same] at h1
  have hmem : Set.Iio b ∈ nhdsWithin a (Set.Ioi a) := nhdsWithin_le_nhds (Iio_mem_nhds hab)
  have heq : nhdsWithin a (Set.Ioo a b) = nhdsWithin a (Set.Ioi a) := by
    have := nhdsWithin_inter_of_mem (a := a) (t := Set.Ioi a) (s := Set.Iio b) hmem
    rwa [Set.Iio_inter_Ioi] at this
  exact h1.mono_left (heq ▸ nhdsWithin_mono a Set.Ioo_subset_Icc_self)

/-- The primitive of a function integrable on `(a,b)` is continuous at the left end `b`
of the interval: `∫_t^b f → 0` as `t → b⁻`. -/
theorem primitive_tendsto_nhdsWithin_right {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioo a b)) :
    Filter.Tendsto (fun t => ∫ x in t..b, g x) (nhdsWithin b (Set.Iio b)) (nhds 0) := by
  have hIcc : MeasureTheory.IntegrableOn g (Set.Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioo (f := g) (μ := MeasureTheory.volume)).2 hint
  have hIcc' : MeasureTheory.IntegrableOn g (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab.le] using hIcc
  have hcont : ContinuousOn (fun x => ∫ t in b..x, g t) (Set.Icc a b) := by
    have hh := intervalIntegral.continuousOn_primitive_interval (a := b) (b := a) (f := g)
      (by simpa [Set.uIcc_comm] using hIcc')
    simpa [Set.uIcc_comm, Set.uIcc_of_le hab.le] using hh
  have h1 : Filter.Tendsto (fun x => ∫ t in b..x, g t) (nhdsWithin b (Set.Icc a b))
      (nhds (∫ t in b..b, g t)) := hcont.continuousWithinAt (Set.right_mem_Icc.2 hab.le)
  rw [intervalIntegral.integral_same] at h1
  have h2 : Filter.Tendsto (fun x => -∫ t in b..x, g t) (nhdsWithin b (Set.Icc a b)) (nhds 0) := by
    simpa using h1.neg
  have h3 : Filter.Tendsto (fun x => ∫ t in x..b, g t) (nhdsWithin b (Set.Icc a b)) (nhds 0) := by
    refine Filter.Tendsto.congr (fun x => ?_) h2
    rw [intervalIntegral.integral_symm]
    ring
  have hmem : Set.Ioi a ∈ nhdsWithin b (Set.Iio b) := nhdsWithin_le_nhds (Ioi_mem_nhds hab)
  have heq : nhdsWithin b (Set.Ioo a b) = nhdsWithin b (Set.Iio b) := by
    have := nhdsWithin_inter_of_mem (a := b) (t := Set.Iio b) (s := Set.Ioi a) hmem
    rwa [Set.Ioi_inter_Iio] at this
  exact h3.mono_left (heq ▸ nhdsWithin_mono b Set.Ioo_subset_Icc_self)

/-- **Fundamental theorem of calculus, improper version.**  If `f` has derivative `f'` at every
point of the open interval `(a,b)` and `f'` is (Lebesgue) integrable on `(a,b)`, then `f` has
finite one-sided limits at the two endpoints and the integral of `f'` over `(a,b)` is the
difference of those limits. -/
theorem ftc_open_interval {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint : MeasureTheory.IntegrableOn f' (Set.Ioo a b)) :
    ∃ fa fb : ℝ, Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds fa) ∧
      Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds fb) ∧
      (∫ x in Set.Ioo a b, f' x) = fb - fa := by
  have hIcc : MeasureTheory.IntegrableOn f' (Set.Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioo (f := f') (μ := MeasureTheory.volume)).2 hint
  have keyA := primitive_tendsto_nhdsWithin_left hab hint
  have keyB := primitive_tendsto_nhdsWithin_right hab hint
  -- a midpoint of `(a,b)`, used as the reference point for the two limits
  set c : ℝ := (a + b) / 2 with hc
  have hac : a < c := by rw [hc]; linarith
  have hcb : c < b := by rw [hc]; linarith
  have hII : ∀ {p q : ℝ}, Set.uIoc p q ⊆ Set.Icc a b →
      IntervalIntegrable f' MeasureTheory.volume p q :=
    fun hpq => intervalIntegrable_iff.2 (hIcc.mono_set hpq)
  have hlt_a : ∀ᶠ x in nhdsWithin a (Set.Ioi a), x < c :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hac)
  have hlt_b : ∀ᶠ x in nhdsWithin b (Set.Iio b), c < x :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hcb)
  -- Newton–Leibniz on the part of the interval to the left of `c`
  have hFTC : ∀ x ∈ Set.Ioo a c, f x = f c - ∫ t in x..c, f' t := by
    intro x hx
    have hsub' : ∀ y ∈ Set.uIcc x c, y ∈ Set.Ioo a b := by
      intro y hy
      rw [Set.uIcc_of_le hx.2.le] at hy
      exact ⟨lt_of_lt_of_le hx.1 hy.1, lt_of_le_of_lt hy.2 hcb⟩
    have hsub : Set.uIoc x c ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le hx.2.le]
      exact fun y hy => ⟨le_trans hx.1.le hy.1.le, le_trans hy.2 hcb.le⟩
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hderiv y (hsub' y hy)) (hII hsub)
    linarith [h]
  have hmodel_a : Filter.Tendsto (fun x => (f c - ∫ t in a..c, f' t) + ∫ t in a..x, f' t)
      (nhdsWithin a (Set.Ioi a)) (nhds (f c - ∫ t in a..c, f' t)) := by
    have h := (tendsto_const_nhds (x := f c - ∫ t in a..c, f' t)).add keyA
    simpa using h
  have heq_a : (fun x => f c - ∫ t in x..c, f' t) =ᶠ[nhdsWithin a (Set.Ioi a)]
      (fun x => (f c - ∫ t in a..c, f' t) + ∫ t in a..x, f' t) := by
    filter_upwards [self_mem_nhdsWithin, hlt_a] with x hx hxc
    have h1 : IntervalIntegrable f' MeasureTheory.volume a x := hII (by
      rw [Set.uIoc_of_le hx.le]
      exact fun y hy => ⟨hy.1.le, le_trans hy.2 (le_trans hxc.le hcb.le)⟩)
    have h2 : IntervalIntegrable f' MeasureTheory.volume x c := hII (by
      rw [Set.uIoc_of_le hxc.le]
      exact fun y hy => ⟨le_trans hx.le hy.1.le, le_trans hy.2 hcb.le⟩)
    have h := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [h]
  have hFa : Filter.Tendsto (fun x => f c - ∫ t in x..c, f' t) (nhdsWithin a (Set.Ioi a))
      (nhds (f c - ∫ t in a..c, f' t)) := Filter.Tendsto.congr' heq_a.symm hmodel_a
  have hfa : Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds (f c - ∫ t in a..c, f' t)) := by
    refine Filter.Tendsto.congr' ?_ hFa
    filter_upwards [self_mem_nhdsWithin, hlt_a] with x hx hxc
    exact (hFTC x ⟨hx, hxc⟩).symm
  -- Newton–Leibniz on the part of the interval to the right of `c`
  have hFTCb : ∀ x ∈ Set.Ioo c b, f x = f c + ∫ t in c..x, f' t := by
    intro x hx
    have hsub' : ∀ y ∈ Set.uIcc c x, y ∈ Set.Ioo a b := by
      intro y hy
      rw [Set.uIcc_of_le hx.1.le] at hy
      exact ⟨lt_of_lt_of_le hac hy.1, lt_of_le_of_lt hy.2 hx.2⟩
    have hsub : Set.uIoc c x ⊆ Set.Icc a b := by
      rw [Set.uIoc_of_le hx.1.le]
      exact fun y hy => ⟨le_trans hac.le hy.1.le, le_trans hy.2 hx.2.le⟩
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hderiv y (hsub' y hy)) (hII hsub)
    linarith [h]
  have hmodel_b : Filter.Tendsto (fun x => (f c + ∫ t in c..b, f' t) - ∫ t in x..b, f' t)
      (nhdsWithin b (Set.Iio b)) (nhds (f c + ∫ t in c..b, f' t)) := by
    have h := (tendsto_const_nhds (x := f c + ∫ t in c..b, f' t)).sub keyB
    simpa using h
  have heq_b : (fun x => f c + ∫ t in c..x, f' t) =ᶠ[nhdsWithin b (Set.Iio b)]
      (fun x => (f c + ∫ t in c..b, f' t) - ∫ t in x..b, f' t) := by
    filter_upwards [self_mem_nhdsWithin, hlt_b] with x hx hxc
    have h1 : IntervalIntegrable f' MeasureTheory.volume c x := hII (by
      rw [Set.uIoc_of_le hxc.le]
      exact fun y hy => ⟨le_trans hac.le hy.1.le, le_trans hy.2 (le_of_lt hx)⟩)
    have h2 : IntervalIntegrable f' MeasureTheory.volume x b := hII (by
      rw [Set.uIoc_of_le hx.le]
      exact fun y hy => ⟨le_trans hac.le (le_trans hxc.le hy.1.le), hy.2⟩)
    have h := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [h]
  have hFb : Filter.Tendsto (fun x => f c + ∫ t in c..x, f' t) (nhdsWithin b (Set.Iio b))
      (nhds (f c + ∫ t in c..b, f' t)) := Filter.Tendsto.congr' heq_b.symm hmodel_b
  have hfb : Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds (f c + ∫ t in c..b, f' t)) := by
    refine Filter.Tendsto.congr' ?_ hFb
    filter_upwards [self_mem_nhdsWithin, hlt_b] with x hx hxc
    exact (hFTCb x ⟨hxc, hx⟩).symm
  refine ⟨f c - ∫ t in a..c, f' t, f c + ∫ t in c..b, f' t, hfa, hfb, ?_⟩
  -- the integral over `(a,b)` is the sum of the two halves, by Chasles
  have h1 : IntervalIntegrable f' MeasureTheory.volume a c := hII (by
    rw [Set.uIoc_of_le hac.le]
    exact fun y hy => ⟨hy.1.le, le_trans hy.2 hcb.le⟩)
  have h2 : IntervalIntegrable f' MeasureTheory.volume c b := hII (by
    rw [Set.uIoc_of_le hcb.le]
    exact fun y hy => ⟨le_trans hac.le hy.1.le, hy.2⟩)
  have h := intervalIntegral.integral_add_adjacent_intervals h1 h2
  rw [intervalIntegral.integral_of_le hab.le, MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  linarith [h]

end Work.FTS.EllipticEst.H2W.I1cb
