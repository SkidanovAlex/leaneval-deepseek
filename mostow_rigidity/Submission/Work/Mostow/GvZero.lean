import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.barycentre
import Submission.Work.Mostow.segfunHdist
import Submission.Work.Mostow.segfunHasDerivAt
import Submission.Work.Mostow.segfunSpeed
import Submission.Work.Mostow.BusemannLipschitz
import Submission.Work.Mostow.tpartSegfun
import Submission.Work.Mostow.BaryMidpointGen

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped Real ENNReal Topology

noncomputable section

variable {n : ℕ}


/-! ## Pushforward of the visual measure along a bijection of the boundary sphere -/

/-- A map which is continuous on the boundary sphere is a.e. measurable for any measure
carried by the sphere. -/
private lemma gz_aemeasurable_of_continuousOn_sphere {φ : E n → E n}
    (hcont : ContinuousOn φ (Sph n)) (μ : Measure (E n)) (hμ : μ (Sph n)ᶜ = 0) :
    AEMeasurable φ μ := by
  have hSp : MeasurableSet (Sph n) := Metric.isClosed_sphere.measurableSet
  have hcont' : Continuous ((Sph n).domRestrict φ) :=
    continuousOn_iff_continuous_domRestrict.mp hcont
  have hmeas : Measurable (fun x : (Sph n : Set (E n)) => φ x) := hcont'.measurable
  have hae : AEMeasurable φ (μ.restrict (Sph n)) :=
    aemeasurable_restrict_of_measurable_subtype hSp hmeas
  rwa [Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hμ)] at hae

/-- Evaluation of the pushforward of the visual measure on a measurable set. -/
lemma gz_map_visual_apply {φ : E n → E n} (hV : VisualProp n)
    (hcont : ContinuousOn φ (Sph n)) (u : E n) (s : Set (E n)) (hs : MeasurableSet s) :
    ((visual n u).map φ) s = visual n u (φ ⁻¹' s) :=
  Measure.map_apply_of_aemeasurable (gz_aemeasurable_of_continuousOn_sphere hcont _ (hV u).2.1) hs

/-- The pushforward of a visual measure is a probability measure. -/
lemma gz_map_visual_isProbability {φ : E n → E n} (hV : VisualProp n)
    (hcont : ContinuousOn φ (Sph n)) (u : E n) :
    IsProbabilityMeasure ((visual n u).map φ) :=
  (Measure.isProbabilityMeasure_map_iff
    (gz_aemeasurable_of_continuousOn_sphere hcont _ (hV u).2.1)).mpr (hV u).1

/-- The pushforward of a visual measure is carried by the boundary sphere. -/
lemma gz_map_visual_compl_sphere {φ : E n → E n} (hV : VisualProp n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n)) (u : E n) :
    ((visual n u).map φ) (Sph n)ᶜ = 0 := by
  rw [gz_map_visual_apply hV hcont u (Sph n)ᶜ (Metric.isClosed_sphere.measurableSet.compl)]
  refine measure_mono_null ?_ (hV u).2.1
  intro x hx
  exact fun hxS => hx (hbij.mapsTo hxS)

/-- The pushforward of a visual measure is atomless. -/
lemma gz_map_visual_singleton {φ : E n → E n} (hV : VisualProp n)
    (hbij : Set.BijOn φ (Sph n) (Sph n)) (hcont : ContinuousOn φ (Sph n)) (u ξ : E n) :
    ((visual n u).map φ) {ξ} = 0 := by
  rw [gz_map_visual_apply hV hcont u {ξ} (measurableSet_singleton ξ)]
  by_cases hξ : ξ ∈ Sph n
  · obtain ⟨w, hwS, hw⟩ := hbij.surjOn hξ
    have hsub : φ ⁻¹' {ξ} ⊆ (Sph n)ᶜ ∪ {w} := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      by_cases hxS : x ∈ Sph n
      · refine Or.inr (Set.mem_singleton_iff.mpr ?_)
        exact hbij.injOn hxS hwS (by rw [hx, hw])
      · exact Or.inl hxS
    refine measure_mono_null hsub ?_
    rw [measure_union_null_iff]
    exact ⟨(hV u).2.1, (hV u).2.2.1 w⟩
  · have hsub : φ ⁻¹' {ξ} ⊆ (Sph n)ᶜ := by
      intro x hx hxS
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      exact hξ (hx ▸ hbij.mapsTo hxS)
    exact measure_mono_null hsub (hV u).2.1


/-! ## The Busemann argument is linear along a geodesic segment -/

/-- `sinh a + sinh b = 2 sinh ((a+b)/2) cosh ((a-b)/2)`. -/
lemma gz_sinh_add_sinh (a b : ℝ) :
    Real.sinh a + Real.sinh b = 2 * Real.sinh ((a + b) / 2) * Real.cosh ((a - b) / 2) := by
  have h₁ := Real.sinh_add ((a + b) / 2) ((a - b) / 2)
  have h₂ := Real.sinh_sub ((a + b) / 2) ((a - b) / 2)
  rw [show (a + b) / 2 + (a - b) / 2 = a from by ring] at h₁
  rw [show (a + b) / 2 - (a - b) / 2 = b from by ring] at h₂
  rw [h₁, h₂]
  ring

/-- The inner product of a point of the geodesic segment `segfun y w ·` with a fixed vector. -/
lemma gz_inner_segfun (y w ξ : E n) (r : ℝ) :
    inner ℝ (segfun y w r) ξ =
      (Real.sinh (hdist y w - r) * inner ℝ y ξ + Real.sinh r * inner ℝ w ξ) /
        Real.sinh (hdist y w) := by
  rw [segfun, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  ring

/-- On the segment, the Busemann argument `tpart · - ⟪·,η⟫` is the corresponding linear
combination of the values at the endpoints. -/
lemma gz_tpart_sub_inner_segfun (y w η : E n) (hyw : y ≠ w) {r : ℝ}
    (hr : r ∈ Set.Icc 0 (hdist y w)) :
    tpart (segfun y w r) - inner ℝ (segfun y w r) η =
      (Real.sinh (hdist y w - r) * (tpart y - inner ℝ y η) +
        Real.sinh r * (tpart w - inner ℝ w η)) / Real.sinh (hdist y w) := by
  have hsinh : Real.sinh (hdist y w) ≠ 0 := sinh_hdist_ne_zero hyw
  rw [tpartSegfun y w r hsinh hr, gz_inner_segfun y w η r]
  field_simp
  ring

/-- The scalar identity underlying the midpoint convexity of the Busemann function. -/
lemma gz_mid_scalar (d s t Ay Aw : ℝ) (hd : Real.sinh d ≠ 0) :
    (Real.sinh (d - (s + t) / 2) * Ay + Real.sinh ((s + t) / 2) * Aw) / Real.sinh d =
      ((Real.sinh (d - s) * Ay + Real.sinh s * Aw) / Real.sinh d +
        (Real.sinh (d - t) * Ay + Real.sinh t * Aw) / Real.sinh d) /
      (2 * Real.cosh ((t - s) / 2)) := by
  have h₁ := gz_sinh_add_sinh (d - s) (d - t)
  rw [show (d - s + (d - t)) / 2 = d - (s + t) / 2 from by ring,
      show (d - s - (d - t)) / 2 = (t - s) / 2 from by ring] at h₁
  have h₂ := gz_sinh_add_sinh s t
  rw [show (s - t) / 2 = -((t - s) / 2) from by ring, Real.cosh_neg] at h₂
  have hstep : (Real.sinh (d - s) * Ay + Real.sinh s * Aw) / Real.sinh d +
        (Real.sinh (d - t) * Ay + Real.sinh t * Aw) / Real.sinh d =
      ((Real.sinh (d - s) + Real.sinh (d - t)) * Ay +
        (Real.sinh s + Real.sinh t) * Aw) / Real.sinh d := by
    rw [← add_div]
    ring
  rw [hstep, h₁, h₂]
  field_simp

/-- The Busemann argument at the hyperbolic midpoint of two points of a segment. -/
lemma gz_mid_arg (y w : E n) (hyw : y ≠ w) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 (hdist y w)) (ht : t ∈ Set.Icc 0 (hdist y w)) (η : E n) :
    tpart (segfun y w ((s + t) / 2)) - inner ℝ (segfun y w ((s + t) / 2)) η =
      ((tpart (segfun y w s) - inner ℝ (segfun y w s) η) +
        (tpart (segfun y w t) - inner ℝ (segfun y w t) η)) /
      (2 * Real.cosh (hdist (segfun y w s) (segfun y w t) / 2)) := by
  have hsinh : Real.sinh (hdist y w) ≠ 0 := sinh_hdist_ne_zero hyw
  have hu : (s + t) / 2 ∈ Set.Icc 0 (hdist y w) :=
    ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
  have hDt : hdist (segfun y w s) (segfun y w t) = |s - t| := segfunHdist y w hyw s t hs ht
  rw [gz_tpart_sub_inner_segfun y w η hyw hu, gz_tpart_sub_inner_segfun y w η hyw hs,
    gz_tpart_sub_inner_segfun y w η hyw ht, hDt]
  have hcosh : Real.cosh (|s - t| / 2) = Real.cosh ((t - s) / 2) := by
    rw [show |s - t| / 2 = |(s - t) / 2| from by rw [abs_div]; norm_num, Real.cosh_abs]
    rw [show (s - t) / 2 = -((t - s) / 2) from by ring, Real.cosh_neg]
  rw [hcosh]
  exact gz_mid_scalar (hdist y w) s t (tpart y - inner ℝ y η) (tpart w - inner ℝ w η) hsinh

/-- **Midpoint convexity of the Busemann function along a geodesic segment.** -/
lemma gz_busemann_midpoint (y w η : E n) (hyw : y ≠ w) (hη : η ∈ Sph n) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 (hdist y w)) (ht : t ∈ Set.Icc 0 (hdist y w)) :
    2 * busemann η (segfun y w ((s + t) / 2)) ≤
      busemann η (segfun y w s) + busemann η (segfun y w t) :=
  convex_midpoint (fun ξ _ => gz_mid_arg y w hyw hs ht ξ)
    (fun ξ hξ => BusemannLipschitz n ξ hξ _ _) η hη


/-! ## Midpoint convexity of the barycentre functional along a geodesic -/

/-- Pointwise midpoint convexity integrates against the visual measure. -/
lemma gz_baryFun_midpoint (ν : Measure (E n)) (hν : IsProbabilityMeasure ν)
    (hsupp : ν (Sph n)ᶜ = 0) (y w : E n) (hyw : y ≠ w) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 (hdist y w)) (ht : t ∈ Set.Icc 0 (hdist y w)) :
    2 * baryFun ν (segfun y w ((s + t) / 2)) ≤
      baryFun ν (segfun y w s) + baryFun ν (segfun y w t) := by
  have hae : ∀ᵐ ξ ∂ν, ξ ∈ Sph n := by rw [ae_iff]; exact hsupp
  have h₁ := integrable_busemann ν hν hsupp (segfun y w ((s + t) / 2))
  have h₂ := integrable_busemann ν hν hsupp (segfun y w s)
  have h₃ := integrable_busemann ν hν hsupp (segfun y w t)
  have hle : (fun ξ => 2 * busemann ξ (segfun y w ((s + t) / 2))) ≤ᵐ[ν]
      fun ξ => busemann ξ (segfun y w s) + busemann ξ (segfun y w t) := by
    filter_upwards [hae] with ξ hξ
    exact gz_busemann_midpoint y w ξ hyw hξ hs ht
  have h := integral_mono_ae (h₁.const_mul 2) (h₂.add h₃) hle
  rw [integral_const_mul] at h
  simp only [Pi.add_apply] at h
  rw [integral_add h₂ h₃] at h
  exact h

/-- A midpoint-convex function on `[0,d]` whose derivative at `0` vanishes satisfies
`h 0 ≤ h d`.  (The dyadic points `d/2^k` together with the vanishing slope at `0` suffice.) -/
lemma gz_le_of_midpointConvex_of_hasDerivAt_zero {h : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hmid : ∀ s ∈ Set.Icc 0 d, ∀ t ∈ Set.Icc 0 d, 2 * h ((s + t) / 2) ≤ h s + h t)
    (hder : HasDerivAt h 0 0) : h 0 ≤ h d := by
  by_contra hcon
  push_neg at hcon
  set c0 : ℝ := h d - h 0 with hc0
  have hc0neg : c0 < 0 := by rw [hc0]; linarith
  have hmem : ∀ k : ℕ, d / (2 : ℝ) ^ k ∈ Set.Icc 0 d := by
    intro k
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    exact ⟨div_nonneg hd.le h2.le, by
      rw [div_le_iff₀ h2]
      nlinarith [h1, hd.le]⟩
  have hind : ∀ k : ℕ, h (d / (2 : ℝ) ^ k) - h 0 ≤ c0 / (2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp [hc0]
    | succ k ih =>
      have h0mem : (0 : ℝ) ∈ Set.Icc 0 d := ⟨le_refl 0, hd.le⟩
      have hstep : (0 + d / (2 : ℝ) ^ k) / 2 = d / (2 : ℝ) ^ (k + 1) := by
        rw [zero_add, pow_succ, div_div]
      have hm := hmid 0 h0mem (d / (2 : ℝ) ^ k) (hmem k)
      rw [hstep] at hm
      have h1 : h (d / (2 : ℝ) ^ (k + 1)) - h 0 ≤ (h (d / (2 : ℝ) ^ k) - h 0) / 2 := by
        linarith
      have h2 : (c0 / (2 : ℝ) ^ k) / 2 = c0 / (2 : ℝ) ^ (k + 1) := by
        rw [pow_succ, div_div]
      linarith [h1, ih, h2.le, h2.ge]
  have hq : ∀ k : ℕ, (h (d / (2 : ℝ) ^ k) - h 0) / (d / (2 : ℝ) ^ k) ≤ c0 / d := by
    intro k
    have h2 : (0 : ℝ) < d / (2 : ℝ) ^ k := by
      have : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      positivity
    have hmul := div_le_div_of_nonneg_right (hind k) h2.le
    have heq : (c0 / (2 : ℝ) ^ k) / (d / (2 : ℝ) ^ k) = c0 / d := by
      field_simp
    linarith [hmul, heq.le, heq.ge]
  have hlim : Filter.Tendsto (fun k : ℕ => (h (d / (2 : ℝ) ^ k) - h 0) / (d / (2 : ℝ) ^ k))
      Filter.atTop (𝓝 0) := by
    have hslope : Filter.Tendsto (slope h 0) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      hasDerivAt_iff_tendsto_slope.mp hder
    have hz : Filter.Tendsto (fun k : ℕ => d / (2 : ℝ) ^ k) Filter.atTop (𝓝[≠] (0 : ℝ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hp : Filter.Tendsto (fun k : ℕ => ((1 : ℝ) / 2) ^ k) Filter.atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
        have := hp.const_mul d
        simpa [div_eq_mul_inv, inv_pow, one_div] using this
      · filter_upwards with k
        exact div_ne_zero hd.ne' (by positivity)
    have := hslope.comp hz
    simpa [slope_def_field, sub_zero, Function.comp_def] using this
  have hfin := le_of_tendsto hlim (Filter.Eventually.of_forall (fun k => hq k))
  have hneg : c0 / d < 0 := div_neg_of_neg_of_pos hc0neg hd
  linarith


/-! ## The two endpoints of the segment -/

lemma gz_segfun_zero (p q : E n) (hpq : p ≠ q) : segfun p q 0 = p := by
  have hsinh : Real.sinh (hdist p q) ≠ 0 := sinh_hdist_ne_zero hpq
  rw [segfun, sub_zero, Real.sinh_zero, zero_div, zero_smul, add_zero, div_self hsinh, one_smul]

lemma gz_segfun_end (p q : E n) (hpq : p ≠ q) : segfun p q (hdist p q) = q := by
  have hsinh : Real.sinh (hdist p q) ≠ 0 := sinh_hdist_ne_zero hpq
  rw [segfun, sub_self, Real.sinh_zero, zero_div, zero_smul, zero_add, div_self hsinh, one_smul]

theorem GvZero (n : ℕ) (hV : Submission.Mostow.VisualProp n) (hB : Submission.Mostow.BaryProp n)
    (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hbary : ∀ x y : Submission.Mostow.E n,
      Work.Mostow.Phi n φ x y = Submission.Mostow.baryFun ((Submission.Mostow.visual n x).map φ) y)
    (hder : ∀ x y : Submission.Mostow.E n,
      HasFDerivAt (fun y => Work.Mostow.Phi n φ x y)
        (innerSL ℝ (Work.Mostow.Gv n φ x y)) y) :
    ∀ x y : Submission.Mostow.E n, Work.Mostow.Gv n φ x y = 0 ↔ y = Submission.Mostow.natMap φ x := by
  intro x y
  -- the pushed-forward visual measure and the facts the barycentre theorem needs
  set ν : Measure (E n) := (visual n x).map φ with hνdef
  have hprob : IsProbabilityMeasure ν := gz_map_visual_isProbability hV hcont x
  haveI := hprob
  have hsupp : ν (Sph n)ᶜ = 0 := gz_map_visual_compl_sphere hV hbij hcont x
  have hatom : ∀ ξ : E n, ν {ξ} = 0 := fun ξ => gz_map_visual_singleton hV hbij hcont x ξ
  obtain ⟨hmin, huniq, -⟩ := hB ν hprob hsupp hatom
  have hbar : natMap φ x = bar ν := by simp only [natMap, ← hνdef]
  have hzeq : ∀ z : E n, Phi n φ x z = baryFun ν z :=
    fun z => by rw [hbary x z, ← hνdef]
  constructor
  · -- a vanishing gradient is a minimum: convexity of the barycentre functional along a geodesic
    intro hGv
    rw [hbar]
    by_contra hne
    set d : ℝ := hdist y (bar ν) with hd
    have hdpos : 0 < d := by rw [hd]; exact hdist_pos_of_ne hne
    have hmem0 : (0 : ℝ) ∈ Set.Icc 0 d := ⟨le_refl 0, hdpos.le⟩
    have hmemHS : (0 : ℝ) ∈ Set.Icc 0 (hdist y (bar ν)) := by rw [← hd]; exact hmem0
    -- the midpoint convexity of `u ↦ baryFun ν (segfun y (bar ν) u)` on `[0,d]`
    have hmid : ∀ s ∈ Set.Icc 0 d, ∀ t ∈ Set.Icc 0 d,
        2 * (fun u => baryFun ν (segfun y (bar ν) u)) ((s + t) / 2) ≤
          (fun u => baryFun ν (segfun y (bar ν) u)) s +
            (fun u => baryFun ν (segfun y (bar ν) u)) t := by
      intro s hs t ht
      have hs' : s ∈ Set.Icc 0 (hdist y (bar ν)) := by rw [← hd]; exact hs
      have ht' : t ∈ Set.Icc 0 (hdist y (bar ν)) := by rw [← hd]; exact ht
      exact gz_baryFun_midpoint ν hprob hsupp y (bar ν) hne hs' ht'
    -- the derivative of that function at `0` is the gradient of `Phi`, hence vanishes
    have hψder : HasDerivAt (fun u => baryFun ν (segfun y (bar ν) u)) 0 0 := by
      have hseg := segfunHasDerivAt y (bar ν) hne 0 hmemHS
      have hf0 : HasFDerivAt (fun z : E n => Phi n φ x z) (innerSL ℝ (Gv n φ x y))
          (segfun y (bar ν) 0) := by
        rw [gz_segfun_zero y (bar ν) hne]
        exact hder x y
      have hcomp := hf0.comp_hasDerivAt 0 hseg
      have hcomp' : HasDerivAt (fun u => baryFun ν (segfun y (bar ν) u))
          ((innerSL ℝ (Gv n φ x y))
            ((-Real.cosh (hdist y (bar ν) - 0) / Real.sinh (hdist y (bar ν))) • y +
              (Real.cosh 0 / Real.sinh (hdist y (bar ν))) • bar ν)) 0 := by
        have hfun : (fun u => Phi n φ x (segfun y (bar ν) u)) =
            fun u => baryFun ν (segfun y (bar ν) u) :=
          funext fun u => hzeq (segfun y (bar ν) u)
        simpa only [Function.comp_def, hfun] using hcomp
      have hz : (innerSL ℝ (Gv n φ x y))
          ((-Real.cosh (hdist y (bar ν) - 0) / Real.sinh (hdist y (bar ν))) • y +
            (Real.cosh 0 / Real.sinh (hdist y (bar ν))) • bar ν) = 0 := by
        rw [hGv]
        simp
      rwa [hz] at hcomp'
    have hle := gz_le_of_midpointConvex_of_hasDerivAt_zero
      (h := fun u => baryFun ν (segfun y (bar ν) u)) hdpos hmid hψder
    rw [gz_segfun_zero y (bar ν) hne, gz_segfun_end y (bar ν) hne] at hle
    -- hence `y` is also a minimiser, so it equals the barycentre
    have hymin : ∀ z : E n, baryFun ν y ≤ baryFun ν z := by
      intro z
      have hEq : baryFun ν y = baryFun ν (bar ν) := le_antisymm hle (hmin y)
      rw [hEq]
      exact hmin z
    exact absurd (huniq y hymin) hne
  · -- at the barycentre the gradient of `Phi` vanishes (Fermat)
    intro hy
    have hy' : y = bar ν := by rw [hy, hbar]
    have hminOn : IsMinOn (fun z : E n => baryFun ν z) Set.univ (bar ν) := fun z _ => hmin z
    have hloc : IsLocalMin (fun z : E n => baryFun ν z) (bar ν) :=
      hminOn.isLocalMin (Filter.Eventually.of_forall fun _ => trivial)
    have hderbar : HasFDerivAt (fun z : E n => baryFun ν z)
        (innerSL ℝ (Gv n φ x (bar ν))) (bar ν) := by
      have h := hder x (bar ν)
      rwa [funext hzeq] at h
    have hzero : innerSL ℝ (Gv n φ x (bar ν)) = 0 := hloc.hasFDerivAt_eq_zero hderbar
    have hGvbar : Gv n φ x (bar ν) = 0 := by
      have h2 := congrArg (fun L : E n →L[ℝ] ℝ => L (Gv n φ x (bar ν))) hzero
      simp only [ContinuousLinearMap.zero_apply] at h2
      rw [innerSL_apply_apply] at h2
      exact inner_self_eq_zero.mp h2
    simpa [hy'] using hGvbar

end

end Work.Mostow

