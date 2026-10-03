import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.green_reduction.sector_chartBall_freeDirection
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-!
# The no-tangency reduction: two balls through a frontier point suffice

This module upgrades the reduction of the target theorem
`Work.SimplyConnected.ABS.green_reduction.exists_barrier_regular_precompact_region` to a form in
which the geometric hypothesis on the family of chart balls is purely local and *combinatorial*:

> at every point of the closed union outside the open union, (i) **at most two** of the closed balls
> contain the point, and (ii) any two of them are **not externally tangent** there.

Condition (i) excludes the pinwheel configurations (three or more balls through a point) and
condition (ii) excludes external tangency; together they produce the *free direction* of
`hasSectorBoundary_iUnion_chartBall_of_freeDirection`, hence the sector condition, hence a barrier.

The two ingredients are elementary:

* `exists_pos_of_not_neg_smul`: two non-zero complex numbers which are not negative multiples of one
  another admit a common strictly positive direction `v`, i.e. `Re (conj m i * v) > 0` for both.
  This is the unit-vector wedge lemma `exists_wedge_witness_of_ne_neg` after normalisation.
* `deriv_transition_ne_zero`: the derivative of a chart transition never vanishes (the transition
  is injective near its point, and `Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn`).

The resulting reduction `exists_barrier_regular_precompact_region_of_twofold` consumes, instead of
a free direction, the two conditions (i) and (ii), and is the form in which the geometric
construction of the family (a *beaded* cover: a chain of small chart balls attached at boundary
points of the previous ones, each pair crossing transversally) is to be verified.
-/

namespace Work.SimplyConnected.ABS.green_reduction

open scoped _root_.Topology Manifold ContDiff ComplexConjugate
open Set Filter

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Two non-antipodal vectors have a common strictly positive direction -/

/-- If the normalised vectors of `m₁` and `m₂` are negatives of each other, then `m₂` is a negative
multiple of `m₁`. -/
lemma eq_neg_smul_of_unit_smul_eq {m₁ m₂ : ℂ} (h₂ : m₂ ≠ 0)
    (h : (‖m₂‖⁻¹) • m₂ = -((‖m₁‖⁻¹) • m₁)) :
    m₂ = -(((‖m₂‖ * ‖m₁‖⁻¹ : ℝ)) • m₁) := by
  have h₂ne : ‖m₂‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr h₂)
  calc m₂ = ‖m₂‖ • ((‖m₂‖⁻¹) • m₂) := by
        rw [smul_smul, mul_inv_cancel₀ h₂ne, one_smul]
    _ = ‖m₂‖ • (-((‖m₁‖⁻¹) • m₁)) := by rw [h]
    _ = -(((‖m₂‖ * ‖m₁‖⁻¹ : ℝ)) • m₁) := by rw [smul_neg, smul_smul]

/-- **Two non-antipodal non-zero complex numbers have a common strictly positive direction.**

This is the unit-vector wedge lemma `Work.SimplyConnected.ABS.exists_wedge_witness_of_ne_neg`
applied to the normalisations of `m₁` and `m₂`; the case `m₂ = -t m₁` (`t > 0`) is exactly the
case in which the two normalised vectors are negatives of each other. -/
theorem exists_pos_of_not_neg_smul {m₁ m₂ : ℂ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0)
    (h : ∀ t : ℝ, 0 < t → m₂ ≠ -(t • m₁)) :
    ∃ v : ℂ, 0 < (starRingEnd ℂ m₁ * v).re ∧ 0 < (starRingEnd ℂ m₂ * v).re := by
  have h₁pos : 0 < ‖m₁‖ := norm_pos_iff.mpr h₁
  have h₂pos : 0 < ‖m₂‖ := norm_pos_iff.mpr h₂
  have hu₁ : ‖(‖m₁‖⁻¹) • m₁‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr h₁pos.le),
      inv_mul_cancel₀ (ne_of_gt h₁pos)]
  have hu₂ : ‖(‖m₂‖⁻¹) • m₂‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr h₂pos.le),
      inv_mul_cancel₀ (ne_of_gt h₂pos)]
  have hne : (‖m₁‖⁻¹) • m₁ ≠ -((‖m₂‖⁻¹) • m₂) := by
    intro hcon
    exact h (‖m₂‖ * ‖m₁‖⁻¹) (mul_pos h₂pos (inv_pos.mpr h₁pos))
      (eq_neg_smul_of_unit_smul_eq h₂ (by rw [hcon, neg_neg]))
  obtain ⟨w, hw₁, hw₂⟩ := Work.SimplyConnected.ABS.exists_wedge_witness_of_ne_neg hu₁ hu₂ hne
  refine ⟨w, ?_, ?_⟩
  · rw [show m₁ = (‖m₁‖ : ℂ) * ((‖m₁‖⁻¹) • m₁) from by
        rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (ne_of_gt h₁pos), Complex.ofReal_one, one_mul]]
    rw [map_mul, Complex.conj_ofReal, mul_assoc]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simp only [zero_mul, sub_zero]
    exact mul_pos h₁pos hw₁
  · rw [show m₂ = (‖m₂‖ : ℂ) * ((‖m₂‖⁻¹) • m₂) from by
        rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ (ne_of_gt h₂pos), Complex.ofReal_one, one_mul]]
    rw [map_mul, Complex.conj_ofReal, mul_assoc]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simp only [zero_mul, sub_zero]
    exact mul_pos h₂pos hw₂

/-! ## The derivative of a chart transition never vanishes -/

/-- **The derivative of a chart transition does not vanish.**  The transition
`z ↦ c (d.symm z)` is injective on a neighbourhood of `z`, being a composite of two partial
homeomorphisms; `Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn` then gives the claim. -/
theorem deriv_transition_ne_zero {c d : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X)
    (hd : d ∈ atlas ℂ X) {z : ℂ} (hz : z ∈ d.target) (hzs : d.symm z ∈ c.source) :
    deriv (fun w => c (d.symm w)) z ≠ 0 := by
  have hAnal : AnalyticAt ℂ (fun w => c (d.symm w)) z :=
    Submission.analyticAt_transition_of_mem_atlas hc hd z hz hzs
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.isOpen_iff.mp d.open_target z hz
  have hcont : ContinuousAt (fun w => d.symm w) z :=
    d.continuousOn_symm.continuousAt (d.open_target.mem_nhds hz)
  obtain ⟨r₂, hr₂, hr₂sub⟩ :=
    Metric.mem_nhds_iff.mp (hcont.preimage_mem_nhds (c.open_source.mem_nhds hzs))
  refine Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn (lt_min hr₁ hr₂) hAnal ?_
  intro z' hz' z'' hz'' hEq
  have hz'T : z' ∈ d.target := hr₁sub (Metric.ball_subset_ball (min_le_left _ _) hz')
  have hz''T : z'' ∈ d.target := hr₁sub (Metric.ball_subset_ball (min_le_left _ _) hz'')
  have hz'S : d.symm z' ∈ c.source := hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hz')
  have hz''S : d.symm z'' ∈ c.source := hr₂sub (Metric.ball_subset_ball (min_le_right _ _) hz'')
  have h1 : d.symm z' = d.symm z'' := c.injOn hz'S hz''S hEq
  exact d.symm.injOn hz'T hz''T h1

/-! ## The normal of a chart ball at a point, in the chart at that point -/

/-- The outward normal vector of the ball `chartBall cc a ρ` at the point `p` of its sphere,
expressed in the chart `chartAt ℂ p`: the product of the radial vector `(cc p - a)` with the
conjugate of the derivative of the transition to the chart at `p`. -/
noncomputable def normalAt (cc : OpenPartialHomeomorph X ℂ) (a : ℂ) (p : X) : ℂ :=
  (cc p - a) * starRingEnd ℂ
    (deriv (fun z => cc ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p))

/-- The free-direction functional is the pairing with the normal. -/
lemma functional_eq_reConj_normalAt (cc : OpenPartialHomeomorph X ℂ) (a : ℂ) (p : X) (v : ℂ) :
    (starRingEnd ℂ (cc p - a) *
        deriv (fun z => cc ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) * v).re
      = (starRingEnd ℂ (normalAt cc a p) * v).re := by
  simp only [normalAt, map_mul, Complex.conj_conj]

/-! ## The conormal field in another reference chart -/

/-- The chain rule for chart transitions: the derivative of `c ∘ (chartAt ℂ q).symm` at
`(chartAt ℂ q) q` factors through any other chart `d` containing `q`. -/
lemma deriv_transition_comp {c d : OpenPartialHomeomorph X ℂ} {q : X}
    (hc : c ∈ atlas ℂ X) (hd : d ∈ atlas ℂ X) (hqc : q ∈ c.source) (hqd : q ∈ d.source) :
    deriv (fun z => c ((chartAt ℂ q).symm z)) ((chartAt ℂ q) q)
      = deriv (fun z => c (d.symm z)) (d q) *
        deriv (fun z => d ((chartAt ℂ q).symm z)) ((chartAt ℂ q) q) := by
  set e : OpenPartialHomeomorph X ℂ := chartAt ℂ q with he
  set b₀ : ℂ := e q with hb₀def
  have hb₀t : b₀ ∈ e.target := e.map_source (mem_chart_source ℂ q)
  have hesymm : e.symm b₀ = q := by
    rw [hb₀def]; exact e.left_inv (mem_chart_source ℂ q)
  have hcont : ContinuousAt (fun z => e.symm z) b₀ :=
    e.continuousOn_symm.continuousAt (e.open_target.mem_nhds hb₀t)
  have hev : ∀ᶠ z in 𝓝 b₀, e.symm z ∈ d.source := by
    refine hcont.preimage_mem_nhds (d.open_source.mem_nhds ?_)
    rw [hesymm]
    exact hqd
  have hfun : (fun z => c (e.symm z))
      =ᶠ[𝓝 b₀] ((fun z => c (d.symm z)) ∘ (fun z => d (e.symm z))) := by
    filter_upwards [hev] with z hz
    simp only [Function.comp_apply]
    rw [d.left_inv hz]
  have hd₁ : DifferentiableAt ℂ (fun z => c (d.symm z)) (d q) :=
    (Submission.analyticAt_transition_of_mem_atlas hc hd (d q) (d.map_source hqd)
      (by rw [d.left_inv hqd]; exact hqc)).differentiableAt
  have hd₂ : DifferentiableAt ℂ (fun z => d (e.symm z)) b₀ :=
    (Submission.analyticAt_transition_of_mem_atlas hd (chart_mem_atlas ℂ q) b₀ hb₀t
      (by rw [hesymm]; exact hqd)).differentiableAt
  rw [hfun.deriv_eq]
  have hd₁' : DifferentiableAt ℂ (fun z => c (d.symm z)) ((fun z => d (e.symm z)) b₀) := by
    simpa only [hesymm] using hd₁
  have hcomp := ((hasDerivAt_deriv_iff.mpr hd₁').comp b₀
    (hasDerivAt_deriv_iff.mpr hd₂)).deriv
  rw [hcomp]
  simp only [Function.comp_apply, hesymm]

/-- **The conormal of a chart ball in another reference chart.**  Changing the reference chart at
`q` from `chartAt ℂ q` to `d` multiplies the conormal by the same factor
`conj (deriv (d ∘ (chartAt ℂ q).symm) ((chartAt ℂ q) q))` for every chart ball. -/
lemma normalAt_chart_transport {c d : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X)
    (hd : d ∈ atlas ℂ X) {a : ℂ} {q : X} (hqc : q ∈ c.source) (hqd : q ∈ d.source) :
    normalAt c a q = ((c q - a) * starRingEnd ℂ (deriv (fun z => c (d.symm z)) (d q))) *
      starRingEnd ℂ (deriv (fun z => d ((chartAt ℂ q).symm z)) ((chartAt ℂ q) q)) := by
  rw [normalAt, deriv_transition_comp hc hd hqc hqd, map_mul]
  ring

/-- **Non-antipodality is independent of the reference chart.**  Two conormals are negative
multiples of one another in the chart at `q` if and only if they are so in any other chart `d`
containing `q`; indeed both conormals are multiplied by the same non-zero factor. -/
lemma neg_smul_normalAt_iff {c₁ c₂ d : OpenPartialHomeomorph X ℂ}
    (h₁ : c₁ ∈ atlas ℂ X) (h₂ : c₂ ∈ atlas ℂ X) (hd : d ∈ atlas ℂ X) {a₁ a₂ : ℂ} {q : X}
    (hq₁ : q ∈ c₁.source) (hq₂ : q ∈ c₂.source) (hqd : q ∈ d.source) {t : ℝ} :
    normalAt c₁ a₁ q = -(t • normalAt c₂ a₂ q) ↔
      (c₁ q - a₁) * starRingEnd ℂ (deriv (fun z => c₁ (d.symm z)) (d q)) =
        -(t • ((c₂ q - a₂) * starRingEnd ℂ (deriv (fun z => c₂ (d.symm z)) (d q)))) := by
  set T : ℂ := starRingEnd ℂ (deriv (fun z => d ((chartAt ℂ q).symm z)) ((chartAt ℂ q) q))
    with hTdef
  have hTne : T ≠ 0 := by
    have hne : deriv (fun z => d ((chartAt ℂ q).symm z)) ((chartAt ℂ q) q) ≠ 0 :=
      deriv_transition_ne_zero hd (chart_mem_atlas ℂ q) ((chartAt ℂ q).map_source (mem_chart_source ℂ q))
        (by rw [(chartAt ℂ q).left_inv (mem_chart_source ℂ q)]; exact hqd)
    rw [hTdef]
    intro h
    exact hne (by simpa using congrArg (starRingEnd ℂ) h)
  have htr₁ := normalAt_chart_transport (a := a₁) h₁ hd hq₁ hqd
  have htr₂ := normalAt_chart_transport (a := a₂) h₂ hd hq₂ hqd
  constructor
  · intro h
    rw [htr₁, htr₂] at h
    have h' : ((c₁ q - a₁) * starRingEnd ℂ (deriv (fun z => c₁ (d.symm z)) (d q))) * T
        = (-(t • ((c₂ q - a₂) * starRingEnd ℂ (deriv (fun z => c₂ (d.symm z)) (d q))))) * T := by
      rw [h]
      congr 1
      rw [Complex.real_smul, Complex.real_smul]
      ring
    exact mul_right_cancel₀ hTne h'
  · intro h
    rw [htr₁, htr₂, h]
    congr 1
    rw [Complex.real_smul, Complex.real_smul]
    ring

/-! ## The free direction from the twofold/no-tangency conditions -/

/-- **The free direction at a point of the closed union outside the open union.**

Assume at most two of the closed chart balls contain `p` (no three distinct indices), and that any
two balls containing `p` are not externally tangent there (their normals are not negative
multiples).  Then the balls through `p` admit a common direction `v` with all free-direction
functionals positive.

The proof is a two-case argument: if exactly one ball contains `p`, its own normal is the witness
(`Re (conj m * m) = ‖m‖ ^ 2 > 0`); if two balls `i₀, j` contain `p`, apply
`exists_pos_of_not_neg_smul`.  The hypothesis "no three distinct indices" reduces every point of
the closed union to one of these two cases. -/
theorem freeDirection_of_noAntipodal {ι : Type*}
    (cc : ι → OpenPartialHomeomorph X ℂ) (hc : ∀ i, cc i ∈ atlas ℂ X)
    (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    {p : X} (hpU : p ∉ ⋃ i, Submission.chartBall (cc i) (a i) (ρ i))
    (htwo : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
      p ∈ Submission.chartClosedBall (cc j) (a j) (ρ j) →
      p ∈ Submission.chartClosedBall (cc k) (a k) (ρ k) → False)
    (hno : ∀ i j, i ≠ j → p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
      p ∈ Submission.chartClosedBall (cc j) (a j) (ρ j) → ∀ t : ℝ, 0 < t →
      normalAt (cc i) (a i) p ≠ -(t • normalAt (cc j) (a j) p)) :
    ∃ v : ℂ, ∀ i, p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
      0 < (starRingEnd ℂ ((cc i) p - a i) *
        deriv (fun z => (cc i) ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) * v).re := by
  classical
  by_cases hex : ∃ i, p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i)
  · obtain ⟨i₀, hi₀⟩ := hex
    have hsphere : ∀ i, p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
        ‖(cc i) p - a i‖ = ρ i := by
      intro i hi
      obtain ⟨hsrc, hcl⟩ := Submission.mem_chartClosedBall.mp hi
      have hinb : p ∉ Submission.chartBall (cc i) (a i) (ρ i) :=
        fun h => hpU (Set.mem_iUnion.mpr ⟨i, h⟩)
      have hnb : (cc i) p ∉ Metric.ball (a i) (ρ i) := fun h =>
        hinb (Submission.mem_chartBall.mpr ⟨hsrc, h⟩)
      have hle : ‖(cc i) p - a i‖ ≤ ρ i := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hcl
      have hge : ¬ (‖(cc i) p - a i‖ < ρ i) := fun h =>
        hnb (by simpa only [Metric.mem_ball, dist_eq_norm] using h)
      exact le_antisymm hle (not_lt.mp hge)
    have hDne : ∀ i, p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
        deriv (fun z => (cc i) ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) ≠ 0 := by
      intro i hi
      have hsrc : p ∈ (cc i).source := (Submission.mem_chartClosedBall.mp hi).1
      exact deriv_transition_ne_zero (hc i) (chart_mem_atlas ℂ p)
        ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
        (by rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]; exact hsrc)
    have hNne : ∀ i, p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
        normalAt (cc i) (a i) p ≠ 0 := by
      intro i hi
      have hAne : (cc i) p - a i ≠ 0 := by
        intro h
        have h0 : ‖(cc i) p - a i‖ = 0 := by rw [h, norm_zero]
        rw [hsphere i hi] at h0
        exact absurd h0 (ne_of_gt (hρ i))
      have hDconj : starRingEnd ℂ
          (deriv (fun z => (cc i) ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p)) ≠ 0 := by
        intro h
        exact hDne i hi (by simpa using congrArg (starRingEnd ℂ) h)
      rw [normalAt]
      exact mul_ne_zero hAne hDconj
    by_cases huniq : ∀ j, p ∈ Submission.chartClosedBall (cc j) (a j) (ρ j) → j = i₀
    · refine ⟨normalAt (cc i₀) (a i₀) p, ?_⟩
      intro i hi
      rw [functional_eq_reConj_normalAt, huniq i hi]
      have hmne : normalAt (cc i₀) (a i₀) p ≠ 0 := hNne i₀ hi₀
      rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
      exact pow_pos (norm_pos_iff.mpr hmne) 2
    · push_neg at huniq
      obtain ⟨j, hjmem, hji⟩ := huniq
      have hji' : j ≠ i₀ := hji
      have hcases : ∀ i, p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
          i = i₀ ∨ i = j := by
        intro i hi
        by_contra hcon
        push_neg at hcon
        obtain ⟨hii₀, hij⟩ := hcon
        exact htwo i i₀ j hii₀ (Ne.symm hji') hij hi hi₀ hjmem
      obtain ⟨v, hv₁, hv₂⟩ := exists_pos_of_not_neg_smul (hNne i₀ hi₀) (hNne j hjmem)
        (hno j i₀ hji' hjmem hi₀)
      refine ⟨v, ?_⟩
      intro i hi
      rcases hcases i hi with h | h
      · subst h
        rw [functional_eq_reConj_normalAt]
        exact hv₁
      · subst h
        rw [functional_eq_reConj_normalAt]
        exact hv₂
  · exact ⟨1, fun i hi => absurd ⟨i, hi⟩ hex⟩

/-! ## The target theorem from a twofold, tangency-free family -/

/-- **The target theorem from a family of chart balls with at most two balls through each frontier
point and no external tangency there.**

This is the reduction `exists_barrier_regular_precompact_region_of_freeFamily` fed with the free
direction produced by `freeDirection_of_noAntipodal`: the hypotheses on `(cc, a, ρ)` are purely
geometric (covering, connected union, no three distinct balls through a point of the closed union
outside the open union, and no two balls externally tangent there). -/
theorem exists_barrier_regular_precompact_region_of_twofold
    [ConnectedSpace X] [SecondCountableTopology X]
    (hX : ¬ CompactSpace X) {K : Set X} (hK : IsCompact K) (x₀ : X)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (cc : ι → OpenPartialHomeomorph X ℂ) (hc : ∀ i, cc i ∈ atlas ℂ X)
    (a : ι → ℂ) (ρ : ι → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hsub : ∀ i, Metric.closedBall (a i) (ρ i) ⊆ (cc i).target)
    (hcov : K ∪ {x₀} ⊆ ⋃ i, Submission.chartBall (cc i) (a i) (ρ i))
    (hconn : IsConnected (⋃ i, Submission.chartBall (cc i) (a i) (ρ i)))
    (htwo : ∀ p ∈ (⋃ i, Submission.chartClosedBall (cc i) (a i) (ρ i)) \
        (⋃ i, Submission.chartBall (cc i) (a i) (ρ i)),
      ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
        p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
        p ∈ Submission.chartClosedBall (cc j) (a j) (ρ j) →
        p ∈ Submission.chartClosedBall (cc k) (a k) (ρ k) → False)
    (hno : ∀ p ∈ (⋃ i, Submission.chartClosedBall (cc i) (a i) (ρ i)) \
        (⋃ i, Submission.chartBall (cc i) (a i) (ρ i)),
      ∀ i j, i ≠ j → p ∈ Submission.chartClosedBall (cc i) (a i) (ρ i) →
        p ∈ Submission.chartClosedBall (cc j) (a j) (ρ j) → ∀ t : ℝ, 0 < t →
        normalAt (cc i) (a i) p ≠ -(t • normalAt (cc j) (a j) p)) :
    ∃ Ω : Set X, IsOpen Ω ∧ IsConnected Ω ∧ IsCompact (closure Ω) ∧ K ∪ {x₀} ⊆ Ω ∧
      Ω ≠ Set.univ ∧
      (∀ p ∈ frontier Ω, ∃ (u : X → ℝ) (V : Set X), IsOpen V ∧ p ∈ V ∧
        Submission.SuperharmonicOnX u (Ω ∩ V) ∧ (∀ x ∈ Ω ∩ V, 0 < u x) ∧
        ContinuousOn u V ∧ u p = 0) :=
  exists_barrier_regular_precompact_region_of_freeFamily (X := X) hX hK x₀ cc hc a ρ hρ hsub
    hcov hconn fun p hp =>
      freeDirection_of_noAntipodal cc hc a ρ hρ hp.2 (htwo p hp) (hno p hp)

end Work.SimplyConnected.ABS.green_reduction
