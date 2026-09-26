/-
# Holomorphy of the left detour of the CKMRV contour

The target lemma is `Work.Asymptotics.detourLeft_mdifferentiableOn`: for `τ` in a small
hyperbolic ball around `1 + i t₀`, the left-detour integral

  `detourLeft ℓ d r t₀ A₂ ξ₂ τ`

with `c± = t₀⁻¹ ∓ A₂` is complex differentiable as a function of `τ`.

The content is differentiation under the integral sign, and the file is organised accordingly:

* `jInvariant_ne_closedEdge_leftDetour` : the cleanliness hypothesis of the target, stated with
  *strict* inequalities on the three open sides of the detour rectangle, implies cleanliness on
  the *closed* sides (the four corners included).  This is the step that makes a bound on the
  closed contour available at all;
* `localBound_Kfun_leftDetour` : compactness: `Kfun` is uniformly bounded near each point of the
  ball along the closed contour;
* `mdifferentiableOn_paramIntegral_Kfun` : the parametric-integral engine: for a continuous
  contour map `Z : ℝ → ℍ`, a continuous weight `κ` and a ball on which every contour point is
  `j`-clean and `Kfun` is locally bounded, `τ ↦ ∫_u K(τ,Z u)κ u` is holomorphic.
-/
import Mathlib
import Submission.Work.Asymptotics.continuationDefs
import Submission.Work.Asymptotics.differentiableAt_Kfun_tau
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_ne
import Submission.Work.Asymptotics.measurable_Kfun_snd_all

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

open UpperHalfPlane Filter Topology MeasureTheory
open scoped Topology Manifold

namespace Work.Asymptotics

/-! ## The `j`-invariant as a holomorphic, non-constant function -/

private lemma detourLeft_mdifferentiable_jInvariantFun :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Work.Kernels.jInvariantFun) :=
  ((ModularFormClass.holo ModularForm.E₄).pow 3).div
    (CuspFormClass.holo CuspForm.discriminant)
    (fun z => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)

private lemma detourLeft_analyticOnNhd_jInvariantFun_comp :
    AnalyticOnNhd ℂ (fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im} :=
  (UpperHalfPlane.mdifferentiable_iff.mp detourLeft_mdifferentiable_jInvariantFun).analyticOnNhd
    UpperHalfPlane.isOpen_upperHalfPlaneSet

private lemma detourLeft_not_const_jInvariantFun_comp :
    ¬ (∃ c : ℂ, ∀ w : ℂ, 0 < w.im →
      Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w) = c) := by
  rintro ⟨c, hc⟩
  obtain ⟨t, ht, hne⟩ := Work.Asymptotics.jInvariantFun_imagAxis_ne c
  refine hne (hc ((t : ℂ) * Complex.I) ?_)
  rw [Complex.mul_im]
  simp [ht]

/-! ## Cleanliness of the corners of the left detour rectangle

A corner coincidence would put an open neighbourhood of the corresponding `j`-value inside the
image of the ball under `w ↦ j(ofComplex w)` (open mapping theorem for a non-constant analytic
function); by continuity of `t ↦ j(ofReImT t v₀)` the interior points of the adjacent side which
are close to the corner would then also be coincidences, contradicting `hclean`. -/

/-- The edge parametrisation `t ↦ ofReImT t v` is continuous for `v > 0`. -/
private lemma continuous_ofReImT_snd {v : ℝ} (hv : 0 < v) :
    Continuous (fun t : ℝ => ofReImT t v) := by
  rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
  have h_eq : (fun t : ℝ => ((ofReImT t v : UpperHalfPlane) : ℂ))
      = fun t : ℝ => (t : ℂ) + (v : ℂ) * Complex.I := by
    funext t; exact ofReImT_coe t v hv
  rw [show (UpperHalfPlane.coe ∘ fun t : ℝ => ofReImT t v)
      = fun t : ℝ => ((ofReImT t v : UpperHalfPlane) : ℂ) from rfl, h_eq]
  fun_prop

/-- **The four corners of the left detour rectangle are clean.** -/
private lemma clean_at_corner_left {t₀ A₂ ξ₂ ε : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂)
    (hA₂t₀ : A₂ < t₀⁻¹) (hε : 0 < ε)
    (hclean : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ < u ∧ u < 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ < v ∧ v < t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v))
    {u₀ v₀ : ℝ} (hu₀ : u₀ = -ξ₂ ∨ u₀ = 0) (hv₀ : v₀ = t₀⁻¹ - A₂ ∨ v₀ = t₀⁻¹ + A₂) :
    ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u₀ v₀) := by
  have hv₀pos : 0 < v₀ := by rcases hv₀ with h | h <;> linarith
  intro τ₁ hτ₁ heq
  -- ## The open mapping input
  have hopen : ∀ s ⊆ {w : ℂ | 0 < w.im}, IsOpen s →
      IsOpen ((fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) '' s) :=
    (detourLeft_analyticOnNhd_jInvariantFun_comp.is_constant_or_isOpen
      (convex_halfSpace_im_gt 0).isPreconnected).resolve_left
        detourLeft_not_const_jInvariantFun_comp
  -- ## The Euclidean ball `D` around `τ₁` on which the whole ball condition holds
  have hΦcont : Continuous fun w : {w : ℂ // 0 < w.im} =>
      (⟨w.1, w.2⟩ : UpperHalfPlane) :=
    Continuous.upperHalfPlaneMk continuous_subtype_val (fun w => w.2)
  have hψcont : Continuous fun w : {w : ℂ // 0 < w.im} =>
      dist (⟨w.1, w.2⟩ : UpperHalfPlane) (onePlusI t₀ ht₀) :=
    hΦcont.dist continuous_const
  have hψ₀ : dist (⟨(τ₁ : ℂ), τ₁.im_pos⟩ : UpperHalfPlane) (onePlusI t₀ ht₀) < ε := hτ₁
  have hOpen : IsOpen {w : {w : ℂ // 0 < w.im} |
      dist (⟨w.1, w.2⟩ : UpperHalfPlane) (onePlusI t₀ ht₀) < ε} :=
    isOpen_lt hψcont continuous_const
  have hψmem : (⟨(τ₁ : ℂ), τ₁.im_pos⟩ : {w : ℂ // 0 < w.im}) ∈
      {w : {w : ℂ // 0 < w.im} |
        dist (⟨w.1, w.2⟩ : UpperHalfPlane) (onePlusI t₀ ht₀) < ε} := hψ₀
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.1 (hOpen.mem_nhds hψmem)
  set δ : ℝ := min δ₁ τ₁.im / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos (lt_min hδ₁pos τ₁.im_pos) two_pos
  have hδle₁ : δ ≤ δ₁ := by
    rw [hδdef]; have := min_le_left δ₁ τ₁.im; linarith
  have hδltim : δ < τ₁.im := by
    rw [hδdef]; have := min_le_right δ₁ τ₁.im; linarith
  set D : Set ℂ := Metric.ball (τ₁ : ℂ) δ with hDdef
  have hδltim' : δ < (τ₁ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact hδltim
  have hDsub : D ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have h1 : ‖w - (τ₁ : ℂ)‖ < δ := by simpa [hDdef, Metric.mem_ball, dist_eq_norm] using hw
    have h2 : |(w - (τ₁ : ℂ)).im| ≤ ‖w - (τ₁ : ℂ)‖ := Complex.abs_im_le_norm _
    have h5 : |(w - (τ₁ : ℂ)).im| < δ := lt_of_le_of_lt h2 h1
    have h6 : -δ < w.im - (τ₁ : ℂ).im := by
      have h := (abs_lt.mp h5).1
      have h3 : (w - (τ₁ : ℂ)).im = w.im - (τ₁ : ℂ).im := by simp
      rwa [h3] at h
    have h8 : 0 < (τ₁ : ℂ).im - δ := by linarith
    show 0 < w.im
    linarith
  -- the image of `D` is a neighbourhood of `j τ₁`
  have hGD : ((fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) '' D)
      ∈ 𝓝 (Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex (τ₁ : ℂ))) := by
    refine (hopen D hDsub Metric.isOpen_ball).mem_nhds ⟨(τ₁ : ℂ), ?_, rfl⟩
    simp [hDdef, Metric.mem_ball, hδpos]
  obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhds_iff.1 hGD
  -- ## The adjacent edge meets the preimage of `ball (j τ₁) η`
  have hofReImT_cont : Continuous (fun t : ℝ => ofReImT t v₀) :=
    continuous_ofReImT_snd hv₀pos
  have hφcont : Continuous fun t : ℝ =>
      Work.Kernels.jInvariantFun (ofReImT t v₀) :=
    continuous_jInvariantFun'.comp hofReImT_cont
  have hu₀cl : u₀ ∈ closure (Set.Ioo (-ξ₂) (0 : ℝ)) := by
    rw [closure_Ioo (by linarith : (-ξ₂) ≠ (0:ℝ))]
    rw [Set.mem_Icc]
    rcases hu₀ with h | h <;> rw [h] <;> constructor <;> linarith
  have hpre : ((fun t : ℝ => Work.Kernels.jInvariantFun (ofReImT t v₀)) ⁻¹'
      Metric.ball (Work.Kernels.jInvariantFun (ofReImT u₀ v₀)) η) ∈ 𝓝 u₀ :=
    hφcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hηpos)
  obtain ⟨t, htball, htIoo⟩ := (mem_closure_iff_nhds.1 hu₀cl) _ hpre
  rw [Set.mem_Ioo] at htIoo
  -- ## The contradiction
  have hτ₁c : UpperHalfPlane.ofComplex (τ₁ : ℂ) = τ₁ :=
    (UpperHalfPlane.ofComplex_apply_of_im_pos τ₁.im_pos).trans (UpperHalfPlane.ext rfl)
  have hzmem : Work.Kernels.jInvariantFun (ofReImT t v₀) ∈
      ((fun w : ℂ => Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)) '' D) := by
    refine hη ?_
    rw [hτ₁c, heq]
    exact htball
  obtain ⟨w, hwD, hwG⟩ := hzmem
  have hwpos : 0 < w.im := hDsub hwD
  have hwball : (⟨w, hwpos⟩ : {w : ℂ // 0 < w.im}) ∈ Metric.ball
      (⟨(τ₁ : ℂ), τ₁.im_pos⟩ : {w : ℂ // 0 < w.im}) δ₁ := by
    have h1 : ‖w - (τ₁ : ℂ)‖ < δ := by simpa [hDdef, Metric.mem_ball, dist_eq_norm] using hwD
    rw [Metric.mem_ball]
    show dist (⟨w, hwpos⟩ : {w : ℂ // 0 < w.im}) ⟨(τ₁ : ℂ), τ₁.im_pos⟩ < δ₁
    rw [Subtype.dist_eq]
    rw [dist_eq_norm]
    exact lt_of_lt_of_le h1 hδle₁
  have hwG' : Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)
      = Work.Kernels.jInvariantFun (ofReImT t v₀) := hwG
  have hjw : Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex w)
      = Work.Kernels.jInvariantFun (⟨w, hwpos⟩ : UpperHalfPlane) := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwpos]
  exact (hclean t v₀ hv₀pos (Or.inl ⟨htIoo.1, htIoo.2, hv₀⟩) ⟨w, hwpos⟩ (hδ₁ hwball))
    (by rw [← hjw, hwG'])

/-! ## Cleanliness on the closed sides of the left detour rectangle -/

/-- **The closed sides of the left detour rectangle are clean.**  In the target lemma
`detourLeft_mdifferentiableOn` the hypothesis `hclean` only covers the *open* sides (strict
inequalities); the same inequality holds on the closed sides, the four corners included.  Only
the corners are new: an interior point of a side is already covered by `hclean`. -/
theorem jInvariant_ne_closedEdge_leftDetour {t₀ A₂ ξ₂ ε : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂)
    (hξ₂ : 0 < ξ₂) (hA₂t₀ : A₂ < t₀⁻¹) (hε : 0 < ε)
    (hclean : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ < u ∧ u < 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ < v ∧ v < t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v)) :
    ∀ (τ : UpperHalfPlane), dist τ (onePlusI t₀ ht₀) < ε →
      ∀ (u v : ℝ), 0 < v →
        ((-ξ₂ ≤ u ∧ u ≤ 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
          ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ ≤ v ∧ v ≤ t₀⁻¹ + A₂)) →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v) := by
  intro τ hτ u v hv hdisj
  rcases hdisj with ⟨hu₁, hu₂, hv'⟩ | ⟨hu, hv₁, hv₂⟩
  · by_cases hu : -ξ₂ < u ∧ u < 0
    · exact hclean u v hv (Or.inl ⟨hu.1, hu.2, hv'⟩) τ hτ
    · have hu' : u = -ξ₂ ∨ u = 0 := by
        rcases lt_or_eq_of_le hu₁ with h | h
        · exact Or.inr (le_antisymm hu₂ (le_of_not_gt fun hlt => hu ⟨h, hlt⟩))
        · exact Or.inl h.symm
      exact clean_at_corner_left ht₀ hA₂ hξ₂ hA₂t₀ hε hclean hu' hv' τ hτ
  · by_cases hv'' : t₀⁻¹ - A₂ < v ∧ v < t₀⁻¹ + A₂
    · exact hclean u v hv (Or.inr ⟨hu, hv''.1, hv''.2⟩) τ hτ
    · have hv''' : v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂ := by
        rcases lt_or_eq_of_le hv₁ with h | h
        · exact Or.inr (le_antisymm hv₂ (le_of_not_gt fun hlt => hv'' ⟨h, hlt⟩))
        · exact Or.inl h.symm
      exact clean_at_corner_left ht₀ hA₂ hξ₂ hA₂t₀ hε hclean (Or.inl hu) hv''' τ hτ


/-! ## Continuity and measurability helpers -/

/-- `v ↦ ofReImT a (max v c)` is continuous for `c > 0` (the parametrisation of a vertical
edge, extended to all of `ℝ` by clamping so that it never leaves the upper half plane). -/
private lemma continuous_ofReImT_fst_max (a c : ℝ) (hc : 0 < c) :
    Continuous (fun v : ℝ => ofReImT a (max v c)) := by
  rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
  have h_eq : (fun v : ℝ => ((ofReImT a (max v c) : UpperHalfPlane) : ℂ))
      = fun v : ℝ => (a : ℂ) + ((max v c : ℝ) : ℂ) * Complex.I := by
    funext v
    exact ofReImT_coe a (max v c) (lt_of_lt_of_le hc (le_max_right _ _))
  rw [show (UpperHalfPlane.coe ∘ fun v : ℝ => ofReImT a (max v c))
      = fun v : ℝ => ((ofReImT a (max v c) : UpperHalfPlane) : ℂ) from rfl, h_eq]
  fun_prop

/-- The clamping is invisible in the range of the parameter. -/
private lemma ofReImT_max_eq (a c v : ℝ) (hv : c ≤ v) : ofReImT a (max v c) = ofReImT a v := by
  rw [max_eq_left hv]

/-- `w ↦ dist (ofComplex w) τ` is continuous at every point of the upper half plane. -/
private lemma continuousAt_dist_ofComplex (τ x : UpperHalfPlane) :
    ContinuousAt (fun w : ℂ => dist (UpperHalfPlane.ofComplex w) τ) (x : ℂ) := by
  have hcont : ContinuousOn (fun w : ℂ => dist (UpperHalfPlane.ofComplex w) τ)
      {w : ℂ | 0 < w.im} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Set.domRestrict {w : ℂ | 0 < w.im}
          (fun w : ℂ => dist (UpperHalfPlane.ofComplex w) τ))
        = fun w : {w : ℂ // 0 < w.im} => dist (⟨(w : ℂ), w.2⟩ : UpperHalfPlane) τ := by
      funext w
      show dist (UpperHalfPlane.ofComplex ((w : ℂ))) τ = dist (⟨(w : ℂ), w.2⟩ : UpperHalfPlane) τ
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos w.2]
    rw [heq]
    exact (Continuous.upperHalfPlaneMk continuous_subtype_val (fun w => w.2)).dist continuous_const
  refine hcont.continuousAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds ?_)
  show 0 < (x : ℂ).im
  rw [UpperHalfPlane.coe_im]; exact x.im_pos

/-- **Measurability of the `τ`-derivative of a parametric integrand.**  Generalisation of
`Work.Asymptotics.aeStronglyMeasurable_deriv_of_differentiableOn` to an arbitrary measure `ν` on
the parameter space: if `t ↦ f z t` is a.e. strongly measurable for every `z` in the open set
`U` and `z ↦ f z t` is holomorphic on `U` for a.e. `t`, then the same holds for the derivative. -/
private lemma detourLeft_aestronglyMeasurable_deriv {f : ℂ → ℝ → ℂ} {U : Set ℂ} {ν : Measure ℝ}
    (hU : IsOpen U)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => f z t) ν)
    (hdiff : ∀ᵐ t ∂ν, ∀ z ∈ U, DifferentiableAt ℂ (fun z' : ℂ => f z' t) z) :
    ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => deriv (fun z' : ℂ => f z' t) z) ν := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz)
  let c : ℝ := r / 2
  have hc : 0 < c := by positivity
  let hq : ℕ → ℂ := fun n => ((c / (n + 1) : ℝ) : ℂ)
  have hq_ne : ∀ n, hq n ≠ 0 := by
    intro n
    simp only [hq]
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) (by positivity))
  have hq_tendsto : Tendsto hq atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => (c / (n + 1) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
      simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using h
    have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    simpa [hq, Function.comp_def] using h2
  have hq_tendstoNE : Tendsto hq atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hq_tendsto, eventually_atTop.mpr ⟨0, fun n _ => by simpa using hq_ne n⟩⟩
  have hq_mem : ∀ n, z + hq n ∈ U := by
    intro n
    apply hball
    rw [Metric.mem_ball]
    have hnorm : ‖hq n‖ = c / (n + 1) := by
      have h1 := RCLike.norm_ofReal (K := ℂ) (c / (n + 1))
      rw [abs_of_nonneg (by positivity)] at h1
      simpa [hq] using h1
    have hlt : c / (n + 1) < r := by
      have hle : c / (n + 1) ≤ c := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hc.le, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hcr : c = r / 2 := rfl
      linarith
    calc dist (z + hq n) z = ‖hq n‖ := by rw [dist_eq_norm]; simp
      _ = c / (n + 1) := hnorm
      _ < r := hlt
  have hFmeas : ∀ n, AEStronglyMeasurable
      (fun t : ℝ => (hq n)⁻¹ * (f (z + hq n) t - f z t)) ν := by
    intro n
    exact ((hmeas (z + hq n) (hq_mem n)).sub (hmeas z hz)).const_mul _
  have hlim : ∀ᵐ t ∂ν,
      Tendsto (fun n => (hq n)⁻¹ * (f (z + hq n) t - f z t)) atTop
        (𝓝 (deriv (fun z' : ℂ => f z' t) z)) := by
    filter_upwards [hdiff] with t ht
    have hd := (ht z hz).hasDerivAt
    have hcomp := hd.tendsto_slope_zero.comp hq_tendstoNE
    simpa [Function.comp_def, smul_eq_mul] using hcomp
  exact aestronglyMeasurable_of_tendsto_ae (μ := ν) atTop hFmeas hlim

/-! ## Local boundedness of `Kfun` along the closed contour -/

/-- The three closed sides of the left detour rectangle `[-ξ₂,0] × [t₀⁻¹-A₂, t₀⁻¹+A₂]`, as a
subset of `ℍ`. -/
private def leftContour (t₀ A₂ ξ₂ : ℝ) : Set UpperHalfPlane :=
  ((fun u : ℝ => ofReImT u (t₀⁻¹ - A₂)) '' Set.Icc (-ξ₂) 0)
  ∪ ((fun u : ℝ => ofReImT u (t₀⁻¹ + A₂)) '' Set.Icc (-ξ₂) 0)
  ∪ ((fun v : ℝ => ofReImT (-ξ₂) v) '' Set.Icc (t₀⁻¹ - A₂) (t₀⁻¹ + A₂))

/-- The contour is compact. -/
private lemma isCompact_leftContour {t₀ A₂ ξ₂ : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂)
    (hA₂t₀ : A₂ < t₀⁻¹) :
    IsCompact (leftContour t₀ A₂ ξ₂) := by
  have hc₁ : 0 < t₀⁻¹ - A₂ := by
    have := inv_pos.mpr ht₀; linarith
  have hc₂ : 0 < t₀⁻¹ + A₂ := by
    have := inv_pos.mpr ht₀; linarith
  have h3 : IsCompact ((fun v : ℝ => ofReImT (-ξ₂) v)
      '' Set.Icc (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) := by
    have hcont : ContinuousOn (fun v : ℝ => ofReImT (-ξ₂) v)
        (Set.Icc (t₀⁻¹ - A₂) (t₀⁻¹ + A₂)) :=
      (continuous_ofReImT_fst_max (-ξ₂) (t₀⁻¹ - A₂) hc₁).continuousOn.congr
        (fun v hv => (ofReImT_max_eq (-ξ₂) (t₀⁻¹ - A₂) v hv.1).symm)
    exact isCompact_Icc.image_of_continuousOn hcont
  unfold leftContour
  exact ((isCompact_Icc.image (continuous_ofReImT_snd hc₁)).union
    (isCompact_Icc.image (continuous_ofReImT_snd hc₂))).union h3

/-- **`Kfun` is locally uniformly bounded along the closed three-sided contour.**  Given
cleanliness on the closed contour, compactness of the contour together with the joint continuity
of `Kfun` off the coincidence divisor gives a bound in a neighbourhood of every point of the
ball. -/
theorem localBound_Kfun_leftDetour (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {t₀ A₂ ξ₂ ε : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hA₂t₀ : A₂ < t₀⁻¹)
    (hε : 0 < ε)
    (hclean : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ ≤ u ∧ u ≤ 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ ≤ v ∧ v ≤ t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v)) :
    ∀ τ₁ : UpperHalfPlane, dist τ₁ (onePlusI t₀ ht₀) < ε →
      ∃ M r : ℝ, 0 < r ∧
        (∀ u ∈ Set.Icc (-ξ₂) 0, ∀ τ : UpperHalfPlane, dist τ τ₁ < r →
          ‖Work.Kernels.Kfun ℓ d τ (ofReImT u (t₀⁻¹ - A₂))‖ ≤ M) ∧
        (∀ u ∈ Set.Icc (-ξ₂) 0, ∀ τ : UpperHalfPlane, dist τ τ₁ < r →
          ‖Work.Kernels.Kfun ℓ d τ (ofReImT u (t₀⁻¹ + A₂))‖ ≤ M) ∧
        (∀ v ∈ Set.Icc (t₀⁻¹ - A₂) (t₀⁻¹ + A₂), ∀ τ : UpperHalfPlane, dist τ τ₁ < r →
          ‖Work.Kernels.Kfun ℓ d τ (ofReImT (-ξ₂) v)‖ ≤ M) := by
  have hc₁ : 0 < t₀⁻¹ - A₂ := by linarith
  have hc₂ : 0 < t₀⁻¹ + A₂ := by positivity
  have hS : IsCompact (leftContour t₀ A₂ ξ₂) := isCompact_leftContour ht₀ hA₂ hA₂t₀
  have hcleanS : ∀ z ∈ leftContour t₀ A₂ ξ₂, ∀ τ : UpperHalfPlane,
      dist τ (onePlusI t₀ ht₀) < ε →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro z hz τ hτ
    unfold leftContour at hz
    rcases hz with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨v, hv, rfl⟩
    · exact hclean u (t₀⁻¹ - A₂) hc₁ (Or.inl ⟨hu.1, hu.2, Or.inl rfl⟩) τ hτ
    · exact hclean u (t₀⁻¹ + A₂) hc₂ (Or.inl ⟨hu.1, hu.2, Or.inr rfl⟩) τ hτ
    · exact hclean (-ξ₂) v (lt_of_lt_of_le hc₁ hv.1) (Or.inr ⟨rfl, hv.1, hv.2⟩) τ hτ
  intro τ₁ hτ₁
  set r : ℝ := (ε - dist τ₁ (onePlusI t₀ ht₀)) / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hsub : (Metric.closedBall τ₁ r ×ˢ leftContour t₀ A₂ ξ₂) ⊆
      {p : UpperHalfPlane × UpperHalfPlane |
        Work.Kernels.jInvariantFun p.1 ≠ Work.Kernels.jInvariantFun p.2} := by
    rintro ⟨τ, z⟩ ⟨hτ, hz⟩
    have h2 : dist τ τ₁ ≤ r := Metric.mem_closedBall.mp hτ
    have hlt : dist τ (onePlusI t₀ ht₀) < ε := by
      calc dist τ (onePlusI t₀ ht₀) ≤ dist τ τ₁ + dist τ₁ (onePlusI t₀ ht₀) := dist_triangle _ _ _
        _ ≤ r + dist τ₁ (onePlusI t₀ ht₀) := by linarith
        _ < ε := by rw [hrdef]; linarith
    exact hcleanS z hz τ hlt
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
    ((isCompact_closedBall τ₁ r).prod hS) ((continuousOn_Kfun_clean ℓ d hd).mono hsub)
  refine ⟨M, r, hrpos, ?_, ?_, ?_⟩
  · intro u hu τ hτ
    refine hM (τ, ofReImT u (t₀⁻¹ - A₂)) ⟨Metric.mem_closedBall.mpr (le_of_lt hτ), ?_⟩
    unfold leftContour
    exact Or.inl (Or.inl ⟨u, hu, rfl⟩)
  · intro u hu τ hτ
    refine hM (τ, ofReImT u (t₀⁻¹ + A₂)) ⟨Metric.mem_closedBall.mpr (le_of_lt hτ), ?_⟩
    unfold leftContour
    exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
  · intro v hv τ hτ
    refine hM (τ, ofReImT (-ξ₂) v) ⟨Metric.mem_closedBall.mpr (le_of_lt hτ), ?_⟩
    unfold leftContour
    exact Or.inr ⟨v, hv, rfl⟩

/-! ## Differentiating the parametric integral -/

/-- **Differentiation under the integral sign for the CKMRV kernel.**  If `Z : ℝ → ℍ` is a
continuous contour, `κ` a continuous weight, every contour point of the closed interval `[a,b]`
is `j`-clean with respect to the ball `B(τ₀,ε)`, and `Kfun` is locally bounded along the contour
near every point of the ball, then

  `τ ↦ ∫_{a}^{b} K^{(d)}(τ, Z u) κ u du`

is holomorphic on `B(τ₀,ε)`.

The proof is the standard dominated-convergence argument: for `u` in the open interval the
integrand is holomorphic in `τ` (`differentiableAt_Kfun_tau`), and Cauchy's estimate on a small
Euclidean disc inside the hyperbolic ball converts the uniform value bound into a uniform bound
on the `τ`-derivative, which is integrable on the bounded interval. -/
theorem mdifferentiableOn_paramIntegral_Kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {a b : ℝ} (hab : a ≤ b) {Z : ℝ → UpperHalfPlane} (hZ : Continuous Z)
    {κ : ℝ → ℂ} (hκ : Continuous κ) {τ₀ : UpperHalfPlane} {ε : ℝ} (hε : 0 < ε)
    (hclean : ∀ u ∈ Set.Icc a b, ∀ τ : UpperHalfPlane, dist τ τ₀ < ε →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Z u))
    (hbound : ∀ τ₁ : UpperHalfPlane, dist τ₁ τ₀ < ε → ∃ M r : ℝ, 0 < r ∧
      ∀ u ∈ Set.Icc a b, ∀ τ : UpperHalfPlane, dist τ τ₁ < r →
        ‖Work.Kernels.Kfun ℓ d τ (Z u)‖ ≤ M) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ => ∫ u in Set.Ioo a b, Work.Kernels.Kfun ℓ d τ (Z u) * κ u)
      (Metric.ball τ₀ ε) := by
  intro τ₁ hτ₁
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  rw [UpperHalfPlane.mdifferentiableAt_iff]
  obtain ⟨M, r_b, hrb, hMb⟩ := hbound τ₁ hτ₁
  have hτ₁c : UpperHalfPlane.ofComplex (τ₁ : ℂ) = τ₁ :=
    (UpperHalfPlane.ofComplex_apply_of_im_pos τ₁.im_pos).trans (UpperHalfPlane.ext rfl)
  have him : 0 < (τ₁ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact τ₁.im_pos
  -- ## The Euclidean radii on which all the hypotheses are available
  obtain ⟨ρ_im, hρ_im_pos, hρ_im⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : ℂ, dist w (τ₁ : ℂ) < ρ → 0 < w.im := by
    refine ⟨(τ₁ : ℂ).im / 2, by linarith, ?_⟩
    intro w hw
    have h1 : ‖w - (τ₁ : ℂ)‖ < (τ₁ : ℂ).im / 2 := by simpa [dist_eq_norm] using hw
    have h2 : |(w - (τ₁ : ℂ)).im| ≤ ‖w - (τ₁ : ℂ)‖ := Complex.abs_im_le_norm _
    have h5 : |(w - (τ₁ : ℂ)).im| < (τ₁ : ℂ).im / 2 := lt_of_le_of_lt h2 h1
    have h6 : -((τ₁ : ℂ).im / 2) < w.im - (τ₁ : ℂ).im := by
      have h := (abs_lt.mp h5).1
      have h3 : (w - (τ₁ : ℂ)).im = w.im - (τ₁ : ℂ).im := by simp
      rwa [h3] at h
    linarith
  obtain ⟨ρ_ε, hρ_ε_pos, hρ_ε⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : ℂ, dist w (τ₁ : ℂ) < ρ →
      dist (UpperHalfPlane.ofComplex w) τ₀ < ε := by
    have h0 : dist (UpperHalfPlane.ofComplex (τ₁ : ℂ)) τ₀ < ε := by
      rw [hτ₁c]; exact hτ₁
    exact Metric.mem_nhds_iff.1
      ((continuousAt_dist_ofComplex τ₀ τ₁).eventually (isOpen_Iio.mem_nhds h0))
  obtain ⟨ρ_b, hρ_b_pos, hρ_b⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : ℂ, dist w (τ₁ : ℂ) < ρ →
      dist (UpperHalfPlane.ofComplex w) τ₁ < r_b := by
    have h0 : dist (UpperHalfPlane.ofComplex (τ₁ : ℂ)) τ₁ < r_b := by
      rw [hτ₁c, dist_self]; exact hrb
    exact Metric.mem_nhds_iff.1
      ((continuousAt_dist_ofComplex τ₁ τ₁).eventually (isOpen_Iio.mem_nhds h0))
  set ρfull : ℝ := min ρ_im (min ρ_ε ρ_b) with hρfulldef
  set ρ : ℝ := ρfull / 2 with hρdef
  have hρfullpos : 0 < ρfull := by
    rw [hρfulldef]; exact lt_min hρ_im_pos (lt_min hρ_ε_pos hρ_b_pos)
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have htwo : 2 * ρ = ρfull := by rw [hρdef]; ring
  have hρfull_le_im : ρfull ≤ ρ_im := by rw [hρfulldef]; exact min_le_left _ _
  have hρfull_le_ε : ρfull ≤ ρ_ε := by
    rw [hρfulldef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρfull_le_b : ρfull ≤ ρ_b := by
    rw [hρfulldef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hgood : ∀ w : ℂ, dist w (τ₁ : ℂ) < 2 * ρ → 0 < w.im ∧
      dist (UpperHalfPlane.ofComplex w) τ₀ < ε ∧ dist (UpperHalfPlane.ofComplex w) τ₁ < r_b := by
    intro w hw
    have h1 : dist w (τ₁ : ℂ) < ρfull := by rw [← htwo]; exact hw
    exact ⟨hρ_im w (lt_of_lt_of_le h1 hρfull_le_im),
      hρ_ε w (lt_of_lt_of_le h1 hρfull_le_ε),
      hρ_b w (lt_of_lt_of_le h1 hρfull_le_b)⟩
  -- ## Holomorphy of the integrand
  have hdiffK : ∀ u ∈ Set.Ioo a b, ∀ x : ℂ, dist x (τ₁ : ℂ) < 2 * ρ →
      DifferentiableAt ℂ (fun y : ℂ =>
        Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u)) x := by
    intro u hu x hx
    obtain ⟨hxim, hxε, _⟩ := hgood x hx
    have huIcc : u ∈ Set.Icc a b := ⟨le_of_lt hu.1, hu.2.le⟩
    have hxε' : dist (⟨x, hxim⟩ : UpperHalfPlane) τ₀ < ε := by
      rw [← show UpperHalfPlane.ofComplex x = (⟨x, hxim⟩ : UpperHalfPlane) from
        UpperHalfPlane.ofComplex_apply_of_im_pos hxim]
      exact hxε
    have hJ : Work.Kernels.jInvariantFun (⟨x, hxim⟩ : UpperHalfPlane)
        ≠ Work.Kernels.jInvariantFun (Z u) := hclean u huIcc (⟨x, hxim⟩ : UpperHalfPlane) hxε'
    simpa using differentiableAt_Kfun_tau (ℓ := ℓ) (d := d) hd hJ
  have hdiffAt : ∀ u ∈ Set.Ioo a b, ∀ x : ℂ, dist x (τ₁ : ℂ) < 2 * ρ →
      DifferentiableAt ℂ (fun y : ℂ =>
        Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u) * κ u) x :=
    fun u hu x hx => (hdiffK u hu x hx).mul_const (κ u)
  -- ## Measurability in `u`
  have hmeas_all : ∀ z : ℂ, AEStronglyMeasurable (fun u : ℝ =>
      Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex z) (Z u) * κ u)
      (volume.restrict (Set.Ioo a b)) := by
    intro z
    exact (((measurable_Kfun_snd_all ℓ d hd (UpperHalfPlane.ofComplex z)).comp hZ.measurable).mul
      hκ.measurable).aestronglyMeasurable
  have hF_meas : ∀ᶠ x in 𝓝 (τ₁ : ℂ), AEStronglyMeasurable
      (fun u : ℝ => Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex x) (Z u) * κ u)
      (volume.restrict (Set.Ioo a b)) :=
    Filter.Eventually.of_forall hmeas_all
  -- ## Integrability of the integrand at `τ₁`
  have hκint : Integrable (fun u : ℝ => |M| * ‖κ u‖) (volume.restrict (Set.Ioo a b)) := by
    have h2 : IntervalIntegrable (fun u : ℝ => |M| * ‖κ u‖) volume a b :=
      (hκ.norm.const_mul |M|).intervalIntegrable a b
    have h3 : IntegrableOn (fun u : ℝ => |M| * ‖κ u‖) (Set.uIoc a b) volume :=
      intervalIntegrable_iff.mp h2
    rw [Set.uIoc_of_le hab] at h3
    exact h3.mono_set (fun x hx => ⟨hx.1, hx.2.le⟩)
  have hF_int : Integrable (fun u : ℝ =>
      Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex (τ₁ : ℂ)) (Z u) * κ u)
      (volume.restrict (Set.Ioo a b)) := by
    refine hκint.mono' (hmeas_all (τ₁ : ℂ)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu
    have huIcc : u ∈ Set.Icc a b := ⟨le_of_lt hu.1, hu.2.le⟩
    have hK : ‖Work.Kernels.Kfun ℓ d τ₁ (Z u)‖ ≤ M :=
      hMb u huIcc τ₁ (by rw [dist_self]; exact hrb)
    calc ‖Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex (τ₁ : ℂ)) (Z u) * κ u‖
        = ‖Work.Kernels.Kfun ℓ d τ₁ (Z u)‖ * ‖κ u‖ := by rw [norm_mul, hτ₁c]
      _ ≤ M * ‖κ u‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ ≤ |M| * ‖κ u‖ := mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg _)
  -- ## Measurability of the derivative in `u`
  have hF'_meas : AEStronglyMeasurable (fun u : ℝ => deriv (fun y : ℂ =>
      Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u) * κ u) (τ₁ : ℂ))
      (volume.restrict (Set.Ioo a b)) :=
    detourLeft_aestronglyMeasurable_deriv (ν := volume.restrict (Set.Ioo a b))
      (U := Metric.ball (τ₁ : ℂ) ρ)
      (f := fun (y : ℂ) (u : ℝ) =>
        Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u) * κ u)
      Metric.isOpen_ball (fun z _ => hmeas_all z) (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu z hz
        have hz1 : dist z (τ₁ : ℂ) < ρ := by simpa [Metric.mem_ball] using hz
        exact hdiffAt u hu z (by linarith))
      (τ₁ : ℂ) (Metric.mem_ball_self hρpos)
  -- ## The derivative bound (Cauchy's estimate)
  have h_bound : ∀ᵐ u ∂(volume.restrict (Set.Ioo a b)), ∀ x ∈ Metric.ball (τ₁ : ℂ) ρ,
      ‖deriv (fun y : ℂ => Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u) * κ u) x‖
        ≤ (|M| / ρ) * ‖κ u‖ := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu x hx
    have huIcc : u ∈ Set.Icc a b := ⟨le_of_lt hu.1, hu.2.le⟩
    have hx1 : dist x (τ₁ : ℂ) < ρ := by simpa [Metric.mem_ball] using hx
    have hxd : dist x (τ₁ : ℂ) < 2 * ρ := by linarith
    have hderiv : deriv (fun y : ℂ =>
          Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u) * κ u) x
        = deriv (fun y : ℂ => Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u)) x * κ u :=
      deriv_mul_const (hdiffK u hu x hxd) (κ u)
    have hCauchy : ‖deriv (fun y : ℂ =>
        Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u)) x‖ ≤ |M| / ρ := by
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := x) (R := ρ) (C := |M|)
        hρpos ?_ ?_
      · refine DifferentiableOn.diffContOnCl fun y hy => ?_
        have hyc : y ∈ Metric.closedBall x ρ :=
          closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hy
        have hyx : dist y x ≤ ρ := Metric.mem_closedBall.mp hyc
        exact (hdiffK u hu y (by
          calc dist y (τ₁ : ℂ) ≤ dist y x + dist x (τ₁ : ℂ) := dist_triangle _ _ _
            _ < ρ + ρ := by linarith
            _ = 2 * ρ := by ring)).differentiableWithinAt
      · intro y hy
        have hyd : dist y (τ₁ : ℂ) < 2 * ρ := by
          have h1 : dist y x = ρ := Metric.mem_sphere.mp hy
          calc dist y (τ₁ : ℂ) ≤ dist y x + dist x (τ₁ : ℂ) := dist_triangle _ _ _
            _ < ρ + ρ := by linarith
            _ = 2 * ρ := by ring
        obtain ⟨hyim, -, hyr⟩ := hgood y hyd
        have hof : UpperHalfPlane.ofComplex y = (⟨y, hyim⟩ : UpperHalfPlane) :=
          UpperHalfPlane.ofComplex_apply_of_im_pos hyim
        have h1 : ‖Work.Kernels.Kfun ℓ d (⟨y, hyim⟩ : UpperHalfPlane) (Z u)‖ ≤ M :=
          hMb u huIcc ⟨y, hyim⟩ (by rwa [← hof])
        have h2 : ‖Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u)‖ ≤ M := by
          rwa [hof]
        exact le_trans h2 (le_abs_self M)
    rw [hderiv, norm_mul]
    exact mul_le_mul_of_nonneg_right hCauchy (norm_nonneg _)
  -- ## Integrability of the derivative bound
  have hbound_int : Integrable (fun u : ℝ => (|M| / ρ) * ‖κ u‖)
      (volume.restrict (Set.Ioo a b)) := by
    have h2 : IntervalIntegrable (fun u : ℝ => (|M| / ρ) * ‖κ u‖) volume a b :=
      (hκ.norm.const_mul (|M| / ρ)).intervalIntegrable a b
    have h3 : IntegrableOn (fun u : ℝ => (|M| / ρ) * ‖κ u‖) (Set.uIoc a b) volume :=
      intervalIntegrable_iff.mp h2
    rw [Set.uIoc_of_le hab] at h3
    exact h3.mono_set (fun x hx => ⟨hx.1, hx.2.le⟩)
  have h_diff : ∀ᵐ u ∂(volume.restrict (Set.Ioo a b)), ∀ x ∈ Metric.ball (τ₁ : ℂ) ρ,
      HasDerivAt (fun x : ℂ =>
          Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex x) (Z u) * κ u)
        (deriv (fun y : ℂ =>
          Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u) * κ u) x) x := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u hu x hx
    have hx1 : dist x (τ₁ : ℂ) < ρ := by simpa [Metric.mem_ball] using hx
    exact (hdiffAt u hu x (by linarith)).hasDerivAt
  -- ## Domination and conclusion
  obtain ⟨-, hDCT⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioo a b)) (𝕜 := ℂ)
    (F := fun (x : ℂ) (u : ℝ) =>
      Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex x) (Z u) * κ u)
    (F' := fun (x : ℂ) (u : ℝ) => deriv (fun y : ℂ =>
      Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex y) (Z u) * κ u) x)
    (x₀ := (τ₁ : ℂ)) (s := Metric.ball (τ₁ : ℂ) ρ) (bound := fun u : ℝ => (|M| / ρ) * ‖κ u‖)
    (Metric.ball_mem_nhds _ hρpos) hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hgoal : DifferentiableAt ℂ (fun x : ℂ => ∫ u in Set.Ioo a b,
      Work.Kernels.Kfun ℓ d (UpperHalfPlane.ofComplex x) (Z u) * κ u) (τ₁ : ℂ) :=
    hDCT.differentiableAt
  exact hgoal

/-! ## Small-interface helpers for the assembly

The three bounds of `localBound_Kfun_leftDetour` and the three function equalities comparing the
parametric-integral integrands with `edgeH`/`edgeV` are isolated here as top-level lemmas with a
small local context (elaborating them inside the large proof of the target theorem is very
expensive for the elaborator), and the three single-edge integrals are wrapped in `def`s so that
the goal of the assembly consists of small terms. -/

private def edgeHTerm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r c ξ₂ : ℝ) :
    UpperHalfPlane → ℂ :=
  fun τ => ∫ u in Set.Ioo (0 : ℝ) ξ₂, edgeH ℓ d r τ (-u) c

private def edgeVTerm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r c₁ c₂ ξ₂ : ℝ) :
    UpperHalfPlane → ℂ :=
  fun τ => ∫ v in Set.Ioo c₁ c₂, edgeV ℓ d r τ (-ξ₂) v

private lemma localBoundA (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {t₀ A₂ ξ₂ ε : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hA₂t₀ : A₂ < t₀⁻¹)
    (hε : 0 < ε)
    (hclean : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ ≤ u ∧ u ≤ 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ ≤ v ∧ v ≤ t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v)) :
    ∀ τ₁ : UpperHalfPlane, dist τ₁ (onePlusI t₀ ht₀) < ε → ∃ M r : ℝ, 0 < r ∧
      ∀ u ∈ Set.Icc (0 : ℝ) ξ₂, ∀ τ : UpperHalfPlane, dist τ τ₁ < r →
        ‖Work.Kernels.Kfun ℓ d τ (ofReImT (-u) (t₀⁻¹ - A₂))‖ ≤ M := by
  intro τ₁ hτ₁
  have H := localBound_Kfun_leftDetour ℓ d hd ht₀ hA₂ hξ₂ hA₂t₀ hε hclean τ₁ hτ₁
  refine ⟨H.choose, H.choose_spec.choose, H.choose_spec.choose_spec.1, ?_⟩
  intro u hu τ hτ
  obtain ⟨hu1, hu2⟩ := hu
  exact H.choose_spec.choose_spec.2.1 (-u) ⟨by linarith, by linarith⟩ τ hτ

private lemma localBoundB (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {t₀ A₂ ξ₂ ε : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hA₂t₀ : A₂ < t₀⁻¹)
    (hε : 0 < ε)
    (hclean : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ ≤ u ∧ u ≤ 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ ≤ v ∧ v ≤ t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v)) :
    ∀ τ₁ : UpperHalfPlane, dist τ₁ (onePlusI t₀ ht₀) < ε → ∃ M r : ℝ, 0 < r ∧
      ∀ u ∈ Set.Icc (0 : ℝ) ξ₂, ∀ τ : UpperHalfPlane, dist τ τ₁ < r →
        ‖Work.Kernels.Kfun ℓ d τ (ofReImT (-u) (t₀⁻¹ + A₂))‖ ≤ M := by
  intro τ₁ hτ₁
  have H := localBound_Kfun_leftDetour ℓ d hd ht₀ hA₂ hξ₂ hA₂t₀ hε hclean τ₁ hτ₁
  refine ⟨H.choose, H.choose_spec.choose, H.choose_spec.choose_spec.1, ?_⟩
  intro u hu τ hτ
  obtain ⟨hu1, hu2⟩ := hu
  exact H.choose_spec.choose_spec.2.2.1 (-u) ⟨by linarith, by linarith⟩ τ hτ

private lemma localBoundC (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {t₀ A₂ ξ₂ ε : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂) (hA₂t₀ : A₂ < t₀⁻¹)
    (hε : 0 < ε)
    (hclean : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ ≤ u ∧ u ≤ 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ ≤ v ∧ v ≤ t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v)) :
    ∀ τ₁ : UpperHalfPlane, dist τ₁ (onePlusI t₀ ht₀) < ε → ∃ M r : ℝ, 0 < r ∧
      ∀ v ∈ Set.Icc (t₀⁻¹ - A₂) (t₀⁻¹ + A₂), ∀ τ : UpperHalfPlane, dist τ τ₁ < r →
        ‖Work.Kernels.Kfun ℓ d τ (ofReImT (-ξ₂) (max v (t₀⁻¹ - A₂)))‖ ≤ M := by
  intro τ₁ hτ₁
  have H := localBound_Kfun_leftDetour ℓ d hd ht₀ hA₂ hξ₂ hA₂t₀ hε hclean τ₁ hτ₁
  refine ⟨H.choose, H.choose_spec.choose, H.choose_spec.choose_spec.1, ?_⟩
  intro v hv τ hτ
  rw [ofReImT_max_eq (-ξ₂) (t₀⁻¹ - A₂) v hv.1]
  exact H.choose_spec.choose_spec.2.2.2 v hv τ hτ

/-- The horizontal-edge integrand of the engine agrees with `edgeH`. -/
private lemma edgeH_eq_Kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r c ξ₂ : ℝ) :
    (fun τ : UpperHalfPlane => ∫ u in Set.Ioo (0 : ℝ) ξ₂, edgeH ℓ d r τ (-u) c)
      = fun τ : UpperHalfPlane => ∫ u in Set.Ioo (0 : ℝ) ξ₂,
          Work.Kernels.Kfun ℓ d τ (ofReImT (-u) c)
            * ((phaseWeight r (-u) * gaussWeight r c) / Complex.I) := by
  funext τ
  refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  simp only [edgeH]
  ring

/-- The vertical-edge integrand of the engine agrees with `edgeV`. -/
private lemma edgeV_eq_Kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r c₁ c₂ ξ₂ : ℝ) :
    (fun τ : UpperHalfPlane => ∫ v in Set.Ioo c₁ c₂,
        Work.Kernels.Kfun ℓ d τ (ofReImT (-ξ₂) (max v c₁))
          * (phaseWeight r (-ξ₂) * gaussWeight r v))
      = fun τ : UpperHalfPlane => ∫ v in Set.Ioo c₁ c₂, edgeV ℓ d r τ (-ξ₂) v := by
  funext τ
  refine setIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  simp only [edgeV]
  rw [ofReImT_max_eq (-ξ₂) c₁ v (le_of_lt hv.1)]

/-- `detourLeft` is the combination of the three single-edge integrals. -/
private lemma detourLeft_eq_terms (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (r t₀ A₂ ξ₂ : ℝ) :
    (fun τ : UpperHalfPlane => detourLeft ℓ d r t₀ A₂ ξ₂ τ)
      = edgeHTerm ℓ d r (t₀⁻¹ - A₂) ξ₂ + edgeVTerm ℓ d r (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) ξ₂
        - edgeHTerm ℓ d r (t₀⁻¹ + A₂) ξ₂ := by
  funext τ
  simp only [detourLeft, edgeHTerm, edgeVTerm, Pi.add_apply, Pi.sub_apply]

/-! ## The target -/

theorem detourLeft_mdifferentiableOn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {r t₀ A₂ ξ₂ ε : ℝ} (ht₀ : 0 < t₀) (hA₂ : 0 < A₂) (hξ₂ : 0 < ξ₂)
    (hA₂t₀ : A₂ < t₀⁻¹) (hε : 0 < ε)
    (hclean : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ < u ∧ u < 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ < v ∧ v < t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v)) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ => Work.Asymptotics.detourLeft ℓ d r t₀ A₂ ξ₂ τ)
      (Metric.ball (Work.Asymptotics.onePlusI t₀ ht₀) ε) := by
  have hcl : ∀ (u v : ℝ), 0 < v →
      ((-ξ₂ ≤ u ∧ u ≤ 0 ∧ (v = t₀⁻¹ - A₂ ∨ v = t₀⁻¹ + A₂))
        ∨ (u = -ξ₂ ∧ t₀⁻¹ - A₂ ≤ v ∧ v ≤ t₀⁻¹ + A₂)) →
      ∀ τ : UpperHalfPlane, dist τ (onePlusI t₀ ht₀) < ε →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (ofReImT u v) :=
    fun u v hv hdisj τ hτ =>
      jInvariant_ne_closedEdge_leftDetour ht₀ hA₂ hξ₂ hA₂t₀ hε hclean τ hτ u v hv hdisj
  have hc₁ : 0 < t₀⁻¹ - A₂ := by linarith
  have hc₂ : 0 < t₀⁻¹ + A₂ := by positivity
  have hc₁₂ : t₀⁻¹ - A₂ ≤ t₀⁻¹ + A₂ := by linarith
  have hterm1 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (edgeHTerm ℓ d r (t₀⁻¹ - A₂) ξ₂) (Metric.ball (onePlusI t₀ ht₀) ε) := by
    change MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ => ∫ u in Set.Ioo (0 : ℝ) ξ₂, edgeH ℓ d r τ (-u) (t₀⁻¹ - A₂))
      (Metric.ball (onePlusI t₀ ht₀) ε)
    have hZ : Continuous (fun u : ℝ => ofReImT (-u) (t₀⁻¹ - A₂)) :=
      (continuous_ofReImT_snd hc₁).comp continuous_neg
    have hκ : Continuous (fun u : ℝ =>
        (phaseWeight r (-u) * gaussWeight r (t₀⁻¹ - A₂)) / Complex.I) := by
      refine Continuous.div_const (Continuous.mul ?_ continuous_const) _
      rw [show (fun u : ℝ => phaseWeight r (-u)) = fun u : ℝ =>
        Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * ((-u : ℝ) : ℂ)) from rfl]
      exact Complex.continuous_exp.comp (by fun_prop)
    have h := mdifferentiableOn_paramIntegral_Kfun ℓ d hd (a := 0) (b := ξ₂) hξ₂.le
      hZ hκ hε (fun u hu τ hτ => by
        obtain ⟨hu1, hu2⟩ := hu
        exact hcl (-u) (t₀⁻¹ - A₂) hc₁
          (Or.inl ⟨by linarith, by linarith, Or.inl rfl⟩) τ hτ)
      (localBoundA ℓ d hd ht₀ hA₂ hξ₂ hA₂t₀ hε hcl)
    rw [← edgeH_eq_Kfun ℓ d r (t₀⁻¹ - A₂) ξ₂] at h
    exact h
  have hterm2 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (edgeVTerm ℓ d r (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) ξ₂) (Metric.ball (onePlusI t₀ ht₀) ε) := by
    change MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ => ∫ v in Set.Ioo (t₀⁻¹ - A₂) (t₀⁻¹ + A₂), edgeV ℓ d r τ (-ξ₂) v)
      (Metric.ball (onePlusI t₀ ht₀) ε)
    have hZ : Continuous (fun v : ℝ => ofReImT (-ξ₂) (max v (t₀⁻¹ - A₂))) :=
      continuous_ofReImT_fst_max (-ξ₂) (t₀⁻¹ - A₂) hc₁
    have hκ : Continuous (fun v : ℝ => phaseWeight r (-ξ₂) * gaussWeight r v) := by
      refine Continuous.mul continuous_const ?_
      show Continuous (fun v : ℝ => Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (v : ℂ))))
      exact Complex.continuous_exp.comp (by fun_prop)
    have h := mdifferentiableOn_paramIntegral_Kfun ℓ d hd (a := t₀⁻¹ - A₂) (b := t₀⁻¹ + A₂)
      hc₁₂ hZ hκ hε (fun v hv τ hτ => by
        exact hcl (-ξ₂) (max v (t₀⁻¹ - A₂)) (lt_of_lt_of_le hc₁ (le_max_right _ _))
          (Or.inr ⟨rfl, le_max_right v (t₀⁻¹ - A₂), max_le hv.2 hc₁₂⟩) τ hτ)
      (localBoundC ℓ d hd ht₀ hA₂ hξ₂ hA₂t₀ hε hcl)
    rw [edgeV_eq_Kfun ℓ d r (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) ξ₂] at h
    exact h
  have hterm3 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (edgeHTerm ℓ d r (t₀⁻¹ + A₂) ξ₂) (Metric.ball (onePlusI t₀ ht₀) ε) := by
    change MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ => ∫ u in Set.Ioo (0 : ℝ) ξ₂, edgeH ℓ d r τ (-u) (t₀⁻¹ + A₂))
      (Metric.ball (onePlusI t₀ ht₀) ε)
    have hZ : Continuous (fun u : ℝ => ofReImT (-u) (t₀⁻¹ + A₂)) :=
      (continuous_ofReImT_snd hc₂).comp continuous_neg
    have hκ : Continuous (fun u : ℝ =>
        (phaseWeight r (-u) * gaussWeight r (t₀⁻¹ + A₂)) / Complex.I) := by
      refine Continuous.div_const (Continuous.mul ?_ continuous_const) _
      rw [show (fun u : ℝ => phaseWeight r (-u)) = fun u : ℝ =>
        Complex.exp (Real.pi * Complex.I * (r : ℂ) ^ 2 * ((-u : ℝ) : ℂ)) from rfl]
      exact Complex.continuous_exp.comp (by fun_prop)
    have h := mdifferentiableOn_paramIntegral_Kfun ℓ d hd (a := 0) (b := ξ₂) hξ₂.le
      hZ hκ hε (fun u hu τ hτ => by
        obtain ⟨hu1, hu2⟩ := hu
        exact hcl (-u) (t₀⁻¹ + A₂) hc₂
          (Or.inl ⟨by linarith, by linarith, Or.inr rfl⟩) τ hτ)
      (localBoundB ℓ d hd ht₀ hA₂ hξ₂ hA₂t₀ hε hcl)
    rw [← edgeH_eq_Kfun ℓ d r (t₀⁻¹ + A₂) ξ₂] at h
    exact h
  have hsum : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (edgeHTerm ℓ d r (t₀⁻¹ - A₂) ξ₂ + edgeVTerm ℓ d r (t₀⁻¹ - A₂) (t₀⁻¹ + A₂) ξ₂
        - edgeHTerm ℓ d r (t₀⁻¹ + A₂) ξ₂) (Metric.ball (onePlusI t₀ ht₀) ε) :=
    (hterm1.add hterm2).sub hterm3
  rw [detourLeft_eq_terms ℓ d r t₀ A₂ ξ₂]
  exact hsum

end Work.Asymptotics
