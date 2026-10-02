import Mathlib
import Submission.Work.Morse.quadratic_bounds

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Topology

namespace Work.Morse

open Metric

/-!
# The sublevel set at a strict minimum is a ball, for a range of levels

This file proves `Work.Morse.sublevel_ball_range`: at a strict global minimum `p` of a smooth
function `f` which is exactly a positive definite quadratic form in a chart at `p`, the sublevel
set `{f ≤ f p + δ}` is a closed ball `Dⁿ` for *every* sufficiently small `δ > 0`, with boundary the
level set `{f = f p + δ}`.

The geometric content is the auxiliary fact that a positive definite quadratic form's closed
sublevel set (an ellipsoid) is homeomorphic to the closed unit ball, with the ellipsoid boundary
corresponding to the sphere.  This is proved here from `gaugeRescale`-type results in Mathlib: the
ellipsoid is a convex, bounded set with nonempty interior, and any such set is carried to the unit
ball by a homeomorphism of the ambient space which also carries frontier to sphere.
-/

section QuadFormAux

/-- A continuous bilinear form which is positive on the diagonal off the origin is nonnegative on
the whole diagonal. -/
lemma quadform_nonneg {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hApos : ∀ v, v ≠ 0 → 0 < A v v) (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ A v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact le_of_lt (hApos v hv)

/-- Exact expansion of a continuous bilinear form on a convex combination. -/
lemma quadform_convex_comb {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (a b : ℝ) (hab : a + b = 1) :
    A (a • x + b • y) (a • x + b • y)
      = a * (A x x) + b * (A y y) - a * b * (A (x - y) (x - y)) := by
  have h1 : A (x - y) (x - y) = A x x - A x y - A y x + A y y := by
    simp only [map_sub, sub_apply]
    ring
  rw [h1]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  have hb : b = 1 - a := by linarith
  subst hb
  ring

/-- A continuous bilinear form which is positive on the diagonal is convex. -/
lemma convexOn_quadform {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hApos : ∀ v, v ≠ 0 → 0 < A v v) :
    ConvexOn ℝ Set.univ (fun y : EuclideanSpace ℝ (Fin n) => A y y) := by
  rw [convexOn_iff_forall_pos]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  rw [quadform_convex_comb A x y a b hab]
  have hnn : 0 ≤ A (x - y) (x - y) := quadform_nonneg hApos (x - y)
  have hprod : 0 ≤ a * b * (A (x - y) (x - y)) :=
    mul_nonneg (mul_nonneg (le_of_lt ha) (le_of_lt hb)) hnn
  simp only [smul_eq_mul]
  linarith

/-- The closed sublevel set of a positive definite quadratic form is convex. -/
lemma convex_quadform_sublevel_le {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hApos : ∀ v, v ≠ 0 → 0 < A v v) (δ : ℝ) :
    Convex ℝ {y : EuclideanSpace ℝ (Fin n) | A y y ≤ δ} := by
  have h := (convexOn_quadform hApos).convex_le δ
  simpa using h

/-- The open sublevel set of a positive definite quadratic form is convex. -/
lemma convex_quadform_sublevel_lt {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hApos : ∀ v, v ≠ 0 → 0 < A v v) (δ : ℝ) :
    Convex ℝ {y : EuclideanSpace ℝ (Fin n) | A y y < δ} := by
  have h := (convexOn_quadform hApos).convex_lt δ
  simpa using h

/-- Homogeneity of the quadratic form. -/
lemma quadform_smul {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (c : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    A (c • y) (c • y) = c ^ 2 * (A y y) := by
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- Continuity of the quadratic form `y ↦ A y y`. -/
lemma continuous_quadform {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    Continuous fun y : EuclideanSpace ℝ (Fin n) => A y y :=
  A.continuous.clm_apply continuous_id

/-- The interior of the closed sublevel set of a positive definite quadratic form is the open
sublevel set. -/
lemma interior_quadform_sublevel {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hApos : ∀ v, v ≠ 0 → 0 < A v v) {δ : ℝ} (hδ : 0 < δ) :
    interior {y : EuclideanSpace ℝ (Fin n) | A y y ≤ δ} = {y | A y y < δ} := by
  apply Set.Subset.antisymm
  · intro y hy
    have hyS : A y y ≤ δ := by simpa using interior_subset hy
    by_contra hcon
    have hcon' : ¬ (A y y < δ) := hcon
    rw [not_lt] at hcon'
    have hyval : A y y = δ := le_antisymm hyS hcon'
    have hyne : y ≠ 0 := by
      intro h
      rw [h] at hyval
      simp at hyval
      linarith
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
    have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hyne
    set c : ℝ := 1 + ε / (2 * ‖y‖) with hcdef
    have hcgt : 1 < c := by
      rw [hcdef]
      have : 0 < ε / (2 * ‖y‖) := by positivity
      linarith
    have hcd : 0 < c - 1 := by linarith
    have hcy : c • y ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : c • y - y = (c - 1) • y := by module
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hcd]
      have hcc : (c - 1) * ‖y‖ = ε / 2 := by
        rw [hcdef, add_sub_cancel_left]
        field_simp
      rw [hcc]
      linarith
    have hmem : A (c • y) (c • y) ≤ δ := hε hcy
    rw [quadform_smul A c y, hyval] at hmem
    have hcsq : 1 < c ^ 2 := by nlinarith
    nlinarith [hδ]
  · intro y hy
    refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
      ((isOpen_Iio.preimage (continuous_quadform A)).mem_nhds hy) ?_)
    intro z hz
    rw [Set.mem_preimage, Set.mem_Iio] at hz
    exact le_of_lt hz

/-- The closed sublevel set of a positive definite quadratic form is bounded. -/
lemma isBounded_quadform_sublevel {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hApos : ∀ v, v ≠ 0 → 0 < A v v) {δ : ℝ} (hδ : 0 < δ) :
    Bornology.IsBounded {y : EuclideanSpace ℝ (Fin n) | A y y ≤ δ} := by
  obtain ⟨c, hcpos, C, hC⟩ := quadratic_bounds hApos
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin n)))
    (r := Real.sqrt (δ / c))).subset ?_
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : c * ‖y‖ ^ 2 ≤ A y y := (hC y).1
  have h2 : c * ‖y‖ ^ 2 ≤ δ := le_trans h1 hy
  have h3 : ‖y‖ ^ 2 ≤ δ / c := by rw [le_div_iff₀ hcpos]; linarith
  calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg y)).symm
    _ ≤ Real.sqrt (δ / c) := Real.sqrt_le_sqrt h3

end QuadFormAux

/-- The closed Euclidean ellipsoid `{A y y ≤ δ}` of a positive definite quadratic form is
homeomorphic to the closed unit ball, with the ellipsoid boundary corresponding to the sphere. -/
theorem ellipsoid_ball_homeo {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hApos : ∀ v, v ≠ 0 → 0 < A v v) :
    ∃ E : {y : EuclideanSpace ℝ (Fin n) // A y y ≤ δ} ≃ₜ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      ∀ y, E y ∈ Metric.sphere 0 1 ↔ A (y : EuclideanSpace ℝ (Fin n)) y = δ := by
  classical
  have hclosed : IsClosed {y : EuclideanSpace ℝ (Fin n) | A y y ≤ δ} :=
    isClosed_le (continuous_quadform A) continuous_const
  have hfr : frontier {y : EuclideanSpace ℝ (Fin n) | A y y ≤ δ} = {y | A y y = δ} := by
    rw [hclosed.frontier_eq, interior_quadform_sublevel hApos hδ]
    ext y
    constructor
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 (le_of_not_gt h2)
    · intro h1
      have h1' : A y y = δ := h1
      refine ⟨le_of_eq h1', ?_⟩
      show ¬ (A y y < δ)
      rw [h1']
      exact lt_irrefl δ
  obtain ⟨h, _hInt, hClo, hFr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_quadform_sublevel_le hApos δ)
      (by rw [interior_quadform_sublevel hApos hδ]; exact ⟨0, by simpa using hδ⟩)
      (isBounded_quadform_sublevel hApos hδ)
  have heq : h '' {y : EuclideanSpace ℝ (Fin n) | A y y ≤ δ} =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [← hclosed.closure_eq]
    exact hClo
  refine ⟨(h.image {y : EuclideanSpace ℝ (Fin n) | A y y ≤ δ}).trans
    (Homeomorph.setCongr heq), ?_⟩
  intro y
  change h (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere 0 1 ↔
    A (y : EuclideanSpace ℝ (Fin n)) y = δ
  rw [← hFr]
  constructor
  · rintro ⟨w, hw, hwy⟩
    have hw' : w = (y : EuclideanSpace ℝ (Fin n)) := h.injective hwy
    rw [hw'] at hw
    rw [hfr] at hw
    exact hw
  · intro hy
    exact ⟨(y : EuclideanSpace ℝ (Fin n)), by rw [hfr]; exact hy, rfl⟩

section Range

/-- If `p` is a strict global minimum of a continuous function `f` on a compact space `X`, then the
sublevel sets `{f ≤ f p + δ}` form a neighbourhood basis of `p`. -/
theorem exists_sublevel_nhds' {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {f : X → ℝ} (hf : Continuous f) {p : X} (hmin : ∀ x, x ≠ p → f p < f x)
    {U : Set X} (hU : U ∈ 𝓝 p) :
    ∃ δ > 0, ∀ x, f x ≤ f p + δ → x ∈ U := by
  have hpV : p ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  have hVU : interior U ⊆ U := interior_subset
  by_cases hK : ((interior U)ᶜ).Nonempty
  · obtain ⟨x₀, hx₀K, hx₀min⟩ :=
      IsCompact.exists_isMinOn (isClosed_compl_iff.mpr isOpen_interior).isCompact hK
        hf.continuousOn
    have hx₀ne : x₀ ≠ p := by
      intro h; rw [h] at hx₀K; exact hx₀K hpV
    have hm : f p < f x₀ := hmin x₀ hx₀ne
    refine ⟨(f x₀ - f p) / 2, by linarith, fun x hx => ?_⟩
    by_contra hxU
    have hxK : x ∈ (interior U)ᶜ := fun hxiu => hxU (hVU hxiu)
    have hle : f x₀ ≤ f x := hx₀min hxK
    linarith
  · have hUniv : interior U = Set.univ :=
      Set.compl_empty_iff.mp (Set.not_nonempty_iff_eq_empty.mp hK)
    exact ⟨1, one_pos, fun x _ => hVU (by rw [hUniv]; trivial)⟩

/-- Reduction step for the range version: the sublevel ball theorem for every sufficiently small
`δ`, given the Euclidean lower/upper bounds for `A` and the Euclidean ellipsoid-homeomorphism
lemma. -/
theorem sublevel_ball_range_of {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] [T2Space M] {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {p : M}
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ (contDiffGroupoid ∞ (𝓡 n)).maximalAtlas M)
    (hp : p ∈ e.source) (he0 : e p = 0)
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hApos : ∀ v, v ≠ 0 → 0 < A v v)
    (hA : ∀ᶠ x in 𝓝 0, f (e.symm x) - f p = A x x)
    (hmin : ∀ x, x ≠ p → f p < f x)
    (hbound : ∃ c > 0, ∃ C, ∀ y : EuclideanSpace ℝ (Fin n),
        c * ‖y‖ ^ 2 ≤ A y y ∧ A y y ≤ C * ‖y‖ ^ 2)
    (hell : ∀ δ : ℝ, 0 < δ → ∃ E : {y : EuclideanSpace ℝ (Fin n) // A y y ≤ δ} ≃ₜ
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∀ y, E y ∈ Metric.sphere 0 1 ↔ A (y : EuclideanSpace ℝ (Fin n)) y = δ) :
    ∃ δ₀ > 0, ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀,
      ∃ E : {x // f x ≤ f p + δ} ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∀ x, E x ∈ Metric.sphere 0 1 ↔ f (x : M) = f p + δ := by
  have hfcont : Continuous f := hf.continuous
  have hQev : {y : EuclideanSpace ℝ (Fin n) | f (e.symm y) - f p = A y y} ∈ 𝓝 0 :=
    Filter.eventually_iff.mp hA
  have h0target : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.target := by
    rw [← he0]; exact e.map_source hp
  have hetarget : e.target ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)) :=
    e.open_target.mem_nhds h0target
  have hN : ({y : EuclideanSpace ℝ (Fin n) | f (e.symm y) - f p = A y y} ∩ e.target) ∈ 𝓝 0 :=
    Filter.inter_mem hQev hetarget
  obtain ⟨r, hrpos, hrsub⟩ := Metric.mem_nhds_iff.mp hN
  obtain ⟨c, hcpos, C, hC⟩ := hbound
  have hr2 : 0 < c * r ^ 2 / 4 := by positivity
  have hsource_nhds : e.source ∈ 𝓝 p := e.open_source.mem_nhds hp
  have hcontAt : ContinuousAt (e : M → EuclideanSpace ℝ (Fin n)) p :=
    e.continuousOn.continuousAt hsource_nhds
  have hpre : (e : M → EuclideanSpace ℝ (Fin n)) ⁻¹'
      ball (0 : EuclideanSpace ℝ (Fin n)) r ∈ 𝓝 p := by
    refine hcontAt.preimage_mem_nhds ?_
    rw [he0]
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrpos)
  have hU : (e.source ∩ (e : M → EuclideanSpace ℝ (Fin n)) ⁻¹'
      ball (0 : EuclideanSpace ℝ (Fin n)) r) ∈ 𝓝 p :=
    Filter.inter_mem hsource_nhds hpre
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := exists_sublevel_nhds' hfcont hmin hU
  refine ⟨min δ₀ (c * r ^ 2 / 4), lt_min hδ₀pos hr2, fun δ hδ => ?_⟩
  have hδpos : 0 < δ := hδ.1
  have hδle₀ : δ ≤ δ₀ := le_trans (le_of_lt hδ.2) (min_le_left _ _)
  have hδle₂ : δ ≤ c * r ^ 2 / 4 := le_trans (le_of_lt hδ.2) (min_le_right _ _)
  have key_x : ∀ x : M, f x ≤ f p + δ →
      x ∈ e.source ∧ (e x) ∈ e.target ∧ A (e x) (e x) = f x - f p := by
    intro x hx
    have hxU : x ∈ e.source ∩ (e : M → EuclideanSpace ℝ (Fin n)) ⁻¹' ball 0 r :=
      hδ₀ x (by linarith)
    have hxsrc : x ∈ e.source := hxU.1
    have hxball : e x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r := hxU.2
    obtain ⟨hQ, htgt⟩ := hrsub hxball
    have hQ' : f (e.symm (e x)) - f p = A (e x) (e x) := by simpa using hQ
    have h1 : f x - f p = A (e x) (e x) := by
      rw [e.left_inv hxsrc] at hQ'
      exact hQ'
    exact ⟨hxsrc, htgt, h1.symm⟩
  have key_y : ∀ y : EuclideanSpace ℝ (Fin n), A y y ≤ δ →
      y ∈ e.target ∧ f (e.symm y) - f p = A y y := by
    intro y hy
    have h1 : c * ‖y‖ ^ 2 ≤ A y y := (hC y).1
    have h2 : A y y ≤ c * r ^ 2 / 4 := le_trans hy hδle₂
    have h3 : ‖y‖ ^ 2 ≤ r ^ 2 / 4 := by nlinarith [h1, h2, hcpos]
    have h4 : ‖y‖ ≤ r / 2 := by nlinarith [norm_nonneg y, hrpos]
    have h5 : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    obtain ⟨hQ, htgt⟩ := hrsub h5
    exact ⟨htgt, by simpa using hQ⟩
  obtain ⟨E₀, hE₀⟩ := hell δ hδpos
  have hcont_toFun : Continuous (fun x : {x : M // f x ≤ f p + δ} => e (x : M)) :=
    e.continuousOn.comp_continuous continuous_subtype_val (fun x => (key_x x x.2).1)
  have hcont_invFun : Continuous
      (fun y : {y : EuclideanSpace ℝ (Fin n) // A y y ≤ δ} =>
        e.symm (y : EuclideanSpace ℝ (Fin n))) :=
    e.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun y => by rw [OpenPartialHomeomorph.symm_source]; exact (key_y y y.2).1)
  let Φ : {x : M // f x ≤ f p + δ} ≃ₜ {y : EuclideanSpace ℝ (Fin n) // A y y ≤ δ} :=
    { toFun := fun x => ⟨e (x : M), by
        have h := (key_x x x.2).2.2
        show A (e (x : M)) (e (x : M)) ≤ δ
        linarith [x.2]⟩
      invFun := fun y => ⟨e.symm (y : EuclideanSpace ℝ (Fin n)), by
        have h := (key_y y y.2).2
        show f (e.symm (y : EuclideanSpace ℝ (Fin n))) ≤ f p + δ
        linarith [y.2]⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact e.left_inv (key_x x x.2).1
      right_inv := fun y => by
        apply Subtype.ext
        exact e.right_inv (key_y y y.2).1
      continuous_toFun := Continuous.subtype_mk hcont_toFun (fun x => by
        have h := (key_x x x.2).2.2
        show A (e (x : M)) (e (x : M)) ≤ δ
        linarith [x.2])
      continuous_invFun := Continuous.subtype_mk hcont_invFun (fun y => by
        have h := (key_y y y.2).2
        show f (e.symm (y : EuclideanSpace ℝ (Fin n))) ≤ f p + δ
        linarith [y.2]) }
  refine ⟨Φ.trans E₀, fun x => ?_⟩
  rw [Homeomorph.trans_apply, hE₀ (Φ x)]
  show A (e (x : M)) (e (x : M)) = δ ↔ f (x : M) = f p + δ
  rw [(key_x x x.2).2.2]
  constructor <;> intro h <;> linarith

end Range

/-- At a strict global minimum `p` of a smooth function `f` which is exactly a positive definite
quadratic form in a chart at `p`, the sublevel set `{f ≤ f p + δ}` is a closed ball `Dⁿ` for
*every* sufficiently small `δ > 0`, with boundary the level set `{f = f p + δ}`. -/
theorem sublevel_ball_range {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] [T2Space M] {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) {p : M}
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (he : e ∈ (contDiffGroupoid ∞ (𝓡 n)).maximalAtlas M)
    (hp : p ∈ e.source) (he0 : e p = 0)
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hApos : ∀ v, v ≠ 0 → 0 < A v v)
    (hA : ∀ᶠ x in 𝓝 0, f (e.symm x) - f p = A x x)
    (hmin : ∀ x, x ≠ p → f p < f x) :
    ∃ δ₀ > 0, ∀ δ ∈ Set.Ioo (0 : ℝ) δ₀,
      ∃ E : {x // f x ≤ f p + δ} ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∀ x, E x ∈ Metric.sphere 0 1 ↔ f (x : M) = f p + δ :=
  sublevel_ball_range_of hf he hp he0 hApos hA hmin (quadratic_bounds hApos)
    (fun δ hδ => ellipsoid_ball_homeo hδ hApos)

end Work.Morse
