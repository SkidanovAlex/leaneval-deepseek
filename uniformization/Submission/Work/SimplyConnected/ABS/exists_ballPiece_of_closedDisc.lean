import Mathlib
import Submission.Work.Topology.Surface.sphere_not_interior

/-!
# A ball piece containing a set inside a closed disc

Let `X` be a complex one-manifold (a Riemann surface), `D ⊆ X` a set homeomorphic to the closed
unit disc (via `e`), and `K ⊆ interior D`.  We produce an open `Ω ⊇ K` with `closure Ω` compact,
`frontier Ω` connected and `Ω` homeomorphic to the open unit disc: namely `Ω = interior D`.

The mathematical content is **invariance of boundary** for the embedded disc: `e` maps the open
unit disc onto `interior D` and the unit circle onto `frontier D`.

* the direction `interior D ⊆ e '' 𝔻` (no boundary point is an interior point) is
  `interior_subset_discMap_ball`, an immediate consequence of the local statement
  `Work.Topology.Surface.false_of_homeomorph_nhds_sphere` (a chart at a boundary point would
  produce a local coordinate for the half-disc);
* the direction `e '' 𝔻 ⊆ interior D` is two-dimensional invariance of domain, isolated in
  `discMap_ball_subset_interior`.
-/

open Set Metric
open scoped Topology

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- The parametrisation of a closed disc in `X` by the closed unit disc, extended by junk outside
the unit disc. -/
noncomputable def discMap {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) : ℂ → X := by
  classical
  exact fun z => if h : z ∈ Metric.closedBall (0 : ℂ) 1 then ((e ⟨z, h⟩ : ↥D) : X)
    else ((e 0 : ↥D) : X)

lemma discMap_of_mem {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    discMap e z = ((e ⟨z, hz⟩ : ↥D) : X) := by
  rw [discMap, dif_pos hz]

lemma discMap_continuousOn {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) :
    ContinuousOn (discMap e) (Metric.closedBall (0 : ℂ) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  refine Continuous.congr (continuous_subtype_val.comp e.continuous) ?_
  intro z
  show ((e z : ↥D) : X) = discMap e (z : ℂ)
  rw [discMap_of_mem e z.2]

lemma discMap_mem {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) : discMap e z ∈ D := by
  rw [discMap_of_mem e hz]; exact (e ⟨z, hz⟩ : ↥D).2

lemma discMap_image_closedBall {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) :
    discMap e '' Metric.closedBall (0 : ℂ) 1 = D := by
  ext x; constructor
  · rintro ⟨z, hz, rfl⟩; exact discMap_mem e hz
  · intro hx
    obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
    refine ⟨(z : ℂ), z.2, ?_⟩
    rw [discMap_of_mem e z.2,
      show (⟨(z : ℂ), z.2⟩ : Metric.closedBall (0 : ℂ) 1) = z from Subtype.ext rfl]
    exact congrArg (fun u : ↥D => (u : X)) hz

lemma isCompact_discDisc {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) :
    IsCompact D := by
  rw [← discMap_image_closedBall e]
  exact (isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn (discMap_continuousOn e)

/-- **The closure of the image of the open unit disc is `D`.** -/
lemma closure_discMap_image_ball {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) :
    closure (discMap e '' Metric.ball (0 : ℂ) 1) = D := by
  refine Set.Subset.antisymm ?_ ?_
  · refine closure_minimal ?_ (isCompact_discDisc e).isClosed
    rintro x ⟨z, hz, rfl⟩
    exact discMap_mem e (Metric.ball_subset_closedBall hz)
  · intro x hx
    rw [← discMap_image_closedBall e] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hzle : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    rcases lt_or_eq_of_le hzle with hlt | heq
    · exact subset_closure ⟨z, Metric.mem_ball.mpr (by simpa [dist_eq_norm] using hlt), rfl⟩
    · rw [_root_.mem_closure_iff]
      intro U hU hxU
      have hzmem : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.mem_closedBall.mpr (by
        rw [dist_zero_right]; exact hzle)
      have hpre : (discMap e) ⁻¹' U ∈ 𝓝[Metric.closedBall (0 : ℂ) 1] z :=
        (discMap_continuousOn e).continuousWithinAt hzmem (hU.mem_nhds hxU)
      obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhdsWithin_iff.mp hpre
      set t : ℝ := max (1 / 2) (1 - δ / 2) with htdef
      have ht1 : t < 1 := by
        rw [htdef, max_lt_iff]
        exact ⟨by norm_num, by linarith⟩
      have ht0 : 0 < t := by
        rw [htdef]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      have htdist : dist ((t : ℂ) * z) z < δ := by
        have h1 : (1 / 2) ≤ t := le_max_left _ _
        have h2 : 1 - δ / 2 ≤ t := le_max_right _ _
        rw [Complex.dist_eq,
          show (t : ℂ) * z - z = ((t - 1 : ℝ) : ℂ) * z by push_cast; ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, heq, mul_one,
          abs_of_nonpos (by linarith : t - 1 ≤ 0)]
        linarith
      have hball : ((t : ℂ) * z) ∈ Metric.ball (0 : ℂ) 1 := by
        rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht0.le, heq, mul_one]
        exact ht1
      have hUmem : discMap e ((t : ℂ) * z) ∈ U :=
        hδ' ⟨htdist, Metric.ball_subset_closedBall hball⟩
      exact ⟨discMap e ((t : ℂ) * z), hUmem, ⟨(t : ℂ) * z, hball, rfl⟩⟩

/-! ## The chart transfer -/

/-- For an open partial homeomorphism `ψ` and an open `U ⊆ ψ.source`, the image `ψ '' U` is open
in `ℂ`. -/
lemma isOpen_image_of_subset_source {ψ : OpenPartialHomeomorph X ℂ} {U : Set X}
    (hU : IsOpen U) (hUs : U ⊆ ψ.source) : IsOpen (ψ '' U) := by
  have h1 : IsOpen (Subtype.val ⁻¹' U : Set ↥ψ.source) := hU.preimage continuous_subtype_val
  have h2 : IsOpen (ψ.toHomeomorphSourceTarget '' (Subtype.val ⁻¹' U : Set ↥ψ.source)) :=
    ψ.toHomeomorphSourceTarget.isOpenMap _ h1
  have h3 : IsOpen
      (Subtype.val '' (ψ.toHomeomorphSourceTarget '' (Subtype.val ⁻¹' U : Set ↥ψ.source))) :=
    ψ.open_target.isOpenMap_subtype_val _ h2
  have heq : Subtype.val '' (ψ.toHomeomorphSourceTarget '' (Subtype.val ⁻¹' U : Set ↥ψ.source))
      = ψ '' U := by
    ext y
    constructor
    · rintro ⟨q, ⟨p, hp, hpq⟩, hqy⟩
      exact ⟨(p : X), hp, by rw [← hqy, ← hpq]; rfl⟩
    · rintro ⟨y, hyU, rfl⟩
      exact ⟨ψ.toHomeomorphSourceTarget ⟨y, hUs hyU⟩,
        ⟨⟨y, hUs hyU⟩, hyU, rfl⟩, rfl⟩
  rw [heq] at h3
  exact h3

/-- **A boundary point of the disc is not an interior point.**  Let `D ⊆ X` be a set
homeomorphic to the closed unit disc via `e`, and let `z` be a point of the unit circle.  Then
`e z` is not an interior point of `D`.

Indeed a chart at `e z` would exhibit a neighbourhood of `z` in the closed disc that is
homeomorphic to an open subset of `ℂ`, contradicting
`Work.Topology.Surface.false_of_homeomorph_nhds_sphere`. -/
theorem spherePoint_not_mem_interior {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D)
    {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 1) :
    ((e ⟨z, Metric.sphere_subset_closedBall hz⟩ : ↥D) : X) ∉ interior D := by
  intro hx
  have hz𝔻 : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.sphere_subset_closedBall hz
  set x : X := ((e ⟨z, hz𝔻⟩ : ↥D) : X) with hxdef
  set ψ : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hψdef
  have hxψ : x ∈ ψ.source := mem_chart_source ℂ x
  set U : Set X := interior D ∩ ψ.source with hUdef
  have hUopen : IsOpen U := isOpen_interior.inter ψ.open_source
  have hxU : x ∈ U := ⟨hx, hxψ⟩
  have hUD : U ⊆ D := fun y hy => interior_subset hy.1
  have hUψ : U ⊆ ψ.source := fun y hy => hy.2
  set N : Set ↥(Metric.closedBall (0 : ℂ) 1) := e ⁻¹' (Subtype.val ⁻¹' U) with hNdef
  have hzN : (⟨z, hz𝔻⟩ : ↥(Metric.closedBall (0 : ℂ) 1)) ∈ N := by
    show ((e ⟨z, hz𝔻⟩ : ↥D) : X) ∈ U
    rw [← hxdef]; exact hxU
  have hNopen : IsOpen N := ((hUopen.preimage continuous_subtype_val).preimage e.continuous)
  set W : Set ℂ := ψ '' U with hWdef
  have hWopen : IsOpen W := isOpen_image_of_subset_source hUopen hUψ
  have hDmem : ∀ w : ↥W, ψ.symm (w : ℂ) ∈ D := by
    intro w
    obtain ⟨y, hyU, hyw⟩ := w.2
    have h1 : w = ⟨ψ y, ⟨y, hyU, rfl⟩⟩ := Subtype.ext hyw.symm
    rw [h1, ψ.left_inv (hUψ hyU)]
    exact hUD hyU
  have hNmem : ∀ w : ↥W, e.symm (⟨ψ.symm (w : ℂ), hDmem w⟩ : ↥D) ∈ N := by
    intro w
    change ((e (e.symm (⟨ψ.symm (w : ℂ), hDmem w⟩ : ↥D)) : ↥D) : X) ∈ U
    rw [e.apply_symm_apply]
    change ψ.symm (w : ℂ) ∈ U
    obtain ⟨y, hyU, hyw⟩ := w.2
    have h1 : w = ⟨ψ y, ⟨y, hyU, rfl⟩⟩ := Subtype.ext hyw.symm
    rw [h1, ψ.left_inv (hUψ hyU)]
    exact hyU
  let toF : ↥N → ↥W := fun n => ⟨ψ ((e (n : ↥(Metric.closedBall (0 : ℂ) 1)) : ↥D) : X),
      (e (n : ↥(Metric.closedBall (0 : ℂ) 1)) : ↥D), n.2, rfl⟩
  let invF : ↥W → ↥N := fun w => ⟨e.symm (⟨ψ.symm (w : ℂ), hDmem w⟩ : ↥D), hNmem w⟩
  have hleft : Function.LeftInverse invF toF := by
    intro n
    refine Subtype.ext ?_
    show e.symm (⟨ψ.symm (ψ ((e (n : ↥(Metric.closedBall (0 : ℂ) 1)) : ↥D) : X)),
      hDmem (toF n)⟩ : ↥D) = n
    have hψinv : (⟨ψ.symm (ψ ((e (n : ↥(Metric.closedBall (0 : ℂ) 1)) : ↥D) : X)),
        hDmem (toF n)⟩ : ↥D) = e (n : ↥(Metric.closedBall (0 : ℂ) 1)) := by
      refine Subtype.ext ?_
      exact ψ.left_inv (hUψ n.2)
    rw [hψinv, e.symm_apply_apply]
  have hright : Function.RightInverse invF toF := by
    intro w
    refine Subtype.ext ?_
    show ψ ((e (e.symm (⟨ψ.symm (w : ℂ), hDmem w⟩ : ↥D)) : ↥D) : X) = (w : ℂ)
    rw [e.apply_symm_apply]
    exact ψ.right_inv (by
      obtain ⟨y, hyU, hyw⟩ := w.2
      rw [← hyw]
      exact ψ.map_source (hUψ hyU))
  have htoFcont : Continuous toF := by
    refine Continuous.subtype_mk ?_ _
    refine ψ.continuousOn.comp_continuous ?_ ?_
    · exact continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)
    · intro n
      exact hUψ n.2
  have hinvFcont : Continuous invF := by
    refine Continuous.subtype_mk ?_ _
    refine e.symm.continuous.comp (Continuous.subtype_mk ?_ hDmem)
    exact ψ.symm.continuousOn.comp_continuous continuous_subtype_val (by
      intro w
      obtain ⟨y, hyU, hyw⟩ := w.2
      rw [← hyw]
      exact ψ.map_source (hUψ hyU))
  let Φ : ↥N ≃ₜ ↥W :=
    { toFun := toF, invFun := invF, left_inv := hleft, right_inv := hright,
      continuous_toFun := htoFcont, continuous_invFun := hinvFcont }
  obtain ⟨δ, hδ, hδN⟩ := Metric.mem_nhds_iff.mp (hNopen.mem_nhds hzN)
  refine Work.Topology.Surface.false_of_homeomorph_nhds_sphere hz (δ := min δ 1)
    (lt_min hδ one_pos) (lt_of_le_of_lt (min_le_right _ _) one_lt_two) ?_ hWopen Φ
    Work.Topology.Surface.notHasArg_roundCircle
  intro w hw
  apply hδN
  rw [Metric.mem_ball, Subtype.dist_eq]
  exact lt_of_lt_of_le hw.1 (min_le_left _ _)

/-- **No boundary point of `D` is an interior point** (the `⊇` direction of invariance of
boundary): the interior of `D` is contained in the image of the open unit disc. -/
lemma interior_subset_discMap_ball {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) :
    interior D ⊆ discMap e '' Metric.ball (0 : ℂ) 1 := by
  intro y hy
  have hyD : y ∈ D := interior_subset hy
  obtain ⟨w, hw⟩ := e.surjective ⟨y, hyD⟩
  have hyw : discMap e (w : ℂ) = y := by
    rw [discMap_of_mem e w.2,
      show (⟨(w : ℂ), w.2⟩ : Metric.closedBall (0 : ℂ) 1) = w from Subtype.ext rfl]
    exact congrArg (fun u : ↥D => (u : X)) hw
  rw [← hyw]
  refine ⟨(w : ℂ), ?_, rfl⟩
  by_contra hnot
  rw [Metric.mem_ball, not_lt] at hnot
  have hwle : dist (w : ℂ) 0 ≤ 1 := Metric.mem_closedBall.mp w.2
  have hsp : (w : ℂ) ∈ Metric.sphere (0 : ℂ) 1 :=
    Metric.mem_sphere.mpr (le_antisymm hwle hnot)
  have hdisc : discMap e (w : ℂ)
      = ((e ⟨(w : ℂ), Metric.sphere_subset_closedBall hsp⟩ : ↥D) : X) := by
    rw [discMap_of_mem e (Metric.sphere_subset_closedBall hsp)]
  exact spherePoint_not_mem_interior e hsp (hdisc ▸ hyw ▸ hy)

/-! ## Invariance of domain for the disc -/

/-- **Invariance of domain** (plane form).  The image of the open unit disc is contained in the
interior of the image of the closed unit disc.  This is Brouwer's invariance of domain in
dimension two; it is the analytic content of the engulfing step. -/
theorem image_ball_subset_interior_image_closedBall {g : ℂ → ℂ}
    (hc : ContinuousOn g (Metric.closedBall (0 : ℂ) 1))
    (hi : Set.InjOn g (Metric.closedBall (0 : ℂ) 1)) :
    g '' Metric.ball (0 : ℂ) 1 ⊆ interior (g '' Metric.closedBall (0 : ℂ) 1) :=
  Work.Topology.Surface.image_ball_subset_interior_image_closedBall hc hi

/-- **Invariance of boundary for the embedded disc** (the crux): the image of the open unit disc
is the interior of `D`. -/
theorem discMap_ball_subset_interior {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) :
    discMap e '' Metric.ball (0 : ℂ) 1 ⊆ interior D := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hzD : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz
  have hzn : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  set x : X := discMap e z with hxdef
  let ψ : OpenPartialHomeomorph X ℂ := chartAt ℂ x
  have hxψ : x ∈ ψ.source := mem_chart_source ℂ x
  -- `discMap e` is continuous at `z`, which lies in the open unit disc
  have hcat : ContinuousAt (discMap e) z :=
    (((discMap_continuousOn e).mono Metric.ball_subset_closedBall).continuousWithinAt hz).continuousAt
      (Metric.isOpen_ball.mem_nhds hz)
  -- a small ball around `z` mapped into the chart source
  obtain ⟨ρ, hρpos, hρsub⟩ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ (discMap e) ⁻¹' ψ.source := by
    have h : (discMap e) ⁻¹' ψ.source ∈ 𝓝 z :=
      hcat.preimage_mem_nhds (ψ.open_source.mem_nhds hxψ)
    rwa [Metric.mem_nhds_iff] at h
  -- shrink so that the image stays inside the unit disc as well
  set r : ℝ := min (ρ / 2) ((1 - ‖z‖) / 2) with hr
  have hrpos : 0 < r := lt_min (by linarith) (by linarith)
  have hrρ : r < ρ := lt_of_le_of_lt (min_le_left (ρ / 2) ((1 - ‖z‖) / 2)) (by linarith)
  have hrz : ‖z‖ + r < 1 := by
    have h := min_le_right (ρ / 2) ((1 - ‖z‖) / 2)
    linarith
  have hnormr : ‖((r : ℝ) : ℂ)‖ = r := by simp [abs_of_pos hrpos]
  set T : Set ℂ := (fun u : ℂ => z + ((r : ℝ) : ℂ) * u) '' Metric.closedBall (0 : ℂ) 1 with hT
  have hTsub : T ⊆ Metric.ball z ρ := by
    rintro w ⟨u, hu, rfl⟩
    have hun : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hu
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, hnormr]
    calc r * ‖u‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hun hrpos.le
      _ < ρ := by rw [mul_one]; exact hrρ
  have hTn : T ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rintro w ⟨u, hu, rfl⟩
    have hun : ‖u‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hu
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z + ((r : ℝ) : ℂ) * u‖ ≤ ‖z‖ + ‖((r : ℝ) : ℂ) * u‖ := norm_add_le _ _
      _ = ‖z‖ + r * ‖u‖ := by rw [norm_mul, hnormr]
      _ ≤ ‖z‖ + r * 1 := by
            have h := mul_le_mul_of_nonneg_left hun hrpos.le
            linarith
      _ ≤ 1 := by rw [mul_one]; linarith
  have hTS : discMap e '' T ⊆ ψ.source := by
    rintro w ⟨v, hv, rfl⟩
    exact hρsub (hTsub hv)
  -- the transported map on the unit disc, and its two properties
  have hcont : ContinuousOn (fun u : ℂ => ψ (discMap e (z + ((r : ℝ) : ℂ) * u)))
      (Metric.closedBall (0 : ℂ) 1) := by
    have h1 : ContinuousOn (fun u : ℂ => z + ((r : ℝ) : ℂ) * u)
        (Metric.closedBall (0 : ℂ) 1) :=
      (by fun_prop : Continuous fun u : ℂ => z + ((r : ℝ) : ℂ) * u).continuousOn
    have h2 : ContinuousOn (discMap e) T := (discMap_continuousOn e).mono hTn
    have h3 : ContinuousOn ψ (discMap e '' T) :=
      fun p hp => (ψ.continuousAt (hTS hp)).continuousWithinAt
    have h4 : ContinuousOn (fun u : ℂ => discMap e (z + ((r : ℝ) : ℂ) * u))
        (Metric.closedBall (0 : ℂ) 1) := h2.comp' h1 (fun u hu => ⟨u, hu, rfl⟩)
    exact h3.comp' h4 (fun u hu => ⟨_, ⟨u, hu, rfl⟩, rfl⟩)
  have hinj : Set.InjOn (fun u : ℂ => ψ (discMap e (z + ((r : ℝ) : ℂ) * u)))
      (Metric.closedBall (0 : ℂ) 1) := by
    intro u hu v hv huv
    have huT : z + ((r : ℝ) : ℂ) * u ∈ T := ⟨u, hu, rfl⟩
    have hvT : z + ((r : ℝ) : ℂ) * v ∈ T := ⟨v, hv, rfl⟩
    have h1 : discMap e (z + ((r : ℝ) : ℂ) * u) = discMap e (z + ((r : ℝ) : ℂ) * v) :=
      ψ.injOn (hTS ⟨_, huT, rfl⟩) (hTS ⟨_, hvT, rfl⟩) huv
    have h1' : ((e ⟨z + ((r : ℝ) : ℂ) * u, hTn huT⟩ : ↥D) : X)
        = ((e ⟨z + ((r : ℝ) : ℂ) * v, hTn hvT⟩ : ↥D) : X) := by
      rw [← discMap_of_mem e (hTn huT), ← discMap_of_mem e (hTn hvT)]
      exact h1
    have h2 : (⟨z + ((r : ℝ) : ℂ) * u, hTn huT⟩ : Metric.closedBall (0 : ℂ) 1)
        = ⟨z + ((r : ℝ) : ℂ) * v, hTn hvT⟩ :=
      e.injective (Subtype.ext h1')
    have h3 : z + ((r : ℝ) : ℂ) * u = z + ((r : ℝ) : ℂ) * v := congrArg Subtype.val h2
    have h4 : ((r : ℝ) : ℂ) * u = ((r : ℝ) : ℂ) * v := add_left_cancel h3
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hrpos)) h4
  set G : Set ℂ := (fun u : ℂ => ψ (discMap e (z + ((r : ℝ) : ℂ) * u))) ''
      Metric.closedBall (0 : ℂ) 1 with hG
  have hmain : (fun u : ℂ => ψ (discMap e (z + ((r : ℝ) : ℂ) * u))) '' Metric.ball (0 : ℂ) 1
      ⊆ interior G := by
    rw [hG]
    exact image_ball_subset_interior_image_closedBall hcont hinj
  have hmem : ψ x ∈ interior G := by
    apply hmain
    refine ⟨0, Metric.mem_ball_self (by norm_num), ?_⟩
    simp only [mul_zero, add_zero]
    rw [hxdef]
  have hGtarget : G ⊆ ψ.target := by
    intro w hw
    rw [hG] at hw
    obtain ⟨u, hu, htu⟩ := hw
    rw [← ψ.image_source_eq_target]
    exact ⟨discMap e (z + ((r : ℝ) : ℂ) * u),
      hTS ⟨_, ⟨u, hu, rfl⟩, rfl⟩, htu⟩
  have hopen : IsOpen (ψ.symm '' interior G) :=
    ψ.isOpen_image_symm_of_subset_target isOpen_interior (interior_subset.trans hGtarget)
  have hGD : ψ.symm '' interior G ⊆ D := by
    rintro y ⟨t, ht, hty⟩
    have htG : t ∈ G := interior_subset ht
    rw [hG] at htG
    obtain ⟨u, hu, htu⟩ := htG
    have hsource : discMap e (z + ((r : ℝ) : ℂ) * u) ∈ ψ.source :=
      hTS ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have hleft : ψ.symm t = discMap e (z + ((r : ℝ) : ℂ) * u) := by
      rw [← htu]
      exact ψ.left_inv hsource
    rw [← hty, hleft]
    exact discMap_mem e (hTn ⟨u, hu, rfl⟩)
  have hxmem : x ∈ ψ.symm '' interior G := ⟨ψ x, hmem, ψ.left_inv hxψ⟩
  exact interior_maximal hGD hopen hxmem

/-! ## The homeomorphism onto the interior -/

/-- `↥t` is homeomorphic to `{x : ↥s // (x : α) ∈ t}` for `t ⊆ s`. -/
def subtypeValHomeomorph {α : Type*} [TopologicalSpace α] {s t : Set α} (h : t ⊆ s) :
    ↥t ≃ₜ ↥(Subtype.val ⁻¹' t : Set ↥s) where
  toFun y := ⟨⟨(y : α), h y.2⟩, y.2⟩
  invFun z := ⟨(z.1 : α), z.2⟩
  left_inv y := rfl
  right_inv z := rfl
  continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
  continuous_invFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

/-- The open unit disc is homeomorphic to the interior of `D`. -/
theorem nonempty_ball_homeomorph_interior {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D)
    (hcrux : interior D = discMap e '' Metric.ball (0 : ℂ) 1) :
    Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥(interior D)) := by
  have hiff : ∀ x : ↥(Metric.closedBall (0 : ℂ) 1),
      ((x : ℂ) ∈ Metric.ball (0 : ℂ) 1) ↔ ((e x : ↥D) : X) ∈ interior D := by
    intro x
    constructor
    · intro hx
      rw [hcrux]
      exact ⟨(x : ℂ), hx, by rw [discMap_of_mem e x.2]⟩
    · intro hx
      rw [hcrux] at hx
      obtain ⟨u, hu, hue⟩ := hx
      have h1 : (⟨u, Metric.ball_subset_closedBall hu⟩ : ↥(Metric.closedBall (0 : ℂ) 1)) = x := by
        refine e.injective (Subtype.ext ?_)
        rw [discMap_of_mem e (Metric.ball_subset_closedBall hu)] at hue
        exact hue
      rw [← h1]
      exact hu
  have h1 : ↥(Metric.ball (0 : ℂ) 1) ≃ₜ
      ↥(Subtype.val ⁻¹' Metric.ball (0 : ℂ) 1 : Set ↥(Metric.closedBall (0 : ℂ) 1)) :=
    subtypeValHomeomorph Metric.ball_subset_closedBall
  have h2 : ↥(Subtype.val ⁻¹' Metric.ball (0 : ℂ) 1 : Set ↥(Metric.closedBall (0 : ℂ) 1)) ≃ₜ
      ↥(Subtype.val ⁻¹' interior D : Set ↥D) := Homeomorph.subtype e hiff
  have h3 : ↥(Subtype.val ⁻¹' interior D : Set ↥D) ≃ₜ ↥(interior D) :=
    (subtypeValHomeomorph interior_subset).symm
  exact ⟨h1.trans (h2.trans h3)⟩

/-- **Invariance of boundary for the embedded disc.** -/
theorem disc_interior_invariance {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) :
    interior D = discMap e '' Metric.ball (0 : ℂ) 1 ∧
      Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥(interior D)) := by
  have h := Set.Subset.antisymm (interior_subset_discMap_ball e) (discMap_ball_subset_interior e)
  exact ⟨h, nonempty_ball_homeomorph_interior e h⟩

/-- The frontier of the interior of the disc is the image of the unit circle. -/
lemma frontier_interior_eq_discMap_sphere {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) :
    frontier (interior D) = discMap e '' Metric.sphere (0 : ℂ) 1 := by
  have hcrux : interior D = discMap e '' Metric.ball (0 : ℂ) 1 := (disc_interior_invariance e).1
  have hcl : closure (interior D) = D := by
    rw [hcrux]; exact closure_discMap_image_ball e
  have hfront : frontier (interior D) = D \ interior D := by
    rw [frontier_eq_closure_inter_closure, hcl, closure_compl, isOpen_interior.interior_eq]
    rfl
  have hsphere_sub : discMap e '' Metric.sphere (0 : ℂ) 1 ⊆ D \ interior D := by
    rintro y ⟨z, hz, rfl⟩
    refine ⟨discMap_mem e (Metric.sphere_subset_closedBall hz), ?_⟩
    intro hyint
    rw [hcrux] at hyint
    obtain ⟨w, hw, hwz⟩ := hyint
    have hzw : (⟨z, Metric.sphere_subset_closedBall hz⟩ : Metric.closedBall (0 : ℂ) 1)
        = ⟨w, Metric.ball_subset_closedBall hw⟩ := by
      have h1 : ((e ⟨z, Metric.sphere_subset_closedBall hz⟩ : ↥D) : X)
          = ((e ⟨w, Metric.ball_subset_closedBall hw⟩ : ↥D) : X) := by
        rw [← discMap_of_mem e (Metric.sphere_subset_closedBall hz),
          ← discMap_of_mem e (Metric.ball_subset_closedBall hw)]
        exact hwz.symm
      exact e.injective (Subtype.ext h1)
    have hz1 : dist (z : ℂ) 0 = 1 := Metric.mem_sphere.mp hz
    have hw1 : dist (w : ℂ) 0 < 1 := Metric.mem_ball.mp hw
    have hzw' : (z : ℂ) = (w : ℂ) := congrArg Subtype.val hzw
    rw [hzw'] at hz1
    linarith
  have hsphere_sup : D \ interior D ⊆ discMap e '' Metric.sphere (0 : ℂ) 1 := by
    rintro y ⟨hyD, hynotint⟩
    rw [← discMap_image_closedBall e] at hyD
    obtain ⟨w, hw, hwy⟩ := hyD
    have hw1 : dist (w : ℂ) 0 = 1 := by
      rcases lt_or_eq_of_le (by simpa [Metric.mem_closedBall, dist_zero_right] using hw) with
        h | h
      · exfalso
        apply hynotint
        rw [hcrux, ← hwy]
        exact ⟨w, Metric.mem_ball.mpr (by simpa using h), rfl⟩
      · simpa using h
    exact ⟨w, Metric.mem_sphere.mpr hw1, hwy⟩
  rw [hfront]
  exact Set.Subset.antisymm hsphere_sup hsphere_sub

theorem exists_ballPiece_of_closedDisc {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X)
    {D : Set X} (e : Metric.closedBall (0 : ℂ) 1 ≃ₜ ↥D) {K : Set X} (hK : K ⊆ interior D) :
    ∃ Ω : Set X, IsOpen Ω ∧ K ⊆ Ω ∧ IsCompact (closure Ω) ∧ IsConnected (frontier Ω) ∧
      Nonempty (Metric.ball (0 : ℂ) 1 ≃ₜ ↥Ω) := by
  refine ⟨interior D, isOpen_interior, hK, ?_, ?_, ?_⟩
  · refine (isCompact_discDisc e).of_isClosed_subset isClosed_closure ?_
    exact closure_minimal interior_subset (isCompact_discDisc e).isClosed
  · rw [frontier_interior_eq_discMap_sphere e]
    exact IsConnected.image
      (isConnected_sphere (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) (0 : ℂ)
        (by norm_num : (0 : ℝ) ≤ 1)) (discMap e)
      ((discMap_continuousOn e).mono Metric.sphere_subset_closedBall)
  · exact (disc_interior_invariance e).2

end Work.SimplyConnected.ABS
