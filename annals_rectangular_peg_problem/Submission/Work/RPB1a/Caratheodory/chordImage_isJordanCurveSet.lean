import Mathlib
import Submission.Work.RPB1a.Caratheodory.IOD.interior_image_of_continuousOn_injOn

/-!
# The image of a chord of the unit disc under a map injective on the disc is a Jordan curve

Let `Ψ : ℂ → ℂ` be continuous on the closed unit disc and injective on the open unit disc, and let
`ζ1 ≠ ζ2` be points of the unit circle with `Ψ ζ1 = Ψ ζ2`.  Then the image of the chord
`segment ℝ ζ1 ζ2` under `Ψ` is homeomorphic to the circle: the chord's interior lies in the open
disc, where `Ψ` is injective, so the parametrised loop `t ↦ Ψ ((1 - t) • ζ1 + t • ζ2)` identifies
exactly the two endpoints `ζ1`, `ζ2`.

The one input that is not purely bookkeeping is that no *boundary* value of `Ψ` is attained at an
*interior* point of the disc (`sphere_notMem_image_ball` below): this is a form of Brouwer's
invariance of domain in the plane, proved in `Work.RPB1a.Caratheodory.IOD`.
-/

namespace Work.RPB1a.Caratheodory

open Complex Set Metric
open scoped ContDiff Real Topology

noncomputable section

/-! ## The affine chord parametrisation -/

/-- The affine parametrisation `t ↦ (1 - t) • ζ1 + t • ζ2` of the segment from `ζ1` to `ζ2`. -/
def chord (ζ1 ζ2 : ℂ) (t : ℝ) : ℂ := (1 - t) • ζ1 + t • ζ2

@[simp] theorem chord_zero (ζ1 ζ2 : ℂ) : chord ζ1 ζ2 0 = ζ1 := by simp [chord]

@[simp] theorem chord_one (ζ1 ζ2 : ℂ) : chord ζ1 ζ2 1 = ζ2 := by simp [chord]

theorem chord_continuous (ζ1 ζ2 : ℂ) : Continuous (chord ζ1 ζ2) := by
  unfold chord
  fun_prop

theorem chord_injective {ζ1 ζ2 : ℂ} (hne : ζ1 ≠ ζ2) : Function.Injective (chord ζ1 ζ2) := by
  intro t t' h
  have h2 : chord ζ1 ζ2 t - chord ζ1 ζ2 t' = (t - t') • (ζ2 - ζ1) := by
    simp only [chord]
    module
  have hd : (t - t') • (ζ2 - ζ1) = 0 := by rw [← h2]; exact sub_eq_zero.mpr h
  rcases smul_eq_zero.mp hd with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd (sub_eq_zero.mp h').symm hne

theorem chord_image (ζ1 ζ2 : ℂ) :
    chord ζ1 ζ2 '' Icc (0 : ℝ) 1 = segment ℝ ζ1 ζ2 := by
  rw [segment_eq_image]
  rfl

theorem chord_mem_closedBall {ζ1 ζ2 : ℂ} (hζ1 : ζ1 ∈ sphere (0 : ℂ) 1)
    (hζ2 : ζ2 ∈ sphere (0 : ℂ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    chord ζ1 ζ2 t ∈ closedBall (0 : ℂ) 1 := by
  rw [mem_closedBall, dist_zero_right]
  have hn1 : ‖ζ1‖ = 1 := mem_sphere_zero_iff_norm.mp hζ1
  have hn2 : ‖ζ2‖ = 1 := mem_sphere_zero_iff_norm.mp hζ2
  calc ‖chord ζ1 ζ2 t‖ = ‖(1 - t) • ζ1 + t • ζ2‖ := by rw [chord]
    _ ≤ ‖(1 - t) • ζ1‖ + ‖t • ζ2‖ := norm_add_le _ _
    _ = |1 - t| * ‖ζ1‖ + |t| * ‖ζ2‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ = 1 := by
        rw [hn1, hn2, mul_one, mul_one,
          abs_of_nonneg (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t), abs_of_nonneg ht.1]
        ring

theorem chord_mem_ball {ζ1 ζ2 : ℂ} (hne : ζ1 ≠ ζ2) (hζ1 : ζ1 ∈ sphere (0 : ℂ) 1)
    (hζ2 : ζ2 ∈ sphere (0 : ℂ) 1) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    chord ζ1 ζ2 t ∈ ball (0 : ℂ) 1 := by
  have h1 : ζ1 ∈ closedBall (0 : ℂ) 1 := Metric.sphere_subset_closedBall hζ1
  have h2 : ζ2 ∈ closedBall (0 : ℂ) 1 := Metric.sphere_subset_closedBall hζ2
  have hsc := strictConvex_closedBall ℝ (0 : ℂ) 1
  have h := hsc h1 h2 hne (show (0 : ℝ) < 1 - t by linarith [ht.2]) ht.1 (by ring)
  have h3 : interior (closedBall (0 : ℂ) 1) = ball (0 : ℂ) 1 :=
    interior_closedBall (0 : ℂ) one_ne_zero
  rw [h3] at h
  simpa only [chord] using h

/-! ## The invariance-of-domain input -/

/-- Scaling and translating the closed unit ball: the image of `closedBall 0 1` under
`u ↦ w + ε • u` is `closedBall w ε` (for `ε > 0`). -/
theorem affine_image_closedBall (w : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun u : ℂ => w + ε • u) '' closedBall (0 : ℂ) 1 = closedBall w ε := by
  have h1 : ∀ u : ℂ, ‖(w + ε • u) - w‖ = ε * ‖u‖ := by
    intro u
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_closedBall, dist_eq_norm, sub_zero] at hu
    rw [mem_closedBall, dist_eq_norm, h1]
    calc ε * ‖u‖ ≤ ε * 1 := by gcongr
      _ = ε := mul_one _
  · intro hx
    rw [mem_closedBall, dist_eq_norm] at hx
    refine ⟨ε⁻¹ • (x - w), ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hε), ← div_eq_inv_mul, div_le_one hε]
      exact hx
    · show w + ε • (ε⁻¹ • (x - w)) = x
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hε), one_smul]
      abel

/-- **A boundary value of `Ψ` is not attained in the open disc.**  This is a form of Brouwer's
invariance of domain in the plane (see `Work.RPB1a.Caratheodory.IOD`).

Proof: suppose `Ψ ζ = Ψ w` with `ζ ∈ sphere 0 1` and `w ∈ ball 0 1`.  Invariance of domain,
applied to the rescaled map `u ↦ Ψ (w + (δ/2) • u)` where `closedBall w δ ⊆ ball 0 1`, shows that
`Ψ w` is an *interior* point of `Ψ '' closedBall w (δ/2)`.  Since `Ψ` is continuous at `ζ` and
`ζ ∉ closedBall w (δ/2)` while the latter is closed, a point `z` of the open disc can be found that
is simultaneously close enough to `ζ` for `Ψ z` to land in the interior of `Ψ '' closedBall w (δ/2)`
and close enough to `ζ` for `z` to lie outside `closedBall w (δ/2)`; but then `z` itself is the
(unique, by injectivity) preimage of `Ψ z` inside `closedBall w (δ/2)`, a contradiction. -/
theorem sphere_notMem_image_ball {Ψ : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hΨc : ContinuousOn Ψ (closedBall (0 : ℂ) 1)) (hΨi : InjOn Ψ (ball (0 : ℂ) 1)) :
    Ψ ζ ∉ Ψ '' ball (0 : ℂ) 1 := by
  classical
  rintro ⟨w, hw, hwζ⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (Metric.isOpen_ball.mem_nhds hw)
  have hεpos : 0 < δ / 2 := by linarith
  have hεcl : closedBall w (δ / 2) ⊆ ball (0 : ℂ) 1 :=
    subset_trans (Metric.closedBall_subset_ball (by linarith : δ / 2 < δ)) hδ
  have hmem_cl : ∀ u ∈ closedBall (0 : ℂ) 1, w + (δ / 2) • u ∈ ball (0 : ℂ) 1 := by
    intro u hu
    refine hεcl ?_
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hεpos]
    rw [mem_closedBall, dist_eq_norm, sub_zero] at hu
    calc δ / 2 * ‖u‖ ≤ δ / 2 * 1 := by gcongr
      _ = δ / 2 := mul_one _
  have hmem : Ψ w ∈ interior (Ψ '' closedBall w (δ / 2)) := by
    have hgcont : ContinuousOn (fun u : ℂ => Ψ (w + (δ / 2) • u)) (closedBall (0 : ℂ) 1) :=
      hΨc.comp (by fun_prop) (fun u hu => Metric.ball_subset_closedBall (hmem_cl u hu))
    have hginj : InjOn (fun u : ℂ => Ψ (w + (δ / 2) • u)) (closedBall (0 : ℂ) 1) := by
      intro u hu u' hu' huv
      have h3 : w + (δ / 2) • u = w + (δ / 2) • u' :=
        hΨi (hmem_cl u hu) (hmem_cl u' hu') huv
      have h4 : (δ / 2) • u = (δ / 2) • u' := add_left_cancel h3
      have h5 := congrArg (fun v : ℂ => (δ / 2)⁻¹ • v) h4
      simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hεpos), one_smul] using h5
    have hk := IOD.interior_image_of_continuousOn_injOn hgcont hginj
    have himg : (fun u : ℂ => Ψ (w + (δ / 2) • u)) '' closedBall (0 : ℂ) 1
        = Ψ '' closedBall w (δ / 2) := by
      show (Ψ ∘ fun u : ℂ => w + (δ / 2) • u) '' closedBall (0 : ℂ) 1
        = Ψ '' closedBall w (δ / 2)
      rw [Set.image_comp, affine_image_closedBall w hεpos]
    rw [himg] at hk
    simpa using hk
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hmem)
  have hζnot : ζ ∉ closedBall w (δ / 2) := by
    intro h
    have h1 : ζ ∈ ball (0 : ℂ) 1 := hεcl h
    rw [mem_ball, dist_zero_right] at h1
    rw [mem_sphere_zero_iff_norm.mp hζ] at h1
    exact lt_irrefl 1 h1
  obtain ⟨η, hηpos, hη⟩ :=
    Metric.mem_nhds_iff.mp (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hζnot)
  have hζcb : ζ ∈ closedBall (0 : ℂ) 1 := Metric.sphere_subset_closedBall hζ
  obtain ⟨η', hη'pos, hη'⟩ :=
    Metric.continuousWithinAt_iff.mp (hΨc ζ hζcb) ρ hρpos
  have hζclos : ζ ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball _ one_ne_zero]
    exact hζcb
  obtain ⟨z, hz, hzdist⟩ :=
    Metric.mem_closure_iff.mp hζclos (min η η') (lt_min hηpos hη'pos)
  have hzη : dist ζ z < η := lt_of_lt_of_le hzdist (min_le_left _ _)
  have hzη' : dist z ζ < η' := by
    rw [dist_comm]; exact lt_of_lt_of_le hzdist (min_le_right _ _)
  have hzα : Ψ z ∈ ball (Ψ w) ρ := by
    have h := hη' (Metric.ball_subset_closedBall hz) hzη'
    rw [← hwζ] at h
    exact h
  have hzS : Ψ z ∈ Ψ '' closedBall w (δ / 2) := interior_subset (hρ hzα)
  obtain ⟨v, hv, hvΨ⟩ := hzS
  have hveq : v = z := hΨi (hεcl hv) hz hvΨ
  have hzcl : z ∈ closedBall w (δ / 2) := hveq ▸ hv
  have hzball : z ∈ ball ζ η := by rwa [mem_ball, dist_comm]
  exact (hη hzball) hzcl

/-! ## The loop is a simple closed curve -/

theorem chordImage_isJordanCurveSet {Ψ : ℂ → ℂ} {ζ1 ζ2 : ℂ}
    (hζ1 : ζ1 ∈ sphere 0 1) (hζ2 : ζ2 ∈ sphere 0 1) (hne : ζ1 ≠ ζ2)
    (hΨc : ContinuousOn Ψ (closedBall 0 1)) (hΨi : InjOn Ψ (ball 0 1))
    (hΨa : Ψ ζ1 = Ψ ζ2) :
    Nonempty ((Ψ '' (segment ℝ ζ1 ζ2)) ≃ₜ Circle) := by
  classical
  have hA : ∀ w ∈ ball (0 : ℂ) 1, Ψ ζ1 ≠ Ψ w := fun w hw h =>
    sphere_notMem_image_ball hζ1 hΨc hΨi ⟨w, hw, h.symm⟩
  have hFcont : ContinuousOn (fun t : ℝ => Ψ (chord ζ1 ζ2 t)) (Icc (0 : ℝ) 1) :=
    hΨc.comp (chord_continuous ζ1 ζ2).continuousOn
      (fun t ht => chord_mem_closedBall hζ1 hζ2 ht)
  have hFimg : (fun t : ℝ => Ψ (chord ζ1 ζ2 t)) '' Icc (0 : ℝ) 1 =
      Ψ '' segment ℝ ζ1 ζ2 := by
    have hfun : (fun t : ℝ => Ψ (chord ζ1 ζ2 t)) = Ψ ∘ chord ζ1 ζ2 := rfl
    rw [hfun, ← chord_image ζ1 ζ2, Set.image_comp]
  have hinj : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
      Ψ (chord ζ1 ζ2 a) = Ψ (chord ζ1 ζ2 b) → a = b := by
    intro a ha b hb hab
    exact chord_injective hne (hΨi (chord_mem_ball hne hζ1 hζ2 ha)
      (chord_mem_ball hne hζ1 hζ2 hb) hab)
  have hnot : ∀ t ∈ Ioo (0 : ℝ) 1, Ψ (chord ζ1 ζ2 t) ≠ Ψ ζ1 := by
    intro t ht h
    exact hA _ (chord_mem_ball hne hζ1 hζ2 ht) h.symm
  have hnot' : ∀ t ∈ Ioo (0 : ℝ) 1, Ψ (chord ζ1 ζ2 t) ≠ Ψ ζ2 := by
    intro t ht h
    exact hnot t ht (by rw [h, hΨa])
  have hfiber : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      Ψ (chord ζ1 ζ2 a) = Ψ (chord ζ1 ζ2 b) →
        a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    intro a ha b hb hab
    by_cases ha0 : a = 0
    · subst ha0
      rw [chord_zero] at hab
      by_cases hb0 : b = 0
      · exact Or.inl hb0.symm
      by_cases hb1 : b = 1
      · exact Or.inr (Or.inl ⟨rfl, hb1⟩)
      · exact absurd hab.symm (hnot b ⟨lt_of_le_of_ne hb.1 (Ne.symm hb0),
          lt_of_le_of_ne hb.2 hb1⟩)
    by_cases ha1 : a = 1
    · subst ha1
      rw [chord_one] at hab
      by_cases hb1 : b = 1
      · exact Or.inl hb1.symm
      by_cases hb0 : b = 0
      · exact Or.inr (Or.inr ⟨rfl, hb0⟩)
      · exact absurd hab.symm (hnot' b ⟨lt_of_le_of_ne hb.1 (Ne.symm hb0),
          lt_of_le_of_ne hb.2 hb1⟩)
    · have hAint : a ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne ha.1 (Ne.symm ha0), lt_of_le_of_ne ha.2 ha1⟩
      have hb0 : b ≠ 0 := by
        intro h; subst h
        rw [chord_zero] at hab
        exact hnot a hAint hab
      have hb1 : b ≠ 1 := by
        intro h; subst h
        rw [chord_one] at hab
        exact hnot' a hAint hab
      exact Or.inl (hinj a hAint b ⟨lt_of_le_of_ne hb.1 (Ne.symm hb0),
        lt_of_le_of_ne hb.2 hb1⟩ hab)
  let Φ : ↥(Icc (0 : ℝ) 1) → ↥(Ψ '' segment ℝ ζ1 ζ2) :=
    fun t => ⟨Ψ (chord ζ1 ζ2 t.1), by
      rw [← chord_image ζ1 ζ2]
      exact ⟨chord ζ1 ζ2 t.1, ⟨t.1, t.2, rfl⟩, rfl⟩⟩
  have hΦcont : Continuous Φ := by
    refine Continuous.subtype_mk ?_ _
    exact hFcont.comp_continuous continuous_subtype_val (fun t => t.2)
  haveI : CompactSpace ↥(Icc (0 : ℝ) 1) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have hΦsurj : Function.Surjective Φ := by
    intro y
    have hy : y.1 ∈ (fun t : ℝ => Ψ (chord ζ1 ζ2 t)) '' Icc (0 : ℝ) 1 := by
      rw [hFimg]; exact y.2
    obtain ⟨t, ht, hty⟩ := hy
    exact ⟨⟨t, ht⟩, Subtype.ext hty⟩
  have hΦquot : Topology.IsQuotientMap Φ := by
    refine IsClosedMap.isQuotientMap ?_ hΦcont hΦsurj
    intro C hC
    exact (hC.isCompact.image hΦcont).isClosed
  have hclass : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      Ψ (chord ζ1 ζ2 a) = Ψ (chord ζ1 ζ2 b) →
        ((a : ℝ) : UnitAddCircle) = ((b : ℝ) : UnitAddCircle) := by
    intro a ha b hb hab
    have h01 : ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) := by
      have h := AddCircle.coe_add_period (1 : ℝ) 0
      rw [zero_add] at h
      exact h
    rcases hfiber a ha b hb hab with h | ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
    · rw [h]
    · rw [ha0, hb1]; exact h01.symm
    · rw [ha1, hb0]; exact h01
  have hmain : ∃ δ : ↥(Ψ '' segment ℝ ζ1 ζ2) → UnitAddCircle,
      Continuous δ ∧ Function.Bijective δ := by
    let δ : ↥(Ψ '' segment ℝ ζ1 ζ2) → UnitAddCircle :=
      fun y => (((Classical.choose (hΦsurj y) : ↥(Icc (0 : ℝ) 1)) : ℝ) : UnitAddCircle)
    have hδΦ : ∀ t : ↥(Icc (0 : ℝ) 1), δ (Φ t) = ((t : ℝ) : UnitAddCircle) := by
      intro t
      have h1 : Φ (Classical.choose (hΦsurj (Φ t))) = Φ t :=
        Classical.choose_spec (hΦsurj (Φ t))
      have h2 : Ψ (chord ζ1 ζ2 ((Classical.choose (hΦsurj (Φ t)) : ↥(Icc (0 : ℝ) 1)) : ℝ)) =
          Ψ (chord ζ1 ζ2 (t : ℝ)) := by
        have := congrArg Subtype.val h1
        simpa [Φ] using this
      exact hclass _ (Classical.choose (hΦsurj (Φ t))).2 _ t.2 h2
    have hδcont : Continuous δ := by
      rw [hΦquot.continuous_iff]
      have hcomp : δ ∘ Φ = fun t : ↥(Icc (0 : ℝ) 1) => ((t : ℝ) : UnitAddCircle) :=
        funext fun t => hδΦ t
      rw [hcomp]
      fun_prop
    have hδinj : Function.Injective δ := by
      intro y y' hyy
      obtain ⟨a, rfl⟩ := hΦsurj y
      obtain ⟨b, rfl⟩ := hΦsurj y'
      have h1 : ((a : ℝ) : UnitAddCircle) = ((b : ℝ) : UnitAddCircle) := by
        rw [← hδΦ a, ← hδΦ b]; exact hyy
      have h2 : ((a : ℝ) - (b : ℝ)) ∈ AddSubgroup.zmultiples (1 : ℝ) :=
        (QuotientAddGroup.eq_iff_sub_mem).mp h1
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp h2
      simp only [zsmul_eq_mul, mul_one] at hm
      have hm' : (a : ℝ) - (b : ℝ) = (m : ℝ) := hm.symm
      have ha := a.2; have hb := b.2
      have hmlow : (-1 : ℝ) ≤ (m : ℝ) := by linarith [ha.1, hb.2]
      have hmhigh : (m : ℝ) ≤ 1 := by linarith [ha.2, hb.1]
      have hkey : a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
        rcases lt_trichotomy m 0 with hm0 | hm0 | hm0
        · right; left
          have hm1 : m = -1 := by
            have h1 : (-1 : ℤ) ≤ m := by exact_mod_cast hmlow
            omega
          have hab1 : (a : ℝ) - (b : ℝ) = -1 := by rw [hm', hm1]; norm_num
          have ha0 : (a : ℝ) = 0 := by linarith [ha.1, hb.2]
          have hb1 : (b : ℝ) = 1 := by linarith [hb.2, ha.1]
          exact ⟨Subtype.ext ha0, Subtype.ext hb1⟩
        · left
          have hab0 : (a : ℝ) - (b : ℝ) = 0 := by rw [hm', hm0]; norm_num
          exact Subtype.ext (by linarith)
        · right; right
          have hm1 : m = 1 := by
            have h1 : m ≤ (1 : ℤ) := by exact_mod_cast hmhigh
            omega
          have hab1 : (a : ℝ) - (b : ℝ) = 1 := by rw [hm', hm1]; norm_num
          have ha1 : (a : ℝ) = 1 := by linarith [ha.2, hb.1]
          have hb0 : (b : ℝ) = 0 := by linarith [hb.1, ha.2]
          exact ⟨Subtype.ext ha1, Subtype.ext hb0⟩
      rcases hkey with h | ⟨ha0, hb1⟩ | ⟨ha1, hb0⟩
      · rw [h]
      · have hzero : (a : ℝ) = 0 := by simpa using congrArg Subtype.val ha0
        have hone : (b : ℝ) = 1 := by simpa using congrArg Subtype.val hb1
        apply Subtype.ext
        show Ψ (chord ζ1 ζ2 (a : ℝ)) = Ψ (chord ζ1 ζ2 (b : ℝ))
        rw [hzero, hone, chord_zero, chord_one, hΨa]
      · have hone : (a : ℝ) = 1 := by simpa using congrArg Subtype.val ha1
        have hzero : (b : ℝ) = 0 := by simpa using congrArg Subtype.val hb0
        apply Subtype.ext
        show Ψ (chord ζ1 ζ2 (a : ℝ)) = Ψ (chord ζ1 ζ2 (b : ℝ))
        rw [hone, hzero, chord_zero, chord_one, hΨa]
    have hδsurj : Function.Surjective δ := by
      intro c
      have huI : ((AddCircle.equivIco (1 : ℝ) 0 c : ℝ)) ∈ Icc (0 : ℝ) 1 := by
        have h := (AddCircle.equivIco (1 : ℝ) 0 c).2
        simp only [Set.mem_Ico] at h
        refine ⟨h.1, le_of_lt ?_⟩
        simpa using h.2
      refine ⟨Φ ⟨↑(AddCircle.equivIco (1 : ℝ) 0 c), huI⟩, ?_⟩
      have h1 := hδΦ ⟨↑(AddCircle.equivIco (1 : ℝ) 0 c), huI⟩
      rw [h1]
      exact AddCircle.coe_equivIco (p := (1 : ℝ)) (a := 0) (y := c)
    exact ⟨δ, hδcont, hδinj, hδsurj⟩
  obtain ⟨δ, hδcont, hδbij⟩ := hmain
  have hcomp : IsCompact (Ψ '' segment ℝ ζ1 ζ2) := by
    rw [← hFimg]
    exact isCompact_Icc.image_of_continuousOn hFcont
  haveI : CompactSpace ↥(Ψ '' segment ℝ ζ1 ζ2) := isCompact_iff_compactSpace.mp hcomp
  exact ⟨(IsHomeomorph.homeomorph δ
      (isHomeomorph_iff_continuous_bijective.mpr ⟨hδcont, hδbij⟩)).trans
    (AddCircle.homeomorphCircle (T := 1) one_ne_zero)⟩

end

end Work.RPB1a.Caratheodory
