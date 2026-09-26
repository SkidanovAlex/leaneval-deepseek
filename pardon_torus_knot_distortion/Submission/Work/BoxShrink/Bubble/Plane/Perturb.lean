import Mathlib

/-!
# Perturbing a path off a locally finite closed set by a translation

This file is the elementary core of the perturbation method for the plane-level form of the push-off
(`Work.BoxShrink.Bubble.SlicePushOff`).

Let `T ⊆ ℝ²` be the image of a path which is *closed* with *empty interior* (a "thin" path — for
instance a polygonal path, see `Work.BoxShrink.Bubble.Plane.thinPath`), let `W ⊆ ℝ²` be closed with
`W ∩ K` finite for every compact `K` (the lifted slice of a configuration in which the plane meets
the region inside the box in finitely many points, see
`Work.BoxShrink.Bubble.Plane.finite_preimage`), and let `δ > 0`.  Then

  `Work.BoxShrink.Bubble.Plane.exists_translate_disjoint`:
    there is `v` with `‖v‖ < δ` and `(T + v) ∩ W = ∅`,

i.e. a *small translation* of the path avoids `W`, hence stays in any open set containing the
`δ`-neighbourhood of `T`.

**Proof.**  A vector `v` with `‖v‖ < δ` is bad exactly when `v ∈ W - T`; if every such `v` were bad,
then `B(0,δ) ⊆ ⋃_{w ∈ W ∩ (T + B(0,δ))} (w - T)`, a *finite* union of translates of `-T`.  Each of
those is closed with empty interior, and a finite union of closed sets with empty interior has empty
interior (`interior_biUnion_empty`), whereas `B(0,δ)` does not.  Hence not every `v` is bad.

The interest of the statement is that it needs no regularity of `W` beyond "closed and finite on
compacta".  A slice which is locally an arc *violates* the finiteness hypothesis, and that is exactly
the case in which the translation method fails (documented in `PLAN.md`).
-/

open Set

namespace Work.BoxShrink.Bubble.Plane

/-- **The union of two closed sets of empty interior has empty interior.** -/
theorem interior_union_empty {C T : Set (ℝ × ℝ)} (hC : IsClosed C)
    (hCi : interior C = ∅) (hTi : interior T = ∅) : interior (C ∪ T) = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ : (interior (C ∪ T)).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  have hUopen : IsOpen (interior (C ∪ T)) := isOpen_interior
  have hUsub : interior (C ∪ T) ⊆ C ∪ T := interior_subset
  have hnotsub : ¬ interior (C ∪ T) ⊆ C := by
    intro hsub
    have : interior (C ∪ T) ⊆ interior C := interior_maximal hsub hUopen
    rw [hCi] at this
    exact (this hx)
  obtain ⟨y, hyU, hyC⟩ := Set.not_subset.mp hnotsub
  have hpiece_open : IsOpen (interior (C ∪ T) \ C) := hUopen.sdiff hC
  have hpiece_sub : interior (C ∪ T) \ C ⊆ T := by
    intro z hz
    rcases hUsub hz.1 with h | h
    · exact absurd h hz.2
    · exact h
  have : y ∈ interior T := interior_maximal hpiece_sub hpiece_open ⟨hyU, hyC⟩
  rw [hTi] at this
  exact this

/-- **A finite union of closed sets with empty interior has empty interior.** -/
theorem interior_biUnion_empty {ι : Type*} (s : Finset ι) (f : ι → Set (ℝ × ℝ))
    (h : ∀ i ∈ s, IsClosed (f i) ∧ interior (f i) = ∅) :
    interior (⋃ i ∈ s, f i) = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.set_biUnion_insert]
      have ha' : IsClosed (f a) ∧ interior (f a) = ∅ := h a (Finset.mem_insert_self a S)
      have hS' : ∀ i ∈ S, IsClosed (f i) ∧ interior (f i) = ∅ :=
        fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hclosed : IsClosed (⋃ i ∈ S, f i) :=
        isClosed_biUnion_finset (fun i hi => (hS' i hi).1)
      exact interior_union_empty ha'.1 ha'.2 (ih hS')

/-- **A small translation moves a closed thin set off a closed set which is finite on compacta.**

If `T` is closed with empty interior, `W` is such that `W ∩ {q | ∃ t ∈ T, dist q t < δ}` is finite,
then some `v` with `‖v‖ < δ` satisfies `(T + v) ∩ W = ∅`. -/
theorem exists_translate_disjoint {T W : Set (ℝ × ℝ)} {δ : ℝ} (hδ : 0 < δ)
    (hTc : IsClosed T) (hTi : interior T = ∅)
    (hfin : (W ∩ {q : ℝ × ℝ | ∃ t ∈ T, dist q t < δ}).Finite) :
    ∃ v : ℝ × ℝ, ‖v‖ < δ ∧
      Disjoint ((fun t : ℝ × ℝ => t + v) '' T) W := by
  classical
  set Wf : Set (ℝ × ℝ) := W ∩ {q : ℝ × ℝ | ∃ t ∈ T, dist q t < δ} with hWf
  have hWfs : Wf.Finite := hfin
  by_contra hcon
  rw [not_exists] at hcon
  -- every small `v` is bad: it is the difference of a point of `W` and a point of `T`
  have hbad : ∀ v : ℝ × ℝ, ‖v‖ < δ → ∃ w ∈ W, ∃ t ∈ T, w = t + v := by
    intro v hv
    have hnd : ¬ Disjoint ((fun t : ℝ × ℝ => t + v) '' T) W :=
      fun hd => hcon v ⟨hv, hd⟩
    obtain ⟨x, hxA, hxW⟩ := Set.not_disjoint_iff.mp hnd
    obtain ⟨t, htT, rfl⟩ := hxA
    exact ⟨t + v, hxW, t, htT, rfl⟩
  -- hence `ball 0 δ` is covered by the finitely many translates `w - T`, `w ∈ Wf`
  have hcover : Metric.ball (0 : ℝ × ℝ) δ ⊆
      ⋃ w ∈ (hWfs.toFinset : Set (ℝ × ℝ)), (fun t : ℝ × ℝ => w - t) '' T := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hv
    obtain ⟨w, hwW, t, htT, hwt⟩ := hbad v hv
    have hwWf : w ∈ Wf := by
      refine ⟨hwW, t, htT, ?_⟩
      have hwt' : w - t = v := by rw [hwt]; simp
      rw [dist_eq_norm, hwt']
      exact hv
    have hwWf' : w ∈ (hWfs.toFinset : Set (ℝ × ℝ)) := by
      rw [hWfs.coe_toFinset]
      exact hwWf
    exact Set.mem_biUnion hwWf' ⟨t, htT, by rw [hwt]; simp⟩
  -- each piece is closed with empty interior
  have hpiece : ∀ w ∈ (hWfs.toFinset : Set (ℝ × ℝ)),
      IsClosed ((fun t : ℝ × ℝ => w - t) '' T) ∧
        interior ((fun t : ℝ × ℝ => w - t) '' T) = ∅ := by
    intro w _
    have hρ : ((Homeomorph.neg (ℝ × ℝ)).trans (Homeomorph.addRight w) :
        (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) = (Homeomorph.neg (ℝ × ℝ)).trans (Homeomorph.addRight w) := rfl
    set ρ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
      (Homeomorph.neg (ℝ × ℝ)).trans (Homeomorph.addRight w) with hρdef
    have hfun : (fun t : ℝ × ℝ => w - t) = (ρ : ℝ × ℝ → ℝ × ℝ) := by
      funext t
      show w - t = ρ t
      rw [hρdef]
      simp [sub_eq_add_neg, add_comm]
    constructor
    · rw [hfun]
      exact (Homeomorph.isClosed_image ρ).mpr hTc
    · rw [hfun, ← Homeomorph.image_interior ρ T, hTi, Set.image_empty]
  have hempty : interior (⋃ w ∈ (hWfs.toFinset : Set (ℝ × ℝ)),
      (fun t : ℝ × ℝ => w - t) '' T) = ∅ :=
    interior_biUnion_empty hWfs.toFinset
      (fun w : ℝ × ℝ => (fun t : ℝ × ℝ => w - t) '' T) hpiece
  -- but `ball 0 δ` has nonempty interior
  have hsub : Metric.ball (0 : ℝ × ℝ) δ ⊆
      ⋃ w ∈ (hWfs.toFinset : Set (ℝ × ℝ)), (fun t : ℝ × ℝ => w - t) '' T := hcover
  have hne : (interior (Metric.ball (0 : ℝ × ℝ) δ)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [(Metric.isOpen_ball.interior_eq)]
    exact Metric.mem_ball_self hδ
  obtain ⟨y, hy⟩ := hne
  have hy' : y ∈ interior (⋃ w ∈ (hWfs.toFinset : Set (ℝ × ℝ)),
      (fun t : ℝ × ℝ => w - t) '' T) := interior_mono hsub hy
  have : y ∈ (∅ : Set (ℝ × ℝ)) := by simpa only [hempty] using hy'
  exact this

/-- **A path with a thin image can be translated off a closed locally finite set, staying in an
open set.**

`p` is a path into the open set `Ω` whose image is closed with empty interior and at distance
`δ₀ > 0` from the complement of `Ω`; `W` is closed with `K ∩ W` finite for every compact `K`.
Then some translate `p + v` with `‖v‖ < δ₀` avoids `W` (and still lies in `Ω`). -/
theorem exists_path_avoiding_of_thin {Ω W : Set (ℝ × ℝ)}
    {p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)}
    (hthin_closed : IsClosed (Set.range p)) (hthin_int : interior (Set.range p) = ∅)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (htube : ∀ v : ℝ × ℝ, ‖v‖ < δ₀ →
      ∀ t : Set.Icc (0 : ℝ) 1, p t + v ∈ Ω)
    (hfin : ∀ K : Set (ℝ × ℝ), IsCompact K → (K ∩ W).Finite) :
    ∃ v : ℝ × ℝ, ‖v‖ < δ₀ ∧ ∀ t : Set.Icc (0 : ℝ) 1, p t + v ∈ Ω \ W := by
  -- the range of `p` is bounded, so the finiteness hypothesis applies to a large ball
  obtain ⟨R, hR⟩ := ((isCompact_range p.continuous).isBounded :
    Bornology.IsBounded (Set.range p)).exists_norm_le
  have hR0 : (0 : ℝ) ≤ R := le_trans (norm_nonneg (p ⟨0, by norm_num⟩)) (hR _ ⟨_, rfl⟩)
  have hfin' : (W ∩ {q : ℝ × ℝ | ∃ t ∈ Set.range p, dist q t < δ₀}).Finite := by
    refine (hfin (Metric.closedBall (0 : ℝ × ℝ) (R + δ₀)) (isCompact_closedBall _ _)).subset ?_
    rintro q ⟨hqW, t, ht, hqt⟩
    have hqcb : q ∈ Metric.closedBall (0 : ℝ × ℝ) (R + δ₀) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      calc ‖q‖ = ‖t + (q - t)‖ := by rw [show t + (q - t) = q from by abel]
        _ ≤ ‖t‖ + ‖q - t‖ := norm_add_le _ _
        _ ≤ R + δ₀ := by
            have h1 : ‖t‖ ≤ R := hR t ht
            have h2 : ‖q - t‖ = dist q t := by rw [dist_eq_norm]
            linarith
    exact ⟨hqcb, hqW⟩
  obtain ⟨v, hv, hdisj⟩ := exists_translate_disjoint hδ₀ hthin_closed hthin_int hfin'
  refine ⟨v, hv, fun t => ⟨htube v hv t, ?_⟩⟩
  intro hmem
  have : p t + v ∈ ((fun t : ℝ × ℝ => t + v) '' Set.range p) := ⟨p t, ⟨t, rfl⟩, rfl⟩
  exact (Set.disjoint_left.mp hdisj this) hmem

end Work.BoxShrink.Bubble.Plane
