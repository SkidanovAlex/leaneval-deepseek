import Submission.Work.BoxShrink.Bubble.Plane.Perturb

/-!
# Perturbing off a slice which is countable on compacta

`Work.BoxShrink.Bubble.Plane.Perturb` moves a *thin* path off a set `W` which is **finite on
compacta**, using that the bad translations form a finite union of translates of the path.  The same
argument works for `W` which is **countable on compacta**: the bad set is then a *countable* union of
closed sets with empty interior, and in the Baire space `ℝ²` such a union still has empty interior
(`interior_iUnion_empty`, from `dense_iInter_of_isOpen`).  What remains true — and is the reason the
method stops here — is that a slice which is locally an arc is *not* countable on compacta and the
bad set genuinely contains a neighbourhood of the origin.
-/

open Set

namespace Work.BoxShrink.Bubble.Plane

/-- **A countable union of closed sets with empty interior has empty interior.**  (Baire: the
complements are dense open sets, so their intersection — the complement of the union — is dense.) -/
theorem interior_iUnion_empty {ι : Type*} [Countable ι] (f : ι → Set (ℝ × ℝ))
    (h : ∀ i, IsClosed (f i) ∧ interior (f i) = ∅) : interior (⋃ i, f i) = ∅ := by
  have hsub : ∀ i, (interior (f i))ᶜ ⊆ closure ((f i)ᶜ) := by
    intro i x hx
    rw [mem_closure_iff]
    intro U hU hxU
    by_contra hcon
    have hUs : U ⊆ f i := by
      intro z hz
      by_contra hzs
      exact hcon ⟨z, hz, hzs⟩
    exact hx (interior_maximal hUs hU hxU)
  have hdense : Dense (⋂ i, (f i)ᶜ) := by
    refine dense_iInter_of_isOpen (fun i => (h i).1.isOpen_compl) (fun i => ?_)
    rw [dense_iff_closure_eq]
    have h' : (interior (f i))ᶜ ⊆ closure ((f i)ᶜ) := hsub i
    rw [(h i).2] at h'
    exact eq_univ_of_univ_subset (by simpa using h')
  have hcompl : Dense ((⋃ i, f i)ᶜ) := by
    rw [Set.compl_iUnion]
    exact hdense
  have hf : interior (⋃ i, f i) = (closure ((⋃ i, f i)ᶜ))ᶜ := by
    have h2 : interior ((⋃ i, f i)ᶜ)ᶜ = (closure ((⋃ i, f i)ᶜ))ᶜ :=
      interior_compl (s := (⋃ i, f i)ᶜ)
    simpa using h2
  rw [hf, hcompl.closure_eq]
  simp

/-- **A small translation moves a closed thin set off a set which is countable on compacta.** -/
theorem exists_translate_disjoint_of_countable {T W : Set (ℝ × ℝ)} {δ : ℝ} (hδ : 0 < δ)
    (hTc : IsClosed T) (hTi : interior T = ∅)
    (hcount : (W ∩ {q : ℝ × ℝ | ∃ t ∈ T, dist q t < δ}).Countable) :
    ∃ v : ℝ × ℝ, ‖v‖ < δ ∧ Disjoint ((fun t : ℝ × ℝ => t + v) '' T) W := by
  classical
  set Wf : Set (ℝ × ℝ) := W ∩ {q : ℝ × ℝ | ∃ t ∈ T, dist q t < δ} with hWf
  letI : Countable Wf := hcount.to_subtype
  by_contra hcon
  rw [not_exists] at hcon
  have hbad : ∀ v : ℝ × ℝ, ‖v‖ < δ → ∃ w ∈ W, ∃ t ∈ T, w = t + v := by
    intro v hv
    have hnd : ¬ Disjoint ((fun t : ℝ × ℝ => t + v) '' T) W :=
      fun hd => hcon v ⟨hv, hd⟩
    obtain ⟨x, hxA, hxW⟩ := Set.not_disjoint_iff.mp hnd
    obtain ⟨t, htT, rfl⟩ := hxA
    exact ⟨t + v, hxW, t, htT, rfl⟩
  have hcover : Metric.ball (0 : ℝ × ℝ) δ ⊆
      ⋃ w ∈ Wf, (fun t : ℝ × ℝ => w - t) '' T := by
    intro v hv
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hv
    obtain ⟨w, hwW, t, htT, hwt⟩ := hbad v hv
    have hmem : w ∈ Wf := ⟨hwW, t, htT, by
      have hwt' : w - t = v := by rw [hwt]; simp
      rw [dist_eq_norm, hwt']
      exact hv⟩
    have hterm : v ∈ (fun t : ℝ × ℝ => w - t) '' T := ⟨t, htT, by rw [hwt]; simp⟩
    exact Set.mem_biUnion hmem hterm
  -- each piece is closed with empty interior
  have hpiece : ∀ w ∈ Wf, IsClosed ((fun t : ℝ × ℝ => w - t) '' T) ∧
      interior ((fun t : ℝ × ℝ => w - t) '' T) = ∅ := by
    intro w _
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
  have hempty : interior (⋃ w ∈ Wf, (fun t : ℝ × ℝ => w - t) '' T) = ∅ := by
    rw [Set.biUnion_eq_iUnion]
    refine interior_iUnion_empty _ (fun w : Wf => hpiece w w.2)
  have hne : (interior (Metric.ball (0 : ℝ × ℝ) δ)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [Metric.isOpen_ball.interior_eq]
    exact Metric.mem_ball_self hδ
  obtain ⟨y, hy⟩ := hne
  have hy' : y ∈ interior (⋃ w ∈ Wf, (fun t : ℝ × ℝ => w - t) '' T) := interior_mono hcover hy
  have : y ∈ (∅ : Set (ℝ × ℝ)) := by simpa only [hempty] using hy'
  exact this

/-- **A path with a thin image can be translated off a set which is countable on compacta.**

Same statement as `Work.BoxShrink.Bubble.Plane.exists_path_avoiding_of_thin`, with `W` only assumed
countable on compact sets (the proof replaces the finite union of the bad-set argument by a
countable one, using Baire). -/
theorem exists_path_avoiding_of_thin_of_countable {Ω W : Set (ℝ × ℝ)}
    {p : C(Set.Icc (0 : ℝ) 1, ℝ × ℝ)}
    (hthin_closed : IsClosed (Set.range p)) (hthin_int : interior (Set.range p) = ∅)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (htube : ∀ v : ℝ × ℝ, ‖v‖ < δ₀ →
      ∀ t : Set.Icc (0 : ℝ) 1, p t + v ∈ Ω)
    (hcount : ∀ K : Set (ℝ × ℝ), IsCompact K → (K ∩ W).Countable) :
    ∃ v : ℝ × ℝ, ‖v‖ < δ₀ ∧ ∀ t : Set.Icc (0 : ℝ) 1, p t + v ∈ Ω \ W := by
  obtain ⟨R, hR⟩ := ((isCompact_range p.continuous).isBounded :
    Bornology.IsBounded (Set.range p)).exists_norm_le
  have hcount' : (W ∩ {q : ℝ × ℝ | ∃ t ∈ Set.range p, dist q t < δ₀}).Countable := by
    refine (hcount (Metric.closedBall (0 : ℝ × ℝ) (R + δ₀)) (isCompact_closedBall _ _)).mono ?_
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
  obtain ⟨v, hv, hdisj⟩ :=
    exists_translate_disjoint_of_countable hδ₀ hthin_closed hthin_int hcount'
  refine ⟨v, hv, fun t => ⟨htube v hv t, ?_⟩⟩
  intro hmem
  have : p t + v ∈ ((fun t : ℝ × ℝ => t + v) '' Set.range p) := ⟨p t, ⟨t, rfl⟩, rfl⟩
  exact (Set.disjoint_left.mp hdisj this) hmem

end Work.BoxShrink.Bubble.Plane
