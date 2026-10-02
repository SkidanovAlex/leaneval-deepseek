import Mathlib
import Submission.Work.ELRig.sign_flip_of_two_components

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open scoped Topology
open Set

/-- `dist (p + t) p = |t|` for a real `t`. -/
lemma dist_add_real (p : ℂ) (t : ℝ) : dist (p + (t : ℂ)) p = |t| := by
  rw [dist_eq_norm]
  have h : p + (t : ℂ) - p = (t : ℂ) := by ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

/-- `dist (p - t) p = |t|` for a real `t`. -/
lemma dist_sub_real (p : ℂ) (t : ℝ) : dist (p - (t : ℂ)) p = |t| := by
  rw [dist_eq_norm]
  have h : p - (t : ℂ) - p = -((t : ℂ)) := by ring
  rw [h, norm_neg, Complex.norm_real, Real.norm_eq_abs]

/-- **Horizontal analogue of `sign_flip_of_two_components`.**  Let `U = ball p ρ \ Z`, where `Z` is
exactly the zero set of `Im ∘ h` in the ball and `h` is continuous and open on the ball.  If the two
horizontal points `p ± δ₀` lie in different components of `U` (`hsep`) and every point of `U` can be
joined inside `U` to one of them (`hcover`), then for every `0 < δ < δ₀` the values of `Im ∘ h` at
`p + δ` and `p - δ` have opposite signs. -/
theorem sign_flip_of_two_components_horiz {p : ℂ} {ρ δ₀ : ℝ} (hρ : 0 < ρ) (hδ₀ : 0 < δ₀)
    (hδ₀ρ : δ₀ < ρ)
    {Z : Set ℂ} (hpZ : p ∈ Z) (hZsub : Z ⊆ Metric.ball p ρ)
    {h : ℂ → ℂ} (hcont : ContinuousOn h (Metric.ball p ρ))
    (hopen : ∀ s : Set ℂ, IsOpen s → s ⊆ Metric.ball p ρ → IsOpen (h '' s))
    (hZero : ∀ w ∈ Metric.ball p ρ, (h w).im = 0 ↔ w ∈ Z)
    (hvray : ∀ t : ℝ, 0 < t → t ≤ δ₀ → p + t ∉ Z ∧ p - t ∉ Z)
    (hcover : ∀ w ∈ Metric.ball p ρ \ Z,
        JoinedIn (Metric.ball p ρ \ Z) w (p + δ₀) ∨
        JoinedIn (Metric.ball p ρ \ Z) w (p - δ₀))
    (hsep : ¬ JoinedIn (Metric.ball p ρ \ Z) (p + δ₀) (p - δ₀)) :
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      (h (p + δ)).im * (h (p - δ)).im < 0 := by
  intro δ hδ hδδ₀
  have hpball : p ∈ Metric.ball p ρ := hZsub hpZ
  -- points of the two rays lie in `ball p ρ \ Z`
  have hmem : ∀ t : ℝ, 0 < t → t ≤ δ₀ →
      (p + (t : ℂ) ∈ Metric.ball p ρ ∧ p + (t : ℂ) ∉ Z) ∧
      (p - (t : ℂ) ∈ Metric.ball p ρ ∧ p - (t : ℂ) ∉ Z) := by
    intro t ht htδ
    obtain ⟨ha, hb⟩ := hvray t ht htδ
    refine ⟨⟨?_, ha⟩, ⟨?_, hb⟩⟩
    · rw [Metric.mem_ball, dist_add_real, abs_of_pos ht]; exact lt_of_le_of_lt htδ hδ₀ρ
    · rw [Metric.mem_ball, dist_sub_real, abs_of_pos ht]; exact lt_of_le_of_lt htδ hδ₀ρ
  have hnonzero : ∀ t : ℝ, 0 < t → t ≤ δ₀ →
      (h (p + (t : ℂ))).im ≠ 0 ∧ (h (p - (t : ℂ))).im ≠ 0 := by
    intro t ht htδ
    obtain ⟨⟨hba, hza⟩, ⟨hbb, hzb⟩⟩ := hmem t ht htδ
    exact ⟨fun h0 => hza ((hZero _ hba).mp h0), fun h0 => hzb ((hZero _ hbb).mp h0)⟩
  set A : ℝ := (h (p + (δ₀ : ℂ))).im with hA
  set B : ℝ := (h (p - (δ₀ : ℂ))).im with hB
  have hAne : A ≠ 0 := by rw [hA]; exact (hnonzero δ₀ hδ₀ le_rfl).1
  have hBne : B ≠ 0 := by rw [hB]; exact (hnonzero δ₀ hδ₀ le_rfl).2
  -- the sign along each ray is constant
  have hray : ∀ t : ℝ, 0 < t → t ≤ δ₀ →
      (0 < (h (p + (t : ℂ))).im ↔ 0 < A) ∧
      (0 < (h (p - (t : ℂ))).im ↔ 0 < B) := by
    intro t ht htδ
    have hmaps : Set.MapsTo (fun s : ℝ => p + (s : ℂ)) (Set.Icc t δ₀)
        (Metric.ball p ρ) := by
      intro s hs
      have h1 : 0 < s := lt_of_lt_of_le ht hs.1
      rw [Metric.mem_ball, dist_add_real, abs_of_pos h1]
      exact lt_of_le_of_lt hs.2 hδ₀ρ
    have hinner : ContinuousOn (fun s : ℝ => p + (s : ℂ)) (Set.Icc t δ₀) := by fun_prop
    have hc : ContinuousOn (fun s : ℝ => h (p + (s : ℂ))) (Set.Icc t δ₀) :=
      hcont.comp hinner hmaps
    have hci : ContinuousOn (fun s : ℝ => (h (p + (s : ℂ))).im) (Set.Icc t δ₀) :=
      Complex.continuous_im.comp_continuousOn hc
    have hneI : ∀ s ∈ Set.Icc t δ₀, (h (p + (s : ℂ))).im ≠ 0 :=
      fun s hs => (hnonzero s (lt_of_lt_of_le ht hs.1) hs.2).1
    have h1 := sign_iff_of_isPreconnected (isPreconnected_Icc (a := t) (b := δ₀)) hci hneI
        (Set.left_mem_Icc.mpr htδ) (Set.right_mem_Icc.mpr htδ)
    have hmapsm : Set.MapsTo (fun s : ℝ => p - (s : ℂ)) (Set.Icc t δ₀)
        (Metric.ball p ρ) := by
      intro s hs
      have h1 : 0 < s := lt_of_lt_of_le ht hs.1
      rw [Metric.mem_ball, dist_sub_real, abs_of_pos h1]
      exact lt_of_le_of_lt hs.2 hδ₀ρ
    have hinnerm : ContinuousOn (fun s : ℝ => p - (s : ℂ)) (Set.Icc t δ₀) := by fun_prop
    have hcm : ContinuousOn (fun s : ℝ => h (p - (s : ℂ))) (Set.Icc t δ₀) :=
      hcont.comp hinnerm hmapsm
    have hcim : ContinuousOn (fun s : ℝ => (h (p - (s : ℂ))).im) (Set.Icc t δ₀) :=
      Complex.continuous_im.comp_continuousOn hcm
    have hneIm : ∀ s ∈ Set.Icc t δ₀, (h (p - (s : ℂ))).im ≠ 0 :=
      fun s hs => (hnonzero s (lt_of_lt_of_le ht hs.1) hs.2).2
    have h2 := sign_iff_of_isPreconnected (isPreconnected_Icc (a := t) (b := δ₀)) hcim hneIm
        (Set.left_mem_Icc.mpr htδ) (Set.right_mem_Icc.mpr htδ)
    exact ⟨by rw [hA]; exact h1, by rw [hB]; exact h2⟩
  -- the zero-free sign function on `U`
  have hgz : ContinuousOn (fun z : ℂ => (h z).im) (Metric.ball p ρ \ Z) :=
    Complex.continuous_im.comp_continuousOn (hcont.mono Set.sdiff_subset)
  have hneZ : ∀ z ∈ Metric.ball p ρ \ Z, (h z).im ≠ 0 :=
    fun z hz h0 => hz.2 ((hZero z hz.1).mp h0)
  -- openness of `h` at `h p`
  have hopenBall : IsOpen (h '' Metric.ball p ρ) := hopen _ Metric.isOpen_ball (Subset.refl _)
  have hmem0 : h p ∈ h '' Metric.ball p ρ := ⟨p, hpball, rfl⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopenBall (h p) hmem0
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  -- the two endpoints cannot have the same sign
  have hnotPos : ¬ (0 < A ∧ 0 < B) := by
    rintro ⟨hAp, hBp⟩
    have hpos : ∀ w ∈ Metric.ball p ρ \ Z, 0 < (h w).im := by
      intro w hw
      rcases hcover w hw with hj | hj
      · exact (sign_iff_of_joinedIn hgz hneZ hj).mpr (hA ▸ hAp)
      · exact (sign_iff_of_joinedIn hgz hneZ hj).mpr (hB ▸ hBp)
    set q : ℂ := h p - ((ε / 2 : ℝ) : ℂ) * Complex.I with hq
    have hqmem : q ∈ Metric.ball (h p) ε := by
      rw [hq, Metric.mem_ball, dist_sub_I, abs_of_pos hε2]; linarith
    obtain ⟨w, hwball, hwq⟩ := hεsub hqmem
    have hqim : q.im < 0 := by
      have hpim : (h p).im = 0 := (hZero p hpball).mpr hpZ
      have : q.im = (h p).im - ε / 2 := by simp [hq, Complex.sub_im, Complex.mul_im]
      rw [this, hpim]; linarith
    have hwim : (h w).im < 0 := by rw [hwq]; exact hqim
    have hwU : w ∈ Metric.ball p ρ \ Z := by
      refine ⟨hwball, fun hwZ => ?_⟩
      rw [(hZero w hwball).mpr hwZ] at hwim
      exact absurd hwim (lt_irrefl 0)
    exact absurd (hpos w hwU) (not_lt.mpr (le_of_lt hwim))
  have hnotNeg : ¬ (A < 0 ∧ B < 0) := by
    rintro ⟨hAn, hBn⟩
    have hneg : ∀ w ∈ Metric.ball p ρ \ Z, (h w).im < 0 := by
      intro w hw
      have hne0 : (h w).im ≠ 0 := hneZ w hw
      rcases hcover w hw with hj | hj
      · have hiff := sign_iff_of_joinedIn hgz hneZ hj
        rcases lt_trichotomy (h w).im 0 with h3 | h3 | h3
        · exact h3
        · exact absurd h3 hne0
        · exact absurd (hiff.mp h3) (not_lt.mpr (le_of_lt (hA ▸ hAn)))
      · have hiff := sign_iff_of_joinedIn hgz hneZ hj
        rcases lt_trichotomy (h w).im 0 with h3 | h3 | h3
        · exact h3
        · exact absurd h3 hne0
        · exact absurd (hiff.mp h3) (not_lt.mpr (le_of_lt (hB ▸ hBn)))
    set q : ℂ := h p + ((ε / 2 : ℝ) : ℂ) * Complex.I with hq
    have hqmem : q ∈ Metric.ball (h p) ε := by
      rw [hq, Metric.mem_ball, dist_add_I, abs_of_pos hε2]; linarith
    obtain ⟨w, hwball, hwq⟩ := hεsub hqmem
    have hqim : 0 < q.im := by
      have hpim : (h p).im = 0 := (hZero p hpball).mpr hpZ
      have : q.im = (h p).im + ε / 2 := by simp [hq, Complex.add_im, Complex.mul_im]
      rw [this, hpim]; linarith
    have hwim : 0 < (h w).im := by rw [hwq]; exact hqim
    have hwU : w ∈ Metric.ball p ρ \ Z := by
      refine ⟨hwball, fun hwZ => ?_⟩
      rw [(hZero w hwball).mpr hwZ] at hwim
      exact absurd hwim (lt_irrefl 0)
    exact absurd (hneg w hwU) (not_lt.mpr (le_of_lt hwim))
  -- transfer the signs to `p ± δ` and conclude
  have hδmem := hnonzero δ hδ (le_of_lt hδδ₀)
  have hsgn := hray δ hδ (le_of_lt hδδ₀)
  rcases lt_or_gt_of_ne hAne with hAlt | hAgt
  · have hBgt : 0 < B := by
      rcases lt_trichotomy B 0 with h | h | h
      · exact absurd ⟨hAlt, h⟩ hnotNeg
      · exact absurd h hBne
      · exact h
    have h1 : (h (p + (δ : ℂ))).im < 0 := by
      rcases lt_trichotomy (h (p + (δ : ℂ))).im 0 with h | h | h
      · exact h
      · exact absurd h hδmem.1
      · exact absurd (hsgn.1.mp h) (not_lt.mpr (le_of_lt hAlt))
    exact mul_neg_of_neg_of_pos h1 (hsgn.2.mpr hBgt)
  · have hBlt : B < 0 := by
      rcases lt_trichotomy B 0 with h | h | h
      · exact h
      · exact absurd h hBne
      · exact absurd ⟨hAgt, h⟩ hnotPos
    have h2 : (h (p - (δ : ℂ))).im < 0 := by
      rcases lt_trichotomy (h (p - (δ : ℂ))).im 0 with h | h | h
      · exact h
      · exact absurd h hδmem.2
      · exact absurd (hsgn.2.mp h) (not_lt.mpr (le_of_lt hBlt))
    exact mul_neg_of_pos_of_neg (hsgn.1.mpr hAgt) h2

end Work.ELRig
