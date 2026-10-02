import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Sign flip across two components of `ball p ρ \ Z`

Let `U = Metric.ball p ρ \ Z`, let `h : ℂ → ℂ` be continuous on the ball with `h` open on the
ball, and suppose the zero set of `im ∘ h` in the ball is exactly `Z`:

`hZero : (h w).im = 0 ↔ w ∈ Z` for `w` in the ball.

Assume moreover that every point of `U` can be joined inside `U` to one of the two points
`p ± δ₀ i` (`hcover`), and that these points lie in different components of `U` (`hsep`).
Then for every `δ ∈ (0, δ₀)` the two points `p + δ i` and `p - δ i` are mapped by `h` to
opposite sides of the real axis.

The proof shows that the sign of `(h w).im` is constant along paths in `U` (continuity plus
`hZero`), so it is constant on each component of `U`; the two points `p ± δ i` joined to
`p ± δ₀ i` accordingly.  If both points `p ± δ₀ i` had the same sign, then the whole of `U`
would be mapped into one open half plane; but `p ∈ Z` gives `(h p).im = 0`, `h p` is an interior
point of the open set `h '' ball p ρ`, and a neighbourhood of `h p` meets the other half plane —
a contradiction.
-/

set_option linter.unusedVariables false

open scoped Topology
open Set

namespace Work.ELRig

/-- On a preconnected set, a continuous real function with no zeros has constant sign,
in the form: the two values have the same sign. -/
lemma sign_iff_of_isPreconnected {Y : Type*} [TopologicalSpace Y] {s : Set Y}
    (hs : IsPreconnected s) {g : Y → ℝ} (hg : ContinuousOn g s)
    (hne : ∀ x ∈ s, g x ≠ 0) {x y : Y} (hx : x ∈ s) (hy : y ∈ s) :
    0 < g x ↔ 0 < g y := by
  constructor
  · intro hx0
    by_contra hy0
    have hy' : g y < 0 := lt_of_le_of_ne (le_of_not_gt hy0) (hne y hy)
    have hmem : (0:ℝ) ∈ Set.Icc (g y) (g x) := ⟨le_of_lt hy', le_of_lt hx0⟩
    obtain ⟨z, hzs, hz⟩ := (hs.intermediate_value hy hx hg) hmem
    exact hne z hzs hz
  · intro hy0
    by_contra hx0
    have hx' : g x < 0 := lt_of_le_of_ne (le_of_not_gt hx0) (hne x hx)
    have hmem : (0:ℝ) ∈ Set.Icc (g x) (g y) := ⟨le_of_lt hx', le_of_lt hy0⟩
    obtain ⟨z, hzs, hz⟩ := (hs.intermediate_value hx hy hg) hmem
    exact hne z hzs hz

/-- The sign of a continuous zero-free real function is constant along a path staying in the
set. -/
lemma sign_iff_of_joinedIn {U : Set ℂ} {g : ℂ → ℝ} (hg : ContinuousOn g U)
    (hne : ∀ x ∈ U, g x ≠ 0) {x y : ℂ} (hxy : JoinedIn U x y) :
    0 < g x ↔ 0 < g y := by
  obtain ⟨γ, hγ⟩ := hxy
  have hcont : Continuous (g ∘ γ) := hg.comp_continuous γ.continuous hγ
  have hne' : ∀ t : unitInterval, (g ∘ γ) t ≠ 0 := fun t => hne (γ t) (hγ t)
  have h := sign_iff_of_isPreconnected
      (isPreconnected_univ : IsPreconnected (Set.univ : Set unitInterval))
      hcont.continuousOn (fun t _ => hne' t)
      (Set.mem_univ (0 : unitInterval)) (Set.mem_univ (1 : unitInterval))
  simp only [Function.comp_apply] at h
  rw [Path.source γ, Path.target γ] at h
  exact h

/-- `dist (p + t·i) p = |t|`. -/
lemma dist_add_I (p : ℂ) (t : ℝ) : dist (p + ((t : ℝ) : ℂ) * Complex.I) p = |t| := by
  rw [dist_eq_norm]
  have h : p + ((t : ℝ) : ℂ) * Complex.I - p = ((t : ℝ) : ℂ) * Complex.I := by ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- `dist (p - t·i) p = |t|`. -/
lemma dist_sub_I (p : ℂ) (t : ℝ) : dist (p - ((t : ℝ) : ℂ) * Complex.I) p = |t| := by
  rw [dist_eq_norm]
  have h : p - ((t : ℝ) : ℂ) * Complex.I - p = -(((t : ℝ) : ℂ) * Complex.I) := by ring
  rw [h, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem sign_flip_of_two_components {p : ℂ} {ρ δ₀ : ℝ} (hρ : 0 < ρ) (hδ₀ : 0 < δ₀) (hδ₀ρ : δ₀ < ρ)
    {Z : Set ℂ} (hpZ : p ∈ Z) (hZsub : Z ⊆ Metric.ball p ρ)
    {h : ℂ → ℂ} (hcont : ContinuousOn h (Metric.ball p ρ))
    (hopen : ∀ s : Set ℂ, IsOpen s → s ⊆ Metric.ball p ρ → IsOpen (h '' s))
    (hZero : ∀ w ∈ Metric.ball p ρ, (h w).im = 0 ↔ w ∈ Z)
    (hvray : ∀ t : ℝ, 0 < t → t ≤ δ₀ → p + t * Complex.I ∉ Z ∧ p - t * Complex.I ∉ Z)
    (hcover : ∀ w ∈ Metric.ball p ρ \ Z,
        JoinedIn (Metric.ball p ρ \ Z) w (p + δ₀ * Complex.I) ∨
        JoinedIn (Metric.ball p ρ \ Z) w (p - δ₀ * Complex.I))
    (hsep : ¬ JoinedIn (Metric.ball p ρ \ Z) (p + δ₀ * Complex.I) (p - δ₀ * Complex.I)) :
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      (h (p + δ * Complex.I)).im * (h (p - δ * Complex.I)).im < 0 := by
  intro δ hδ hδδ₀
  have hpball : p ∈ Metric.ball p ρ := hZsub hpZ
  -- points of the two rays lie in `ball p ρ \ Z`
  have hmem : ∀ t : ℝ, 0 < t → t ≤ δ₀ →
      (p + t * Complex.I ∈ Metric.ball p ρ ∧ p + t * Complex.I ∉ Z) ∧
      (p - t * Complex.I ∈ Metric.ball p ρ ∧ p - t * Complex.I ∉ Z) := by
    intro t ht htδ
    obtain ⟨ha, hb⟩ := hvray t ht htδ
    refine ⟨⟨?_, ha⟩, ⟨?_, hb⟩⟩
    · rw [Metric.mem_ball, dist_add_I, abs_of_pos ht]; exact lt_of_le_of_lt htδ hδ₀ρ
    · rw [Metric.mem_ball, dist_sub_I, abs_of_pos ht]; exact lt_of_le_of_lt htδ hδ₀ρ
  have hnonzero : ∀ t : ℝ, 0 < t → t ≤ δ₀ →
      (h (p + t * Complex.I)).im ≠ 0 ∧ (h (p - t * Complex.I)).im ≠ 0 := by
    intro t ht htδ
    obtain ⟨⟨hba, hza⟩, ⟨hbb, hzb⟩⟩ := hmem t ht htδ
    exact ⟨fun h0 => hza ((hZero _ hba).mp h0), fun h0 => hzb ((hZero _ hbb).mp h0)⟩
  set A : ℝ := (h (p + δ₀ * Complex.I)).im with hA
  set B : ℝ := (h (p - δ₀ * Complex.I)).im with hB
  have hAne : A ≠ 0 := by rw [hA]; exact (hnonzero δ₀ hδ₀ le_rfl).1
  have hBne : B ≠ 0 := by rw [hB]; exact (hnonzero δ₀ hδ₀ le_rfl).2
  -- the sign along each ray is constant
  have hray : ∀ t : ℝ, 0 < t → t ≤ δ₀ →
      (0 < (h (p + t * Complex.I)).im ↔ 0 < A) ∧
      (0 < (h (p - t * Complex.I)).im ↔ 0 < B) := by
    intro t ht htδ
    have hmaps : Set.MapsTo (fun s : ℝ => p + s * Complex.I) (Set.Icc t δ₀)
        (Metric.ball p ρ) := by
      intro s hs
      have h1 : 0 < s := lt_of_lt_of_le ht hs.1
      rw [Metric.mem_ball, dist_add_I, abs_of_pos h1]
      exact lt_of_le_of_lt hs.2 hδ₀ρ
    have hinner : ContinuousOn (fun s : ℝ => p + s * Complex.I) (Set.Icc t δ₀) := by fun_prop
    have hc : ContinuousOn (fun s : ℝ => h (p + s * Complex.I)) (Set.Icc t δ₀) :=
      hcont.comp hinner hmaps
    have hci : ContinuousOn (fun s : ℝ => (h (p + s * Complex.I)).im) (Set.Icc t δ₀) :=
      Complex.continuous_im.comp_continuousOn hc
    have hneI : ∀ s ∈ Set.Icc t δ₀, (h (p + s * Complex.I)).im ≠ 0 :=
      fun s hs => (hnonzero s (lt_of_lt_of_le ht hs.1) hs.2).1
    have h1 := sign_iff_of_isPreconnected (isPreconnected_Icc (a := t) (b := δ₀)) hci hneI
        (Set.left_mem_Icc.mpr htδ) (Set.right_mem_Icc.mpr htδ)
    have hmapsm : Set.MapsTo (fun s : ℝ => p - s * Complex.I) (Set.Icc t δ₀)
        (Metric.ball p ρ) := by
      intro s hs
      have h1 : 0 < s := lt_of_lt_of_le ht hs.1
      rw [Metric.mem_ball, dist_sub_I, abs_of_pos h1]
      exact lt_of_le_of_lt hs.2 hδ₀ρ
    have hinnerm : ContinuousOn (fun s : ℝ => p - s * Complex.I) (Set.Icc t δ₀) := by fun_prop
    have hcm : ContinuousOn (fun s : ℝ => h (p - s * Complex.I)) (Set.Icc t δ₀) :=
      hcont.comp hinnerm hmapsm
    have hcim : ContinuousOn (fun s : ℝ => (h (p - s * Complex.I)).im) (Set.Icc t δ₀) :=
      Complex.continuous_im.comp_continuousOn hcm
    have hneIm : ∀ s ∈ Set.Icc t δ₀, (h (p - s * Complex.I)).im ≠ 0 :=
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
  -- transfer the signs to `p ± δ i` and conclude
  have hδmem := hnonzero δ hδ (le_of_lt hδδ₀)
  have hsgn := hray δ hδ (le_of_lt hδδ₀)
  rcases lt_or_gt_of_ne hAne with hAlt | hAgt
  · have hBgt : 0 < B := by
      rcases lt_trichotomy B 0 with h | h | h
      · exact absurd ⟨hAlt, h⟩ hnotNeg
      · exact absurd h hBne
      · exact h
    have h1 : (h (p + δ * Complex.I)).im < 0 := by
      rcases lt_trichotomy (h (p + δ * Complex.I)).im 0 with h | h | h
      · exact h
      · exact absurd h hδmem.1
      · exact absurd (hsgn.1.mp h) (not_lt.mpr (le_of_lt hAlt))
    exact mul_neg_of_neg_of_pos h1 (hsgn.2.mpr hBgt)
  · have hBlt : B < 0 := by
      rcases lt_trichotomy B 0 with h | h | h
      · exact h
      · exact absurd h hBne
      · exact absurd ⟨hAgt, h⟩ hnotPos
    have h2 : (h (p - δ * Complex.I)).im < 0 := by
      rcases lt_trichotomy (h (p - δ * Complex.I)).im 0 with h | h | h
      · exact h
      · exact absurd h hδmem.2
      · exact absurd (hsgn.2.mp h) (not_lt.mpr (le_of_lt hBlt))
    exact mul_neg_of_pos_of_neg (hsgn.1.mpr hAgt) h2

end Work.ELRig
