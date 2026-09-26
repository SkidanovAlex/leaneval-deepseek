import Mathlib

namespace Work.Drive.Final

open Set

/-!
# Decomposition of the two-cone region `{0 < s₁ (Tξ).₁² + s₂ (Tξ).₂²}`

For `s₁, s₂ ∈ {1, -1}` and an injective linear `T : ℝ × ℝ → ℝ × ℝ`, the intersection of the
square `(-δ, δ)²` with the region where `s₁ (T ξ).₁² + s₂ (T ξ).₂² > 0` is the union of two sets,
each of which is either empty or path connected.

The four cases are:

* `s₁ = s₂ = 1`: the region is the punctured square `Q ∖ {0}`, split into the two "closed
  half-planes minus the origin along one ray" `Q ∩ H⁺` and `Q ∩ (-H⁺)`;
* `s₁ = 1, s₂ = -1`: the region is `Q ∩ {x² > y²}`, the union of the two (convex) cones
  `{|y| < x}` and `{|y| < -x}` — preimages of convex cones under the linear map `T`;
* `s₁ = -1, s₂ = 1`: as above with the two coordinates exchanged;
* `s₁ = s₂ = -1`: the region is empty.

Every set occurring below is convex, hence (when nonempty) path connected.
-/

/-- A convex set is either empty or path connected. -/
private lemma ipcOrEmpty {S : Set (ℝ × ℝ)} (h : Convex ℝ S) : S = ∅ ∨ IsPathConnected S := by
  rcases Set.eq_empty_or_nonempty S with hS | hS
  · exact Or.inl hS
  · exact Or.inr (h.isPathConnected hS)

/-- The open right cone `{|y| < x}` is convex. -/
private lemma convex_coneRight : Convex ℝ {z : ℝ × ℝ | |z.2| < z.1} := by
  have h : {z : ℝ × ℝ | |z.2| < z.1}
      = (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ) ⁻¹' Set.Ioi (0:ℝ) ∩
        (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ) ⁻¹' Set.Ioi (0:ℝ) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    constructor
    · intro hz
      rw [abs_lt] at hz
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    · rintro ⟨h1, h2⟩
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
  rw [h]
  exact ((convex_Ioi (0:ℝ)).linear_preimage _).inter ((convex_Ioi (0:ℝ)).linear_preimage _)

/-- The open left cone `{|y| < -x}` is convex. -/
private lemma convex_coneLeft : Convex ℝ {z : ℝ × ℝ | |z.2| < -z.1} := by
  have h : {z : ℝ × ℝ | |z.2| < -z.1} = -{z : ℝ × ℝ | |z.2| < z.1} := by
    ext z; simp [Prod.fst_neg, Prod.snd_neg]
  rw [h]; exact convex_coneRight.neg

/-- The open upper cone `{|x| < y}` is convex. -/
private lemma convex_coneUp : Convex ℝ {z : ℝ × ℝ | |z.1| < z.2} := by
  have h : {z : ℝ × ℝ | |z.1| < z.2}
      = (LinearMap.snd ℝ ℝ ℝ - LinearMap.fst ℝ ℝ ℝ) ⁻¹' Set.Ioi (0:ℝ) ∩
        (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ) ⁻¹' Set.Ioi (0:ℝ) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.fst_apply, LinearMap.snd_apply]
    constructor
    · intro hz
      rw [abs_lt] at hz
      exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    · rintro ⟨h1, h2⟩
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
  rw [h]
  exact ((convex_Ioi (0:ℝ)).linear_preimage _).inter ((convex_Ioi (0:ℝ)).linear_preimage _)

/-- The open lower cone `{|x| < -y}` is convex. -/
private lemma convex_coneDown : Convex ℝ {z : ℝ × ℝ | |z.1| < -z.2} := by
  have h : {z : ℝ × ℝ | |z.1| < -z.2} = -{z : ℝ × ℝ | |z.1| < z.2} := by
    ext z; simp [Prod.fst_neg, Prod.snd_neg]
  rw [h]; exact convex_coneUp.neg

/-- `H⁺ = {p : p.₁ > 0 ∨ (p.₁ = 0 ∧ p.₂ > 0)}`, the closed right half-plane minus the
non-positive part of the `y`-axis, is convex. -/
private lemma convex_faceOrigin : Convex ℝ {p : ℝ × ℝ | 0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2)} := by
  rw [convex_iff_forall_pos]
  rintro x hx y hy a b ha hb hab
  have hx1' : 0 ≤ x.1 := by rcases hx with h | ⟨h, _⟩ <;> linarith
  have hy1' : 0 ≤ y.1 := by rcases hy with h | ⟨h, _⟩ <;> linarith
  have hx2' : x.1 = 0 → 0 < x.2 := by
    intro h0
    rcases hx with h | ⟨_, h2⟩
    · rw [h0] at h; exact absurd h (lt_irrefl 0)
    · exact h2
  have hy2' : y.1 = 0 → 0 < y.2 := by
    intro h0
    rcases hy with h | ⟨_, h2⟩
    · rw [h0] at h; exact absurd h (lt_irrefl 0)
    · exact h2
  have hax0 : 0 ≤ a * x.1 := mul_nonneg (le_of_lt ha) hx1'
  have hby0 : 0 ≤ b * y.1 := mul_nonneg (le_of_lt hb) hy1'
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  rcases lt_or_eq_of_le (show 0 ≤ a * x.1 + b * y.1 by linarith) with h | h
  · exact Or.inl h
  · right
    refine ⟨h.symm, ?_⟩
    have hax : a * x.1 = 0 := by nlinarith
    have hby : b * y.1 = 0 := by nlinarith
    have hx0 : x.1 = 0 := by
      rcases mul_eq_zero.mp hax with h' | h'
      · exact absurd h' (ne_of_gt ha)
      · exact h'
    have hy0 : y.1 = 0 := by
      rcases mul_eq_zero.mp hby with h' | h'
      · exact absurd h' (ne_of_gt hb)
      · exact h'
    linarith [mul_pos ha (hx2' hx0), mul_pos hb (hy2' hy0)]

/-- `H⁺ ∪ -H⁺ = {0}ᶜ`. -/
private lemma union_faceOrigin_compl :
    {p : ℝ × ℝ | 0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2)} ∪
      -({p : ℝ × ℝ | 0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2)}) = {0}ᶜ := by
  ext p
  constructor
  · rintro (h | h)
    · intro hp
      rw [hp] at h
      simp only [Set.mem_setOf_eq, Prod.fst_zero, Prod.snd_zero, lt_self_iff_false,
        and_false, or_false] at h
    · intro hp
      rw [hp] at h
      simp only [Set.mem_neg, Set.mem_setOf_eq, neg_zero, Prod.fst_zero, Prod.snd_zero,
        lt_self_iff_false, and_false, or_false] at h
  · intro hp
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hp
    rcases lt_trichotomy p.1 0 with h | h | h
    · right; rw [Set.mem_neg]
      left; simp only [Prod.fst_neg]; linarith
    · have hp2 : p.2 ≠ 0 := by intro h2; exact hp (Prod.ext h h2)
      rcases lt_trichotomy p.2 0 with h2 | h2 | h2
      · right; rw [Set.mem_neg]
        right; simp only [Prod.fst_neg, Prod.snd_neg]; exact ⟨by linarith, by linarith⟩
      · exact absurd h2 hp2
      · left; exact Or.inr ⟨h, h2⟩
    · left; exact Or.inl h

/-- For injective linear `T` the region `{0 < (Tξ).₁² + (Tξ).₂²}` is the complement of the
origin. -/
private lemma sq_add_sq_pos_compl (T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (hTinj : Function.Injective T) :
    {ξ : ℝ × ℝ | 0 < (T ξ).1 ^ 2 + (T ξ).2 ^ 2} = {0}ᶜ := by
  ext ξ
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro h h0
    rw [h0, map_zero] at h
    norm_num at h
  · intro hξ
    have hT : T ξ ≠ 0 := fun h => hξ (hTinj (by rw [h, map_zero]))
    rcases eq_or_ne (T ξ).1 0 with h1 | h1
    · have h2 : (T ξ).2 ≠ 0 := by intro h2; exact hT (Prod.ext h1 h2)
      nlinarith [sq_pos_of_ne_zero h2, sq_nonneg (T ξ).1]
    · nlinarith [sq_pos_of_ne_zero h1, sq_nonneg (T ξ).2]

theorem gateNoFace (δ : ℝ) (hδ : 0 < δ)
    (T : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (hTinj : Function.Injective T)
    (s₁ s₂ : ℝ) (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1) :
    ∃ S₁ S₂ : Set (ℝ × ℝ), (S₁ = ∅ ∨ IsPathConnected S₁) ∧ (S₂ = ∅ ∨ IsPathConnected S₂) ∧
      S₁ ∪ S₂ = (Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ) ∩
        {ξ | 0 < s₁ * (T ξ).1 ^ 2 + s₂ * (T ξ).2 ^ 2} := by
  set Q : Set (ℝ × ℝ) := Set.Ioo (-δ) δ ×ˢ Set.Ioo (-δ) δ with hQdef
  have hQconv : Convex ℝ Q := by
    rw [hQdef]; exact (convex_Ioo (-δ) δ).prod (convex_Ioo (-δ) δ)
  rcases hs₁ with h1 | h1 <;> rcases hs₂ with h2 | h2
  · -- s₁ = 1, s₂ = 1 : the punctured square
    rw [h1, h2]
    refine ⟨Q ∩ {p : ℝ × ℝ | 0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2)},
      Q ∩ -{p : ℝ × ℝ | 0 < p.1 ∨ (p.1 = 0 ∧ 0 < p.2)}, ?_, ?_, ?_⟩
    · exact ipcOrEmpty (hQconv.inter convex_faceOrigin)
    · exact ipcOrEmpty (hQconv.inter convex_faceOrigin.neg)
    · have hs : {ξ : ℝ × ℝ | 0 < 1 * (T ξ).1 ^ 2 + 1 * (T ξ).2 ^ 2} = {0}ᶜ := by
        have h' := sq_add_sq_pos_compl T hTinj
        have h'' : {ξ : ℝ × ℝ | 0 < 1 * (T ξ).1 ^ 2 + 1 * (T ξ).2 ^ 2}
            = {ξ : ℝ × ℝ | 0 < (T ξ).1 ^ 2 + (T ξ).2 ^ 2} := by
          ext ξ; simp only [Set.mem_setOf_eq, one_mul]
        rw [h'', h']
      rw [hs, ← union_faceOrigin_compl, Set.inter_union_distrib_left]
  · -- s₁ = 1, s₂ = -1 : the two cones {|y| < x} and {|y| < -x}
    rw [h1, h2]
    have hc1 : Convex ℝ {ξ : ℝ × ℝ | |(T ξ).2| < (T ξ).1} := by
      have h : {ξ : ℝ × ℝ | |(T ξ).2| < (T ξ).1}
          = T.toLinearMap ⁻¹' {z : ℝ × ℝ | |z.2| < z.1} := rfl
      rw [h]; exact convex_coneRight.linear_preimage T.toLinearMap
    have hc2 : Convex ℝ {ξ : ℝ × ℝ | |(T ξ).2| < -(T ξ).1} := by
      have h : {ξ : ℝ × ℝ | |(T ξ).2| < -(T ξ).1}
          = T.toLinearMap ⁻¹' {z : ℝ × ℝ | |z.2| < -z.1} := rfl
      rw [h]; exact convex_coneLeft.linear_preimage T.toLinearMap
    refine ⟨Q ∩ {ξ : ℝ × ℝ | |(T ξ).2| < (T ξ).1},
            Q ∩ {ξ : ℝ × ℝ | |(T ξ).2| < -(T ξ).1}, ?_, ?_, ?_⟩
    · exact ipcOrEmpty (hQconv.inter hc1)
    · exact ipcOrEmpty (hQconv.inter hc2)
    · have hs : {ξ : ℝ × ℝ | |(T ξ).2| < (T ξ).1} ∪ {ξ : ℝ × ℝ | |(T ξ).2| < -(T ξ).1}
          = {ξ : ℝ × ℝ | 0 < 1 * (T ξ).1 ^ 2 + -1 * (T ξ).2 ^ 2} := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_union]
        rw [show 1 * (T ξ).1 ^ 2 + -1 * (T ξ).2 ^ 2 = (T ξ).1 ^ 2 - (T ξ).2 ^ 2 from by ring]
        simp only [sub_pos, sq_lt_sq, abs_eq_max_neg, lt_max_iff]
      rw [← Set.inter_union_distrib_left, hs]
  · -- s₁ = -1, s₂ = 1 : the two cones {|x| < y} and {|x| < -y}
    rw [h1, h2]
    have hc1 : Convex ℝ {ξ : ℝ × ℝ | |(T ξ).1| < (T ξ).2} := by
      have h : {ξ : ℝ × ℝ | |(T ξ).1| < (T ξ).2}
          = T.toLinearMap ⁻¹' {z : ℝ × ℝ | |z.1| < z.2} := rfl
      rw [h]; exact convex_coneUp.linear_preimage T.toLinearMap
    have hc2 : Convex ℝ {ξ : ℝ × ℝ | |(T ξ).1| < -(T ξ).2} := by
      have h : {ξ : ℝ × ℝ | |(T ξ).1| < -(T ξ).2}
          = T.toLinearMap ⁻¹' {z : ℝ × ℝ | |z.1| < -z.2} := rfl
      rw [h]; exact convex_coneDown.linear_preimage T.toLinearMap
    refine ⟨Q ∩ {ξ : ℝ × ℝ | |(T ξ).1| < (T ξ).2},
            Q ∩ {ξ : ℝ × ℝ | |(T ξ).1| < -(T ξ).2}, ?_, ?_, ?_⟩
    · exact ipcOrEmpty (hQconv.inter hc1)
    · exact ipcOrEmpty (hQconv.inter hc2)
    · have hs : {ξ : ℝ × ℝ | |(T ξ).1| < (T ξ).2} ∪ {ξ : ℝ × ℝ | |(T ξ).1| < -(T ξ).2}
          = {ξ : ℝ × ℝ | 0 < -1 * (T ξ).1 ^ 2 + 1 * (T ξ).2 ^ 2} := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_union]
        rw [show -1 * (T ξ).1 ^ 2 + 1 * (T ξ).2 ^ 2 = (T ξ).2 ^ 2 - (T ξ).1 ^ 2 from by ring]
        simp only [sub_pos, sq_lt_sq, abs_eq_max_neg, lt_max_iff]
      rw [← Set.inter_union_distrib_left, hs]
  · -- s₁ = -1, s₂ = -1 : empty
    rw [h1, h2]
    refine ⟨∅, ∅, Or.inl rfl, Or.inl rfl, ?_⟩
    have hs : {ξ : ℝ × ℝ | 0 < -1 * (T ξ).1 ^ 2 + -1 * (T ξ).2 ^ 2} = ∅ := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      nlinarith [sq_nonneg (T ξ).1, sq_nonneg (T ξ).2]
    rw [hs]
    simp

end Work.Drive.Final
