import Submission.Work.FlatFrontierFinite

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# T1-ii Layer 3, part A: separating a frontier chord from its complement

The frontier components of a flat component `C` are full-width chords
(Layer 1) and finitely many (Layer 2).  This file lays the geometric
groundwork for the region decomposition of `stripInterior` by those
chords:

* **half-strips**: each full chord `Γ = stripChord α β` splits
  `stripInterior` into two open half-strips (`aboveChord α β`,
  `belowChord α β`); they are open, disjoint, cover
  `stripInterior ∖ Γ`, and each is connected;
* **chord topology**: a chord is connected;
* **no crossing / ordering**: two chords with EMPTY intersection never
  cross inside the strip and, when ordered at the centre line, are
  pointwise ordered on all of `(0,1)`;
* **frontier components**: distinct frontier components of `C` are
  disjoint (components of a space); **`frComponent_separated`** — two
  distinct frontier components, ordered by the heights at which they
  cross the centre line, lie wholly on opposite sides of one another:
  the lower component sits inside the half-strip below the upper chord
  and the upper component inside the half-strip above the lower chord.

Build: `lake build Submission.Work.FrontierSeparation` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The open half-strip of the unit strip strictly ABOVE the full chord
`stripChord α β`. -/
def aboveChord (α β : ℝ) : Set ℝ² :=
  {x | x ∈ stripInterior ∧ sideH₁ α β (x 0) < x 1}

/-- The open half-strip of the unit strip strictly BELOW the full chord
`stripChord α β`. -/
def belowChord (α β : ℝ) : Set ℝ² :=
  {x | x ∈ stripInterior ∧ x 1 < sideH₁ α β (x 0)}

/-- Membership above a chord. -/
lemma mem_aboveChord {α β : ℝ} {x : ℝ²} :
    x ∈ aboveChord α β ↔ x ∈ stripInterior ∧ sideH₁ α β (x 0) < x 1 := by rfl

/-- Membership below a chord. -/
lemma mem_belowChord {α β : ℝ} {x : ℝ²} :
    x ∈ belowChord α β ↔ x ∈ stripInterior ∧ x 1 < sideH₁ α β (x 0) := by rfl

/-- The half-strips lie in the open strip. -/
lemma aboveChord_subset_stripInterior (α β : ℝ) : aboveChord α β ⊆ stripInterior := by
  intro x hx
  exact (mem_aboveChord.mp hx).1

/-- The half-strips lie in the open strip. -/
lemma belowChord_subset_stripInterior (α β : ℝ) : belowChord α β ⊆ stripInterior := by
  intro x hx
  exact (mem_belowChord.mp hx).1

/-- `sideH₁` is continuous. -/
lemma continuous_sideH₁ (α β : ℝ) : Continuous (fun x : ℝ => sideH₁ α β x) := by
  dsimp [sideH₁]
  fun_prop

/-- `x ↦ sideH₁ α β (x 0)` is continuous on the plane. -/
lemma continuous_height (α β : ℝ) : Continuous (fun x : ℝ² => sideH₁ α β (x 0)) := by
  have hc : Continuous (fun x : ℝ² => x 0) := by fun_prop
  exact (continuous_sideH₁ α β).comp hc

/-- The coordinate functions are continuous. -/
lemma continuous_coord0 : Continuous (fun x : ℝ² => x 0) := by fun_prop
lemma continuous_coord1 : Continuous (fun x : ℝ² => x 1) := by fun_prop

/-- The half-strip above a chord is open. -/
lemma isOpen_aboveChord (α β : ℝ) : IsOpen (aboveChord α β) := by
  unfold aboveChord
  exact stripInterior_isOpen.inter (isOpen_lt (continuous_height α β) continuous_coord1)

/-- The half-strip below a chord is open. -/
lemma isOpen_belowChord (α β : ℝ) : IsOpen (belowChord α β) := by
  unfold belowChord
  exact stripInterior_isOpen.inter (isOpen_lt continuous_coord1 (continuous_height α β))

/-- A point cannot be both above and below the same chord. -/
lemma aboveChord_disjoint_belowChord (α β : ℝ) :
    Disjoint (aboveChord α β) (belowChord α β) := by
  rw [Set.disjoint_left]
  intro x hxAbove hxBelow
  rw [mem_aboveChord] at hxAbove
  rw [mem_belowChord] at hxBelow
  linarith

/-- A strip-interior point off a chord lies above or below it. -/
lemma mem_above_or_below_of_not_mem_chord {α β : ℝ} {x : ℝ²}
    (hxS : x ∈ stripInterior) (hxΓ : x ∉ stripChord α β) :
    x ∈ aboveChord α β ∨ x ∈ belowChord α β := by
  by_cases hlt : sideH₁ α β (x 0) < x 1
  · exact Or.inl ⟨hxS, hlt⟩
  · have hle : x 1 ≤ sideH₁ α β (x 0) := le_of_not_gt hlt
    by_cases hEq : x 1 = sideH₁ α β (x 0)
    · exfalso
      apply hxΓ
      rw [mem_stripChord]
      exact ⟨hxS, hEq⟩
    · exact Or.inr ⟨hxS, lt_of_le_of_ne hle hEq⟩

/-- Removing a chord leaves exactly the two half-strips:
`stripInterior ∖ stripChord α β = aboveChord α β ∪ belowChord α β`. -/
lemma stripInterior_diff_chord_eq_union (α β : ℝ) :
    stripInterior \ stripChord α β = aboveChord α β ∪ belowChord α β := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxS, hxΓ⟩
    exact mem_above_or_below_of_not_mem_chord (α := α) (β := β) hxS hxΓ
  · intro hx
    rcases hx with hxAB | hxAB
    · rw [mem_aboveChord] at hxAB
      exact ⟨hxAB.1, by
        intro hxΓ
        rw [mem_stripChord] at hxΓ
        linarith [hxAB.2, hxΓ.2]⟩
    · rw [mem_belowChord] at hxAB
      exact ⟨hxAB.1, by
        intro hxΓ
        rw [mem_stripChord] at hxΓ
        linarith⟩

/-- The chord parametrisation `t ↦ (t, sideH₁ α β t)` restricted to
`(0,1)` has image exactly `stripChord α β`. -/
lemma stripChord_eq_image (α β : ℝ) :
    stripChord α β = (fun t : ℝ => !₂[t, sideH₁ α β t]) '' Set.Ioo 0 1 := by
  ext x
  constructor
  · intro hx
    rw [mem_stripChord_coords] at hx
    rw [Set.mem_image]
    refine ⟨x 0, ⟨hx.1, hx.2.1⟩, ?_⟩
    ext i <;> fin_cases i <;> simp [hx.2.2]
  · intro hx
    rcases hx with ⟨t, ht, hxeq⟩
    rw [mem_stripChord_coords]
    rw [← hxeq]
    exact ⟨ht.1, ht.2, by simp⟩

/-- A full chord is connected (preconnected). -/
lemma isPreconnected_stripChord (α β : ℝ) : IsPreconnected (stripChord α β) := by
  have hD : IsPreconnected (Set.Ioo (0 : ℝ) 1) := isPreconnected_Ioo
  have hF : ContinuousOn (fun t : ℝ => !₂[t, sideH₁ α β t]) (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    dsimp [sideH₁]
    fun_prop
  have himg : IsPreconnected ((fun t : ℝ => !₂[t, sideH₁ α β t]) '' Set.Ioo (0 : ℝ) 1) :=
    IsPreconnected.image hD (fun t : ℝ => !₂[t, sideH₁ α β t]) hF
  simpa [stripChord_eq_image α β] using himg

/-- Parametrisation of the half-strip above a chord: `(u,v) ↦ (u,
sideH₁ α β u + v)` with `u ∈ (0,1)`, `v > 0`. -/
lemma aboveChord_eq_image (α β : ℝ) :
    aboveChord α β =
      (fun p : ℝ × ℝ => !₂[p.1, sideH₁ α β p.1 + p.2]) ''
        ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioi (0 : ℝ))) := by
  ext x
  constructor
  · intro hx
    rw [mem_aboveChord] at hx
    rw [Set.mem_image]
    refine ⟨(x 0, x 1 - sideH₁ α β (x 0)), ?_, ?_⟩
    · rw [Set.mem_prod]
      rw [stripInterior] at hx
      constructor
      · exact ⟨hx.1.1, hx.1.2⟩
      · rw [Set.mem_Ioi]
        linarith
    · ext i <;> fin_cases i <;> simp <;> ring
  · intro hx
    rcases hx with ⟨p, hp, hxeq⟩
    rw [Set.mem_prod] at hp
    rcases hp with ⟨hp₁, hp₂⟩
    rw [mem_aboveChord]
    rw [← hxeq]
    have hS : (!₂[p.1, sideH₁ α β p.1 + p.2] : ℝ²) ∈ stripInterior := by
      rw [stripInterior]
      rcases (Set.mem_Ioo.mp hp₁) with ⟨hp₁₀, hp₁₁⟩
      constructor <;> simp [hp₁₀, hp₁₁]
    exact ⟨hS, by
      have hpos : 0 < p.2 := (Set.mem_Ioi.mp hp₂)
      simp
      linarith⟩

/-- The half-strip above a chord is connected. -/
lemma isPreconnected_aboveChord (α β : ℝ) : IsPreconnected (aboveChord α β) := by
  have hD : IsPreconnected ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioi (0 : ℝ))) :=
    IsPreconnected.prod isPreconnected_Ioo isPreconnected_Ioi
  have hF : ContinuousOn (fun p : ℝ × ℝ => !₂[p.1, sideH₁ α β p.1 + p.2])
      ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioi (0 : ℝ))) := by
    intro p hp
    dsimp [sideH₁]
    fun_prop
  have himg : IsPreconnected
      ((fun p : ℝ × ℝ => !₂[p.1, sideH₁ α β p.1 + p.2]) ''
        ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioi (0 : ℝ)))) :=
    IsPreconnected.image hD (fun p : ℝ × ℝ => !₂[p.1, sideH₁ α β p.1 + p.2]) hF
  simpa [← aboveChord_eq_image α β] using himg

/-- Parametrisation of the half-strip below a chord: `(u,v) ↦ (u,
sideH₁ α β u − v)` with `u ∈ (0,1)`, `v > 0`. -/
lemma belowChord_eq_image (α β : ℝ) :
    belowChord α β =
      (fun p : ℝ × ℝ => !₂[p.1, sideH₁ α β p.1 - p.2]) ''
        ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioi (0 : ℝ))) := by
  ext x
  constructor
  · intro hx
    rw [mem_belowChord] at hx
    rw [Set.mem_image]
    refine ⟨(x 0, sideH₁ α β (x 0) - x 1), ?_, ?_⟩
    · rw [Set.mem_prod]
      rw [stripInterior] at hx
      constructor
      · exact ⟨hx.1.1, hx.1.2⟩
      · rw [Set.mem_Ioi]
        linarith
    · ext i <;> fin_cases i <;> simp <;> ring
  · intro hx
    rcases hx with ⟨p, hp, hxeq⟩
    rw [Set.mem_prod] at hp
    rcases hp with ⟨hp₁, hp₂⟩
    rw [mem_belowChord]
    rw [← hxeq]
    have hS : (!₂[p.1, sideH₁ α β p.1 - p.2] : ℝ²) ∈ stripInterior := by
      rw [stripInterior]
      rcases (Set.mem_Ioo.mp hp₁) with ⟨hp₁₀, hp₁₁⟩
      constructor <;> simp [hp₁₀, hp₁₁]
    exact ⟨hS, by
      have hpos : 0 < p.2 := (Set.mem_Ioi.mp hp₂)
      simp
      linarith⟩

/-- The half-strip below a chord is connected. -/
lemma isPreconnected_belowChord (α β : ℝ) : IsPreconnected (belowChord α β) := by
  have hD : IsPreconnected ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioi (0 : ℝ))) :=
    IsPreconnected.prod isPreconnected_Ioo isPreconnected_Ioi
  have hF : ContinuousOn (fun p : ℝ × ℝ => !₂[p.1, sideH₁ α β p.1 - p.2])
      ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioi (0 : ℝ))) := by
    intro p hp
    dsimp [sideH₁]
    fun_prop
  have himg : IsPreconnected
      ((fun p : ℝ × ℝ => !₂[p.1, sideH₁ α β p.1 - p.2]) ''
        ((Set.Ioo (0 : ℝ) 1) ×ˢ (Set.Ioi (0 : ℝ)))) :=
    IsPreconnected.image hD (fun p : ℝ × ℝ => !₂[p.1, sideH₁ α β p.1 - p.2]) hF
  simpa [← belowChord_eq_image α β] using himg

/-- A connected set inside the strip that avoids a full chord lies wholly
in one of the two open half-strips. -/
lemma preconnected_avoiding_chord_one_side {α β : ℝ} {s : Set ℝ²}
    (hsS : s ⊆ stripInterior) (hspre : IsPreconnected s)
    (hsΓ : Disjoint s (stripChord α β)) (hsne : s.Nonempty) :
    s ⊆ aboveChord α β ∨ s ⊆ belowChord α β := by
  have hsuv : s ⊆ aboveChord α β ∪ belowChord α β := by
    intro x hx
    have hxS : x ∈ stripInterior := hsS hx
    have hxΓ : x ∉ stripChord α β := (Set.disjoint_left.mp hsΓ) hx
    exact mem_above_or_below_of_not_mem_chord (α := α) (β := β) hxS hxΓ
  by_cases hmeet : (s ∩ aboveChord α β).Nonempty
  · left
    exact IsPreconnected.subset_left_of_subset_union (isOpen_aboveChord α β)
      (isOpen_belowChord α β) (aboveChord_disjoint_belowChord α β) hsuv hmeet hspre
  · right
    have hmeet' : (s ∩ belowChord α β).Nonempty := by
      rcases hsne with ⟨x, hx⟩
      have hxuv := hsuv hx
      rcases hxuv with hxAb | hxAb
      · exfalso
        exact hmeet ⟨x, hx, hxAb⟩
      · exact ⟨x, hx, hxAb⟩
    exact IsPreconnected.subset_right_of_subset_union (isOpen_aboveChord α β)
      (isOpen_belowChord α β) (aboveChord_disjoint_belowChord α β) hsuv hmeet' hspre

/-- Two disjoint full chords never cross inside the open strip: their
heights are never equal at any `x0 ∈ (0,1)`. -/
lemma heights_ne_of_disjoint_chords {α₁ β₁ α₂ β₂ : ℝ}
    (hdisj : Disjoint (stripChord α₁ β₁) (stripChord α₂ β₂)) :
    ∀ x0 : ℝ, x0 ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ x0 ≠ sideH₁ α₂ β₂ x0 := by
  intro x0 hx0
  rw [Set.mem_Ioo] at hx0
  intro hEq
  have hpt : (!₂[x0, sideH₁ α₁ β₁ x0] : ℝ²) ∈ stripChord α₁ β₁ :=
    chord_point_mem (α := α₁) (β := β₁) hx0.1 hx0.2
  have hpt' : (!₂[x0, sideH₁ α₁ β₁ x0] : ℝ²) ∈ stripChord α₂ β₂ := by
    rw [mem_stripChord_coords]
    exact ⟨hx0.1, hx0.2, by simp [hEq]⟩
  exact (Set.disjoint_left.mp hdisj hpt) hpt'

/-- Two disjoint chords that are ordered at one interior point are
pointwise ordered on all of `(0,1)`. -/
lemma chord_order_of_ordered_point {α₁ β₁ α₂ β₂ : ℝ}
    (hdisj : Disjoint (stripChord α₁ β₁) (stripChord α₂ β₂))
    {x0₀ : ℝ} (hx0₀ : x0₀ ∈ Set.Ioo 0 1)
    (hlt : sideH₁ α₁ β₁ x0₀ < sideH₁ α₂ β₂ x0₀) :
    ∀ x0 : ℝ, x0 ∈ Set.Ioo 0 1 → sideH₁ α₁ β₁ x0 < sideH₁ α₂ β₂ x0 := by
  intro x0 hx0
  let δ : ℝ → ℝ := fun u => sideH₁ α₂ β₂ u - sideH₁ α₁ β₁ u
  have hδno : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → δ u ≠ 0 := by
    intro u hu
    have hne := heights_ne_of_disjoint_chords (α₁ := α₁) (β₁ := β₁) (α₂ := α₂) (β₂ := β₂)
      hdisj u hu
    exact sub_ne_zero.mpr hne.symm
  have hδ0 : 0 < δ x0₀ := by
    dsimp [δ]
    linarith
  have hδpos : ∀ u : ℝ, u ∈ Set.Ioo 0 1 → 0 < δ u := by
    intro u hu
    by_cases hpos : 0 < δ u
    · exact hpos
    · have hle : δ u ≤ 0 := le_of_not_gt hpos
      have hδune : δ u ≠ 0 := hδno u hu
      have hneg : δ u < 0 := lt_of_le_of_ne hle hδune
      -- δ is affine and positive at x0₀, negative at u ⟹ zero between
      exfalso
      -- affine: δ v = A + B v for A = α₂−α₁, B = (β₂−α₂)−(β₁−α₁)
      let A : ℝ := α₂ - α₁
      let B : ℝ := (β₂ - α₂) - (β₁ - α₁)
      have hδaff : ∀ v : ℝ, δ v = A + B * v := by
        intro v
        dsimp [δ, A, B, sideH₁]
        ring
      -- zeros of δ: ustar = −A/B if B ≠ 0
      by_cases hB : B = 0
      · have hc : ∀ v : ℝ, δ v = δ u := by
          intro v
          calc δ v = A + B * v := hδaff v
            _ = A := by rw [hB, zero_mul, add_zero]
            _ = A + B * u := by rw [hB, zero_mul, add_zero]
            _ = δ u := (hδaff u).symm
        have : δ x0₀ < 0 := by rw [hc x0₀]; exact hneg
        linarith
      · let ustar : ℝ := -A / B
        have hδu0 : δ ustar = 0 := by
          rw [hδaff ustar]
          dsimp [ustar]
          field_simp [hB]
          ring
        have hfac : ∀ v : ℝ, δ v = B * (v - ustar) := by
          intro v
          calc
            δ v = A + B * v := hδaff v
            _ = B * (v - ustar) := by
              dsimp [ustar]
              field_simp [hB]
              ring
        -- u and x0₀ lie on the same side of ustar (ustar ∉ (0,1), both in (0,1))
        have hsame : (u - ustar) * (x0₀ - ustar) > 0 := by
          have huCase : ustar ≤ 0 ∨ 1 ≤ ustar := by
            by_contra hbad
            rcases not_or.mp hbad with ⟨hnot0, hnot1⟩
            have hgt0 : 0 < ustar := lt_of_not_ge hnot0
            have hlt1 : ustar < 1 := lt_of_not_ge hnot1
            exact hδno ustar ⟨hgt0, hlt1⟩ hδu0
          have hu0 : 0 < u := (Set.mem_Ioo.mp hu).1
          have hu1 : u < 1 := (Set.mem_Ioo.mp hu).2
          have hx0₀_0 : 0 < x0₀ := (Set.mem_Ioo.mp hx0₀).1
          have hx0₀_1 : x0₀ < 1 := (Set.mem_Ioo.mp hx0₀).2
          rcases huCase with hu_le0 | hu_ge1
          · have h1 : 0 < u - ustar := by linarith
            have h2 : 0 < x0₀ - ustar := by linarith
            nlinarith
          · have h1 : u - ustar < 0 := by linarith
            have h2 : x0₀ - ustar < 0 := by linarith
            nlinarith
        have hδx₀pos : 0 < δ x0₀ := hδ0
        have hfacx : δ x0₀ = B * (x0₀ - ustar) := hfac x0₀
        rcases lt_or_gt_of_ne hB with hBneg | hBpos
        · -- B < 0: δ x0₀ > 0 forces x0₀ − ustar < 0; u − ustar < 0 (same sign pair)
          have hx0₀u : x0₀ - ustar < 0 := by
            rw [hfacx] at hδx₀pos
            exact neg_of_mul_pos_right hδx₀pos (le_of_lt hBneg)
          have hu' : u - ustar < 0 := by
            have : (u - ustar) * (x0₀ - ustar) > 0 := hsame
            exact neg_of_mul_pos_left this (le_of_lt hx0₀u)
          have hδu' : δ u > 0 := by
            rw [hfac u]
            exact mul_pos_of_neg_of_neg hBneg hu'
          linarith
        · -- B > 0
          have hx0₀u : 0 < x0₀ - ustar := by
            rw [hfacx] at hδx₀pos
            exact pos_of_mul_pos_right hδx₀pos (le_of_lt hBpos)
          have hu' : 0 < u - ustar := by
            have : (u - ustar) * (x0₀ - ustar) > 0 := hsame
            exact pos_of_mul_pos_left this (le_of_lt hx0₀u)
          have hδu' : δ u > 0 := by
            rw [hfac u]
            exact mul_pos hBpos hu'
          linarith
  have hgoal : sideH₁ α₁ β₁ x0 < sideH₁ α₂ β₂ x0 := by
    dsimp [δ] at hδpos
    exact sub_pos.mp (hδpos x0 hx0)
  exact hgoal

/-- The height of a chord over `x0 = 1/2` is the average of the seam
heights: `(α+β)/2`. -/
lemma sideH₁_half (α β : ℝ) : sideH₁ α β (1 / 2) = (α + β) / 2 := by
  dsimp [sideH₁]
  ring

/-- Distinct frontier components of a flat component are disjoint as
sets. -/
lemma frComponent_disjoint {f : ℝ² → ℝ³} {p e₁ e₂ : ℝ²}
    (hne : frComp f p e₁ ≠ frComp f p e₂)
    (he₁ : e₁ ∈ frontier (flatComponent f p) ∩ stripInterior)
    (he₂ : e₂ ∈ frontier (flatComponent f p) ∩ stripInterior) :
    Disjoint (frComp f p e₁) (frComp f p e₂) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  have h₁ : frComp f p z = frComp f p e₁ := frComponent_eq_of_mem hz₁
  have h₂ : frComp f p z = frComp f p e₂ := frComponent_eq_of_mem hz₂
  apply hne
  exact h₁.symm.trans h₂

/-- **Separation**: two distinct frontier components of a flat component
are disjoint full chords; if the crossing heights at `x0 = 1/2` are
ordered (`e₁` below `e₂`), the first component lies entirely in the
half-strip below the second chord and the second entirely in the
half-strip above the first chord. -/
theorem frComponent_separated {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {e₁ e₂ : ℝ²}
    (he₁F : e₁ ∈ frontier (flatComponent f p)) (he₁S : e₁ ∈ stripInterior)
    (he₂F : e₂ ∈ frontier (flatComponent f p)) (he₂S : e₂ ∈ stripInterior)
    (he₁0 : e₁ 0 = 1 / 2) (he₂0 : e₂ 0 = 1 / 2)
    (hne : frComp f p e₁ ≠ frComp f p e₂)
    (hord : e₁ 1 < e₂ 1) :
    ∃ α₁ β₁ α₂ β₂ : ℝ,
      frComp f p e₁ = stripChord α₁ β₁ ∧ frComp f p e₂ = stripChord α₂ β₂ ∧
      frComp f p e₁ ⊆ belowChord α₂ β₂ ∧ frComp f p e₂ ⊆ aboveChord α₁ β₁ := by
  rcases frontierComponent_full_chord hf ha hp he₁S he₁F with ⟨α₁, β₁, hch₁⟩
  rcases frontierComponent_full_chord hf ha hp he₂S he₂F with ⟨α₂, β₂, hch₂⟩
  refine ⟨α₁, β₁, α₂, β₂, hch₁, hch₂, ?_, ?_⟩
  · -- e₁'s component below e₂'s chord
    have hdisj : Disjoint (stripChord α₁ β₁) (stripChord α₂ β₂) := by
      rw [← hch₁, ← hch₂]
      exact frComponent_disjoint hne ⟨he₁F, he₁S⟩ ⟨he₂F, he₂S⟩
    have hh₁ : sideH₁ α₁ β₁ (1 / 2) = e₁ 1 := by
      have he₁Γ : e₁ ∈ stripChord α₁ β₁ := by
        have he₁C : e₁ ∈ frComp f p e₁ := mem_connectedComponentIn ⟨he₁F, he₁S⟩
        rwa [← hch₁]
      rw [mem_stripChord] at he₁Γ
      have hh : sideH₁ α₁ β₁ (1 / 2) = sideH₁ α₁ β₁ (e₁ 0) := by
        rw [he₁0]
      exact hh.trans he₁Γ.2.symm
    have hh₂ : sideH₁ α₂ β₂ (1 / 2) = e₂ 1 := by
      have he₂Γ : e₂ ∈ stripChord α₂ β₂ := by
        have he₂C : e₂ ∈ frComp f p e₂ := mem_connectedComponentIn ⟨he₂F, he₂S⟩
        rwa [← hch₂]
      rw [mem_stripChord] at he₂Γ
      have hh : sideH₁ α₂ β₂ (1 / 2) = sideH₁ α₂ β₂ (e₂ 0) := by
        rw [he₂0]
      exact hh.trans he₂Γ.2.symm
    have hord' : sideH₁ α₁ β₁ (1 / 2) < sideH₁ α₂ β₂ (1 / 2) := by
      rw [hh₁, hh₂]
      exact hord
    have hbelow : ∀ x0 : ℝ, x0 ∈ Set.Ioo 0 1 →
        sideH₁ α₁ β₁ x0 < sideH₁ α₂ β₂ x0 :=
      chord_order_of_ordered_point (α₁ := α₁) (β₁ := β₁) (α₂ := α₂) (β₂ := β₂)
        hdisj ⟨by norm_num, by norm_num⟩ hord'
    intro x hx₁
    rw [mem_belowChord]
    rw [hch₁] at hx₁
    rw [mem_stripChord] at hx₁
    exact ⟨hx₁.1, by
      have hlt := hbelow (x 0) (by
        rw [Set.mem_Ioo]
        rw [stripInterior] at hx₁
        exact ⟨hx₁.1.1, hx₁.1.2⟩)
      have hx1 : x 1 = sideH₁ α₁ β₁ (x 0) := hx₁.2
      linarith⟩
  · -- e₂'s component above e₁'s chord
    have hdisj : Disjoint (stripChord α₁ β₁) (stripChord α₂ β₂) := by
      rw [← hch₁, ← hch₂]
      exact frComponent_disjoint hne ⟨he₁F, he₁S⟩ ⟨he₂F, he₂S⟩
    have hh₁ : sideH₁ α₁ β₁ (1 / 2) = e₁ 1 := by
      have he₁Γ : e₁ ∈ stripChord α₁ β₁ := by
        have he₁C : e₁ ∈ frComp f p e₁ := mem_connectedComponentIn ⟨he₁F, he₁S⟩
        rwa [← hch₁]
      rw [mem_stripChord] at he₁Γ
      have hh : sideH₁ α₁ β₁ (1 / 2) = sideH₁ α₁ β₁ (e₁ 0) := by
        rw [he₁0]
      exact hh.trans he₁Γ.2.symm
    have hh₂ : sideH₁ α₂ β₂ (1 / 2) = e₂ 1 := by
      have he₂Γ : e₂ ∈ stripChord α₂ β₂ := by
        have he₂C : e₂ ∈ frComp f p e₂ := mem_connectedComponentIn ⟨he₂F, he₂S⟩
        rwa [← hch₂]
      rw [mem_stripChord] at he₂Γ
      have hh : sideH₁ α₂ β₂ (1 / 2) = sideH₁ α₂ β₂ (e₂ 0) := by
        rw [he₂0]
      exact hh.trans he₂Γ.2.symm
    have hord' : sideH₁ α₁ β₁ (1 / 2) < sideH₁ α₂ β₂ (1 / 2) := by
      rw [hh₁, hh₂]
      exact hord
    have habove : ∀ x0 : ℝ, x0 ∈ Set.Ioo 0 1 →
        sideH₁ α₁ β₁ x0 < sideH₁ α₂ β₂ x0 :=
      chord_order_of_ordered_point (α₁ := α₁) (β₁ := β₁) (α₂ := α₂) (β₂ := β₂)
        hdisj ⟨by norm_num, by norm_num⟩ hord'
    intro x hx₂
    rw [mem_aboveChord]
    rw [hch₂] at hx₂
    rw [mem_stripChord] at hx₂
    exact ⟨hx₂.1, by
      have hlt := habove (x 0) (by
        rw [Set.mem_Ioo]
        rw [stripInterior] at hx₂
        exact ⟨hx₂.1.1, hx₂.1.2⟩)
      have hx1 : x 1 = sideH₁ α₂ β₂ (x 0) := hx₂.2
      linarith⟩

end Submission.PaperBand
