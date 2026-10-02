import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Even sign changes

For a continuous, `1`-periodic function `h : ℝ → ℝ` whose level set `{h = c}` meets the
fundamental domain `[0,1)` in a finite set, the number of *transversal crossings* of the level
`c` inside `[0,1)` is even.

The proof reduces to a one-dimensional parity statement on an interval `[p, p+1]` cut out of the
circle at a point `p` with `h p ≠ c`: there the crossings are counted by strong induction on the
number of zeros (removing the smallest zero, the parity changes by the parity of the two
adjacent one-sided signs), and the crossings inside `[0,1)` are in bijection with those inside
`(p, p+1)` along the periodic structure.
-/

set_option maxHeartbeats 1000000

namespace Work.ELRig

open Set

/-- Right-hand positive sign at a point: `f > c` on a small interval to the right. -/
def RPos (f : ℝ → ℝ) (c a : ℝ) : Prop := ∃ ε > 0, ∀ t ∈ Set.Ioo a (a + ε), c < f t

/-- Right-hand negative sign at a point: `f < c` on a small interval to the right. -/
def RNeg (f : ℝ → ℝ) (c a : ℝ) : Prop := ∃ ε > 0, ∀ t ∈ Set.Ioo a (a + ε), f t < c

/-- Left-hand positive sign at a point: `f > c` on a small interval to the left. -/
def LPos (f : ℝ → ℝ) (c b : ℝ) : Prop := ∃ ε > 0, ∀ t ∈ Set.Ioo (b - ε) b, c < f t

/-- Left-hand negative sign at a point: `f < c` on a small interval to the left. -/
def LNeg (f : ℝ → ℝ) (c b : ℝ) : Prop := ∃ ε > 0, ∀ t ∈ Set.Ioo (b - ε) b, f t < c

/-- A transversal crossing of the level `c` at `s`: the function is strictly above `c` on one
side and strictly below `c` on the other. -/
def Cross (f : ℝ → ℝ) (c s : ℝ) : Prop :=
  (LPos f c s ∧ RNeg f c s) ∨ (LNeg f c s ∧ RPos f c s)

/-- The set of zeros of `f - c` inside the open interval `(a,b)`. -/
def Zeros (f : ℝ → ℝ) (c a b : ℝ) : Set ℝ := {x : ℝ | x ∈ Set.Ioo a b ∧ f x = c}

/-- The set of transversal crossings of the level `c` inside the open interval `(a,b)`. -/
def CrossSet (f : ℝ → ℝ) (c a b : ℝ) : Set ℝ := {x : ℝ | x ∈ Set.Ioo a b ∧ Cross f c x}

section basic

variable {f : ℝ → ℝ} {c a b s : ℝ}

lemma not_RPos_and_RNeg : ¬ (RPos f c a ∧ RNeg f c a) := by
  rintro ⟨⟨ε₁, hε₁, h₁⟩, ⟨ε₂, hε₂, h₂⟩⟩
  have hm : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have h1 : a + min ε₁ ε₂ / 2 ∈ Set.Ioo a (a + ε₁) := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [hm], by linarith [min_le_left ε₁ ε₂, hε₁]⟩
  have h2 : a + min ε₁ ε₂ / 2 ∈ Set.Ioo a (a + ε₂) := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [hm], by linarith [min_le_right ε₁ ε₂, hε₂]⟩
  have h3 := h₁ _ h1
  have h4 := h₂ _ h2
  linarith

lemma not_LPos_and_LNeg : ¬ (LPos f c b ∧ LNeg f c b) := by
  rintro ⟨⟨ε₁, hε₁, h₁⟩, ⟨ε₂, hε₂, h₂⟩⟩
  have hm : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
  have h1 : b - min ε₁ ε₂ / 2 ∈ Set.Ioo (b - ε₁) b := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [min_le_left ε₁ ε₂, hε₁], by linarith [hm]⟩
  have h2 : b - min ε₁ ε₂ / 2 ∈ Set.Ioo (b - ε₂) b := by
    rw [Set.mem_Ioo]
    exact ⟨by linarith [min_le_right ε₁ ε₂, hε₂], by linarith [hm]⟩
  have h3 := h₁ _ h1
  have h4 := h₂ _ h2
  linarith

lemma RPos_or_RNeg_iff (h : RPos f c a ∨ RNeg f c a) : RNeg f c a ↔ ¬ RPos f c a := by
  refine ⟨fun h2 h1 => not_RPos_and_RNeg ⟨h1, h2⟩, fun h1 => ?_⟩
  rcases h with h | h
  · exact absurd h h1
  · exact h

lemma LPos_or_LNeg_iff (h : LPos f c b ∨ LNeg f c b) : LNeg f c b ↔ ¬ LPos f c b := by
  refine ⟨fun h2 h1 => not_LPos_and_LNeg ⟨h1, h2⟩, fun h1 => ?_⟩
  rcases h with h | h
  · exact absurd h h1
  · exact h

/-- On a zero-free interval a continuous function has constant sign. -/
lemma sign_const_Ioo (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (h : ∀ t ∈ Set.Ioo a b, f t ≠ c) :
    (∀ t ∈ Set.Ioo a b, c < f t) ∨ (∀ t ∈ Set.Ioo a b, f t < c) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hx, hxle⟩, ⟨y, hy, hyle⟩⟩ := hcon
  have hfx : f x < c := lt_of_le_of_ne hxle (h x hx)
  have hfy : c < f y := lt_of_le_of_ne hyle (Ne.symm (h y hy))
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have hc' : ContinuousOn f (Set.Icc x y) := hcont.mono (Set.Icc_subset_Icc hx.1.le hy.2.le)
    have hmem : c ∈ Set.Icc (f x) (f y) := ⟨le_of_lt hfx, le_of_lt hfy⟩
    obtain ⟨z, hz, hfz⟩ := (intermediate_value_Icc hxy.le hc') hmem
    exact h z ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩ hfz
  · rw [hxy] at hfx
    linarith
  · have hc' : ContinuousOn f (Set.Icc y x) := hcont.mono (Set.Icc_subset_Icc hy.1.le hx.2.le)
    have hmem : c ∈ Set.Icc (f x) (f y) := ⟨le_of_lt hfx, le_of_lt hfy⟩
    obtain ⟨z, hz, hfz⟩ := (intermediate_value_Icc' hxy.le hc') hmem
    exact h z ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩ hfz

lemma RPos_or_RNeg_of_no_zero (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (h : ∀ t ∈ Set.Ioo a b, f t ≠ c) : RPos f c a ∨ RNeg f c a := by
  rcases sign_const_Ioo hab hcont h with h' | h'
  · left
    exact ⟨b - a, by linarith, fun t ht => h' t (by
      rw [Set.mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2])⟩
  · right
    exact ⟨b - a, by linarith, fun t ht => h' t (by
      rw [Set.mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2])⟩

lemma LPos_or_LNeg_of_no_zero (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (h : ∀ t ∈ Set.Ioo a b, f t ≠ c) : LPos f c b ∨ LNeg f c b := by
  rcases sign_const_Ioo hab hcont h with h' | h'
  · left
    exact ⟨b - a, by linarith, fun t ht => h' t (by
      rw [Set.mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2])⟩
  · right
    exact ⟨b - a, by linarith, fun t ht => h' t (by
      rw [Set.mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2])⟩

end basic

section endpoint

variable {f : ℝ → ℝ} {c a b s z : ℝ}

lemma RPos_iff (hc : ContinuousAt f a) (hne : f a ≠ c) : RPos f c a ↔ c < f a := by
  constructor
  · rintro ⟨ε, hε, h⟩
    have htend : Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds (f a)) :=
      hc.continuousWithinAt
    have hev : ∀ᶠ t in nhdsWithin a (Set.Ioi a), c ≤ f t := by
      show ({t : ℝ | c ≤ f t} : Set ℝ) ∈ nhdsWithin a (Set.Ioi a)
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio (a + ε), isOpen_Iio, by rw [Set.mem_Iio]; linarith,
        fun t ht => le_of_lt (h t ⟨ht.2, ht.1⟩)⟩
    have h1 : c ≤ f a := ge_of_tendsto htend hev
    exact lt_of_le_of_ne h1 (Ne.symm hne)
  · intro hlt
    have hmem : Set.Ioi c ∈ nhds (f a) := isOpen_Ioi.mem_nhds hlt
    have hev : ∀ᶠ t in nhds a, c < f t := hc.eventually hmem
    obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ε, hε, fun t ht => hεp ?_⟩
    rw [Set.mem_Ioo] at ht
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma RNeg_iff (hc : ContinuousAt f a) (hne : f a ≠ c) : RNeg f c a ↔ f a < c := by
  constructor
  · rintro ⟨ε, hε, h⟩
    have htend : Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds (f a)) :=
      hc.continuousWithinAt
    have hev : ∀ᶠ t in nhdsWithin a (Set.Ioi a), f t ≤ c := by
      show ({t : ℝ | f t ≤ c} : Set ℝ) ∈ nhdsWithin a (Set.Ioi a)
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio (a + ε), isOpen_Iio, by rw [Set.mem_Iio]; linarith,
        fun t ht => le_of_lt (h t ⟨ht.2, ht.1⟩)⟩
    have h1 : f a ≤ c := le_of_tendsto htend hev
    exact lt_of_le_of_ne h1 hne
  · intro hlt
    have hmem : Set.Iio c ∈ nhds (f a) := isOpen_Iio.mem_nhds hlt
    have hev : ∀ᶠ t in nhds a, f t < c := hc.eventually hmem
    obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ε, hε, fun t ht => hεp ?_⟩
    rw [Set.mem_Ioo] at ht
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma LPos_iff (hc : ContinuousAt f b) (hne : f b ≠ c) : LPos f c b ↔ c < f b := by
  constructor
  · rintro ⟨ε, hε, h⟩
    have htend : Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds (f b)) :=
      hc.continuousWithinAt
    have hev : ∀ᶠ t in nhdsWithin b (Set.Iio b), c ≤ f t := by
      show ({t : ℝ | c ≤ f t} : Set ℝ) ∈ nhdsWithin b (Set.Iio b)
      rw [mem_nhdsWithin]
      exact ⟨Set.Ioi (b - ε), isOpen_Ioi, by rw [Set.mem_Ioi]; linarith,
        fun t ht => le_of_lt (h t ⟨ht.1, ht.2⟩)⟩
    have h1 : c ≤ f b := ge_of_tendsto htend hev
    exact lt_of_le_of_ne h1 (Ne.symm hne)
  · intro hlt
    have hmem : Set.Ioi c ∈ nhds (f b) := isOpen_Ioi.mem_nhds hlt
    have hev : ∀ᶠ t in nhds b, c < f t := hc.eventually hmem
    obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ε, hε, fun t ht => hεp ?_⟩
    rw [Set.mem_Ioo] at ht
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

lemma LNeg_iff (hc : ContinuousAt f b) (hne : f b ≠ c) : LNeg f c b ↔ f b < c := by
  constructor
  · rintro ⟨ε, hε, h⟩
    have htend : Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds (f b)) :=
      hc.continuousWithinAt
    have hev : ∀ᶠ t in nhdsWithin b (Set.Iio b), f t ≤ c := by
      show ({t : ℝ | f t ≤ c} : Set ℝ) ∈ nhdsWithin b (Set.Iio b)
      rw [mem_nhdsWithin]
      exact ⟨Set.Ioi (b - ε), isOpen_Ioi, by rw [Set.mem_Ioi]; linarith,
        fun t ht => le_of_lt (h t ⟨ht.1, ht.2⟩)⟩
    have h1 : f b ≤ c := le_of_tendsto htend hev
    exact lt_of_le_of_ne h1 hne
  · intro hlt
    have hmem : Set.Iio c ∈ nhds (f b) := isOpen_Iio.mem_nhds hlt
    have hev : ∀ᶠ t in nhds b, f t < c := hc.eventually hmem
    obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨ε, hε, fun t ht => hεp ?_⟩
    rw [Set.mem_Ioo] at ht
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- A crossing point is a zero. -/
lemma eq_of_cross (hc : ContinuousAt f s) (h : Cross f c s) : f s = c := by
  have ht1 : Filter.Tendsto f (nhdsWithin s (Set.Ioi s)) (nhds (f s)) := hc.continuousWithinAt
  have ht2 : Filter.Tendsto f (nhdsWithin s (Set.Iio s)) (nhds (f s)) := hc.continuousWithinAt
  rcases h with ⟨hL, hR⟩ | ⟨hL, hR⟩
  · obtain ⟨ε, hε, hεp⟩ := hR
    have h1 : f s ≤ c := by
      refine le_of_tendsto ht1 ?_
      show ({t : ℝ | f t ≤ c} : Set ℝ) ∈ nhdsWithin s (Set.Ioi s)
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio (s + ε), isOpen_Iio, by rw [Set.mem_Iio]; linarith,
        fun t ht => le_of_lt (hεp t ⟨ht.2, ht.1⟩)⟩
    obtain ⟨δ, hδ, hδp⟩ := hL
    have h2 : c ≤ f s := by
      refine ge_of_tendsto ht2 ?_
      show ({t : ℝ | c ≤ f t} : Set ℝ) ∈ nhdsWithin s (Set.Iio s)
      rw [mem_nhdsWithin]
      exact ⟨Set.Ioi (s - δ), isOpen_Ioi, by rw [Set.mem_Ioi]; linarith,
        fun t ht => le_of_lt (hδp t ⟨ht.1, ht.2⟩)⟩
    linarith
  · obtain ⟨ε, hε, hεp⟩ := hR
    have h1 : c ≤ f s := by
      refine ge_of_tendsto ht1 ?_
      show ({t : ℝ | c ≤ f t} : Set ℝ) ∈ nhdsWithin s (Set.Ioi s)
      rw [mem_nhdsWithin]
      exact ⟨Set.Iio (s + ε), isOpen_Iio, by rw [Set.mem_Iio]; linarith,
        fun t ht => le_of_lt (hεp t ⟨ht.2, ht.1⟩)⟩
    obtain ⟨δ, hδ, hδp⟩ := hL
    have h2 : f s ≤ c := by
      refine le_of_tendsto ht2 ?_
      show ({t : ℝ | f t ≤ c} : Set ℝ) ∈ nhdsWithin s (Set.Iio s)
      rw [mem_nhdsWithin]
      exact ⟨Set.Ioi (s - δ), isOpen_Ioi, by rw [Set.mem_Ioi]; linarith,
        fun t ht => le_of_lt (hδp t ⟨ht.1, ht.2⟩)⟩
    linarith

/-- A crossing, expressed through the two one-sided signs. -/
lemma cross_iff (hL : LPos f c s ∨ LNeg f c s) (hR : RPos f c s ∨ RNeg f c s) :
    Cross f c s ↔ ((LPos f c s ∧ ¬ RPos f c s) ∨ (¬ LPos f c s ∧ RPos f c s)) := by
  have h1 : LNeg f c s ↔ ¬ LPos f c s := LPos_or_LNeg_iff hL
  have h2 : RNeg f c s ↔ ¬ RPos f c s := RPos_or_RNeg_iff hR
  rw [Cross]
  tauto

/-- In a zero-free interval the one-sided sign just left of the right endpoint equals the
one-sided sign just right of the left endpoint. -/
lemma LPos_iff_RPos_of_no_zero (haz : a < z) (hcont : ContinuousOn f (Set.Icc a z))
    (hno : ∀ t ∈ Set.Ioo a z, f t ≠ c) : LPos f c z ↔ RPos f c a := by
  rcases sign_const_Ioo haz hcont hno with hpos | hneg
  · constructor
    · intro _
      exact ⟨(z - a) / 2, by linarith, fun t ht => hpos t (by
        rw [Set.mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2])⟩
    · intro _
      exact ⟨z - a, by linarith, fun t ht => hpos t (by
        rw [Set.mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2])⟩
  · constructor
    · intro hL
      obtain ⟨ε, hε, hεp⟩ := hL
      have hlt : max (z - ε) a < z := max_lt (by linarith) haz
      have ht1 : (max (z - ε) a + z) / 2 ∈ Set.Ioo (z - ε) z := by
        rw [Set.mem_Ioo]
        exact ⟨by linarith [le_max_left (z - ε) a, hε], by linarith [hlt]⟩
      have ht2 : (max (z - ε) a + z) / 2 ∈ Set.Ioo a z := by
        rw [Set.mem_Ioo]
        exact ⟨by linarith [le_max_right (z - ε) a], by linarith [hlt]⟩
      exact absurd (hεp _ ht1) (not_lt.mpr (le_of_lt (hneg _ ht2)))
    · intro hR
      obtain ⟨ε, hε, hεp⟩ := hR
      have hgt : a < min (a + ε) z := lt_min (by linarith) haz
      have ht1 : (a + min (a + ε) z) / 2 ∈ Set.Ioo a (a + ε) := by
        rw [Set.mem_Ioo]
        exact ⟨by linarith [hgt], by linarith [min_le_left (a + ε) z]⟩
      have ht2 : (a + min (a + ε) z) / 2 ∈ Set.Ioo a z := by
        rw [Set.mem_Ioo]
        exact ⟨by linarith [hgt], by linarith [min_le_right (a + ε) z]⟩
      exact absurd (hεp _ ht1) (not_lt.mpr (le_of_lt (hneg _ ht2)))

end endpoint

section finitezeros

variable {f : ℝ → ℝ} {c a b : ℝ}

lemma RPos_or_RNeg_of_finite_zeros (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (hfin : (Zeros f c a b).Finite) : RPos f c a ∨ RNeg f c a := by
  by_cases hne : (Zeros f c a b).Nonempty
  · set Z : Set ℝ := Zeros f c a b with hZdef
    have hZfin : Z.Finite := hfin
    set z : ℝ := hZfin.toFinset.min' (hZfin.toFinset_nonempty.mpr hne) with hzdef
    have hzmem : z ∈ Z := by rw [hzdef, ← hZfin.mem_toFinset]; exact Finset.min'_mem _ _
    have hzle : ∀ x ∈ Z, z ≤ x := by
      intro x hx
      rw [hzdef]
      exact Finset.min'_le _ x (hZfin.mem_toFinset.mpr hx)
    have hzab : z ∈ Set.Ioo a b := hzmem.1
    have hno : ∀ t ∈ Set.Ioo a z, f t ≠ c := by
      intro t ht htc
      exact absurd (hzle t ⟨⟨ht.1, lt_trans ht.2 hzab.2⟩, htc⟩) (not_le.mpr ht.2)
    have hcontz : ContinuousOn f (Set.Icc a z) := hcont.mono (Set.Icc_subset_Icc le_rfl hzab.2.le)
    exact RPos_or_RNeg_of_no_zero hzab.1 hcontz hno
  · have hZ : Zeros f c a b = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hno : ∀ t ∈ Set.Ioo a b, f t ≠ c := by
      intro t ht htc
      have hmem : t ∈ Zeros f c a b := ⟨ht, htc⟩
      rw [hZ] at hmem
      exact hmem
    exact RPos_or_RNeg_of_no_zero hab hcont hno

lemma LPos_or_LNeg_of_finite_zeros (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (hfin : (Zeros f c a b).Finite) : LPos f c b ∨ LNeg f c b := by
  by_cases hne : (Zeros f c a b).Nonempty
  · set Z : Set ℝ := Zeros f c a b with hZdef
    have hZfin : Z.Finite := hfin
    set z : ℝ := hZfin.toFinset.max' (hZfin.toFinset_nonempty.mpr hne) with hzdef
    have hzmem : z ∈ Z := by rw [hzdef, ← hZfin.mem_toFinset]; exact Finset.max'_mem _ _
    have hzle : ∀ x ∈ Z, x ≤ z := by
      intro x hx
      rw [hzdef]
      exact Finset.le_max' _ x (hZfin.mem_toFinset.mpr hx)
    have hzab : z ∈ Set.Ioo a b := hzmem.1
    have hno : ∀ t ∈ Set.Ioo z b, f t ≠ c := by
      intro t ht htc
      exact absurd (hzle t ⟨⟨lt_trans hzab.1 ht.1, ht.2⟩, htc⟩) (not_le.mpr ht.1)
    have hcontz : ContinuousOn f (Set.Icc z b) := hcont.mono (Set.Icc_subset_Icc hzab.1.le le_rfl)
    exact LPos_or_LNeg_of_no_zero hzab.2 hcontz hno
  · have hZ : Zeros f c a b = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hno : ∀ t ∈ Set.Ioo a b, f t ≠ c := by
      intro t ht htc
      have hmem : t ∈ Zeros f c a b := ⟨ht, htc⟩
      rw [hZ] at hmem
      exact hmem
    exact LPos_or_LNeg_of_no_zero hab hcont hno

end finitezeros

section parity

variable {f : ℝ → ℝ} {c a b : ℝ}

/-- **One-dimensional parity of crossings.**  For a continuous function on `[a,b]` whose interior
zeros are finite, the number of transversal crossings of the level `c` inside `(a,b)` is even
exactly when the one-sided signs at the two endpoints agree. -/
lemma parity_crossings_aux (k : ℕ) :
    ∀ (a b c : ℝ) (f : ℝ → ℝ), a < b →
    ContinuousOn f (Set.Icc a b) →
    (Zeros f c a b).Finite →
    (Zeros f c a b).ncard = k →
    (RPos f c a ∨ RNeg f c a) → (LPos f c b ∨ LNeg f c b) →
    (Even (CrossSet f c a b).ncard ↔ (RPos f c a ↔ LPos f c b)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a b c f hab hcont hfin hk hRa hLb
    by_cases hk0 : k = 0
    · have hZempty : Zeros f c a b = ∅ :=
        (Set.ncard_eq_zero hfin).mp (by rw [hk, hk0])
      have hcross : CrossSet f c a b = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨hx, hcx⟩
        have hmem : x ∈ Zeros f c a b :=
          ⟨hx, eq_of_cross (hcont.continuousAt (Icc_mem_nhds hx.1 hx.2)) hcx⟩
        rw [hZempty] at hmem
        exact hmem
      rw [hcross, Set.ncard_empty]
      have hno : ∀ t ∈ Set.Ioo a b, f t ≠ c := by
        intro t ht htc
        have hmem : t ∈ Zeros f c a b := ⟨ht, htc⟩
        rw [hZempty] at hmem
        exact hmem
      have hgoal : RPos f c a ↔ LPos f c b := by
        rcases sign_const_Ioo hab hcont hno with hpos | hneg
        · constructor
          · intro _
            exact ⟨b - a, by linarith, fun t ht => hpos t (by
              rw [Set.mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2])⟩
          · intro _
            exact ⟨(b - a) / 2, by linarith, fun t ht => hpos t (by
              rw [Set.mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2])⟩
        · constructor
          · intro hR
            exact absurd hR (fun h1 => not_RPos_and_RNeg ⟨h1, ⟨b - a, by linarith, fun t ht => hneg t (by rw [Set.mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2])⟩⟩)
          · intro hL
            exact absurd hL (fun h1 => not_LPos_and_LNeg ⟨h1, ⟨(b - a) / 2, by linarith, fun t ht => hneg t (by rw [Set.mem_Ioo] at ht ⊢; constructor <;> linarith [ht.1, ht.2])⟩⟩)
      exact ⟨fun _ => hgoal, fun _ => ⟨0, rfl⟩⟩
    · set Z : Set ℝ := Zeros f c a b with hZdef
      have hZfin : Z.Finite := hfin
      have hZnon : Z.Nonempty :=
        (Set.ncard_pos hZfin).mp (by rw [show Z.ncard = k from hk]; exact Nat.pos_of_ne_zero hk0)
      set z : ℝ := hZfin.toFinset.min' (hZfin.toFinset_nonempty.mpr hZnon) with hzdef
      have hzmem : z ∈ Z := by rw [hzdef, ← hZfin.mem_toFinset]; exact Finset.min'_mem _ _
      have hzle : ∀ x ∈ Z, z ≤ x := by
        intro x hx
        rw [hzdef]
        exact Finset.min'_le _ x (hZfin.mem_toFinset.mpr hx)
      have hzab : z ∈ Set.Ioo a b := hzmem.1
      have hznot : ∀ t ∈ Set.Ioo a z, f t ≠ c := by
        intro t ht htc
        exact absurd (hzle t ⟨⟨ht.1, lt_trans ht.2 hzab.2⟩, htc⟩) (not_le.mpr ht.2)
      have hcontz : ContinuousOn f (Set.Icc a z) :=
        hcont.mono (Set.Icc_subset_Icc le_rfl hzab.2.le)
      have hzL : LPos f c z ∨ LNeg f c z := LPos_or_LNeg_of_no_zero hzab.1 hcontz hznot
      have hLP : LPos f c z ↔ RPos f c a := LPos_iff_RPos_of_no_zero hzab.1 hcontz hznot
      have hcontb : ContinuousOn f (Set.Icc z b) :=
        hcont.mono (Set.Icc_subset_Icc hzab.1.le le_rfl)
      have hZrfin : (Zeros f c z b).Finite :=
        hfin.subset (fun _ hx => ⟨⟨lt_trans hzab.1 hx.1.1, hx.1.2⟩, hx.2⟩)
      have hZrn : (Zeros f c z b).ncard < k := by
        have hEq : Zeros f c z b = Z \ {z} := by
          ext x
          constructor
          · intro hx
            refine ⟨⟨⟨lt_trans hzab.1 hx.1.1, hx.1.2⟩, hx.2⟩, ?_⟩
            simp only [Set.mem_singleton_iff]
            exact ne_of_gt hx.1.1
          · intro hx
            rcases hx with ⟨hxZ, hxne⟩
            simp only [Set.mem_singleton_iff] at hxne
            exact ⟨⟨lt_of_le_of_ne (hzle x hxZ) (Ne.symm hxne), hxZ.1.2⟩, hxZ.2⟩
        rw [hEq, Set.ncard_sdiff_singleton_of_mem hzmem]
        have hZk : Z.ncard = k := hk
        omega
      have hRaz : RPos f c z ∨ RNeg f c z :=
        RPos_or_RNeg_of_finite_zeros hzab.2 hcontb hZrfin
      have hih := ih _ hZrn z b c f hzab.2 hcontb hZrfin rfl hRaz hLb
      have hSzfin : (CrossSet f c z b).Finite :=
        hZrfin.subset (fun _ hx => ⟨hx.1, eq_of_cross
          (hcont.continuousAt (Icc_mem_nhds (lt_trans hzab.1 hx.1.1) hx.1.2)) hx.2⟩)
      by_cases hcz : Cross f c z
      · have hSeq : CrossSet f c a b = insert z (CrossSet f c z b) := by
          ext x
          constructor
          · rintro ⟨hx, hcx⟩
            rcases lt_trichotomy x z with hxz | hxz | hxz
            · exact absurd (hzle x ⟨⟨hx.1, lt_trans hxz hzab.2⟩, eq_of_cross
                (hcont.continuousAt (Icc_mem_nhds hx.1 hx.2)) hcx⟩) (not_le.mpr hxz)
            · rw [hxz]; exact Set.mem_insert _ _
            · exact Set.mem_insert_of_mem _ ⟨⟨hxz, hx.2⟩, hcx⟩
          · intro hx
            rcases Set.mem_insert_iff.mp hx with rfl | hx'
            · exact ⟨hzab, hcz⟩
            · exact ⟨⟨lt_trans hzab.1 hx'.1.1, hx'.1.2⟩, hx'.2⟩
        have hzni : z ∉ CrossSet f c z b := fun hx => lt_irrefl z hx.1.1
        have hcard : (CrossSet f c a b).ncard = (CrossSet f c z b).ncard + 1 := by
          rw [hSeq, Set.ncard_insert_of_notMem hzni hSzfin]
        have hRz : RPos f c z ↔ ¬ RPos f c a := by
          have h1 : RPos f c z ↔ ¬ LPos f c z := by
            have h2 := (cross_iff hzL hRaz).mp hcz
            tauto
          rw [h1, ← hLP]
        rw [hcard, Nat.even_add_one, hih, hRz]
        tauto
      · have hEq : CrossSet f c a b = CrossSet f c z b := by
          ext x
          constructor
          · rintro ⟨hx, hcx⟩
            rcases lt_trichotomy x z with hxz | hxz | hxz
            · exact absurd (hzle x ⟨⟨hx.1, lt_trans hxz hzab.2⟩, eq_of_cross
                (hcont.continuousAt (Icc_mem_nhds hx.1 hx.2)) hcx⟩) (not_le.mpr hxz)
            · exact absurd (hxz ▸ hcx) hcz
            · exact ⟨⟨hxz, hx.2⟩, hcx⟩
          · intro hx
            exact ⟨⟨lt_trans hzab.1 hx.1.1, hx.1.2⟩, hx.2⟩
        rw [hEq, hih]
        have hRz : RPos f c z ↔ RPos f c a := by
          have h1 : LPos f c z ↔ RPos f c z := by
            have h2 := (cross_iff hzL hRaz).not.mp hcz
            tauto
          rw [← h1, hLP]
        rw [hRz]

lemma parity_crossings (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (hfin : (Zeros f c a b).Finite)
    (hRa : RPos f c a ∨ RNeg f c a) (hLb : LPos f c b ∨ LNeg f c b) :
    Even (CrossSet f c a b).ncard ↔ (RPos f c a ↔ LPos f c b) :=
  parity_crossings_aux _ a b c f hab hcont hfin rfl hRa hLb

end parity

section periodic

variable {h : ℝ → ℝ}

/-- The shift by an integer is a period. -/
lemma hshift_int (hper : ∀ s : ℝ, h (s + 1) = h s) (k : ℤ) (t : ℝ) :
    h (t + k) = h t := by
  have hp : Function.Periodic h (1 : ℝ) := hper
  have hk : Function.Periodic h ((k : ℝ)) := by
    have := hp.zsmul k
    simpa using this
  exact hk t

/-- On any interval of length `1` the level set of a periodic function is finite. -/
lemma finite_zeros_Icc_of_periodic {c : ℝ}
    (hper : ∀ s : ℝ, h (s + 1) = h s)
    (hfin : ({s : ℝ | h s = c} ∩ Set.Ico (0 : ℝ) 1).Finite) {p : ℝ}
    (hp : p ∈ Set.Ico (0 : ℝ) 1) :
    ({s : ℝ | h s = c} ∩ Set.Icc p (p + 1)).Finite := by
  set Z : Set ℝ := {s : ℝ | h s = c} ∩ Set.Ico (0 : ℝ) 1 with hZdef
  have hsub : ({s : ℝ | h s = c} ∩ Set.Icc p (p + 1))
      ⊆ ⋃ z ∈ Z, ({z, z + 1, z + 2} : Set ℝ) := by
    rintro s ⟨hsc, hsIcc⟩
    have hs0 : 0 ≤ s := le_trans hp.1 hsIcc.1
    have hs2 : s ≤ 2 := by
      have h1 := hsIcc.2
      have h2 := hp.2
      linarith
    have hfr0 : 0 ≤ s - ⌊s⌋ := by rw [Int.self_sub_floor]; exact Int.fract_nonneg s
    have hfr1 : s - ⌊s⌋ < 1 := by rw [Int.self_sub_floor]; exact Int.fract_lt_one s
    have hfl0 : (0 : ℤ) ≤ ⌊s⌋ := by
      have h := Int.floor_mono hs0
      simpa using h
    have hfl2 : ⌊s⌋ ≤ (2 : ℤ) := by
      have h : (⌊s⌋ : ℝ) ≤ 2 := by
        have h3 := Int.floor_le s
        linarith
      exact_mod_cast h
    have hcases : ⌊s⌋ = 0 ∨ ⌊s⌋ = 1 ∨ ⌊s⌋ = 2 := by omega
    have hs_eq : s = (s - ⌊s⌋) + (⌊s⌋ : ℝ) := by ring
    have hh : h (s - ⌊s⌋) = c := by
      have h2 := hshift_int hper ⌊s⌋ (s - ⌊s⌋)
      rw [← hs_eq] at h2
      rw [← h2]; exact hsc
    have hmem : s ∈ ({s - ⌊s⌋, s - ⌊s⌋ + 1, s - ⌊s⌋ + 2} : Set ℝ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hcases with h0 | h1 | h2
      · left
        have hh0 : (⌊s⌋ : ℝ) = 0 := by exact_mod_cast h0
        linarith
      · right; left
        have hh1 : (⌊s⌋ : ℝ) = 1 := by exact_mod_cast h1
        linarith
      · right; right
        have hh2 : (⌊s⌋ : ℝ) = 2 := by exact_mod_cast h2
        linarith
    rw [Set.mem_iUnion]
    refine ⟨s - ⌊s⌋, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨⟨hh, ⟨hfr0, hfr1⟩⟩, hmem⟩
  have hUnion : (⋃ z ∈ Z, ({z, z + 1, z + 2} : Set ℝ)).Finite :=
    hfin.biUnion (fun z _ => ((Set.finite_singleton (z + 2)).insert (z + 1)).insert z)
  exact hUnion.subset hsub

end periodic

section shift

variable {h : ℝ → ℝ} {c x : ℝ}

lemma RPos_add_one (hper : ∀ s : ℝ, h (s + 1) = h s) :
    RPos h c (x + 1) ↔ RPos h c x := by
  constructor
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t + 1 ∈ Set.Ioo (x + 1) (x + 1 + ε) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    rwa [hper t] at h2
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t - 1 ∈ Set.Ioo x (x + ε) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    have h3 : h t = h (t - 1) := by simpa using hper (t - 1)
    rw [h3]; exact h2

lemma RNeg_add_one (hper : ∀ s : ℝ, h (s + 1) = h s) :
    RNeg h c (x + 1) ↔ RNeg h c x := by
  constructor
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t + 1 ∈ Set.Ioo (x + 1) (x + 1 + ε) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    rwa [hper t] at h2
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t - 1 ∈ Set.Ioo x (x + ε) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    have h3 : h t = h (t - 1) := by simpa using hper (t - 1)
    rw [h3]; exact h2

lemma LPos_add_one (hper : ∀ s : ℝ, h (s + 1) = h s) :
    LPos h c (x + 1) ↔ LPos h c x := by
  constructor
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t + 1 ∈ Set.Ioo (x + 1 - ε) (x + 1) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    rwa [hper t] at h2
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t - 1 ∈ Set.Ioo (x - ε) x := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    have h3 : h t = h (t - 1) := by simpa using hper (t - 1)
    rw [h3]; exact h2

lemma LNeg_add_one (hper : ∀ s : ℝ, h (s + 1) = h s) :
    LNeg h c (x + 1) ↔ LNeg h c x := by
  constructor
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t + 1 ∈ Set.Ioo (x + 1 - ε) (x + 1) := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    rwa [hper t] at h2
  · rintro ⟨ε, hε, hεp⟩
    refine ⟨ε, hε, fun t ht => ?_⟩
    have hmem : t - 1 ∈ Set.Ioo (x - ε) x := by
      rw [Set.mem_Ioo] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have h2 := hεp _ hmem
    have h3 : h t = h (t - 1) := by simpa using hper (t - 1)
    rw [h3]; exact h2

lemma Cross_add_one_iff (hper : ∀ s : ℝ, h (s + 1) = h s) :
    Cross h c (x + 1) ↔ Cross h c x := by
  have h1 := RPos_add_one (h := h) (c := c) (x := x) hper
  have h2 := RNeg_add_one (h := h) (c := c) (x := x) hper
  have h3 := LPos_add_one (h := h) (c := c) (x := x) hper
  have h4 := LNeg_add_one (h := h) (c := c) (x := x) hper
  simp only [Cross]
  tauto

end shift

/-- **Even number of sign changes.**  A continuous `1`-periodic function whose level set `{h = c}`
meets the fundamental domain `[0,1)` in finitely many points crosses the level `c`
transversally an even number of times inside `[0,1)`. -/
theorem even_sign_changes (h : ℝ → ℝ) (hc : Continuous h) (hper : ∀ s : ℝ, h (s + 1) = h s)
    (c : ℝ) (hfin : ({s : ℝ | h s = c} ∩ Set.Ico (0 : ℝ) 1).Finite) :
    Even (({s : ℝ | h s = c ∧
        (((∃ ε > 0, ∀ t ∈ Set.Ioo (s - ε) s, c < h t) ∧
            (∃ ε > 0, ∀ t ∈ Set.Ioo s (s + ε), h t < c)) ∨
          ((∃ ε > 0, ∀ t ∈ Set.Ioo (s - ε) s, h t < c) ∧
            (∃ ε > 0, ∀ t ∈ Set.Ioo s (s + ε), c < h t)))}
      ∩ Set.Ico (0 : ℝ) 1).ncard) := by
  classical
  change Even (({s : ℝ | h s = c ∧ Cross h c s} ∩ Set.Ico (0 : ℝ) 1).ncard)
  have hIco : (Set.Ico (0 : ℝ) 1).Infinite := Set.Ico_infinite (by norm_num)
  have hset : (Set.Ico (0 : ℝ) 1 \ ({s : ℝ | h s = c} ∩ Set.Ico (0 : ℝ) 1))
      = (Set.Ico (0 : ℝ) 1 \ {s : ℝ | h s = c}) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hdiff : (Set.Ico (0 : ℝ) 1 \ {s : ℝ | h s = c}).Infinite := by
    rw [← hset]
    exact hIco.sdiff hfin
  obtain ⟨p, hp⟩ := hdiff.nonempty
  have hp01 : p ∈ Set.Ico (0 : ℝ) 1 := hp.1
  have hpc : h p ≠ c := fun hh => hp.2 hh
  have hp1 : h (p + 1) = h p := hper p
  have hpne1 : h (p + 1) ≠ c := by rw [hp1]; exact hpc
  have hpfin : (Zeros h c p (p + 1)).Finite :=
    (finite_zeros_Icc_of_periodic hper hfin hp01).subset
      (fun _ hx => ⟨hx.2, ⟨hx.1.1.le, hx.1.2.le⟩⟩)
  have hcontp : ContinuousOn h (Set.Icc p (p + 1)) := hc.continuousOn
  have hpR : RPos h c p ∨ RNeg h c p :=
    RPos_or_RNeg_of_finite_zeros (lt_add_one p) hcontp hpfin
  have hpL : LPos h c (p + 1) ∨ LNeg h c (p + 1) :=
    LPos_or_LNeg_of_finite_zeros (lt_add_one p) hcontp hpfin
  have hpar := parity_crossings (f := h) (c := c) (a := p) (b := p + 1)
    (lt_add_one p) hcontp hpfin hpR hpL
  have hRp : RPos h c p ↔ c < h p := RPos_iff hc.continuousAt hpc
  have hLp : LPos h c (p + 1) ↔ c < h (p + 1) := LPos_iff hc.continuousAt hpne1
  have hEv : Even (CrossSet h c p (p + 1)).ncard :=
    hpar.mpr (by rw [hRp, hLp, hp1])
  have hTeq : ({x : ℝ | h x = c ∧ Cross h c x} ∩ Set.Ioo p (p + 1))
      = CrossSet h c p (p + 1) := by
    ext x
    constructor
    · rintro ⟨⟨hxc, hcx⟩, hx⟩
      exact ⟨hx, hcx⟩
    · rintro ⟨hx, hcx⟩
      exact ⟨⟨eq_of_cross hc.continuousAt hcx, hcx⟩, hx⟩
  have hEvT : Even ({x : ℝ | h x = c ∧ Cross h c x} ∩ Set.Ioo p (p + 1)).ncard := by
    rw [hTeq]
    exact hEv
  have hbij : Set.BijOn (fun x : ℝ => if x < p then x + 1 else x)
      ({s : ℝ | h s = c ∧ Cross h c s} ∩ Set.Ico (0 : ℝ) 1)
      ({x : ℝ | h x = c ∧ Cross h c x} ∩ Set.Ioo p (p + 1)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases hx with ⟨⟨hxc, hcx⟩, hx01⟩
      by_cases hxp : x < p
      · simp only [if_pos hxp]
        exact ⟨⟨by rw [hper x]; exact hxc, (Cross_add_one_iff hper).mpr hcx⟩, by
          rw [Set.mem_Ioo]
          exact ⟨by linarith [hp01.2, hx01.1, hxp], by linarith [hxp]⟩⟩
      · simp only [if_neg hxp]
        refine ⟨⟨hxc, hcx⟩, ?_⟩
        rw [Set.mem_Ioo]
        exact ⟨lt_of_le_of_ne (not_lt.mp hxp) (fun hh => hpc (hh ▸ hxc)),
          by linarith [hp01.1, hx01.2]⟩
    · intro x hx y hy hxy
      rcases hx with ⟨_, hx01⟩
      rcases hy with ⟨_, hy01⟩
      by_cases hxp : x < p <;> by_cases hyp : y < p
      · simp only [if_pos hxp, if_pos hyp] at hxy
        linarith
      · simp only [if_pos hxp, if_neg hyp] at hxy
        linarith [hx01.1, hy01.2]
      · simp only [if_neg hxp, if_pos hyp] at hxy
        linarith [hy01.1, hx01.2]
      · simp only [if_neg hxp, if_neg hyp] at hxy
        exact hxy
    · intro y hy
      rcases hy with ⟨⟨hyc, hcy⟩, hyIoo⟩
      by_cases hy1 : y < 1
      · refine ⟨y, ⟨⟨hyc, hcy⟩, ⟨by linarith [hyIoo.1, hp01.1], hy1⟩⟩, ?_⟩
        simp only [if_neg (not_lt.mpr hyIoo.1.le)]
      · refine ⟨y - 1, ⟨⟨?_, ?_⟩, ⟨by linarith, by linarith [hyIoo.2, hp01.2]⟩⟩, ?_⟩
        · have h' : h y = h (y - 1) := by simpa using hper (y - 1)
          rw [← h']; exact hyc
        · have hcy' : Cross h c ((y - 1) + 1) := by rw [sub_add_cancel]; exact hcy
          exact (Cross_add_one_iff hper).mp hcy'
        · have hylt : y - 1 < p := by linarith [hyIoo.2]
          simp only [if_pos hylt]
          ring
  have hncard : ({s : ℝ | h s = c ∧ Cross h c s} ∩ Set.Ico (0 : ℝ) 1).ncard
      = ({x : ℝ | h x = c ∧ Cross h c x} ∩ Set.Ioo p (p + 1)).ncard := hbij.ncard_eq
  exact hncard.symm ▸ hEvT

end Work.ELRig
