import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG1.OneDim

open WilkiesDesign

/-! ## 1. Eventual bound sets for difference quotients -/

/-- Right quotients are eventually `≤ r`. -/
def evRle (g : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  {x | ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x < y → y < x + δ → g y - g x ≤ r * (y - x)}

/-- Right quotients are eventually `≥ r`. -/
def evRge (g : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  {x | ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x < y → y < x + δ → r * (y - x) ≤ g y - g x}

/-- Left quotients are eventually `≥ r`. -/
def evLge (g : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  {x | ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x - δ < y → y < x → g y - g x ≤ r * (y - x)}

/-- Left quotients are eventually `≤ r`. -/
def evLle (g : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  {x | ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x - δ < y → y < x → r * (y - x) ≤ g y - g x}

/-- Right quotients are eventually `< r`. -/
def evRlt (g : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  {x | ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x < y → y < x + δ → g y - g x < r * (y - x)}

/-- Right quotients are eventually `> r`. -/
def evRgt (g : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  {x | ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x < y → y < x + δ → r * (y - x) < g y - g x}

/-- Left quotients are eventually `> r`. -/
def evLgt (g : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  {x | ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x - δ < y → y < x → g y - g x < r * (y - x)}

/-- Left quotients are eventually `< r`. -/
def evLlt (g : ℝ → ℝ) (r : ℝ) : Set ℝ :=
  {x | ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, x - δ < y → y < x → r * (y - x) < g y - g x}

/-! ## 2. Arithmetic of the difference quotient -/

section DQ

variable {g : ℝ → ℝ} {x y q : ℝ}

theorem lt_dq_iff (h : x < y) : q < dq g x y ↔ q * (y - x) < g y - g x := by
  rw [dq, lt_div_iff₀ (by linarith)]

theorem dq_lt_iff (h : x < y) : dq g x y < q ↔ g y - g x < q * (y - x) := by
  rw [dq, div_lt_iff₀ (by linarith)]

theorem lt_dq_iff_of_lt (h : y < x) : q < dq g x y ↔ g y - g x < q * (y - x) := by
  rw [dq, lt_div_iff_of_neg (by linarith)]

theorem dq_lt_iff_of_lt (h : y < x) : dq g x y < q ↔ q * (y - x) < g y - g x := by
  rw [dq, div_lt_iff_of_neg (by linarith)]

theorem le_dq_iff (h : x < y) : q ≤ dq g x y ↔ q * (y - x) ≤ g y - g x := by
  rw [dq, le_div_iff₀ (by linarith)]

theorem dq_le_iff (h : x < y) : dq g x y ≤ q ↔ g y - g x ≤ q * (y - x) := by
  rw [dq, div_le_iff₀ (by linarith)]

theorem le_dq_iff_of_lt (h : y < x) : q ≤ dq g x y ↔ g y - g x ≤ q * (y - x) := by
  rw [dq, le_div_iff_of_neg (by linarith)]

theorem dq_le_iff_of_lt (h : y < x) : dq g x y ≤ q ↔ q * (y - x) ≤ g y - g x := by
  rw [dq, div_le_iff_of_neg (by linarith)]

end DQ

/-! ## 3. Monotonicity of the eventual bound sets in the parameter -/

section Mono

variable {g : ℝ → ℝ} {r r' : ℝ}

theorem evRle_mono (h : r ≤ r') : evRle g r ⊆ evRle g r' := by
  rintro x ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun y hy1 hy2 =>
    le_trans (hx y hy1 hy2) (mul_le_mul_of_nonneg_right h (by linarith))⟩

theorem evRge_anti (h : r ≤ r') : evRge g r' ⊆ evRge g r := by
  rintro x ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun y hy1 hy2 =>
    le_trans (mul_le_mul_of_nonneg_right h (by linarith)) (hx y hy1 hy2)⟩

theorem evLle_mono (h : r ≤ r') : evLle g r ⊆ evLle g r' := by
  rintro x ⟨δ, hδ, hx⟩
  refine ⟨δ, hδ, fun y hy1 hy2 => le_trans ?_ (hx y hy1 hy2)⟩
  have hneg : y - x ≤ 0 := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (neg_nonneg.mpr hneg)]

theorem evLge_anti (h : r ≤ r') : evLge g r' ⊆ evLge g r := by
  rintro x ⟨δ, hδ, hx⟩
  refine ⟨δ, hδ, fun y hy1 hy2 => le_trans (hx y hy1 hy2) ?_⟩
  have hneg : y - x ≤ 0 := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (neg_nonneg.mpr hneg)]

theorem evRlt_mono (h : r ≤ r') : evRlt g r ⊆ evRlt g r' := by
  rintro x ⟨δ, hδ, hx⟩
  refine ⟨δ, hδ, fun y hy1 hy2 => lt_of_lt_of_le (hx y hy1 hy2) ?_⟩
  exact mul_le_mul_of_nonneg_right h (by linarith)

theorem evRgt_anti (h : r ≤ r') : evRgt g r' ⊆ evRgt g r := by
  rintro x ⟨δ, hδ, hx⟩
  refine ⟨δ, hδ, fun y hy1 hy2 => lt_of_le_of_lt ?_ (hx y hy1 hy2)⟩
  exact mul_le_mul_of_nonneg_right h (by linarith)

theorem evLlt_mono (h : r ≤ r') : evLlt g r ⊆ evLlt g r' := by
  rintro x ⟨δ, hδ, hx⟩
  refine ⟨δ, hδ, fun y hy1 hy2 => lt_of_le_of_lt ?_ (hx y hy1 hy2)⟩
  have hneg : y - x ≤ 0 := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (neg_nonneg.mpr hneg)]

theorem evLgt_anti (h : r ≤ r') : evLgt g r' ⊆ evLgt g r := by
  rintro x ⟨δ, hδ, hx⟩
  refine ⟨δ, hδ, fun y hy1 hy2 => lt_of_lt_of_le (hx y hy1 hy2) ?_⟩
  have hneg : y - x ≤ 0 := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (neg_nonneg.mpr hneg)]

theorem evRlt_subset_evRle : evRlt g r ⊆ evRle g r := by
  rintro x ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun y hy1 hy2 => le_of_lt (hx y hy1 hy2)⟩

theorem evRgt_subset_evRge : evRgt g r ⊆ evRge g r := by
  rintro x ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun y hy1 hy2 => le_of_lt (hx y hy1 hy2)⟩

theorem evLgt_subset_evLge : evLgt g r ⊆ evLge g r := by
  rintro x ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun y hy1 hy2 => le_of_lt (hx y hy1 hy2)⟩

theorem evLlt_subset_evLle : evLlt g r ⊆ evLle g r := by
  rintro x ⟨δ, hδ, hx⟩
  exact ⟨δ, hδ, fun y hy1 hy2 => le_of_lt (hx y hy1 hy2)⟩

theorem evRle_subset_evRlt (h : r < r') : evRle g r ⊆ evRlt g r' := by
  rintro x ⟨δ, hδ, hx⟩
  refine ⟨δ, hδ, fun y hy1 hy2 => lt_of_le_of_lt (hx y hy1 hy2) ?_⟩
  exact mul_lt_mul_of_pos_right h (by linarith)

theorem evRge_subset_evRgt (h : r' < r) : evRge g r ⊆ evRgt g r' := by
  rintro x ⟨δ, hδ, hx⟩
  refine ⟨δ, hδ, fun y hy1 hy2 => lt_of_lt_of_le ?_ (hx y hy1 hy2)⟩
  exact mul_lt_mul_of_pos_right h (by linarith)

theorem evLle_subset_evLlt (h : r < r') : evLle g r ⊆ evLlt g r' := by
  rintro x ⟨δ, hδ, hx⟩
  refine ⟨δ, hδ, fun y hy1 hy2 => lt_of_lt_of_le ?_ (hx y hy1 hy2)⟩
  have hneg : y - x < 0 := by linarith
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr h) hneg]

theorem evLge_subset_evLgt (h : r' < r) : evLge g r ⊆ evLgt g r' := by
  rintro x ⟨δ, hδ, hx⟩
  refine ⟨δ, hδ, fun y hy1 hy2 => lt_of_le_of_lt (hx y hy1 hy2) ?_⟩
  have hneg : y - x < 0 := by linarith
  nlinarith [mul_pos_of_neg_of_neg (sub_neg.mpr h) hneg]

/-- If both `evRle s` and `evRge r` hold at `x`, then `r ≤ s`. -/
theorem evRge_le_of_mem {s x : ℝ} (hs : x ∈ evRle g s) (hr : x ∈ evRge g r) : r ≤ s := by
  obtain ⟨δ₁, h₁, h₁'⟩ := hs
  obtain ⟨δ₂, h₂, h₂'⟩ := hr
  have hmin : 0 < min δ₁ δ₂ := lt_min h₁ h₂
  have hy : x < x + min δ₁ δ₂ / 2 := by linarith
  have hy' : x + min δ₁ δ₂ / 2 < x + δ₁ := by
    have := min_le_left δ₁ δ₂; linarith
  have hy'' : x + min δ₁ δ₂ / 2 < x + δ₂ := by
    have := min_le_right δ₁ δ₂; linarith
  have h1 := h₁' _ hy hy'
  have h2 := h₂' _ hy hy''
  nlinarith [h1, h2]

/-- If both `evLle s` and `evLge r` hold at `x`, then `r ≤ s`. -/
theorem evLge_le_of_mem {s x : ℝ} (hs : x ∈ evLle g s) (hr : x ∈ evLge g r) : r ≤ s := by
  obtain ⟨δ₁, h₁, h₁'⟩ := hs
  obtain ⟨δ₂, h₂, h₂'⟩ := hr
  have hmin : 0 < min δ₁ δ₂ := lt_min h₁ h₂
  have hy : x - min δ₁ δ₂ / 2 < x := by linarith
  have hy' : x - δ₁ < x - min δ₁ δ₂ / 2 := by
    have := min_le_left δ₁ δ₂; linarith
  have hy'' : x - δ₂ < x - min δ₁ δ₂ / 2 := by
    have := min_le_right δ₁ δ₂; linarith
  have h1 := h₁' _ hy' hy
  have h2 := h₂' _ hy'' hy
  have hneg : (x - min δ₁ δ₂ / 2) - x ≤ 0 := by linarith
  nlinarith [h1, h2]

end Mono

/-! ## 4. The two trichotomies -/

/-- **Right trichotomy.**  If at every rational level the right difference quotients are
eventually on one side of that level, then either they tend to `+∞`, or to `-∞`, or to a
finite limit. -/
theorem right_trichotomy {g : ℝ → ℝ} {x : ℝ}
    (hgood : ∀ r : ℚ, x ∈ evRle g (r : ℝ) ∨ x ∈ evRge g (r : ℝ)) :
    (∀ M : ℚ, 0 < M → x ∈ evRgt g (M : ℝ)) ∨
      (∀ M : ℚ, 0 < M → x ∈ evRlt g (-(M : ℝ))) ∨
      (∃ L : ℝ, ∀ r s : ℚ, (r : ℝ) < L → L < (s : ℝ) →
        x ∈ evRge g (r : ℝ) ∧ x ∈ evRle g (s : ℝ)) := by
  by_cases h1 : ∀ r : ℚ, x ∈ evRge g (r : ℝ)
  · left
    intro M hM
    have hmem := h1 (M + 1)
    have hcast : ((M + 1 : ℚ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hmem
    obtain ⟨δ, hδ, hδ'⟩ := hmem
    refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
    have hlt : (M : ℝ) * (y - x) < ((M : ℝ) + 1) * (y - x) := by
      have : 0 < y - x := by linarith
      nlinarith
    exact lt_of_lt_of_le hlt (hδ' y hy1 hy2)
  · push_neg at h1
    obtain ⟨r₀, hr₀⟩ := h1
    have hr₀' : x ∈ evRle g (r₀ : ℝ) := (hgood r₀).resolve_right hr₀
    by_cases h2 : ∀ M : ℚ, 0 < M → x ∈ evRlt g (-(M : ℝ))
    · exact Or.inr (Or.inl h2)
    · push_neg at h2
      obtain ⟨M₀, hM₀, hM₀'⟩ := h2
      have hlb : ∀ r : ℝ, x ∈ evRle g r → -(M₀ : ℝ) ≤ r := by
        intro r hr
        by_contra hcon
        have hlt : r < -(M₀ : ℝ) := lt_of_not_ge hcon
        obtain ⟨δ, hδ, hδ'⟩ := hr
        refine hM₀' ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
        have h1' := hδ' y hy1 hy2
        have hpos : 0 < y - x := by linarith
        nlinarith [h1', hlt]
      set S : Set ℝ := {r : ℝ | x ∈ evRle g r} with hS
      have hSne : S.Nonempty := ⟨(r₀ : ℝ), hr₀'⟩
      have hbdd : BddBelow S := ⟨-(M₀ : ℝ), fun r hr => hlb r hr⟩
      refine Or.inr (Or.inr ⟨sInf S, ?_⟩)
      intro r s hrs hLs
      constructor
      · by_contra hcon
        have hmem : (r : ℝ) ∈ S := (hgood r).resolve_right hcon
        have := csInf_le hbdd hmem
        linarith
      · by_contra hcon
        have hle : ∀ t ∈ S, (s : ℝ) ≤ t := by
          intro t ht
          by_contra hts
          have hts' : t < (s : ℝ) := lt_of_not_ge hts
          exact hcon (evRle_mono (le_of_lt hts') ht)
        have := le_csInf hSne hle
        linarith

/-- **Left trichotomy.**  The mirror of `right_trichotomy`. -/
theorem left_trichotomy {g : ℝ → ℝ} {x : ℝ}
    (hgood : ∀ r : ℚ, x ∈ evLle g (r : ℝ) ∨ x ∈ evLge g (r : ℝ)) :
    (∀ M : ℚ, 0 < M → x ∈ evLgt g (M : ℝ)) ∨
      (∀ M : ℚ, 0 < M → x ∈ evLlt g (-(M : ℝ))) ∨
      (∃ L : ℝ, ∀ r s : ℚ, (r : ℝ) < L → L < (s : ℝ) →
        x ∈ evLge g (r : ℝ) ∧ x ∈ evLle g (s : ℝ)) := by
  by_cases h1 : ∀ r : ℚ, x ∈ evLge g (r : ℝ)
  · left
    intro M hM
    have hmem := h1 (M + 1)
    have hcast : ((M + 1 : ℚ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hmem
    obtain ⟨δ, hδ, hδ'⟩ := hmem
    refine ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
    have hlt : ((M : ℝ) + 1) * (y - x) < (M : ℝ) * (y - x) := by
      have : y - x < 0 := by linarith
      nlinarith
    exact lt_of_le_of_lt (hδ' y hy1 hy2) hlt
  · push_neg at h1
    obtain ⟨r₀, hr₀⟩ := h1
    have hr₀' : x ∈ evLle g (r₀ : ℝ) := (hgood r₀).resolve_right hr₀
    by_cases h2 : ∀ M : ℚ, 0 < M → x ∈ evLlt g (-(M : ℝ))
    · exact Or.inr (Or.inl h2)
    · push_neg at h2
      obtain ⟨M₀, hM₀, hM₀'⟩ := h2
      have hlb : ∀ r : ℝ, x ∈ evLle g r → -(M₀ : ℝ) ≤ r := by
        intro r hr
        by_contra hcon
        have hlt : r < -(M₀ : ℝ) := lt_of_not_ge hcon
        obtain ⟨δ, hδ, hδ'⟩ := hr
        refine hM₀' ⟨δ, hδ, fun y hy1 hy2 => ?_⟩
        have h1' := hδ' y hy1 hy2
        have hyx : y - x < 0 := by linarith
        nlinarith [h1', hlt]
      set S : Set ℝ := {r : ℝ | x ∈ evLle g r} with hS
      have hSne : S.Nonempty := ⟨(r₀ : ℝ), hr₀'⟩
      have hbdd : BddBelow S := ⟨-(M₀ : ℝ), fun r hr => hlb r hr⟩
      refine Or.inr (Or.inr ⟨sInf S, ?_⟩)
      intro r s hrs hLs
      constructor
      · by_contra hcon
        have hmem : (r : ℝ) ∈ S := (hgood r).resolve_right hcon
        have := csInf_le hbdd hmem
        linarith
      · by_contra hcon
        have hle : ∀ t ∈ S, (s : ℝ) ≤ t := by
          intro t ht
          by_contra hts
          have hts' : t < (s : ℝ) := lt_of_not_ge hts
          exact hcon (evLle_mono (le_of_lt hts') ht)
        have := le_csInf hSne hle
        linarith

end Work.WilG1.OneDim
