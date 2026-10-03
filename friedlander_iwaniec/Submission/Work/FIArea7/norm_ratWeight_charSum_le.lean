import Mathlib
import Submission.Work.FIArea7.GaussUnitClass
import Submission.Work.FIArea7.Section16Expansion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- The weight `ratWeight Q e` is bounded by `1` in absolute value: it is `0` off the rational
classes and a Jacobi symbol (`∈ {-1,0,1}`) on them. -/
lemma norm_ratWeight_le_one (Q e : ℕ) (p : GaussUnit Q) : ‖ratWeight Q e p‖ ≤ 1 := by
  by_cases h : p.1.2 = 0
  · rw [ratWeight, if_pos h, Complex.norm_intCast]
    rcases jacobiSym.trichotomy (p.1.1.val : ℤ) e with hh | hh | hh <;> rw [hh] <;> norm_num
  · rw [ratWeight, if_neg h, norm_zero]; norm_num

/-- The set of `p ∈ G` on which `ratWeight` can be nonzero — the rational classes `(r, 0)` — has
at most `Q` elements, since `p ↦ p.1.1` injects it into `ZMod Q`. -/
lemma card_ratWeight_support_le (Q : ℕ) [NeZero Q] :
    (Finset.univ.filter (fun p : GaussUnit Q => p.1.2 = 0)).card ≤ Q := by
  classical
  set s : Finset (GaussUnit Q) := Finset.univ.filter (fun p => p.1.2 = 0) with hs
  have hinj : Set.InjOn (fun p : GaussUnit Q => p.1.1) ↑s := by
    intro p hp p' hp' heq
    have hp2 : p.1.2 = 0 := by
      have := hp; rw [Finset.mem_coe, hs, Finset.mem_filter] at this; exact this.2
    have hp'2 : p'.1.2 = 0 := by
      have := hp'; rw [Finset.mem_coe, hs, Finset.mem_filter] at this; exact this.2
    exact Subtype.ext (by ext <;> simp_all)
  have h1 : s.card = (s.image (fun p : GaussUnit Q => p.1.1)).card :=
    (Finset.card_image_of_injOn hinj).symm
  rw [h1]
  calc (s.image (fun p : GaussUnit Q => p.1.1)).card
      ≤ (Finset.univ : Finset (ZMod Q)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = Q := by rw [Finset.card_univ, ZMod.card]

theorem norm_ratWeight_charSum_le (Q e : ℕ) [NeZero Q]
    (χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ) :
    ‖∑ p : Work.FIArea7.GaussUnit Q, Work.FIArea7.ratWeight Q e p * χ (Additive.ofMul p)‖ ≤ Q := by
  classical
  set s : Finset (GaussUnit Q) := Finset.univ.filter (fun p => p.1.2 = 0) with hs
  -- `ratWeight` vanishes off the rational classes
  have hsupp : ∀ p : GaussUnit Q, p ∉ s → ratWeight Q e p = 0 := by
    intro p hp
    have h2 : p.1.2 ≠ 0 := by
      intro h
      exact hp (by rw [hs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    simp only [ratWeight, if_neg h2]
  have hsum : ∑ p : GaussUnit Q, ratWeight Q e p * χ (Additive.ofMul p)
      = ∑ p ∈ s, ratWeight Q e p * χ (Additive.ofMul p) := by
    rw [← Finset.sum_subset (Finset.subset_univ s)]
    intro p _ hp
    rw [hsupp p hp, zero_mul]
  have hbound : ‖∑ p ∈ s, ratWeight Q e p * χ (Additive.ofMul p)‖ ≤ (s.card : ℝ) := by
    calc ‖∑ p ∈ s, ratWeight Q e p * χ (Additive.ofMul p)‖
        ≤ ∑ p ∈ s, ‖ratWeight Q e p * χ (Additive.ofMul p)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ s, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro p _
          rw [norm_mul, AddChar.norm_apply, mul_one]
          exact norm_ratWeight_le_one Q e p
      _ = (s.card : ℝ) := by simp
  have hcard : s.card ≤ Q := by
    rw [hs]; exact card_ratWeight_support_le Q
  calc ‖∑ p : GaussUnit Q, ratWeight Q e p * χ (Additive.ofMul p)‖
      = ‖∑ p ∈ s, ratWeight Q e p * χ (Additive.ofMul p)‖ := by rw [hsum]
    _ ≤ (s.card : ℝ) := hbound
    _ ≤ (Q : ℝ) := by exact_mod_cast hcard

end Work.FIArea7
