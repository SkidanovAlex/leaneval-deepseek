import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.EllipticEst.Core.i0Aux

/-- Splitting a set integral over an open interval into the three adjacent open
sub-intervals.  The sets `Ioo a d` and `Ioo a b ∪ Ioo b c ∪ Ioo c d` differ by the
end-point two-point set `{b, c}`, which is null. -/
theorem setIntegral_Ioo_split3 {f : ℝ → ℝ} {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo a d)) :
    (∫ x in Set.Ioo a d, f x)
      = (∫ x in Set.Ioo a b, f x) + (∫ x in Set.Ioo b c, f x) + (∫ x in Set.Ioo c d, f x) := by
  have hsub_ab : Set.Ioo a b ⊆ Set.Ioo a d := fun x hx => ⟨hx.1, lt_trans hx.2 (lt_trans hbc hcd)⟩
  have hsub_bc : Set.Ioo b c ⊆ Set.Ioo a d := fun x hx => ⟨lt_trans hab hx.1, lt_trans hx.2 hcd⟩
  have hsub_cd : Set.Ioo c d ⊆ Set.Ioo a d := fun x hx => ⟨lt_trans (lt_trans hab hbc) hx.1, hx.2⟩
  have hInt_ab : MeasureTheory.IntegrableOn f (Set.Ioo a b) := hf.mono_set hsub_ab
  have hInt_bc : MeasureTheory.IntegrableOn f (Set.Ioo b c) := hf.mono_set hsub_bc
  have hInt_cd : MeasureTheory.IntegrableOn f (Set.Ioo c d) := hf.mono_set hsub_cd
  have hInt_abbc : MeasureTheory.IntegrableOn f (Set.Ioo a b ∪ Set.Ioo b c) :=
    hf.mono_set (Set.union_subset hsub_ab hsub_bc)
  have hdisj1 : Disjoint (Set.Ioo a b) (Set.Ioo b c) := by
    rw [Set.disjoint_left]; intro x hx1 hx2; linarith [hx1.2, hx2.1]
  have hdisj2 : Disjoint (Set.Ioo a b ∪ Set.Ioo b c) (Set.Ioo c d) := by
    rw [Set.disjoint_left]; intro x hx1 hx2
    rcases hx1 with hx1 | hx1 <;> linarith [hx1.1, hx1.2, hx2.1]
  have h1 : ∫ x in (Set.Ioo a b ∪ Set.Ioo b c), f x
      = (∫ x in Set.Ioo a b, f x) + ∫ x in Set.Ioo b c, f x :=
    MeasureTheory.setIntegral_union hdisj1 measurableSet_Ioo hInt_ab hInt_bc
  have h2 : ∫ x in ((Set.Ioo a b ∪ Set.Ioo b c) ∪ Set.Ioo c d), f x
      = (∫ x in (Set.Ioo a b ∪ Set.Ioo b c), f x) + ∫ x in Set.Ioo c d, f x :=
    MeasureTheory.setIntegral_union hdisj2 measurableSet_Ioo hInt_abbc hInt_cd
  have hbnot : b ∉ (Set.Ioo a b ∪ Set.Ioo b c ∪ Set.Ioo c d) := by
    intro hb
    rcases hb with (h | h) | h
    · exact absurd h.2 (lt_irrefl b)
    · exact absurd h.1 (lt_irrefl b)
    · exact absurd h.1 (not_lt.mpr (le_of_lt hbc))
  have hcnot : c ∉ (Set.Ioo a b ∪ Set.Ioo b c ∪ Set.Ioo c d) := by
    intro hc
    rcases hc with (h | h) | h
    · exact absurd h.2 (not_lt.mpr (le_of_lt hbc))
    · exact absurd h.2 (lt_irrefl c)
    · exact absurd h.1 (lt_irrefl c)
  have hdiff : Set.Ioo a d \ (Set.Ioo a b ∪ Set.Ioo b c ∪ Set.Ioo c d) = {b, c} := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxd, hxU⟩ := hx
      by_contra hcon
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hcon
      push Not at hcon
      rcases lt_trichotomy x b with h | h | h
      · exact hxU (Or.inl (Or.inl ⟨hxd.1, h⟩))
      · exact hcon.1 h
      · rcases lt_trichotomy x c with h2 | h2 | h2
        · exact hxU (Or.inl (Or.inr ⟨h, h2⟩))
        · exact hcon.2 h2
        · exact hxU (Or.inr ⟨h2, hxd.2⟩)
    · intro hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hxb | hxc
      · rw [hxb]
        exact ⟨⟨hab, lt_trans hbc hcd⟩, hbnot⟩
      · rw [hxc]
        exact ⟨⟨lt_trans hab hbc, hcd⟩, hcnot⟩
  have hmeas : volume (Set.Ioo a d \ (Set.Ioo a b ∪ Set.Ioo b c ∪ Set.Ioo c d)) = 0 := by
    rw [hdiff, Set.insert_eq]
    exact measure_union_null (Real.volume_singleton) (Real.volume_singleton)
  have hUsub : (Set.Ioo a b ∪ Set.Ioo b c ∪ Set.Ioo c d) ⊆ Set.Ioo a d :=
    Set.union_subset (Set.union_subset hsub_ab hsub_bc) hsub_cd
  have hUdiff : volume ((Set.Ioo a b ∪ Set.Ioo b c ∪ Set.Ioo c d) \ Set.Ioo a d) = 0 := by
    rw [Set.sdiff_eq_empty.mpr hUsub]
    exact measure_empty
  have hae : Set.Ioo a d =ᵐ[volume] (Set.Ioo a b ∪ Set.Ioo b c ∪ Set.Ioo c d) :=
    MeasureTheory.ae_eq_set.mpr ⟨hmeas, hUdiff⟩
  rw [MeasureTheory.setIntegral_congr_set hae, h2, h1]

end Work.EllipticEst.Core.i0Aux
