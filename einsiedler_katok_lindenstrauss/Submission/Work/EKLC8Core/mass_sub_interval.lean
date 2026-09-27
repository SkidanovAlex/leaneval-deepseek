import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

open MeasureTheory

/-- A measurable set `B ⊆ [L,R]` whose measure is at least `(1-ε)(R-L)` covers all but
`ε(R-L)` of `[L,R]`; consequently it covers all but an error at most `ε(R-L)` of any
sub-interval `[p,q]`.  This is the quantitative "density survives on sub-intervals" step
used to localise the low-entropy computation to a small interval. -/
theorem mass_sub_interval {L R p q ε : ℝ} (hLp : L ≤ p) (hpq : p ≤ q) (hqR : q ≤ R)
    {B : Set ℝ} (hBm : MeasurableSet B) (hB : B ⊆ Set.Icc L R) (hε : 0 ≤ ε)
    (hdens : (1 - ε) * (R - L) ≤ Work.EKLC8Core.vol B) :
    (q - p) - ε * (R - L) ≤ Work.EKLC8Core.vol (B ∩ Set.Icc p q) := by
  have hLR : L ≤ R := le_trans hLp (le_trans hpq hqR)
  have hIccsub : Set.Icc p q ⊆ Set.Icc L R := Set.Icc_subset_Icc hLp hqR
  have hfinLR : volume (Set.Icc L R) ≠ ⊤ := volume_ne_top_of_subset_Icc subset_rfl
  -- `B` can lose at most `(p-L)+(R-q)` of its mass outside `[p,q]`.
  have hout : vol (B \ Set.Icc p q) ≤ (p - L) + (R - q) := by
    have hsub : B \ Set.Icc p q ⊆ Set.Icc L R \ Set.Icc p q := by
      intro x hx; exact ⟨hB hx.1, hx.2⟩
    have hfin : volume (Set.Icc L R \ Set.Icc p q) ≠ ⊤ :=
      volume_ne_top_of_subset_Icc Set.sdiff_subset
    have hmono := vol_mono hsub hfin
    have hsd := vol_sdiff hIccsub measurableSet_Icc hfinLR
    rw [vol_Icc hLR, vol_Icc hpq] at hsd
    rw [hsd] at hmono
    linarith
  -- split `B` into its part inside and outside `[p,q]`.
  have hdisj : Disjoint (B \ Set.Icc p q) (B ∩ Set.Icc p q) := by
    rw [Set.disjoint_iff]
    intro x hx
    exact hx.1.2 hx.2.2
  have htm : MeasurableSet (B ∩ Set.Icc p q) := hBm.inter measurableSet_Icc
  have hsm : volume (B \ Set.Icc p q) ≠ ⊤ :=
    volume_ne_top_of_subset_Icc (fun x hx => hB hx.1)
  have htm' : volume (B ∩ Set.Icc p q) ≠ ⊤ :=
    volume_ne_top_of_subset_Icc (fun x hx => hB hx.1)
  have hdec := vol_union hdisj htm hsm htm'
  have hunion : (B \ Set.Icc p q) ∪ (B ∩ Set.Icc p q) = B := by
    ext x; constructor
    · intro hx
      rcases hx with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
    · intro hx
      by_cases h : x ∈ Set.Icc p q
      · exact Or.inr ⟨hx, h⟩
      · exact Or.inl ⟨hx, h⟩
  rw [hunion] at hdec
  -- `(1-ε)(R-L) - ((p-L)+(R-q)) = (q-p) - ε(R-L)`
  have harith : (1 - ε) * (R - L) - ((p - L) + (R - q)) = (q - p) - ε * (R - L) := by ring
  linarith

end Work.EKLC8Core
