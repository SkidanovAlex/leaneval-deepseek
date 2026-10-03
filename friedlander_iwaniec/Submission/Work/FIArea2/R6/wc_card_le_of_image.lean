import Mathlib
import Submission.Work.FIArea2.R6.fibre_card_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2.R6

/-- **One-dimensional fibre bound transported along an injective map.**

Let `T` be a finite set of integer vectors, `g : ℤ × ℤ → ℤ` injective on `T`, whose values on `T`
are bounded by `t` in absolute value and are pairwise congruent modulo a positive `c`
(`c ∣ g w - g w'`). Then `#T ≤ 2t/c + 1`.

This is the image-form of `Work.FIArea2.R6.fibre_card_le`: `T.card = (T.image g).card`, the image
lies in `[-t,t]` and is contained in a single residue class mod `c`, so the fibre bound
`fibre_card_le t c (T.image g) …` gives the claim. -/
theorem wc_card_le_of_image (t c : ℕ) (hc : c ≠ 0) (T : Finset (ℤ × ℤ)) (g : ℤ × ℤ → ℤ)
    (hinj : Set.InjOn g ↑T)
    (hbdd : ∀ w ∈ T, (g w).natAbs ≤ t)
    (hdvd : ∀ w ∈ T, ∀ w' ∈ T, (c : ℤ) ∣ g w - g w') :
    (T.card : ℝ) ≤ 2 * (t : ℝ) / (c : ℝ) + 1 := by
  classical
  -- `c` is nonzero, so `ZMod c` has the `NeZero` instance `fibre_card_le` asks for.
  have hNc : NeZero c := ⟨hc⟩
  -- Push `T` forward along the injective map `g`; this does not change the cardinality.
  set S : Finset ℤ := T.image g with hS
  have hcard : T.card = S.card := (Finset.card_image_of_injOn hinj).symm
  have hbddS : ∀ h ∈ S, h.natAbs ≤ t := by
    intro h hh
    rw [hS, Finset.mem_image] at hh
    obtain ⟨w, hw, rfl⟩ := hh
    exact hbdd w hw
  rcases Finset.eq_empty_or_nonempty T with hemp | hne
  · rw [hemp, Finset.card_empty, Nat.cast_zero]; positivity
  · -- Pick a base point; by `hdvd` every value of `g` on `T` is congruent to it mod `c`,
    -- so `S` is entirely contained in the corresponding fibre of the reduction map.
    obtain ⟨w0, hw0⟩ := hne
    set r : ZMod c := (g w0 : ZMod c) with hr
    have hfilter : S.filter (fun (h : ℤ) => (h : ZMod c) = r) = S := by
      apply Finset.filter_true_of_mem
      intro h hh
      rw [hS, Finset.mem_image] at hh
      obtain ⟨w, hw, rfl⟩ := hh
      rw [hr, ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
      have h : (c : ℤ) ∣ -((g w) - (g w0)) := dvd_neg.mpr (hdvd w hw w0 hw0)
      rwa [neg_sub] at h
    have hfib := fibre_card_le t c S hbddS r
    rw [hfilter] at hfib
    rw [hcard]
    exact hfib

end Work.FIArea2.R6
