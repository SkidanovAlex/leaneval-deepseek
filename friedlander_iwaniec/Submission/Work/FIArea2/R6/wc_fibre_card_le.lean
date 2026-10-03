import Mathlib
import Submission.Work.FIArea2.R6.WCbasicDefs
import Submission.Work.FIArea2.R6.wc_card_le_of_image

namespace Work.FIArea2.R6

/-!
# Fibres of a lattice line inside the sup-norm box

`Work.FIArea2.R6.wc_fibre_card_le`: a set `T` of integer vectors in `wcBox t = [-t,t]²` whose
elements are pairwise congruent modulo a nonzero direction `v` (`w - w' = k • v`) has at most
`2t/|v|∞ + 1` elements.

PROOF ROUTE.  Choose a coordinate `i ∈ {1,2}` with `|vᵢ| = |v|∞ =: c` (which exists by
`max_choice`; `c ≠ 0` because `v ≠ 0`).  The projection `w ↦ wᵢ` is injective on `T`: if
`wᵢ = wᵢ'` then `k vᵢ = 0`, hence `k = 0` (as `vᵢ ≠ 0`), hence `w = w'`.  Its values lie in
`[-t,t]` (`hbox`) and are pairwise congruent modulo `c` (`c ∣ vᵢ` and `wᵢ - wᵢ' = k vᵢ`).
The one-dimensional fibre bound `wc_card_le_of_image` (the image form of `fibre_card_le`) applied
to that projection gives `#T ≤ 2t/c + 1 = 2t/|v|∞ + 1`. -/

/-- **Fibres of the direction `v` inside the box are small.**

A set `T ⊆ [-t,t]²` of integer vectors with all pairwise differences integral multiples of a
nonzero `v` has at most `2t / |v|∞ + 1` elements.

Let `c = |v|∞ = max |v₁| |v₂| ≥ 1`.  A coordinate `i` with `|vᵢ| = c` exists; the projection onto
it is injective on `T` (a vanishing difference `k vᵢ = 0` forces `k = 0`, hence the vectors are
equal) and takes values in one residue class modulo `c` inside `[-t,t]`.  The image therefore
contributes at most `2t/c + 1` elements, which is the claim. -/
theorem wc_fibre_card_le (t : ℕ) (v : ℤ × ℤ) (hv0 : v ≠ 0) (T : Finset (ℤ × ℤ))
    (hbox : ∀ w ∈ T, w ∈ wcBox t)
    (hdiff : ∀ w ∈ T, ∀ w' ∈ T, ∃ k : ℤ, w.1 - w'.1 = k * v.1 ∧ w.2 - w'.2 = k * v.2) :
    (T.card : ℝ) ≤ 2 * (t : ℝ) / (wcSup v : ℝ) + 1 := by
  classical
  -- The direction `v` is nonzero, so its sup-norm `c` is nonzero.
  have hc0 : wcSup v ≠ 0 := by
    intro h
    have h' : max v.1.natAbs v.2.natAbs = 0 := h
    rw [Nat.max_eq_zero_iff] at h'
    exact hv0 (Prod.ext (Int.natAbs_eq_zero.mp h'.1) (Int.natAbs_eq_zero.mp h'.2))
  -- Pick a coordinate realising the sup-norm.
  rcases max_choice v.1.natAbs v.2.natAbs with hmax | hmax
  · -- `|v₁| = |v|∞` : project onto the first coordinate.
    have hcmax : wcSup v = v.1.natAbs := hmax
    have hv1 : v.1 ≠ 0 := by
      intro h
      have h0 : v.1.natAbs = 0 := by rw [h]; rfl
      exact hc0 (by rw [hcmax, h0])
    refine wc_card_le_of_image t (wcSup v) hc0 T (fun w => w.1) ?_ ?_ ?_
    · -- injectivity of the first projection on `T`
      intro a ha b hb hab
      obtain ⟨k, hk1, hk2⟩ := hdiff a ha b hb
      change a.1 = b.1 at hab
      have hk1' : k * v.1 = 0 := by rw [← hk1, hab, sub_self]
      have hk : k = 0 := by
        rcases (mul_eq_zero.mp hk1') with h | h
        · exact h
        · exact absurd h hv1
      refine Prod.ext hab ?_
      have h3 : a.2 - b.2 = 0 := by rw [hk2, hk, zero_mul]
      linarith
    · -- the image lies in `[-t,t]`
      intro w hw
      have hw' : w ∈ wcBox t := hbox w hw
      simp only [wcBox, Finset.mem_product, Finset.mem_Icc] at hw'
      have h : |w.1| ≤ (t : ℤ) := abs_le.mpr hw'.1
      have h2 : (w.1.natAbs : ℤ) ≤ (t : ℤ) := by rwa [Int.natCast_natAbs]
      exact Int.ofNat_le.mp h2
    · -- the image is a single residue class modulo `|v|∞ = |v₁|`
      intro w hw w' hw'
      obtain ⟨k, hk1, _⟩ := hdiff w hw w' hw'
      rw [hk1]
      have hdvd : ((wcSup v : ℕ) : ℤ) ∣ v.1 := by rw [hcmax, Int.natAbs_dvd]
      exact dvd_mul_of_dvd_right hdvd k
  · -- `|v₂| = |v|∞` : project onto the second coordinate.
    have hcmax : wcSup v = v.2.natAbs := hmax
    have hv2 : v.2 ≠ 0 := by
      intro h
      have h0 : v.2.natAbs = 0 := by rw [h]; rfl
      exact hc0 (by rw [hcmax, h0])
    refine wc_card_le_of_image t (wcSup v) hc0 T (fun w => w.2) ?_ ?_ ?_
    · -- injectivity of the second projection on `T`
      intro a ha b hb hab
      obtain ⟨k, hk1, hk2⟩ := hdiff a ha b hb
      change a.2 = b.2 at hab
      have hk2' : k * v.2 = 0 := by rw [← hk2, hab, sub_self]
      have hk : k = 0 := by
        rcases (mul_eq_zero.mp hk2') with h | h
        · exact h
        · exact absurd h hv2
      refine Prod.ext ?_ hab
      have h3 : a.1 - b.1 = 0 := by rw [hk1, hk, zero_mul]
      linarith
    · -- the image lies in `[-t,t]`
      intro w hw
      have hw' : w ∈ wcBox t := hbox w hw
      simp only [wcBox, Finset.mem_product, Finset.mem_Icc] at hw'
      have h : |w.2| ≤ (t : ℤ) := abs_le.mpr hw'.2
      have h2 : (w.2.natAbs : ℤ) ≤ (t : ℤ) := by rwa [Int.natCast_natAbs]
      exact Int.ofNat_le.mp h2
    · -- the image is a single residue class modulo `|v|∞ = |v₂|`
      intro w hw w' hw'
      obtain ⟨k, _, hk2⟩ := hdiff w hw w' hw'
      rw [hk2]
      have hdvd : ((wcSup v : ℕ) : ℤ) ∣ v.2 := by rw [hcmax, Int.natAbs_dvd]
      exact dvd_mul_of_dvd_right hdvd k

end Work.FIArea2.R6
