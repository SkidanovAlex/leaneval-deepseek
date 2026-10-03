import Mathlib
import Submission.Work.FIArea2.card_sq_roots_nat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2.R6

/-- **Counting the solutions of `A z² ≡ B (mod m)` over a complete residue system.** For `m ≠ 0`
and `A B : ℤ`, the number of `z ∈ {0, …, m-1}` with `m ∣ A z² - B` equals the number of
`w : ZMod m` with `(A : ZMod m) * w ^ 2 = (B : ZMod m)`. Proof: the map `w ↦ w.val` is a
bijection from the second solution set onto the first (`Finset.card_bij`, using `ZMod.val_lt`,
`ZMod.val_injective`, `ZMod.val_cast_of_lt`), and it carries `(A) w² = B` to `m ∣ A * w.val² - B`
by `ZMod.intCast_eq_intCast_iff_dvd_sub` (cf. `Work.FIArea2.card_range_filter_sq_mod` in
`Submission/Work/FIArea2/card_sq_roots_nat.lean`, which is the same argument for the right-hand
side `c` instead of `(A) z²`). -/
theorem card_range_filter_dvd_mul_sq (m : ℕ) [NeZero m] (A B : ℤ) :
    ((Finset.range m).filter (fun z : ℕ => (m : ℤ) ∣ A * (z : ℤ) ^ 2 - B)).card
      = ((Finset.univ : Finset (ZMod m)).filter
          (fun z => (A : ZMod m) * z ^ 2 = (B : ZMod m))).card := by
  classical
  symm
  refine Finset.card_bij (fun (z : ZMod m) (_ : z ∈ _) => z.val) ?_ ?_ ?_
  · -- the canonical representative `z.val` of a solution satisfies the divisibility
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt z, ?_⟩
    have h1 : ((A * ((z.val : ℤ) ^ 2) : ℤ) : ZMod m) = (A : ZMod m) * z ^ 2 := by
      nth_rewrite 2 [← ZMod.natCast_zmod_val z]
      push_cast
      ring
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub B (A * (z.val : ℤ) ^ 2) m).mp (by rw [h1, hz])
  · -- `ZMod.val` is injective
    intro z₁ _ z₂ _ h
    exact ZMod.val_injective m h
  · -- every `y` in the range lifts to the residue class `y`
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy
    refine ⟨((y : ℕ) : ZMod m), ?_, ZMod.val_cast_of_lt hy.1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h : ((B : ℤ) : ZMod m) = ((A * (y : ℤ) ^ 2 : ℤ) : ZMod m) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub B (A * (y : ℤ) ^ 2) m).mpr hy.2
    rw [h]
    push_cast
    ring

end Work.FIArea2.R6
