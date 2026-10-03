import Mathlib
import Submission.Work.Peluse.SwapE.linearInLawAux

namespace Work.Peluse.SwapE

/-- Translating the argument of a `tsum` over `ℤ` does not change its value. -/
private lemma tsum_comp_addRight (g : ℤ → ℂ) (c : ℤ) :
    (∑' x : ℤ, g (x + c)) = ∑' y : ℤ, g y :=
  Equiv.tsum_eq (Equiv.addRight c) g

/-- The `ω`-corner of the cube with increment `u - v` and lower corner `0`, translated by the
total shift `∑ i, v i`, is the `ω`-corner of the cube with increment `u` and lower corner `v`:
`∑_{i ∈ ω} (u i) + ∑_{i ∉ ω} (v i) = ∑ i, v i + ∑_{i ∈ ω} (u i - v i)`. -/
private lemma cornerShift_eq_shift (d : ℕ) (u v : Fin d → ℤ) (ω : Fin d → Bool) :
    Work.Peluse.cornerShift u v ω
      = Work.Peluse.cornerShift (u - v) (0 : Fin d → ℤ) ω + ∑ i, v i := by
  simp only [Work.Peluse.cornerShift]
  have hpt : ∀ i : Fin d, (if ω i then u i else v i)
      = (if ω i then (u - v) i else 0) + v i := by
    intro i
    by_cases h : ω i
    · simp [h, Pi.sub_apply]
    · simp [h]
  calc ∑ i, (if ω i then u i else v i)
      = ∑ i, ((if ω i then (u - v) i else 0) + v i) :=
        Finset.sum_congr rfl (fun i _ => hpt i)
    _ = (∑ i, (if ω i then (u - v) i else 0)) + ∑ i, v i := Finset.sum_add_distrib

/-- **The cube mass only depends on the difference of the two slot vectors.**  The `∑' x` of the
cube term with increment `u` and lower corner `v` equals the un-normalised cube mass
`cubeMassRaw d f (u - v)`, because `cornerShift u v ω = cornerShift (u - v) 0 ω + ∑ i, v i` and
the sum over `x` is invariant under the translation `x ↦ x + ∑ i, v i`. -/
theorem cubeMassRaw_shift {d : ℕ} (f : ℤ → ℂ) (u v : Fin d → ℤ) :
    (tsum (fun x : ℤ => Finset.univ.prod (fun ω : Fin d → Bool =>
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift u v ω)))))
      = Work.Peluse.SwapE.cubeMassRaw d f (u - v) := by
  classical
  simp only [Work.Peluse.SwapE.cubeMassRaw]
  rw [show (∑' x : ℤ, ∏ ω : Fin d → Bool,
        (star^[Work.Peluse.weight ω]) (f (x + Work.Peluse.cornerShift u v ω)))
      = ∑' x : ℤ, ∏ ω : Fin d → Bool,
        (star^[Work.Peluse.weight ω])
          (f ((x + ∑ i, v i) + Work.Peluse.cornerShift (u - v) (0 : Fin d → ℤ) ω))
      from by
        apply tsum_congr; intro x
        apply Finset.prod_congr rfl; intro ω _
        congr 1
        rw [cornerShift_eq_shift]
        ring_nf]
  exact tsum_comp_addRight
    (fun y : ℤ => ∏ ω : Fin d → Bool,
      (star^[Work.Peluse.weight ω])
        (f (y + Work.Peluse.cornerShift (u - v) (0 : Fin d → ℤ) ω)))
    (∑ i, v i)

end Work.Peluse.SwapE
