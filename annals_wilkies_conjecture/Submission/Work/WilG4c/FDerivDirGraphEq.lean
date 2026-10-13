import Mathlib
import Submission.Work.WilG4c.FDerivDirDefs

namespace Work.WilG4c

/-- The graph of the *total* directional derivative `w ↦ fderiv ℝ φ w e` splits as the union of

* the good piece `dirGraphSet N φ e`: where `φ` is differentiable at `Fin.init x` with derivative
  `Lin c`, the total `fderiv` *is* `Lin c` (`HasFDerivAt.fderiv`), so the directional derivative is
  `Lin c e`;
* the bad piece `badGraphSet N φ`: where `φ` is not differentiable at `Fin.init x`, the total
  `fderiv` is `0` (`fderiv_zero_of_not_differentiableAt`), so the directional derivative is `0`. -/
theorem FDerivDirGraphEq (N : ℕ) (φ : (Fin N → ℝ) → ℝ) (e : Fin N → ℝ) :
    WilkiesDesign.graphOf (fun w : Fin N → ℝ => fderiv ℝ φ w e) =
      Work.WilG4c.dirGraphSet N φ e ∪ Work.WilG4c.badGraphSet N φ := by
  classical
  ext x
  simp only [WilkiesDesign.graphOf, Work.WilG4c.dirGraphSet, Work.WilG4c.badGraphSet,
    Set.mem_ofPred_eq, Set.mem_union]
  by_cases h : ∃ c, HasFDerivAt φ (Lin c) (Fin.init x)
  · -- differentiable case: the total `fderiv` is `Lin c` for the derivative `c`
    rcases h with ⟨c, hc⟩
    have hf : fderiv ℝ φ (Fin.init x) = Lin c := hc.fderiv
    rw [hf]
    constructor
    · intro hx; exact Or.inl ⟨c, hc, hx⟩
    · rintro (⟨c', hc', hx⟩ | ⟨hno, _⟩)
      · -- differentiability makes the `Lin`'s agree, so `Lin c' e = Lin c e`
        have hc'' : Lin c' = Lin c := by rw [← hc'.fderiv, hf]
        rwa [hc''] at hx
      · exact absurd ⟨c, hc⟩ hno
  · -- non-differentiable case: the total `fderiv` is `0`
    have hf : fderiv ℝ φ (Fin.init x) = 0 := by
      apply fderiv_zero_of_not_differentiableAt
      intro hd
      obtain ⟨c, hc⟩ := exists_Lin_eq (fderiv ℝ φ (Fin.init x))
      exact h ⟨c, hc ▸ hd.hasFDerivAt⟩
    rw [hf]
    constructor
    · intro hx; exact Or.inr ⟨h, hx⟩
    · rintro (⟨c', hc', _⟩ | ⟨_, hx⟩)
      · exact absurd ⟨c', hc'⟩ h
      · exact hx

end Work.WilG4c
