import Mathlib
import Submission.Work.WilG4c.CellMonoDeriv

namespace Work.WilkG4c

/-- **`HasDerivAt` form of the last-coordinate derivative.** -/
theorem hasDerivAt_snoc {p : ℕ} {g : (Fin (p + 1) → ℝ) → ℝ} {l : Fin p → ℝ} {s : ℝ}
    (hg : DifferentiableAt ℝ g (Fin.snoc l s)) :
    HasDerivAt (fun s' : ℝ => g (Fin.snoc l s'))
      (fderiv ℝ g (Fin.snoc l s) (Pi.single (Fin.last p) (1 : ℝ))) s := by
  -- The map `s' ↦ Fin.snoc l s'` is the affine map `s' ↦ Function.update (Fin.snoc l s) (last p) s'`,
  -- whose derivative at `s` is the last basis vector `Pi.single (Fin.last p) 1`.
  have key : HasDerivAt (fun s' : ℝ => Fin.snoc l s')
      (Pi.single (Fin.last p) (1 : ℝ) : Fin (p + 1) → ℝ) s := by
    have hupd : HasDerivAt (fun s' : ℝ => Function.update (Fin.snoc l s) (Fin.last p) s')
        (Pi.single (Fin.last p) (1 : ℝ) : Fin (p + 1) → ℝ) s := by
      rw [hasDerivAt_pi]
      intro i
      by_cases h : i = Fin.last p
      · subst h
        simp only [Function.update_apply, Pi.single_eq_same, ↓reduceIte]
        exact hasDerivAt_id s
      · simp only [Function.update_of_ne h, Pi.single_eq_of_ne (M := fun _ => ℝ) h (1 : ℝ)]
        exact hasDerivAt_const s _
    simpa only [Fin.update_snoc_last] using hupd
  -- Chain rule with the Fréchet derivative of `g`.
  exact hg.hasFDerivAt.comp_hasDerivAt s key

end Work.WilkG4c
