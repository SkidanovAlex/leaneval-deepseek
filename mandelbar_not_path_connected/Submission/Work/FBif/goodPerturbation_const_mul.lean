import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

theorem goodPerturbation_const_mul {c z₁ : ℂ} {q : ℂ → ℂ}
    (h : Work.FBif.GoodPerturbation c z₁ q) {lam : ℝ} (hlam : ¬ (lam = 0)) :
    Work.FBif.GoodPerturbation c z₁ (fun z => (lam : ℂ) * q z) := by
  obtain ⟨P, hrep, hdiv, hdiv4, hne⟩ := h
  refine ⟨Polynomial.C (lam : ℂ) * P, ?_, ?_, ?_, ?_⟩
  · intro z
    show (lam : ℂ) * q z = Polynomial.eval (star z) (Polynomial.C (lam : ℂ) * P)
    rw [Polynomial.eval_mul, Polynomial.eval_C, hrep z]
  · intro j hj
    exact dvd_mul_of_dvd_right (hdiv j hj) _
  · have h1 : Polynomial.C ((Polynomial.C (lam : ℂ) * P).eval (star (cyclePt c z₁ 4)))
        = Polynomial.C (lam : ℂ) * Polynomial.C (P.eval (star (cyclePt c z₁ 4))) := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.C_mul]
    rw [h1, ← mul_sub]
    exact dvd_mul_of_dvd_right hdiv4 _
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hlam) hne

end Work.FBif
