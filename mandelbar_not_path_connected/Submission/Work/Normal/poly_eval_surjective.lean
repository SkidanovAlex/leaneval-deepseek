import Mathlib
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

open Polynomial

/-- A nonconstant polynomial map `ℂ → ℂ` is surjective (`ℂ` is algebraically closed). -/
theorem poly_eval_surjective {d : ℕ} {f : ℂ → ℂ} (hd : 1 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) : Function.Surjective f := by
  rintro y
  obtain ⟨P, hPd, hP⟩ := hf
  -- `P - C y` is a complex polynomial of degree `d ≥ 1`, hence has a root.
  have hnd : (P - C y).natDegree = d := by rw [natDegree_sub_C, hPd]
  have hpos : 0 < (P - C y).natDegree := by omega
  have hne : P - C y ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hpos
    exact lt_irrefl _ hpos
  have hdeg : (0 : WithBot ℕ) < (P - C y).degree := by
    rw [degree_eq_natDegree hne]
    exact_mod_cast hpos
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  refine ⟨z, ?_⟩
  rw [hP z]
  have hz' : (P - C y).eval z = 0 := hz
  rw [eval_sub, eval_C] at hz'
  exact sub_eq_zero.mp hz'

end Work.Normal
