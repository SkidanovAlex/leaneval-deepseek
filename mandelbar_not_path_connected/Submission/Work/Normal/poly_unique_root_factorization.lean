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

/-- If the equation `f z = y` has the single solution `z = w` for a polynomial map `f` of
degree `d`, then `f z - y = a * (z - w)^d` for a nonzero constant `a`. -/
theorem poly_unique_root_factorization {d : ℕ} {f : ℂ → ℂ} (hf : IsPolynomialMapOfDegree d f)
    {y w : ℂ} (h : ∀ z, f z = y ↔ z = w) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ z, f z - y = a * (z - w) ^ d := by
  obtain ⟨P, hPd, hP⟩ := hf
  -- `Q := P - C y` is the polynomial whose only zero is `w`, of degree `d`.
  have hQeval : ∀ z, (P - C y).eval z = f z - y := by
    intro z; simp [hP z]
  have hQroot : ∀ z, (P - C y).eval z = 0 ↔ z = w := by
    intro z; rw [hQeval z, sub_eq_zero]; exact h z
  have hQne : P - C y ≠ 0 := by
    intro h0
    have h1 : (P - C y).eval (w + 1) = 0 := by simp [h0]
    have hw : w + 1 = w := (hQroot (w + 1)).mp h1
    simp at hw
  have hnat : (P - C y).natDegree = d := by rw [natDegree_sub_C, hPd]
  -- Over `ℂ` every polynomial splits, and `Q.roots` is a multiset of size `d` in which
  -- every element equals `w`; hence `Q.roots = d • {w}`.
  have hsplit : (P - C y).Splits := IsAlgClosed.splits _
  have hroots : (P - C y).roots = Multiset.replicate d w := by
    have hcard : (P - C y).roots.card = d := by
      rw [← hsplit.natDegree_eq_card_roots, hnat]
    rw [← hcard]
    exact Multiset.eq_replicate_card.mpr
      (fun b hb => (hQroot b).mp ((Polynomial.mem_roots hQne).mp hb))
  have heq : P - C y = C (P - C y).leadingCoeff * (X - C w) ^ d := by
    have hfac := hsplit.eq_prod_roots
    rw [hroots] at hfac
    simpa [Multiset.map_replicate, Multiset.prod_replicate] using hfac
  refine ⟨(P - C y).leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hQne, fun z => ?_⟩
  rw [← hQeval z, heq]
  simp

end Work.Normal
