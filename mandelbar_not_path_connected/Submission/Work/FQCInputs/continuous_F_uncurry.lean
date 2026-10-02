import Mathlib
import Submission.Work.FQCInputs.Defs
import Submission.Work.FQCInputs.continuous_iteratedDeriv_two_F

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FQCInputs

/-- `Work.Landing.Tsq c = fun z => (z^2 + conj c)^2 + c` is jointly continuous in `(c, z)`. -/
theorem continuous_uncurry_Tsq :
    Continuous fun q : ℂ × ℂ => Work.Landing.Tsq q.1 q.2 := by
  simp only [Work.Landing.Tsq]
  exact (((continuous_snd.pow 2).add (continuous_star.comp continuous_fst)).pow 2).add
    continuous_fst

/-- **`Work.EL.F` is jointly continuous.**  Since `Work.EL.F c = (Work.Landing.Tsq c)^[5]`, the
uncurried map `(c, z) ↦ (Tsq c)^[5] z` is the second component of the `5`-fold iterate of the
continuous self-map `G q = (q.1, Tsq q.1 q.2)` of `ℂ × ℂ`. -/
theorem continuous_F_uncurry : Continuous fun q : ℂ × ℂ => Work.EL.F q.1 q.2 := by
  have hG : Continuous fun q : ℂ × ℂ => (q.1, Work.Landing.Tsq q.1 q.2) :=
    continuous_fst.prodMk continuous_uncurry_Tsq
  have hΦ : ∀ n, Continuous fun q : ℂ × ℂ => (Work.Landing.Tsq q.1)^[n] q.2 := by
    intro n
    induction n with
    | zero => simpa using continuous_snd
    | succ n ih =>
      have hthis : (fun q : ℂ × ℂ => (Work.Landing.Tsq q.1)^[n.succ] q.2)
          = fun q : ℂ × ℂ => (Work.Landing.Tsq q.1)^[n] (Work.Landing.Tsq q.1 q.2) := by
        funext q
        rw [Function.iterate_succ_apply]
      rw [hthis]
      exact ih.comp hG
  have h5 := hΦ 5
  simpa [Work.EL.F] using h5

end Work.FQCInputs
