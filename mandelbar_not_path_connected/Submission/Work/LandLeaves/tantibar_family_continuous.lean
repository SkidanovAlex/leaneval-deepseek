import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- The family of iterates `(f, z) ↦ (T_f)^[2k] z` of the antiholomorphic quadratic
`T_f z = (star z)^2 + f` (the tricorn family) is jointly continuous: as a function of `(f,z)`
it is a polynomial in `f, star f, z, star z`.

Proof sketch: the "skew product" `S : ℂ × ℂ → ℂ × ℂ`, `S (f, z) = (f, (star z)^2 + f)`, is
continuous, satisfies `S^[n] (f,z) = (f, (T_f)^[n] z)` by induction on `n`, and
`(fun p : ℂ × ℂ => (T_{p.1})^[2*k] p.2) = Prod.snd ∘ S^[2*k]`. -/
theorem tantibar_family_continuous (k : ℕ) :
    Continuous (fun p : ℂ × ℂ => (LeanEval.ComplexAnalysis.Tantibar p.1)^[2 * k] p.2) := by
  -- Joint continuity of the whole family of iterates `(f,z) ↦ (T_f)^[n] z`, by induction on `n`.
  have h : ∀ n : ℕ, Continuous fun p : ℂ × ℂ => (LeanEval.ComplexAnalysis.Tantibar p.1)^[n] p.2 := by
    intro n
    induction n with
    | zero =>
      -- `(T_f)^[0] z = z`, so the map is `Prod.snd`.
      simpa using (continuous_snd : Continuous (fun p : ℂ × ℂ => p.2))
    | succ n ih =>
      -- `(T_f)^[n+1] z = T_f ((T_f)^[n] z) = (star ((T_f)^[n] z))^2 + f`, a continuous
      -- expression in `(f, (T_f)^[n] z)`, and `(f,z) ↦ (T_f)^[n] z` is continuous by `ih`.
      have key : (fun p : ℂ × ℂ => (LeanEval.ComplexAnalysis.Tantibar p.1)^[n+1] p.2)
          = fun p : ℂ × ℂ =>
              (starRingEnd ℂ ((LeanEval.ComplexAnalysis.Tantibar p.1)^[n] p.2)) ^ 2 + p.1 := by
        funext p
        rw [Function.iterate_succ_apply']
        rfl
      rw [key]
      exact (continuous_star.comp ih).pow 2 |>.add continuous_fst
  exact h (2 * k)

end Work.LandLeaves
