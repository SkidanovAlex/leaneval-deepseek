import Mathlib
import Submission.Work.WilG1.Cell.Junk.DiscDefs
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG5.Basic
import Submission.Work.WilG1.Basic

set_option autoImplicit false

namespace Work.WilG4c.FibDiscMain

/-- The residue chain of the `Ω`-calculus: the set

  `projN 1 (posESet n ∩ (projN 1 (posDSet n ∩ Xᶜ))ᶜ)`

is `Ω`-definable with a format and degree obtained from those of `X` by *adding* uniform
constants.  Concretely: `Xᶜ` raises the format by one, `posDSet`/`posESet` are positivity sets
of linear polynomials (format `n + 4` resp. `n + 3`, degree `3`), each `inter₂` costs one
format, each projection costs one format, and the degrees only add. -/
theorem fibResChainMem (S : WilkiesDesign.SOMin) (n : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ), ∀ (D : ℕ) (X : Set (Fin (n + 2) → ℝ)) (a : ℕ) (b : Polynomial ℕ),
      X ∈ S.Ω a (b.eval D) (n + 2) →
      Work.WilG5.projN 1 (Work.WilG1.Cell.Junk.posESet n ∩
          (Work.WilG5.projN 1 (Work.WilG1.Cell.Junk.posDSet n ∩ Xᶜ))ᶜ)
        ∈ S.Ω (a + A) ((b + B).eval D) n := by
  refine ⟨2 * n + 15, Polynomial.C 10, fun D X a b hX => ?_⟩
  -- the two tolerance sets, with uniform format/degree
  have hposD : Work.WilG1.Cell.Junk.posDSet n ∈
      S.Ω (n + 4) ((Polynomial.C 3).eval D) (n + 2) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := Work.WilG1.Cell.Junk.aDim n) D
      (MvPolynomial.X (Work.WilG1.Cell.Junk.dIdxA n))
    simpa [Work.WilG1.Cell.Junk.posDSet, Work.WilG1.Cell.Junk.aDim] using h
  have hposE : Work.WilG1.Cell.Junk.posESet n ∈
      S.Ω (n + 3) ((Polynomial.C 3).eval D) (n + 1) := by
    have h := Work.WilG1.Calc.pos_mem (S := S) (m := Work.WilG1.Cell.Junk.bDim n) D
      (MvPolynomial.X (Work.WilG1.Cell.Junk.eIdxB n))
    simpa [Work.WilG1.Cell.Junk.posESet, Work.WilG1.Cell.Junk.bDim] using h
  -- `Xᶜ`
  have h1 : Xᶜ ∈ S.Ω (a + 1) (b.eval D) (n + 2) := S.compl hX
  -- `posDSet n ∩ Xᶜ`
  have h2 : Work.WilG1.Cell.Junk.posDSet n ∩ Xᶜ ∈
      S.Ω (max (n + 4) (a + 1) + 1) ((Polynomial.C 3 + b).eval D) (n + 2) :=
    Work.WilG1.Omega.inter₂ (S := S) hposD h1
  -- `projN 1 (posDSet n ∩ Xᶜ)`
  have h3 : Work.WilG5.projN 1 (Work.WilG1.Cell.Junk.posDSet n ∩ Xᶜ) ∈
      S.Ω (max (n + 4) (a + 1) + 1 + 1) ((Polynomial.C 3 + b).eval D) (n + 1) :=
    Work.WilG5.projN_mem (S := S) (n := n + 1) 1 (max (n + 4) (a + 1) + 1)
      ((Polynomial.C 3 + b).eval D) h2
  -- `(projN 1 (posDSet n ∩ Xᶜ))ᶜ`
  have h4 : (Work.WilG5.projN 1 (Work.WilG1.Cell.Junk.posDSet n ∩ Xᶜ))ᶜ ∈
      S.Ω (max (n + 4) (a + 1) + 1 + 1 + 1) ((Polynomial.C 3 + b).eval D) (n + 1) :=
    S.compl h3
  -- `posESet n ∩ (projN 1 (posDSet n ∩ Xᶜ))ᶜ`
  have h5 : Work.WilG1.Cell.Junk.posESet n ∩
      (Work.WilG5.projN 1 (Work.WilG1.Cell.Junk.posDSet n ∩ Xᶜ))ᶜ ∈
      S.Ω (max (n + 3) (max (n + 4) (a + 1) + 1 + 1 + 1) + 1)
        ((Polynomial.C 3 + (Polynomial.C 3 + b)).eval D) (n + 1) :=
    Work.WilG1.Omega.inter₂ (S := S) hposE h4
  -- the final projection
  have h6 : Work.WilG5.projN 1 (Work.WilG1.Cell.Junk.posESet n ∩
      (Work.WilG5.projN 1 (Work.WilG1.Cell.Junk.posDSet n ∩ Xᶜ))ᶜ) ∈
      S.Ω (max (n + 3) (max (n + 4) (a + 1) + 1 + 1 + 1) + 1 + 1)
        ((Polynomial.C 3 + (Polynomial.C 3 + b)).eval D) n :=
    Work.WilG5.projN_mem (S := S) (n := n) 1
      (max (n + 3) (max (n + 4) (a + 1) + 1 + 1 + 1) + 1)
      ((Polynomial.C 3 + (Polynomial.C 3 + b)).eval D) h5
  refine Work.WilG1.Omega.mono (S := S) h6 ?_ ?_
  · simp only [Nat.max_def]; split <;> split <;> omega
  · simp only [Polynomial.eval_add, Polynomial.eval_C]
    omega

end Work.WilG4c.FibDiscMain
