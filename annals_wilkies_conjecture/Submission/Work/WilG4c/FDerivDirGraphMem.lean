import Mathlib
import Submission.Work.WilG4c.SgnEqDefs
import Submission.Work.WilG4c.FDerivDirDefs
import Submission.Work.WilG4c.FDerivDirGraphEq
import Submission.Work.WilG4c.DirGraphSetMem
import Submission.Work.WilG4c.BadGraphSetMem

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG Work.WilG0 Work.WilG1

/-- **The graph of the total directional derivative is `Ω`-definable.**

The graph of `w ↦ fderiv ℝ φ w e` is the union of the good piece `dirGraphSet` (where `φ` is
differentiable and the directional derivative is `Lin c e`) and the bad piece `badGraphSet`
(where it is `0`).  Both pieces are `Ω`-bounded in terms of `epsFDerivSet N φ`: the good piece
by `DirGraphSetMem` (costing `+3` in the degree polynomial: `2` for the diagonal of the
pullback and `1` for the linear hypersurface), the bad piece by `BadGraphSetMem` (costing `+1`
for the hyperplane `x (last N) = 0`).  The union adds the two degree polynomials, whence the
coefficient `m = 2` and offset `c = 4`. -/
theorem FDerivDirGraphMem (S : WilkiesDesign.SOMin) (N : ℕ) (e : Fin N → ℝ) :
    ∃ (K m c : ℕ),
      ∀ (A : ℕ) (b : Polynomial ℕ) (D : ℕ) (φ : (Fin N → ℝ) → ℝ),
        Work.WilG4c.epsFDerivSet N φ ∈ S.Ω A (b.eval D) (N + N) →
        WilkiesDesign.graphOf (fun w : Fin N → ℝ => fderiv ℝ φ w e) ∈
          S.Ω (A + K) ((Polynomial.C m * b + Polynomial.C c).eval D) (N + 1) := by
  obtain ⟨K₁, h₁⟩ := DirGraphSetMem S N e
  obtain ⟨K₂, h₂⟩ := BadGraphSetMem S N
  refine ⟨max K₁ K₂, 2, 4, ?_⟩
  intro A b D φ hE
  -- the good piece, raised to the common format `A + max K₁ K₂`
  have hb₁ : dirGraphSet N φ e ∈
      S.Ω (A + max K₁ K₂) ((b + Polynomial.C 3).eval D) (N + 1) :=
    Omega.mono (h₁ A b D φ hE) (by omega) le_rfl
  -- the bad piece, raised to the same format
  have hb₂ : badGraphSet N φ ∈
      S.Ω (A + max K₁ K₂) ((b + Polynomial.C 1).eval D) (N + 1) :=
    Omega.mono (h₂ A b D φ hE) (by omega) le_rfl
  -- the union of the two pieces is the graph
  have hunion := Omega.union₂ hb₁ hb₂
  rw [FDerivDirGraphEq N φ e]
  refine Omega.mono hunion (le_of_eq (Nat.max_self _)) ?_
  -- degree bookkeeping: `(b + 3) + (b + 1) = 2b + 4`
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  omega

end Work.WilG4c
