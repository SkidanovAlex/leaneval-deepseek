import Mathlib
import Submission.Work.WilG4c.IterDirAux

namespace Work.WilG4c

open Work.WilkG4c

/-- **Two outermost derivatives commute.** If `H` is `C²` at `z`, then the iterated directional
derivative along `[a, b]` agrees with the one along `[b, a]` (Clairaut/Schwarz). This is the
analytic heart of `iterDir_swap`, isolated so that it can be applied to `H = iterDir M G`:
unfolding, the two sides are `∂ₐ(∂_b H)(z)` and `∂_b(∂ₐ H)(z)`, both of which are the second
Fréchet derivative of `H` at `z` evaluated on `(eₐ, e_b)` resp. `(e_b, eₐ)` — see `key` below —
and the second derivative of a `C²` function is symmetric. -/
theorem iterDir_pair_swap {m : ℕ} (H : (Fin m → ℝ) → ℝ) (a b : Fin m) (z : Fin m → ℝ)
    (hH : ContDiffAt ℝ 2 H z) :
    Work.WilkG4c.iterDir [a, b] H z = Work.WilkG4c.iterDir [b, a] H z := by
  simp only [iterDir_cons, iterDir_nil]
  have hdiff : DifferentiableAt ℝ (fderiv ℝ H) z :=
    (hH.fderiv_right (m := (1 : WithTop ℕ∞)) (by norm_num)).differentiableAt one_ne_zero
  -- the derivative of the evaluation `y ↦ fderiv H y v` is the second derivative of `H`
  have key : ∀ (v w : Fin m → ℝ),
      fderiv ℝ (fun y => (fderiv ℝ H y) v) z w = (fderiv ℝ (fderiv ℝ H) z w) v := by
    intro v w
    rw [fderiv_clm_apply (c := fderiv ℝ H) (u := fun _ : Fin m → ℝ => v) hdiff
      (differentiableAt_const v)]
    simp [ContinuousLinearMap.flip_apply]
  rw [key (Pi.single b 1) (Pi.single a 1), key (Pi.single a 1) (Pi.single b 1)]
  exact (hH.isSymmSndFDerivAt (by norm_num)).eq (Pi.single a 1) (Pi.single b 1)

/-- **Adjacent transposition.** For a function `G` that is `C^{|M|+2}` at `z`, the iterated
directional derivative (of `Submission/Work/WilG4c/Engine.lean`) along `a :: b :: M` equals
that along `b :: a :: M`: the two outermost partial derivatives commute (Clairaut/Schwarz). -/
theorem iterDir_swap {m : ℕ} (G : (Fin m → ℝ) → ℝ) (a b : Fin m) (M : List (Fin m))
    (z : Fin m → ℝ) (hG : ContDiffAt ℝ (M.length + 2) G z) :
    Work.WilkG4c.iterDir (a :: b :: M) G z = Work.WilkG4c.iterDir (b :: a :: M) G z := by
  have hH : ContDiffAt ℝ 2 (Work.WilkG4c.iterDir M G) z :=
    Work.WilG4c.iterDir_contDiffAt G M 2 z (by simpa using hG)
  have e₁ : Work.WilkG4c.iterDir (a :: b :: M) G z =
      Work.WilkG4c.iterDir [a, b] (Work.WilkG4c.iterDir M G) z := by
    simp only [iterDir_cons, iterDir_nil]
  have e₂ : Work.WilkG4c.iterDir (b :: a :: M) G z =
      Work.WilkG4c.iterDir [b, a] (Work.WilkG4c.iterDir M G) z := by
    simp only [iterDir_cons, iterDir_nil]
  rw [e₁, e₂]
  exact iterDir_pair_swap (Work.WilkG4c.iterDir M G) a b z hH

end Work.WilG4c
